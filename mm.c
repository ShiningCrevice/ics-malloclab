/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


// #define VERBOSE
#ifdef VERBOSE
# define vb_printf(...) printf(__VA_ARGS__)
#else
# define vb_printf(...)
#endif

/* Constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */
#define N_SIZECLASS 12 /* number of the size classes */

#define MAX(a, b) (a > b ? a : b)
#define MIN(a, b) (a < b ? a : b)

/* Read a word at address p */
#define GET(p) (*(unsigned int *)(p))
/* Write a word at address p */
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Pack a size and allocated bits into a word */
/* `palloc` - prev block's alloc */
#define PACK(size, alloc, palloc) ((size) | (alloc) | (palloc))

/* Read the size from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
/* Read allocated fields from address p */
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PALLOC(p) (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header */
#define HDRP(bp) ((char *)(bp) - WSIZE)
/* Given block ptr bp, compute address of its footer */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
/* Given block ptr bp, compute address of previous blocks */
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Used in explicit free list */
/* Given free block ptr fbp, compute address of its pred-offset */
#define PRED_OFFP(fbp) ((char *)(fbp))
/* Given free block ptr fbp, compute address of its succ-offset */
#define SUCC_OFFP(fbp) ((char *)(fbp) + WSIZE)
/* Given free block ptr fbp, compute address of predecessor */
#define PRED(fbp) ((char *)(fbp) + *(int *)(PRED_OFFP(fbp)))
/* Given free block ptr fbp, compute address of successor */
#define SUCC(fbp) ((char *)(fbp) + *(int *)(SUCC_OFFP(fbp)))
/* Compute the offset from fbp1 to fbp2 */
#define OFFSET(fbp1, fbp2) ((int)((char *)(fbp2) - (char *)(fbp1)))

/* Used in segretated free list */
/* compute address of offset of the i-th size class */
#define HEAD_OFFP(i) ((char *)(heads) + i*WSIZE)
/* compute head ptr to the i-th size class */
#define HEAD(i) (*(int *)(HEAD_OFFP(i)) == 0 ? NULL : (char *)(heap_listp) + *(int *)(HEAD_OFFP(i)))

/* Global variables */
/* ptr to prologue */
static void *heap_listp = NULL;
/* ptr to header of epilogue */
static void *epi_hdr = NULL;
/* ptr to heads of segretated free list */
static void *heads = NULL;

/* Helper routines */
static void *extend_heap(size_t words, int palloc);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void insert_fb(void *fbp);
static void delete_fb(void *fbp);
static void vb_checklist(void);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    vb_printf("mm_init(): called\n");

    heap_listp = NULL;
    epi_hdr = NULL;
    heads = NULL;

    int padding = N_SIZECLASS%2 ? 0 : 1;
    heads = mem_sbrk((3 + N_SIZECLASS + padding) * WSIZE);
    if (heads == (void *)-1)
        return -1;
    
    for (int i=0; i<N_SIZECLASS; ++i)
        PUT(HEAD_OFFP(i), 0); /* heads of size classes */

    heap_listp = heads + (N_SIZECLASS + padding) * WSIZE;
    if (padding)
        PUT(heap_listp - 1 * WSIZE, 0);
    PUT(heap_listp, PACK(DSIZE, 1, 2)); /* prologue header */
    PUT(heap_listp + 1 * WSIZE, 0); /* prologue padding */
    PUT(heap_listp + 2 * WSIZE, PACK(0, 1, 2)); /* epilogue header */

    heap_listp += 1 * WSIZE; /* point to prologue */
    
    vb_printf("mm_init(): heads = %p, heap_listp = %p\n", heads, heap_listp);

    void *fbp = extend_heap(CHUNKSIZE / WSIZE, 2);
    if (fbp == NULL) /* fail */
        return -1;
    /* suceed */
    insert_fb(fbp);

    vb_printf("mm_init(): epi_hdr = %p\n", epi_hdr);
#ifdef DEBUG
    mm_checkheap(__LINE__);
#endif
    vb_printf("\n");
    return 0;
}

/*
 * malloc
 */
void *malloc(size_t size) {
    vb_printf("malloc(%#lx): called\n", size);

    if (heap_listp == NULL)
        mem_init();

    if (size == 0)
        return NULL;
    
    size_t asize = MAX(ALIGN(size + WSIZE), 2*DSIZE); /* adjust block size */
    void *bp = find_fit(asize);

    if (bp != NULL) { /* found */
        place(bp, asize);
    } else { /* not found, extend heap */
        size_t esize = MAX(asize, CHUNKSIZE); /* size to extend */
        int epalloc = GET_PALLOC(epi_hdr);
        bp = extend_heap(esize / WSIZE, epalloc);
        if (bp == NULL) /* fail */
            return NULL;

        insert_fb(bp);

        place(bp, asize);
    }
    
    vb_printf("malloc(%#lx): will return %p\n", size, bp);
#ifdef DEBUG
    mm_checkheap(__LINE__);
#endif

    vb_printf("\n");
    return bp;
}

/*
 * free - using LIFO order
 */
void free(void *ptr) {
    vb_printf("free(%p): called\n", ptr);

    if(ptr == NULL)
        return;

    if (heap_listp == NULL)
        mem_init();

    size_t size = GET_SIZE(HDRP(ptr));
    int palloc = GET_PALLOC(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0, palloc));
    PUT(FTRP(ptr), PACK(size, 0, palloc));

    size_t nsize = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    int nalloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(nsize, nalloc, 0));

    ptr = coalesce(ptr);

    insert_fb(ptr);

#ifdef DEBUG
    mm_checkheap(__LINE__);
#endif
    vb_printf("\n");
}

/*
 * realloc - naive version
 */
void *realloc(void *oldptr, size_t size) {
    if (size == 0) {
        mm_free(oldptr);
        return NULL;
    }

    if (oldptr == NULL)
        return malloc(size);

    void *newptr = malloc(size);
    if (newptr == NULL)
        return NULL;

    size_t oldsize = GET_SIZE(HDRP(oldptr));
    memcpy(newptr, oldptr, MIN(size, oldsize));

    mm_free(oldptr);

    return newptr;
}

/*
 * calloc - naive version
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr = malloc(bytes);

    memset(newptr, 0, bytes);

    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
    // vb_printf("\tcheck(%d): called\n", lineno);

    /* check prologue and epilogue blocks */
    if (!in_heap(heap_listp) || GET_ALLOC(HDRP(heap_listp)) != 1 || 
        GET_SIZE(HDRP(heap_listp)) != DSIZE || GET_PALLOC(HDRP(heap_listp)) != 2) {
        dbg_printf("line %d: prologue error\n", lineno);
        exit(1);
    }
    if (!in_heap(epi_hdr) || GET_ALLOC(epi_hdr) != 1 || 
        GET_SIZE(epi_hdr) != 0) {
        dbg_printf("line %d: epilogue error\n", lineno);
        exit(1);
    }

    /* count free blocks by 2 ways */
    size_t cnt1 = 0, cnt2 = 0;

    /* check each block by address order */
    void *ptr = heap_listp;
    while (GET_SIZE(HDRP(ptr)) != 0) {
        if (GET_ALLOC(HDRP(ptr)) == 0)
            ++cnt1;
        
        if (!aligned(ptr)) {
            dbg_printf("line %d: block %p not aligned\n", lineno, ptr);
            exit(1);
        }
        if (GET_ALLOC(HDRP(ptr)) == 0 && *(unsigned int *)(HDRP(ptr)) != *(unsigned int *)(FTRP(ptr))) {
            dbg_printf("line %d: block %p head-foot inconsistent\n"
                "\tblock %p: head: %#x foot: %#x\n", lineno, ptr, ptr, 
                *(unsigned int *)(HDRP(ptr)), *(unsigned int *)(FTRP(ptr)));
            exit(1);
        }
        if (GET_ALLOC(HDRP(ptr)) == 0 && GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0) {
            dbg_printf("line %d: block %p & %p not coalensced\n", lineno, ptr, NEXT_BLKP(ptr));
            exit(1);
        }
        if (!GET_ALLOC(HDRP(ptr)) != !GET_PALLOC(HDRP(NEXT_BLKP(ptr)))) {
            dbg_printf("line %d: block %p & %p header inconsistent\n", lineno, ptr, NEXT_BLKP(ptr));
            exit(1);
        }

        ptr = NEXT_BLKP(ptr);
    }

    /* check each free block in each list */
    for (int i=0; i<N_SIZECLASS; ++i) {
        void *head = HEAD(i);
        if (head != NULL) {
            // vb_printf("\tcheck(%d): head = %p\n", lineno, head);

            ptr = head;
            ++cnt2;
            if (!in_heap(ptr)) {
                dbg_printf("line %d: fb %p not in heap\n", lineno, ptr);
                exit(1);
            }
            if (SUCC(PRED(ptr)) != ptr) {
                dbg_printf("line %d: fb %p not matching its pred\n", lineno, ptr);
                exit(1);
            }
            if (PRED(SUCC(ptr)) != ptr) {
                dbg_printf("line %d: fb %p not matching its succ\n", lineno, ptr);
                exit(1);
            }
            ptr = SUCC(ptr);
            while (ptr != head) {
                ++cnt2;
                if (!in_heap(ptr)) {
                    dbg_printf("line %d: fb %p not in heap\n", lineno, ptr);
                    exit(1);
                }
                if (SUCC(PRED(ptr)) != ptr) {
                    dbg_printf("line %d: fb %p not matching its pred\n", lineno, ptr);
                    exit(1);
                }
                if (PRED(SUCC(ptr)) != ptr) {
                    dbg_printf("line %d: fb %p not matching its succ\n", lineno, ptr);
                    exit(1);
                }

                ptr = SUCC(ptr);
            }
        }
    }

    /* check cnt1-cnt2 consistency */
    if (cnt1 != cnt2) {
        dbg_printf("line %d: counts of fbs differ (%lu : %lu)\n", lineno, cnt1, cnt2);
        exit(1);
    }

}



/**
 * Helper routines
*/

/**
 * extend_heap - extend the heap by `words` bytes.
 * Return the block ptr extended. (May coalesced)
 * 
 * NOT add the extended block to list yet.
*/
static void *extend_heap(size_t words, int palloc) {
    size_t size = (words%2 ? words+1 : words) * WSIZE;

    void *bp = mem_sbrk(size);
    if (bp == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0, palloc));
    PUT(FTRP(bp), PACK(size, 0, palloc));
    epi_hdr = HDRP(NEXT_BLKP(bp));
    PUT(epi_hdr, PACK(0, 1, 0)); /* new epilogue header */

    vb_printf("\textend_heap(%#lx): epi_hdr = %p\n", words, epi_hdr);

    return coalesce(bp);
}

/**
 * place - allocate a block
 * 
 * WILL update the free block lists
*/
static void place(void *bp, size_t asize) {
    vb_printf("\tplace(%p, %#lx): called\n", bp, asize);

    size_t csize = GET_SIZE(HDRP(bp));
    // int palloc = GET_PALLOC(HDRP(bp));

    delete_fb(bp);

    if ((csize - asize) >= (2*DSIZE)) { /* split */
        PUT(HDRP(bp), PACK(asize, 1, 2));
        // PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0, 2));
        PUT(FTRP(bp), PACK(csize-asize, 0, 2));

        insert_fb(bp);
        
    } else { /* no split */
        PUT(HDRP(bp), PACK(csize, 1, 2));
        // PUT(FTRP(bp), PACK(csize, 1));
        size_t nsize = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(nsize, 1, 2));
    }
}

/**
 * find_fit - first-fit, segretated free list
*/
static void *find_fit(size_t asize) {
    int i = 0;
    size_t ruler = 2 * DSIZE;
    while (i < N_SIZECLASS-1 && asize > ruler) {
        ++i;
        ruler <<= 1;
    }
    void *head;

    // vb_printf("\tfind_fit(%#lx): head = %p\n", asize, head);

    while (i < N_SIZECLASS) {
        head = HEAD(i);

        if (head == NULL) {
            ++i;
            continue;
        }

        if (!GET_ALLOC(HDRP(head)) && asize <= GET_SIZE(HDRP(head)))
            return head;

        void *fbp = SUCC(head);
        while (fbp != head) {
            if (!GET_ALLOC(HDRP(fbp)) && asize <= GET_SIZE(HDRP(fbp)))
                return fbp;
            fbp = SUCC(fbp);
        }

        ++i;
    }

    /* not found */
    vb_printf("\tfind_fit(%#lx): not found\n", asize);
    return NULL;
}

/**
 * coalesce - coalesce the prev/next blocks if possible
 * 
 * WILL delete the coalesced blocks from the list.
 * NOT add the new block to the list yet.
*/
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_PALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;

    } else if (prev_alloc && !next_alloc) {      /* Case 2 */
        vb_printf("\tcoalesce(%p): will coalesce next\n", bp);

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_fb(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0, prev_alloc));
        PUT(FTRP(bp), PACK(size, 0, prev_alloc));

    } else if (!prev_alloc && next_alloc) {      /* Case 3 */
        vb_printf("\tcoalesce(%p): will coalesce prev\n", bp);
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        int ppalloc = GET_PALLOC(HDRP(PREV_BLKP(bp)));
        delete_fb(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0, ppalloc));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, ppalloc));

        bp = PREV_BLKP(bp);

    } else {                                     /* Case 4 */
        vb_printf("\tcoalesce(%p): will coalesce prev & next\n", bp);
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        int ppalloc = GET_PALLOC(HDRP(PREV_BLKP(bp)));
        delete_fb(PREV_BLKP(bp));
        delete_fb(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, ppalloc));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0, ppalloc));

        bp = PREV_BLKP(bp);
    }

    return bp;
}

/**
 * insert_fb - insert a free block at head
*/
static void insert_fb(void *fbp) {

    size_t size = GET_SIZE(HDRP(fbp));
    int i = 0;
    size_t ruler = 2 * DSIZE;
    while (i < N_SIZECLASS-1 && size > ruler) {
        ++i;
        ruler <<= 1;
    }
    void *head = HEAD(i);

    vb_printf("\t\tinsert_fb(%p): size = %#lx, head[%d] = %p\n", fbp, size, i, head);

    if (head == NULL) {
        // head = fbp;
        PUT(HEAD_OFFP(i), OFFSET(heap_listp, fbp));
        PUT(PRED_OFFP(fbp), 0);
        PUT(SUCC_OFFP(fbp), 0);

    } else {
        /* insert to tail of list */
        void *pred = PRED(head), *succ = head;
        PUT(PRED_OFFP(fbp), OFFSET(fbp, pred));
        PUT(SUCC_OFFP(pred), OFFSET(pred, fbp));
        PUT(SUCC_OFFP(fbp), OFFSET(fbp, succ));
        PUT(PRED_OFFP(succ), OFFSET(succ, fbp));
    }

#ifdef VERBOSE
    // vb_checklist();
#endif

#ifdef DEBUG
    mm_checkheap(__LINE__);
#endif
}

/**
 * delete_fb - delete a free block from list
 * 
 * Usually called when the block is coalesced.
*/
static void delete_fb(void *fbp) {
    size_t size = GET_SIZE(HDRP(fbp));
    int i = 0;
    size_t ruler = 2 * DSIZE;
    while (i < N_SIZECLASS-1 && size > ruler) {
        ++i;
        ruler <<= 1;
    }
    void *head = HEAD(i);

    vb_printf("\t\tdelete_fb(%p): size = %#lx, head[%d] = %p\n", fbp, size, i, head);

    if (fbp == head) {
        if (SUCC(fbp) == head) {
            // head = NULL;
            PUT(HEAD_OFFP(i), 0);

#ifdef VERBOSE
            // vb_checklist();
#endif
            return;
        }

        // head = SUCC(fbp);
        PUT(HEAD_OFFP(i), OFFSET(heap_listp, SUCC(fbp)));
    }

    void *pred = PRED(fbp), *succ = SUCC(fbp);
    PUT(SUCC_OFFP(pred), OFFSET(pred, succ));
    PUT(PRED_OFFP(succ), OFFSET(succ, pred));

#ifdef VERBOSE
    // vb_checklist();
#endif
}

/**
 * vb_checklist - print the whole list
 * 
 * Called by insert_fb & delete_fb when `VERBOSE` is defined.
*/
static void vb_checklist(void) {
    vb_printf("\t\t\tvb_checklist(): called\n");

    for (int i=0; i<N_SIZECLASS; ++i) {
        void *head = HEAD(i);

        if (head == NULL) {
            vb_printf("\t\t\thead[%d] = NULL\n", i);
            return;
        }

        vb_printf("\t\t\tlist[%d][0] = %p (head)\n", i, head);

        void *ptr = SUCC(head);
        size_t j = 1;
        while (ptr != head) {
            vb_printf("\t\t\tlist[%d][%lu] = %p\n", i, j, ptr);
            ++j;
            ptr = SUCC(ptr);
        }
    }
}
