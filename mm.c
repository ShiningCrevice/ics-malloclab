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
#define DEBUG
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

/* constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */

#define MAX(a, b) (a > b ? a : b)
#define MIN(a, b) (a < b ? a : b)

/* Read a word at address p */
#define GET(p) (*(unsigned int *)(p))
/* Write a word at address p */
#define PUT(p, val) (*(unsigned int *)(p) = (val))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))
/* Read the size from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
/* Read allocated fields from address p */
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header */
#define HDRP(bp) ((char *)(bp) - WSIZE)
/* Given block ptr bp, compute address of its footer */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* Given block ptr bp, compute address of next blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
/* Given block ptr bp, compute address of previous blocks */
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* global variables */
static void *heap_listp = 0;

/* helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    heap_listp = mem_sbrk(4*WSIZE);
    if (heap_listp == (void *)-1)
        return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1)); /* prologue header */
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1)); /* prologue footer */
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1)); /* epilogue header */

    heap_listp += 2 * WSIZE; /* point to prologue's footer */

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    if (heap_listp == NULL)
        mem_init();

    if (size == 0)
        return NULL;
    
    size_t asize = ALIGN(size + DSIZE); /* adjust block size */
    void *bp = find_fit(asize);
    /* found */
    if (bp != NULL) {
        place(bp, asize);
        return bp;
    }

    /* not found, extend heap */
    size_t esize = MAX(asize, CHUNKSIZE); /* size to extend */
    bp = extend_heap(esize / WSIZE);
    /* fail */
    if (bp == NULL)
        return NULL;
    /* succeed */
    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    if(ptr == NULL)
        return;

    if (heap_listp == NULL)
        mem_init();

    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
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
        return mm_malloc(size);

    void *newptr = mm_malloc(size);
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
}



/**
 * helper routines
*/

static void *extend_heap(size_t words) {
    size_t size = (words%2 ? words+1 : words) * WSIZE;

    void *bp = mem_sbrk(size);
    if (bp == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    return coalesce(bp);
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (2*DSIZE)) { /* split */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else { /* padding 1*DSIZE */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/**
 * find_fit - first-fit
*/
static void *find_fit(size_t asize) {
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp; /* found */
    }
    /* not found */
    return NULL;
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;

    } else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));

    } else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

    } else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}
