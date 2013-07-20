/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 *
 * Name: Xiao Li
 * Andrew ID: xiaol2
 * Summer 2013
 *
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
#ifndef DEBUG
#define DEBUG 0
#endif

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

/*********************/
/*
 ATTENTION, bp, heap_listp is (char *)
                    */
/*********************/
/* single word (4) or double word (8) alignment */
#define WSIZE     8
#define DSIZE     16
#define ALIGNMENT 8

#define CHUNKSIZE   (1 << 12) /* 4096? why? */

#define MAX(x, y) (((x) > (y))? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

/* RW a Word at address p, x64 WSIZE = 8 */
#define GET(p)          (*(unsigned long *)(p))
#define PUT(p, val)     (*(unsigned long *)(p) = (val))

/* Read header and footer information, !!!ATTENTION!!! GET_SIZE/ALLOC ONLY work for header and footer */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* bp points to one wsize after header, !!!ATTENTION!!! footer called header, therefore header better be set beforehand */
#define GET_HEADER(bp)  ((char *)(bp) - WSIZE)
#define GET_FOOTER(bp)  ((char *)(bp) + GET_SIZE(GET_HEADER(bp)) - DSIZE)

/* Prv block is stored in prev footer */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Helper functions*/
static char *heap_listp = NULL;

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


/* First hit policy */
static void *find_fit(size_t asize) {
    
    char *bp = heap_listp;
    
    while (GET_SIZE(GET_HEADER(NEXT_BLKP(bp))) > 0) {
        bp = NEXT_BLKP(bp);
        if ((GET_SIZE(GET_HEADER(bp)) >= asize) && !(GET_ALLOC(GET_HEADER(bp)))) {
            return bp;
        }
    }
    
    return NULL;
    
}

/* Place an ADJUSTED sized block in heap */
static void place(void *bp, size_t asize) {
    
    /* block free size */
    size_t csize = GET_SIZE(GET_HEADER(bp));
    
    /* Split, say, minimum block size set to 1 WSIZE = 8 byte */
    if ((csize - asize) >= (3 * WSIZE)) {
        PUT(GET_HEADER(bp), PACK(asize, 1));
        PUT(GET_FOOTER(bp), PACK(asize, 1));
        
        PUT(GET_HEADER(NEXT_BLKP(bp)), PACK((csize - asize), 0));
        PUT(GET_FOOTER(NEXT_BLKP(bp)), PACK((csize - asize), 0));
        
    }
    else {
        PUT(GET_HEADER(bp), PACK(csize, 1));
        PUT(GET_FOOTER(bp), PACK(csize, 1));
    }
}

static void *coalesce(void *bp) {
    
    void *prevbp = PREV_BLKP(bp);
    void *nextbp = NEXT_BLKP(bp);
    
    size_t prev_alloc = GET_ALLOC(GET_FOOTER(prevbp));
    size_t next_alloc = GET_ALLOC(GET_HEADER(nextbp));
    size_t bsize = GET_SIZE(GET_HEADER(bp));
    
    if (prev_alloc && next_alloc) {
        return bp;
    }
    /* next block is free */
    else if (prev_alloc && !next_alloc) {
        bsize += GET_SIZE(GET_HEADER(nextbp));
        PUT(GET_HEADER(bp), PACK(bsize, 0));
        PUT(GET_FOOTER(bp), PACK(bsize, 0));
    }
    /* prev block is free */
    else if (!prev_alloc && next_alloc) {
        bsize += GET_SIZE(GET_HEADER(prevbp));
        PUT(GET_HEADER(prevbp), PACK(bsize, 0));
        PUT(GET_FOOTER(bp), PACK(bsize, 0));
        bp = prevbp;
    }
    /* both blocks are free */
    else {
        bsize += GET_SIZE(GET_HEADER(nextbp));
        bsize += GET_SIZE(GET_FOOTER(prevbp));
        PUT(GET_HEADER(prevbp), PACK(bsize, 0));
        PUT(GET_FOOTER(nextbp), PACK(bsize, 0));
        bp = prevbp;
    }
    
    return bp;
}

/* extend heap by number of words */
static void *extend_heap(int words) {
    
    char *bp; /* block pointer */
    int bsize; /* block size to extend */
    
    /* Allocate even number of words to maintain alignment */
    bsize = (words % 2) ? ((words + 1) * WSIZE) : (words * WSIZE);
    
    if ((long)(bp = mem_sbrk(bsize)) == -1) 
        return NULL;
    
    /* Init free block header/footer and the epilogue header */
    PUT(GET_HEADER(bp), PACK(bsize, 0));
    PUT(GET_FOOTER(bp), PACK(bsize, 0));
    PUT(GET_HEADER(NEXT_BLKP(bp)), PACK(0, 1));
    
#if DEBUG
    dbg_printf("In extend heap!\n");
    mm_checkheap(8);
#endif
    
    return coalesce(bp);
}


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    /* Try mm_init with sbrk*/
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += 2 * WSIZE;
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    
#if DEBUG
    dbg_printf("HEAP INIT\n");
    mm_checkheap(1);
#endif
    
    return 0;


}

/*
 * malloc
 */
void *malloc (size_t size) {
    
    size_t asize;       /* adjusted size */
    size_t extendsize;  /* amount to extend to heap */
    char *bp;
    
    if (size <= 0) {
        return NULL;
    }
    
    /* Least alignment size + two headers */
    if (size <= ALIGNMENT)
        asize = ALIGNMENT + DSIZE;
    else
        asize = DSIZE + ALIGN(size);
    
    /* search free list for a fit*/
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        
#if DEBUG
        dbg_printf("MALLOC size = %d\n", (int)size);
        mm_checkheap(31);
#endif
        return bp;
    }
    
    /* No fit found, get more memory */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap((int)extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    if(!ptr) return;
    
    /* Debug */
    if(!in_heap(ptr)) {
        dbg_printf("ptr is not in heap!\n");
    }
    if (!aligned(ptr)) {
        dbg_printf("ptr is not aligned!\n");
    }
    
    size_t bsize = GET_SIZE(GET_HEADER(ptr));
    
    PUT(GET_HEADER(ptr), PACK(bsize, 0));
    PUT(GET_FOOTER(ptr), PACK(bsize, 0));
    coalesce(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    
    size_t oldsize;
    void *newptr = NULL;
    
    /* if ptr is NULL, the call is equivalent to malloc(size) */
    if (!oldptr) {
        return malloc(size);
    }
    /* if size is equal to zero, the call is equivalent to free(ptr) and should return NULL */
    if (size <= 0) {
        free(oldptr);
        return NULL;
    }
    
    /* Debug */
    if(!in_heap(oldptr)) {
        dbg_printf("ptr is not in heap!\n");
        return NULL;
    }
    if (!aligned(oldptr)) {
        dbg_printf("ptr is not aligned!\n");
        return NULL;
    }
    
    /* Reallocate a ptr that has been released */
    if (!GET_ALLOC(GET_HEADER(oldptr))) {
        dbg_printf("ptr has been freed!\n");
        return NULL;
    }
    
    
    /* no free, just allocate new */
    newptr = malloc(size);
    
    /* Copy contents */
    oldsize = GET_SIZE(GET_HEADER(oldptr));
    oldsize = size < oldsize ? size : oldsize;
    memcpy(newptr, oldptr, oldsize);
    
    free(oldptr);
    
    return newptr;
    
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    
    size_t bytes = nmemb * size;
    void *newptr;
    
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    
    return newptr;
}

/*
 * mm_checkheap
 *
 * @param verbose mask:
 *  val         func desc
 *  0x1         Check Prologue and Epilogue
 *  0x2         Check heap boundaries
 *  0x4         Check each block's address alignment
 *  0x8         Check each block’s header and footer
 *  0x10        Check coalescing: no two consecutive free blocks in the heap.
 */
void mm_checkheap(int verbose) {
    
    verbose = verbose;
    
    char *bp = heap_listp;
    int i = 1;
    int hd_size, hd_alloc, ft_size, ft_alloc;
    
    if (heap_listp == NULL)
        dbg_printf("Heap Uninitialized!\n");
    
    /* check prologue and epilogue blocks */
    if (verbose & 0x1) {
        
        dbg_printf("Prologue Header size = %d, alloc = %d\n", (int)GET_SIZE(GET_HEADER(heap_listp)), (int)GET_ALLOC(GET_HEADER(heap_listp)));
        dbg_printf("Prologue Footer size = %d, alloc = %d\n", (int)GET_SIZE(GET_FOOTER(heap_listp)), (int)GET_ALLOC(GET_FOOTER(heap_listp)));
        
        bp = heap_listp;
        while (GET_SIZE(GET_HEADER(NEXT_BLKP(bp))) > 0)
            bp = NEXT_BLKP(bp);
        bp = NEXT_BLKP(bp);
        dbg_printf("Epilogue Header size = %d, alloc = %d\n", (int)GET_SIZE(GET_HEADER(bp)), (int)GET_ALLOC(GET_HEADER(bp)));
    }
    
    /* Check heap size and boundary */
    if (verbose & 0x2) {
        dbg_printf("Heap Information:\n");
        dbg_printf("Heap size(long) = %ld\n Heap first address = %ld\n Heap last address = %ld\n", mem_heapsize(), (unsigned long)mem_heap_lo(), (unsigned long)mem_heap_hi());
    }
    
    /* Check each block's information */
    if (verbose & 0xc) {
        i = 1;
        bp = heap_listp;
        
        while (GET_SIZE(GET_HEADER(NEXT_BLKP(bp))) > 0) {
            bp = NEXT_BLKP(bp);
            
            hd_size = (int)GET_SIZE(GET_HEADER(bp));
            hd_alloc = (int)GET_ALLOC(GET_HEADER(bp));
            ft_size = (int)GET_SIZE(GET_FOOTER(bp));
            ft_alloc = (int)GET_ALLOC(GET_FOOTER(bp));
            
            if (verbose & 0x8) {
                if (hd_size - ft_size) {
                    dbg_printf("SIZE NOT MATCH!!! Block (%d), addr = %ld, header_size = %d footer_size = %d \n", i, (unsigned long)bp , hd_size, ft_size);
                    exit(1);
                }
                if (hd_alloc - ft_alloc) {
                    dbg_printf("ALLOC NOT MATCH!!! Block (%d), addr = %ld, header_alloc = %d footer_alloc = %d \n", i, (unsigned long)bp, hd_alloc, ft_alloc);
                    exit(1);
                }
            }
            
            if (verbose & 0x4) {
                dbg_printf("Block %d, addr = %ld, size = %d, alloc = %d \n", i, (unsigned long)bp, hd_size, hd_alloc);
            }
            
            
            ++i;
        }
    }
    
    /* Check coalescing */
    if (verbose & 0x10) {
        bp = heap_listp;
        i = 1;
        while (GET_SIZE(GET_HEADER(NEXT_BLKP(bp))) > 0) {
            bp = NEXT_BLKP(bp);
            if ((GET_ALLOC(GET_HEADER(bp)) == 0) && (GET_ALLOC(GET_HEADER(NEXT_BLKP(bp))) == 0)) {
                dbg_printf("Not coalesced: (%ld) and (%ld)\n", (unsigned long)bp, (unsigned long)NEXT_BLKP(bp));
            }
        }
    }
    
    /* Check each block’s address alignment */
    
    dbg_printf("******************\n");
}


