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
#include <math.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
/*#define DEBUG   1*/
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


#define CHECK_HEAP  0

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

#define CHUNKSIZE   (1 << 8) /* 512, got best score */

#define MAX(x, y) (((x) > (y))? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

/* RW a Word at address p, x64 WSIZE = 8 */
#define GET(p)          (*(unsigned long *)(p))
#define PUT(p, val)     (*(unsigned long *)(p) = (val))

#define GET_CLASS_ROOT_BLK(p)         (char *)(*(size_t *)(p))
#define SET_CLASS_ROOT_BLK(p, val)    (*(size_t *)(p) = (size_t)(val))

/* Read header and footer information, !!!ATTENTION!!! GET_SIZE/ALLOC ONLY work for header and footer */
#define GET_SIZE(p)             (GET(p) & ~0x7)
#define GET_ALLOC(p)            (GET(p) & 0x1)
#define GET_PREV_ALLOC(p)       (GET(p) & 0x2)  /**! the second least significant bit is for recording if previous block is allocated */

/* bp points to one wsize after header, !!!ATTENTION!!! footer called header, therefore header better be set beforehand */
#define GET_HEADER(bp)  ((char *)(bp) - WSIZE)
#define GET_FOOTER(bp)  ((char *)(bp) + GET_SIZE(GET_HEADER(bp)) - DSIZE)

/* Prev block is stored in prev footer */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define GET_PRED_BLK(bp)    (char *)(*(size_t *)(bp))
#define GET_SUCC_BLK(bp)    (char *)(*(size_t *)((char *)(bp) + WSIZE))

#define SET_PRED(bp, val)   if ((void *)bp != NULL) \
if ((size_t)(bp) - (size_t)(val)) \
((*(size_t *)(bp)) = (size_t)val);


#define SET_SUCC(bp, val)   if (((void *)bp != NULL)) \
if ((size_t)(bp) - (size_t)(val)) \
((*(size_t *)((char *)(bp) + WSIZE)) = (size_t)(val));


/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* number of block size classes in seglist */
#define CLASS_NUM       12


/* Helper functions*/
static char *heap_listp = NULL;
static char *classp = NULL;

#define GET_CLASS(idx)      ((char *)classp + idx * WSIZE)

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

static inline int get_class_idx_by_size(size_t asize) {
    
    int index = 0;
    if ((asize < 32) || (asize % ALIGNMENT)) {
        dbg_printf("Illegal adjusted size. asize = %ld\n",asize);
        exit(1);
        return -1;
    }
    
    if (asize == 32) {
        index = 0;
    }
    if ((asize > 32) && (asize <= 64)) {
        index = 1;
    }
    if ((asize > 64) && (asize <= 128)) {
        index = 2;
    }
    if ((asize > 128) && (asize <= 256)) {
        index = 3;
    }
    if ((asize > 256) && (asize <= 512)){
        index = 4;
    }
    if ((asize > 512) && (asize <= 1024)){
        index = 5;
    }
    if ((asize > 1024) && (asize <= 2048)){
        index = 6;
    }
    if ((asize > 2048) && (asize <= 4096)){
        index = 7;
    }
    if ((asize > 4096) && (asize <= 8192)){
        index = 8;
    }
    if ((asize > 8192) && (asize <= 16384)){
        index = 9;
    }
    if ((asize > 16384) && (asize <= 32768)){
        index = 10;
    }
    if ((asize > 32768)){
        index = 11;
    }
    
    return index;
}

static inline char *get_class_ptr_by_bsize(size_t asize) {
    
    int index = get_class_idx_by_size(asize);
    return ((char *)classp + index * WSIZE);
}

/* Insert the block before the root */
static inline void insert_first(void *bp) {
    
    size_t asize = GET_SIZE(GET_HEADER(bp));
    /* root block adress for class size of asize */
    char *bclassp = get_class_ptr_by_bsize(asize);
    
    dbg_printf("bclassp = 0x%lx\n", (size_t)bclassp);
    
    char *rootbp = GET_CLASS_ROOT_BLK(bclassp);
    
    if (rootbp == NULL) {
        
        SET_PRED(bp, NULL);
        SET_SUCC(bp, NULL);
    }
    else {
        
        SET_SUCC(bp, rootbp);
        SET_PRED(bp, NULL);
        
        SET_PRED(rootbp, bp);
    }
    
    rootbp = bp;
    
    SET_CLASS_ROOT_BLK(bclassp, rootbp);
}

/* Linked List helper functions */
/* Equals to remove a node from linked list */
static inline void remove_free_block(void *bp, int class_idx) {
    
    char *bclassp = GET_CLASS(class_idx);
    char *rootbp = GET_CLASS_ROOT_BLK(bclassp);
    
    if (!bp) {
        dbg_printf("Trying to remove NULL\n");
        exit(1);
    }
    
    if (!GET_PRED_BLK(bp) && !GET_SUCC_BLK(bp)) {
        rootbp = NULL;
        
        SET_CLASS_ROOT_BLK(bclassp, rootbp);
    }
    
    /* has pred, no succ */
    if (GET_PRED_BLK(bp) && !GET_SUCC_BLK(bp)) {
        SET_SUCC(GET_PRED_BLK(bp), NULL);
    }
    
    /* has succ, no pred */
    if (!GET_PRED_BLK(bp) && GET_SUCC_BLK(bp)) {
        rootbp = GET_SUCC_BLK(bp);
        SET_PRED(rootbp, NULL);
        
        SET_CLASS_ROOT_BLK(bclassp, rootbp);
    }
    
    if (GET_PRED_BLK(bp) && GET_SUCC_BLK(bp)) {
        
        SET_SUCC(GET_PRED_BLK(bp), GET_SUCC_BLK(bp));
        SET_PRED(GET_SUCC_BLK(bp), GET_PRED_BLK(bp));
    }
    
    SET_PRED(bp, NULL);
    SET_SUCC(bp, NULL);
}

static inline void split_free_block(void *bp, void *nextbp) {
    
    if (!GET_SUCC_BLK(bp)) {
        SET_SUCC(nextbp, NULL);
    }
    else {
        SET_SUCC(nextbp, GET_SUCC_BLK(bp));
        SET_PRED(GET_SUCC_BLK(bp), nextbp);
    }
    
    SET_SUCC(bp, nextbp);
    SET_PRED(nextbp, bp);
    
}

static inline void check_bp_pred_succ(void *bp) {
    
    bp = bp;
    /*
     dbg_printf("(size_t)(bp) = 0x%lx\n",(size_t)(bp));
     dbg_printf("(size_t)(bp pred) = 0x%lx\n",(size_t)GET_PRED_BLK(bp));
     dbg_printf("(size_t)(bp succ) = 0x%lx\n",(size_t)GET_SUCC_BLK(bp));
     
     if (GET_SUCC_BLK(bp)) {
     if ((size_t)bp - (size_t)GET_PRED_BLK(GET_SUCC_BLK(bp))) {
     dbg_printf("Pred not match! (size_t)GET_PRED_BLK(GET_SUCC_BLK(bp)) = 0x%lx\n",(size_t)GET_PRED_BLK(GET_SUCC_BLK(bp)));
     exit(1);
     }
     }
     */
}

/* LIFO policy, first hit policy */
static void *find_fit(size_t asize) {
    
    char *bp = NULL;
    char *bclassp = NULL;
    char *bestfit = NULL;
    unsigned long bestsize = (1 << 31);
    unsigned long tmpsize = 0;
    
    int index = get_class_idx_by_size(asize);
    
    dbg_printf("=== FIND_FIT adjusted size: %ld class index = %d\n", asize, index);
    
    for (index = index; index < CLASS_NUM; index ++) {
        if (index < 1) {
            bclassp = GET_CLASS(index);
            bp = GET_CLASS_ROOT_BLK(bclassp);
            
            if (bp) return bp;
            
        }
        else {
            bclassp = GET_CLASS(index);
            bp = GET_CLASS_ROOT_BLK(bclassp);
            
            if (bp) {
                do {
                    check_bp_pred_succ(bp);
                    tmpsize = GET_SIZE(GET_HEADER(bp));
                    if (tmpsize == asize) {
                        return bp;
                    }
                    else if (tmpsize > asize) {
                        if (tmpsize < bestsize) {
                            bestsize = tmpsize;
                            bestfit = bp;
                        }
                        /*return bp;*/
                    }
                    
                } while ((bp = (char *)GET_SUCC_BLK(bp)) != NULL);
                
                if (bestfit) 
                    return bestfit;
                
            }
        }
    }
    return NULL;
}

/* Place an ADJUSTED sized block in heap */
static void place(void *bp, size_t asize) {
    
#if DEBUG
    if (NEXT_BLKP(bp)) {
        if (GET_PREV_ALLOC(GET_HEADER(NEXT_BLKP(bp)))) {
            dbg_printf("0x%lx: Fail to inform next block when free\n", (size_t)bp);
            exit(2);
        }
    }
#endif
    
    dbg_printf("=== Place, bp = 0x%lx, adjusted size = %ld \n", (size_t)bp, asize);
    
    /* block free size */
    size_t csize = GET_SIZE(GET_HEADER(bp));
    char *nextbp = NULL;
    int class_idx = 0;
    size_t flag = 0;
    
    /* Split, say, minimum block size set to 1 WSIZE = 8 byte */
    if ((csize - asize) >= (4 * WSIZE)) {
        
        class_idx = get_class_idx_by_size(GET_SIZE(GET_HEADER(bp)));
        
        /* Include previous block's information */
        flag = GET_PREV_ALLOC(GET_HEADER(bp)) ? 0x3 : 0x1;
        
        PUT(GET_HEADER(bp), PACK(asize, flag));
        PUT(GET_FOOTER(bp), PACK(asize, flag));
        
        nextbp = NEXT_BLKP(bp);
        
        PUT(GET_HEADER(nextbp), PACK((csize - asize), 0));
        PUT(GET_FOOTER(nextbp), PACK((csize - asize), 0));
        
        /* Inform the next block that this block is allocated */
        flag = GET(GET_HEADER(nextbp));
        flag |= 0x2;
        PUT(GET_HEADER(nextbp), flag);
        PUT(GET_FOOTER(nextbp), flag);
        
        split_free_block(bp, nextbp);
        remove_free_block(bp, class_idx);
        
        remove_free_block(nextbp, class_idx);
        insert_first(nextbp);
        
        mm_checkheap(CHECK_HEAP);
        
    }
    else {
        /* Include previous block's information */
        flag = GET_PREV_ALLOC(GET_HEADER(bp)) ? 0x3 : 0x1;
        
        PUT(GET_HEADER(bp), PACK(csize, flag));
        PUT(GET_FOOTER(bp), PACK(csize, flag));
        
        /* Inform the next block that this block is allocated */
        nextbp = NEXT_BLKP(bp);
        if (nextbp) {
            flag = GET(GET_HEADER(nextbp));
            flag |= 0x2;
            PUT(GET_HEADER(nextbp), flag);
            /* Only put footer when next block is free */
            if (!GET_ALLOC(GET_HEADER(nextbp))) {
                PUT(GET_FOOTER(nextbp), flag);
            }
            
        }
        
        remove_free_block(bp, get_class_idx_by_size(csize));
    }
}

static void *coalesce(void *bp) {
    
    dbg_printf("=== Coalesce bp = 0x%lx\n", (size_t)bp);
    
    void *prevbp = PREV_BLKP(bp);
    void *nextbp = NEXT_BLKP(bp);
    
    /*ONLY use the former alloc flag  */
    size_t prev_alloc = GET_PREV_ALLOC(GET_HEADER(bp)); /*GET_ALLOC(GET_FOOTER(prevbp));*/
    size_t next_alloc = GET_ALLOC(GET_HEADER(nextbp));
    size_t bsize = GET_SIZE(GET_HEADER(bp));
    size_t flag = 0;
    
    int class_idx = 0;
    
    /* case 1: make newly freed block to be root */
    if (prev_alloc && next_alloc) {
        
        dbg_printf("Coalesce Case 1\n");
        
        insert_first(bp);
        
        return bp;
        
    }
    /* case 3: next block is free */
    else if (prev_alloc && !next_alloc) {
        
        dbg_printf("Coalesce Case 3\n");
        
        class_idx = get_class_idx_by_size(GET_SIZE(GET_HEADER(nextbp)));
        remove_free_block(nextbp, class_idx);
        
        /* Telling coalesced free block about if bp's previous allocated */
        flag = GET_PREV_ALLOC(GET_HEADER(bp)) ? 0x2 : 0x0;
        
        bsize += GET_SIZE(GET_HEADER(nextbp));
        PUT(GET_HEADER(bp), PACK(bsize, flag));
        PUT(GET_FOOTER(bp), PACK(bsize, flag));
        
        insert_first(bp);
        
        return bp;
        
    }
    /* case 2: prev block is free */
    else if (!prev_alloc && next_alloc) {
        
        dbg_printf("Coalesce Case 2\n");
        
        class_idx = get_class_idx_by_size(GET_SIZE(GET_HEADER(prevbp)));
        
        dbg_printf("class_idx = %d, class_address = 0x%lx\n", class_idx, (size_t)GET_CLASS(class_idx));
        
        remove_free_block(prevbp, class_idx);
        
        /* Telling coalesced free block about if bp's previous's previous allocated */
        flag = GET_PREV_ALLOC(GET_HEADER(prevbp)) ? 0x2 : 0x0;
        
        if (flag == 0) {
            printf("Implies fail coalese: 0x%lx with former\n", (size_t)prevbp);
            exit(2);
        }
        
        bsize += GET_SIZE(GET_HEADER(prevbp));
        PUT(GET_HEADER(prevbp), PACK(bsize, flag));
        PUT(GET_FOOTER(prevbp), PACK(bsize, flag));
        
        insert_first(prevbp);
        
        return prevbp;
    }
    /* case 4: both blocks are free */
    else {
        
        dbg_printf("Coalesce Case 4\n");
        
        class_idx = get_class_idx_by_size(GET_SIZE(GET_HEADER(nextbp)));
        remove_free_block(nextbp, class_idx);
        class_idx = get_class_idx_by_size(GET_SIZE(GET_HEADER(prevbp)));
        remove_free_block(prevbp, class_idx);
        
        /* Telling coalesced free block about if bp's previous's previous allocated */
        flag = GET_PREV_ALLOC(GET_HEADER(prevbp)) ? 0x2 : 0x0;
        
        if (flag == 0) {
            printf("Implies fail coalese: 0x%lx with former\n", (size_t)prevbp);
            exit(2);
        }
        
        bsize += GET_SIZE(GET_HEADER(nextbp));
        bsize += GET_SIZE(GET_FOOTER(prevbp));
        PUT(GET_HEADER(prevbp), PACK(bsize, flag));
        PUT(GET_FOOTER(nextbp), PACK(bsize, flag));
        
        insert_first(prevbp);
        
        return prevbp;
    }
    
    dbg_printf("Unable to coalesce!\n");
    return NULL;
}

/* extend heap by number of words */
/*  */
static void *extend_heap(int words) {
    
    /* last block of heap, size = 0, alloc = 1 */
    char *epilogue = (mem_heap_hi() + 1);
    char *bp; /* block pointer */
    int bsize; /* block size to extend */
    int adjusted_bsize = 0; /* Incase heap doesn't need to extend that much */
    size_t flag = 0;
    
    /* Allocate even number of words to maintain alignment */
    bsize = (words % 2) ? ((words + 1) * WSIZE) : (words * WSIZE);
    
    if (!GET_PREV_ALLOC(GET_HEADER(epilogue))) {
        adjusted_bsize = bsize - (int)GET_SIZE(GET_HEADER(PREV_BLKP(epilogue)));
        if(adjusted_bsize > 2 * DSIZE)
            bsize = adjusted_bsize;
    }
    
    dbg_printf("EXTEND_HEAD: words = %d bszie = %d\n", words, bsize);
    
    dbg_printf("!!!!!!!!!!!!!!!!!!!!!!!!Before Extend!!!!\n");
    mm_checkheap(CHECK_HEAP);
    
    /* Record if last block is allocated or not */
    flag = GET_PREV_ALLOC(GET_HEADER(epilogue)) ? 0x2 : 0x0;
    
    if ((long)(bp = mem_sbrk(bsize)) == -1)
        return NULL;
    
    
    
    /* Init free block header/footer and the epilogue header */
    PUT(GET_HEADER(bp), PACK(bsize, flag));
    PUT(GET_FOOTER(bp), PACK(bsize, flag));
    
    /* Set epilogue to be size = 0, alloc = 1 */
    PUT(GET_HEADER(NEXT_BLKP(bp)), PACK(0, 1));
    
    SET_PRED(bp, NULL);
    SET_SUCC(bp, NULL);
    
    mm_checkheap(CHECK_HEAP);
    
    return coalesce(bp);
}


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    
    heap_listp = NULL;
    classp = NULL;
    
    int i = 0;
    
    /* Init segregated free list class pointer space */
    if ((classp = mem_sbrk(CLASS_NUM * WSIZE)) == (void *)-1)
        return -1;
    
    for (i = 0; i < CLASS_NUM; i++) {
        SET_CLASS_ROOT_BLK(classp + (i * WSIZE), NULL);
    }
    
    /* Try mm_init with sbrk*/
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 3)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 3)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 3));     /* Epilogue header */
    heap_listp += 2 * WSIZE;
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    
    dbg_printf("HEAP INIT\n");
    mm_checkheap(CHECK_HEAP);
    
    return 0;
    
    
}

/*
 * malloc
 */
void *malloc(size_t size) {
    
    dbg_printf("=== MALLOC! = %ld\n", size);
    
    size_t asize;       /* adjusted size */
    size_t extendsize;  /* amount to extend to heap */
    char *bp;
    
    if (size <= 0) {
        return NULL;
    }
    
    /* Least alignment size + two headers */
    if (size <= 2 * ALIGNMENT)
        asize = 2 * ALIGNMENT + DSIZE;
    else
        asize = WSIZE + ALIGN(size);    /* for > 16 bytes size, could remove footer when not need */
    
    
    /* search free list for a fit*/
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        
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
void free(void *ptr) {
    
    dbg_printf("=== FREE : 0x%lx\n",(size_t)ptr);
    
#if DEBUG
    if (NEXT_BLKP(ptr)) {
        if (!GET_PREV_ALLOC(GET_HEADER(NEXT_BLKP(ptr)))) {
            dbg_printf("0x%lx Fail to inform next block when malloc, or next block fail to update\n", (size_t)ptr);
            exit(3);
        }
    }
#endif
    
    if(!ptr) return;
    
    /* Debug */
    if(!in_heap(ptr)) {
        dbg_printf("ptr is not in heap!\n");
        
        mm_checkheap(63);
        exit(1);
    }
    if (!aligned(ptr)) {
        dbg_printf("ptr is not aligned!\n");
        
        mm_checkheap(63);
        exit(1);
    }
    
    size_t bsize = GET_SIZE(GET_HEADER(ptr));
    
    size_t flag = GET_PREV_ALLOC(GET_HEADER(ptr)) ? 0x2 : 0x0;
    PUT(GET_HEADER(ptr), PACK(bsize, flag));
    PUT(GET_FOOTER(ptr), PACK(bsize, flag));
    
    /* Inform the next block that this block is freed */
    char *nextbp = NEXT_BLKP(ptr);
    if (nextbp) {
        flag = GET(GET_HEADER(nextbp));
        flag &= ~0x2;
        PUT(GET_HEADER(nextbp), flag);
        /* Only put footer when next block is free */
        if (!GET_ALLOC(GET_HEADER(nextbp))) {
            PUT(GET_FOOTER(nextbp), flag);
        }
    }
    
    coalesce(ptr);
    
    mm_checkheap(CHECK_HEAP);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    
    dbg_printf("=== Realloc : 0x%ld\n size = %ld",(size_t)oldptr, size);
    
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
    
    dbg_printf("=== Calloc : 0x%ld\n size = %ld",(size_t)nmemb, size);
    
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
 *  0x10(16)    Check coalescing: no two consecutive free blocks in the heap.
 *  0x20(32)    Check next/previous pointers are consistent
 */
void mm_checkheap(int verbose) {
    
    if (!verbose) {
        return;
    }
    
    verbose = verbose;
    
    char *bp = heap_listp;
    int i = 1;
    int hd_size, hd_alloc, ft_size, ft_alloc;
    /*char *blkp = root;*/
    
    if (heap_listp == NULL) {
        dbg_printf("Heap Uninitialized!\n");
    }
    
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
        dbg_printf("Heap size(long) = %ld\n Heap first address = 0x%lx\n Heap last address = 0x%lx\n", mem_heapsize(), (unsigned long)mem_heap_lo(), (unsigned long)mem_heap_hi());
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
                if (!hd_alloc) {
                    if (hd_size - ft_size) {
                        dbg_printf("SIZE NOT MATCH!!! Block (%d), addr = 0x%lx, header_size = %d footer_size = %d \n", i, (unsigned long)bp , hd_size, ft_size);
                        exit(1);
                    }
                    if (hd_alloc - ft_alloc) {
                        dbg_printf("ALLOC NOT MATCH!!! Block (%d), addr = 0x%lx, header_alloc = %d footer_alloc = %d \n", i, (unsigned long)bp, hd_alloc, ft_alloc);
                        exit(1);
                    }
                }
                
            }
            
            if (verbose & 0x4) {
                dbg_printf("Block %d, addr = 0x%lx, size = %d, alloc = %d \n", i, (unsigned long)bp, hd_size, hd_alloc);
            }
            
            
            ++i;
        }
    }
    
    /* Check coalescing */
    if (verbose & 0x10) {
        bp = heap_listp;
        while (GET_SIZE(GET_HEADER(NEXT_BLKP(bp))) > 0) {
            bp = NEXT_BLKP(bp);
            if ((GET_ALLOC(GET_HEADER(bp)) == 0) && (GET_ALLOC(GET_HEADER(NEXT_BLKP(bp))) == 0)) {
                dbg_printf("Not coalesced: (%lx) and (%lx)\n", (unsigned long)bp, (unsigned long)NEXT_BLKP(bp));
            }
        }
    }
    
    /* Check pred, succ pointers */
    if (verbose & 0x20) {
        
        for (i = 0; i < CLASS_NUM; i++) {
            dbg_printf("CLASS No. %d, class_address = 0x%lx ,root block address = 0x%lx\n", i, (size_t)GET_CLASS(i), (size_t)GET_CLASS_ROOT_BLK(GET_CLASS(i)));
        }
        
        /*i = 1;
         blkp = root;
         
         if (root != NULL) {
         dbg_printf("root address = 0x%lx\n", (size_t)root);
         
         do {
         dbg_printf("Check Free Block %d\n",i);
         check_bp_pred_succ(blkp);
         i++;
         if (i > 100) {
         exit(1);
         }
         } while ((blkp = GET_SUCC_BLK(blkp)) != NULL);
         }*/
    }
    
    /* Check each block’s address alignment */
    
    dbg_printf("******************\n");
}