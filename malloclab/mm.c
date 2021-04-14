/*
 *		< header comment >
 *	studentID:		1800017771
 *	student name:	董翌飞
 *		< header comment >
 */


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
# define CHECKHEAP(verbose) mm_checkheap(verbose)
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



/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  

#define MAX(x, y) ((x) > (y)? (x) : (y))  
#define MIN(x, y) ((x) < (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* for explict linkedlist */ 
#define PRED_PTR(bp) ((char *)(bp))
#define SUCC_PTR(bp) ((char *)(bp) + WSIZE)
#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(SUCC_PTR(bp)))
#define SET_PTR(p, bp) (*(size_t *)(p) = (size_t)(bp))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define LISTMAX 16

/* Global variables */
static char *heap_listp;  /* Pointer to first block */  
void *seg_free_lists[LISTMAX];

/*
 * If NEXT_FIT defined use next fit search, else use first-fit search 
 */
#define NEXT_FITx
#ifdef NEXT_FIT
static char *pre_listp;           /* Next fit pre_listp */
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize);
static void *find_fit(size_t asize);//delete
static void *coalesce(void *bp);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);
static size_t get_asize(size_t size);
static void *realloc_coalesce(void *bp,size_t newSize,int *isNextFree);
static void realloc_place(void *bp,size_t asize);
void checkheap(int verbose);
void mm_checkheap(int verbose);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    /* initiliaze seg_free_lists */
    for(int i=0;i<LISTMAX;++i){
        seg_free_lists[i]=NULL;
    }

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);  
                    

#ifdef NEXT_FIT
    pre_listp = heap_listp;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    CHECKHEAP(1);
    return 0;
}

/* 
 * malloc - Allocate a block with at least size bytes of payload 
 */
void *malloc(size_t size) 
{
    size_t asize, search;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp=NULL;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    asize = get_asize(size);
    search = asize;
    int target;
    for (target = 0; target < LISTMAX; target++, search >>= 1) {
        /* find target seg_free_list*/
        if ((search > 1) || (seg_free_lists[target] == NULL)) continue;
        char *i = seg_free_lists[target];
        for(;i != NULL;i = SUCC(i))
        {
            if (GET_SIZE(HDRP(i)) < asize) continue;
            bp = i;
            break;
        }
        if (bp != NULL) break;
    }
    if (bp == NULL) {
        /* No fit found. Get more memory and place the block */
        extendsize = MAX(asize,CHUNKSIZE);
        if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
            return NULL;
    }
    bp = place(bp, asize);
    CHECKHEAP(1);
    return bp;
} 

/* 
 * free - Free a block 
 */
void free(void *bp)
{
    if (bp == 0) 
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
    CHECKHEAP(1);
}

/*
 * realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return NULL;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    void *newptr;
    size_t asize, oldsize;
    oldsize = GET_SIZE(HDRP(ptr));
    asize = get_asize(size);
    if(oldsize<asize)
    {
        int isnextFree;
        char *bp = realloc_coalesce(ptr,asize,&isnextFree);
        if(isnextFree==1){ /*next block is free*/
            realloc_place(bp,asize);
        } else if(isnextFree ==0 && bp != ptr){ /*previous block is free, move the point to new address,and move the payload*/
            memcpy(bp, ptr, size);
            realloc_place(bp,asize);
        }else{
        /*realloc_coalesce is fail*/
            newptr = mm_malloc(size);
            memcpy(newptr, ptr, size);
            mm_free(ptr);
            CHECKHEAP(1);
            return newptr;
        }
        CHECKHEAP(1);
        return bp;
    }
    else if(oldsize>asize)
    {/*just change the size of ptr*/
        realloc_place(ptr,asize);
        CHECKHEAP(1);
        return ptr;
    }
    CHECKHEAP(1);
    return ptr;
}


/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    return NULL;
}


/*
 * mm_checkheap
 */
/*
void mm_checkheap(int lineno) {
}
*/



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
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_node(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_node(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else if (!prev_alloc && !next_alloc){        /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
            
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp)); 
        
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
#ifdef NEXT_FIT
    /* Make sure the pre_listp isn't pointing into the free block */
    /* that we just coalesced */
    if ((pre_listp > (char *)bp) && (pre_listp < NEXT_BLKP(bp))) 
        pre_listp = bp;
#endif

    insert_node(bp, size);
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void *place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   
    delete_node(bp);

    if((csize - asize) < (2*DSIZE)){
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    else if(asize >= 96){
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        
        PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        
        insert_node(bp, csize - asize);
        return NEXT_BLKP(bp);
    }
    else { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        PUT(HDRP(NEXT_BLKP(bp)), PACK(csize-asize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(csize-asize, 0));
        insert_node(NEXT_BLKP(bp), csize - asize);
    }
    return bp;
}

static void insert_node(void *bp, size_t size){
    int tar = 0;
    for (size_t j = size; (j > 1) && (tar < LISTMAX - 1); ) {
        j >>= 1;
        tar++;
    }
    char *i = seg_free_lists[tar];
    char *pre = NULL;
    while ((i != NULL) && (size > GET_SIZE(HDRP(i)))) {
        pre = i;
        i = SUCC(i);
    }// i should be first node size >= input size
    if (i == NULL && pre == NULL) {//empty list
        seg_free_lists[tar] = bp;
        SET_PTR(PRED_PTR(bp), NULL);
        SET_PTR(SUCC_PTR(bp), NULL);
    } else if (i == NULL && pre != NULL) {// add the last
        SET_PTR(PRED_PTR(bp), pre);
        SET_PTR(SUCC_PTR(bp), NULL);
        SET_PTR(SUCC_PTR(pre), bp);
    } else if (pre == NULL) {// add the first
        seg_free_lists[tar] = bp;
        SET_PTR(PRED_PTR(i), bp);
        SET_PTR(SUCC_PTR(bp), i);
        SET_PTR(PRED_PTR(bp), NULL);
    } else {
        SET_PTR(PRED_PTR(bp), pre);
        SET_PTR(SUCC_PTR(bp), i);
        SET_PTR(PRED_PTR(i), bp);
        SET_PTR(SUCC_PTR(pre), bp);
    }
}

static void delete_node(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    int tar = 0;
    for (size_t j = size; (j > 1) && (tar < LISTMAX - 1); j >>= 1) {
        tar++;
    }

    if (PRED(bp) == NULL) { // first one
        seg_free_lists[tar] = SUCC(bp);
        if (SUCC(bp) != NULL)
            SET_PTR(PRED_PTR(SUCC(bp)), NULL);
    } else if (SUCC(bp) == NULL) { //last one
        SET_PTR(SUCC_PTR(PRED(bp)), NULL);
    } else {
        SET_PTR(SUCC_PTR(PRED(bp)), SUCC(bp));
        SET_PTR(PRED_PTR(SUCC(bp)), PRED(bp));
    }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
#ifdef NEXT_FIT 
    /* Next fit search */
    char *oldrover = pre_listp;

    /* Search from the pre_listp to the end of list */
    for ( ; GET_SIZE(HDRP(pre_listp)) > 0; pre_listp = NEXT_BLKP(pre_listp))
        if (!GET_ALLOC(HDRP(pre_listp)) && (asize <= GET_SIZE(HDRP(pre_listp))))
            return pre_listp;

    /* search from start of list to old pre_listp */
    for (pre_listp = heap_listp; pre_listp < oldrover; pre_listp = NEXT_BLKP(pre_listp))
        if (!GET_ALLOC(HDRP(pre_listp)) && (asize <= GET_SIZE(HDRP(pre_listp))))
            return pre_listp;

    return NULL;  /* no fit found */
#else 
    /* First-fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* No fit */
#endif
}

static size_t get_asize(size_t size) 
{
    size_t asize;
    if(size <= DSIZE){
        asize = 2*(DSIZE);
    }else{
        asize = ALIGN(size + DSIZE);
    }
    return asize;
}

static void *realloc_coalesce(void *bp,size_t newSize,int *isNextFree)
{
    size_t  prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t  next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    *isNextFree = 0;
    /*coalesce the block and change the point*/
    if(prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if(size>=newSize)
        {
            delete_node(NEXT_BLKP(bp));
            PUT(HDRP(bp), PACK(size,1));
            PUT(FTRP(bp), PACK(size,1));
            *isNextFree = 1;
        }
    }
    else if(!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        if(size>=newSize)
        {
            delete_node(PREV_BLKP(bp));
            PUT(FTRP(bp),PACK(size,1));
            PUT(HDRP(PREV_BLKP(bp)),PACK(size,1));
            bp = PREV_BLKP(bp);
        }
    }
    else if(!prev_alloc && !next_alloc)
    {
        size +=GET_SIZE(FTRP(NEXT_BLKP(bp)))+ GET_SIZE(HDRP(PREV_BLKP(bp)));
        if(size>=newSize)
        {
            delete_node(PREV_BLKP(bp));
            delete_node(NEXT_BLKP(bp));
            PUT(FTRP(NEXT_BLKP(bp)),PACK(size,1));
            PUT(HDRP(PREV_BLKP(bp)),PACK(size,1));
            bp = PREV_BLKP(bp);
        }
    }
    return bp;
}
static void realloc_place(void *bp,size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
   /*
    if((csize-asize)>=(2*DSIZE))
    {
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize,0));
        coalesce(bp);
    }
    else
    {
         PUT(HDRP(bp),PACK(csize,1));
         PUT(FTRP(bp),PACK(csize,1));
    } */
    PUT(HDRP(bp),PACK(csize,1));
    PUT(FTRP(bp),PACK(csize,1));
}

/* below code if for check heap invarints */

static void printblock(void *bp) 
{
    long int hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static int checkblock(void *bp) 
{
    //area is aligned
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    //header and footer match
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
    size_t size = GET_SIZE(HDRP(bp));
    //size is valid
    if (size % 8)
       printf("Error: %p payload size is not doubleword aligned\n", bp);
    return GET_ALLOC(HDRP(bp));
}

static void printlist(void *i, long size) 
{
    long int hsize, halloc;

    for(;i != NULL;i = SUCC(i))
    {
        hsize = GET_SIZE(HDRP(i));
        halloc = GET_ALLOC(HDRP(i));
        printf("[listnode %ld] %p: header: [%ld:%c] prev: [%p]  next: [%p]\n",
           size, i, 
           hsize, (halloc ? 'a' : 'f'), 
           PRED(i), SUCC(i)); 
    }
}
static void checklist(void *i, size_t tar) 
{
    void *pre = NULL;
    size_t hsize, halloc;
    for(;i != NULL;i = SUCC(i))
    {
        if (PRED(i) != pre) printf("Error: pred point error\n");
        if (pre != NULL && SUCC(pre) != i) printf("Error: succ point error\n");
        hsize = GET_SIZE(HDRP(i));
        halloc = GET_ALLOC(HDRP(i));
        if (halloc) printf("Error: list node should be free\n");
        if (pre != NULL && (GET_SIZE(HDRP(pre)) > hsize)) 
           printf("Error: list size order error\n");
        if (hsize < tar || ((tar != (1<<15)) && (hsize > (tar << 1)-1)))
           printf("Error: list node size error\n");
        pre = i;
    }
}
/* 
 * mm_checkheap - Check the heap for correctness
 */
void mm_checkheap(int verbose)  
{ 
    checkheap(verbose);
}
//heap level
void checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    // block level
    checkblock(heap_listp);
    int pre_free = 0;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        int cur_free = checkblock(bp);
        //no contiguous free blocks
        if (pre_free && cur_free) {
            printf("Contiguous free blocks\n");
        }
   
    }
    //list level
    int i = 0, tarsize = 1;
    for (; i < LISTMAX; i++) {
        if (verbose) 
            printlist(seg_free_lists[i], tarsize);
        checklist(seg_free_lists[i],tarsize);
        tarsize <<= 1;
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}
