/*
 *          <header comment>
 * 
 *      Student ID:     1800017771
 *      Student Name:   董翌飞
 * 
 *      Some Functions' Description:
 *          1)  使用了segregated_free_list
 *          2)  free_head[i]表示free_list中第i位块的hdr
 *              free_tail[i]表示free_list中第i位块的ftr
 *          3)  在malloc中，使用first_fit在合适的list里找合适的位置，随后将它从freelist中删除
 *          4)  在free中，将块free的方法是简单地将其放进free_list
 *          5)  在coalesce中，先从free_list中删除相邻空闲块，把它们合并之后再重新加入free_list
 * 
 *      Data Structure's Description:
 * 
 *  Allocated Block:
 *               31                      3 2  1  0
 *              +-------------------------+-----+-+
 *    Header:   |           size          |     |A|
 *       bp ->  +-------------------------+-----+-+
 *              |                                 |
 *              |     Payload and padding         |
 *              |          (optional)             |
 *              +-------------------------+-----+-+
 *    Footer:   |           size          |     |A|
 *              +-------------------------+-----+-+
 * 
 *  Free block:
 *               31                      3 2  1  0
 *              +-------------------------+-----+-+
 *    Header:   |           size          |     |F|
 *       bp ->  +-------------------------+-----+-+
 *  bp+WSIZE->  |        pointer to PRED          |
 *              +-------------------------+-----+-+
 *              |        pointer to SUCC          |
 *              +-------------------------+-----+-+
 *              |                                 |
 *              |     Payload and padding         |
 *              |          (optional)             |
 *              +-------------------------+-----+-+
 *    Footer:   |           size          |     |F|
 *              +-------------------------+-----+-+
 * 
 *  Heap:
 *               31                      3 2  1  0
 * start of heap+-------------------------+-----+-+
 *              |           0(padding)    |     | |
 *              +-------------------------+-----+-+
 * heap_listp-> |           8             |     |A|
 *              +-------------------------+-----+-+
 *              |           8             |     |A|
 *              +-------------------------+-----+-+
 *              |                                 |
 *              |    Free and allocated blocks    |
 *              |                                 |
 *              +-------------------------+-----+-+
 *              |           0             |     |A|
 *  end of heap +-------------------------+-----+-+
 * 
 *  Segregated Free Lists: 双向链表
 *      +----+             +----+            +----+
 *      |    |  <——————>   |  A |  <——————>  |  B | ...
 *      +----+             +----+            +----+
 *      |    |
 *      +----+
 *      |    |
 *      +----+ 
 *      |    |
 *      +----+
 *      |    |
 *      +----+
 *      |    |
 *      +----+ 
 *      |    |
 *      +----+
 *      |    |
 *      +----+
 *      |    |
 *      +----+ 
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
//#define DEBUG
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

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define BLOCKSIZE   16      /* 最小块字节数 */
#define INFOSIZE    8       /* 头尾字节总数 */
#define CHUNKSIZE   0x150   /* Extend heap by this amount (bytes) */ 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size_t)(size) + (ALIGNMENT - 1)) & ~0x7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))            
#define PUT(p, val) (*(unsigned int *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)      

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)                      
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 简化操作 */
#define THIS_SIZE(bp) (GET_SIZE(HDRP(bp)))                              /* bp指向块大小 */
#define PREV_SIZE(bp) (GET_SIZE((char *)(bp) - DSIZE))                  /* bp前一块大小 */
#define NEXT_SIZE(bp) (GET_SIZE((char *)(bp) + THIS_SIZE(bp) - WSIZE))  /* bp后一块大小 */
#define THIS_ALLOC(bp) (GET_ALLOC(HDRP(bp)))                            /* bp指向块分配与否 */

/* 显式空闲链表相关定义 */
#define GET_PRED(bp) ((char *)(bp) - GET(bp)) /* 获得祖先的值 */
#define GET_SUCC(bp) ((char *)(bp) + GET((char *)(bp) + WSIZE))  /* 获得后继的值 */

#define PUT_PRED(bp, pred) PUT(bp, (unsigned int)((char *)(bp) - (char *)(pred))) /* 给祖先赋值 */
#define PUT_SUCC(bp, succ) PUT((char *)(bp) + WSIZE, (unsigned int)((char *)(succ) - (char *)(bp))) /* 给后继赋值 */

/* 四种节点类型 */
#define ALLNULL     0
#define HEADNULL    1
#define TAILNULL    2
#define NORMAL      3

/* Global variables */
static char *heap_listp = NULL;  
static size_t *free_head;  /* point to every list head */
static size_t *free_tail;  /* point to every list tail */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t bytes);    
static void *place(void *bp, size_t bytes);
static void *find_fit(size_t bytes);      
static void *coalesce(void *bp);         
static inline int  getIndex(size_t size);
static inline void *insertNode(void *bp);
static inline void deleteNode(void *bp);        
static inline int getType(void *bp);



/**
 * @brief mm_init - Initialize the heap for 84 WSIZE, 
 *      4 to set the foreword, 80 to store the pointer to free_list
 * @param   {void}  no param
 * @return  {int}   success ->   0
 *                  fail    ->   -1
 */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk( 104 * WSIZE)) == (void *)-1) 
        return -1;
    free_head = (size_t *)heap_listp;
    free_tail = (size_t *)(heap_listp + 50 * WSIZE);
    int i;
    for (i = 0; i < 25; ++i){
        free_head[i] = (size_t)NULL;
        free_tail[i] = (size_t)NULL;
    }
    heap_listp += 100* WSIZE;   
    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1));    /* Prologue header */ 
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));    /* Prologue footer */ 
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));        /* Epilogue header */  
    heap_listp += 2 * WSIZE;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL) 
        return -1;
    return 0;
}

/**
 * @brief malloc - Allocate a block with at least size bytes of payload 
 * @param   {size_t}    size
 * @return  {void}      no return
 */
void *malloc(size_t size) 
{
    size_t bytes, extendsize;      /* Adjusted block size */
    char *bp;      
    bytes=size+INFOSIZE;
    /* Adjust block size to include overhead and alignment reqs. */
    if (bytes <= BLOCKSIZE)                    
        bytes = BLOCKSIZE;                                     
    else
        bytes = DSIZE * ((bytes + (DSIZE - 1)) / DSIZE); 
    
    /* Search the free list for a fit */
    if ((bp = find_fit(bytes)) != NULL) {
        bp = place(bp, bytes);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(bytes, CHUNKSIZE);
    if ((bp = extend_heap(extendsize)) == NULL) {
            return NULL;
    }
    place(bp, bytes);
    return bp;
}

/**
 * @brief free - Free a block 
 * @param   {void *}    bp
 * @return  {void}      no return
 */
void free(void *bp)
{
    if(bp == NULL) 
        return;
    
    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    bp = insertNode(bp);
    coalesce(bp);
}

/**
 * @brief realloc - Give a newSize to an allocted block
 *      (1) if the oldsize is enough to store newsize
 *          ->  simply change the size of oldblock
 *      (2) if the oldsize is not enough to store newsize
 *          ->  memcpy the memory to newPlace
 * @param   {void *}    ptr
 *          {size_t}    size
 * @return  {void}      no return
 */
void *realloc(void *ptr, size_t size)
{
    size_t oldsize, bytes;
    void *newptr;
    if(size == 0){
        mm_free(ptr);
        return NULL;
    }
    if(ptr == NULL)
        return mm_malloc(size);
    oldsize = THIS_SIZE(ptr);
    bytes = ALIGN(size + INFOSIZE);
    if(oldsize >= bytes){
        PUT(HDRP(ptr), PACK( oldsize, 1));
        PUT(FTRP(ptr), PACK( oldsize, 1));
        return ptr;
    }
    else
    {
        newptr = mm_malloc(size);
        memcpy(newptr, ptr, size);
        mm_free(ptr);
        return newptr;
    }
}

/**
 * @brief calloc - Allocate the block and set it to zero
 * @param   {size_t}    nmemb
 *          {size_t}    size
 * @return  {void *}    success  ->  已分配块的指针
 *                      fail     ->  NULL
 */
void *calloc (size_t nmemb, size_t size){
        size_t bytes = nmemb * size;
        void *newptr;

        newptr = malloc(bytes);
        memset(newptr, 0, bytes);

        return newptr;
}

/**
 * @brief mm_checkheap - Print out all of the heap and the free list info.
 * @param   {int}   verbose(no use)
 * @return  {void}  no return
 */
void mm_checkheap(int verbose) {
    char* curBp;
    int i=1;

    /* Checking the free list */
    printf("free list:\n");
    for (;i<=19;++i)
    {
        printf("size %d\n",i);
        if (free_head[i]==0){
            printf("NULL\n");
            continue;
        } 
        for (curBp=(char*)free_head[i];curBp!=(char*)free_tail[i];curBp=GET_SUCC(curBp)){
            printf("THIS_SIZE :%u , THIS_ALLOC: %d\n",THIS_SIZE(curBp),THIS_ALLOC(curBp));
        }
        printf("THIS_SIZE :%u , THIS_ALLOC: %d\n\n",THIS_SIZE(curBp),THIS_ALLOC(curBp));
    }

    /* Checking the heap */
    printf("\nheap block:\n");
    for (curBp=heap_listp;curBp!=mem_heap_hi();curBp=NEXT_BLKP(curBp)){
        printf("THIS_SIZE :%u , THIS_ALLOC: %d\n\n",THIS_SIZE(curBp),THIS_ALLOC(curBp));
    }
}


/* Helper Rountines */

/**
 * @brief coalesce - Boundary tag coalescing. 
 * @param   {void *}    bp 
 * @return  {void *}    ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        deleteNode(NEXT_BLKP(bp));
        deleteNode(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        insertNode(bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        deleteNode(PREV_BLKP(bp));
        deleteNode(bp);
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insertNode(bp);
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        deleteNode(bp);
        deleteNode(NEXT_BLKP(bp));
        deleteNode(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insertNode(bp);
    }
    return bp;
}

/**
 * @brief place - Place block of asize bytes at start of free block bp 
 *          and split if remainder would be at least minimum block size
 * @param   {void *}    bp
 *          {size_t}    bytes
 * @return  {void *}    原指针
 */
static void* place(void *bp, size_t bytes)
{
    size_t csize = THIS_SIZE(bp);   
    deleteNode(bp);
    if ((csize - bytes) >= BLOCKSIZE) { 
        PUT(HDRP(bp), PACK(bytes, 1));
        PUT(FTRP(bp), PACK(bytes, 1));
        void*nextBp= NEXT_BLKP(bp);
        PUT(HDRP(nextBp), PACK(csize-bytes, 0));
        PUT(FTRP(nextBp), PACK(csize-bytes, 0));
        insertNode(nextBp);
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    return bp;
}

/**
 * @brief find_fit - Find a fit for a block with asize bytes, 
 *            using first fit method, by getIndex function
 * @param   {size_t}    bytes
 * @return  {void *}    success  ->  找到的合适位置
 *                      fail     ->  NULL
 */
static void* find_fit(size_t bytes)
{
    void *curBp;
    int i=getIndex(bytes);
    for (;i<=19;++i)
    {
        if ((void*)free_head[i]==NULL)
            continue;
        for (curBp=(char *)free_head[i];curBp!=(void*)free_tail[i];curBp=GET_SUCC(curBp)){
            if (THIS_SIZE(curBp)>=bytes)
                return curBp;
        }
        if (THIS_SIZE(curBp)>=bytes)
            return curBp;
    }
    return NULL;
}

/**
 * @brief insertNode - Insert a block to the list,
 *          以地址顺序维护链表, 每个块的地址都小于其后继的地址
 * @param   {void *}    bp
 * @return  {void *}    bp
 */
static inline void* insertNode(void* bp)
{
    int index = getIndex(THIS_SIZE(bp));
    char *curBp = (char *)free_head[index];

    if ((void*)free_head[index]==NULL)
        free_head[index]=free_tail[index]=(size_t)bp;
    else{
        if (free_head[index]>(size_t)bp){
            PUT_SUCC(bp,free_head[index]);
            PUT_PRED(free_head[index],bp);
            free_head[index]=(size_t)bp;
        }
        else if (free_tail[index]<(size_t)bp){
            PUT_SUCC(free_tail[index],bp);
            PUT_PRED(bp,free_tail[index]);
            free_tail[index]=(size_t)bp;
        }
        else{
            while (GET_SUCC(curBp)<(char*)bp){
                curBp=GET_SUCC(curBp);
            }
            char* nextBp=GET_SUCC(curBp);
            PUT_PRED(nextBp,bp);
            PUT_SUCC(curBp,bp);
            PUT_SUCC(bp,nextBp);
            PUT_PRED(bp,curBp);
        }
    }

    return bp;
}

/**
 * @brief getType - Return a node's type
 * @param   {void *}    bp
 * @return  {int}   四种预定义类型
 */
static inline int getType(void *bp)
{
    int index=getIndex(THIS_SIZE(bp));
    if (free_head[index]==free_tail[index])
        return ALLNULL;
    else if (free_head[index]==(size_t)(bp))
        return HEADNULL;
    else if (free_tail[index]==(size_t)(bp))
        return TAILNULL;
    else
        return NORMAL;
}

/**
 * @brief deleteNode - Delete a block from the list
 * @param   {void *}    bp
 * @return  {void}      no return
 */
static inline void deleteNode(void *bp){
        int type=getType(bp);
        int i=getIndex(THIS_SIZE(bp));

        switch (type)
        {
            case ALLNULL:
                free_head[i] = free_tail[i] = (size_t)NULL;
                break;
            case HEADNULL:
                free_head[i] = (size_t)GET_SUCC(bp);
                break;
            case TAILNULL:
                free_tail[i] = (size_t)GET_PRED(bp);
                break;
            case NORMAL:
                PUT_PRED(GET_SUCC(bp),GET_PRED(bp));
                PUT_SUCC(GET_PRED(bp),GET_SUCC(bp));
                break;
        }
}

/**
 * @brief getIndex - Get the target list with proper size
 * @param   {size_t}    size
 * @return  {int}       success  ->  size所对应应分配的大小
 *                      fail     ->  -1 (control never reaches here)
 */
static inline int getIndex(size_t size){
    if (size<=(1<<4))
        return 0;
    if (size>(1<<22))
        return 19;
    int i=4;
    unsigned int nowSize=(1<<4);

    for (i=5;i<=23;++i)
    {
        nowSize<<=1;
        if (size<=nowSize){
            return i-4;
        }
    }
    return -1; /* control never reaches here ; to avoid warning */
}

/**
 * @brief extend_heap - Extend heap with free block and return its block pointer
 * @param   {size_t}    words
 * @return  {void *}    指向扩展后堆的指针
 */
static void *extend_heap(size_t words) 
{
    char *bp;

    /* Allocate an even number of words to maintain alignment */
    words = (words % 2) ? (words+1): words; 
    if ((long)(bp = mem_sbrk(words)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(words, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(words, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    /* 插入节点顺便整合 */
    return insertNode(bp);  
                                         
}

/**
 * @brief  in_heap - Return whether the pointer is in the heap.(useful for debugging)
 * @param   {const void *}  p
 * @return  {int}   1 or 0, whether the pointer is in the heap.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/**
 * @brief aligned - Return whether the pointer is aligned. (useful for debugging)
 * @param   {const void *}  p
 * @return  {int}   1 or 0, whether the pointer is aligned.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

