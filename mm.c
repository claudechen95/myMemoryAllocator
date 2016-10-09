// Name : Claude Chen 
// Andrew ID :qiangc
// uses segregated list(pointer array) and explicit free list to implement
// system call malloc 
//
// if (mood == upset) write_a_poem();
// void write_a_poem(void){
// printf("%s \n",
// 一二三四五
// CS 好辛苦
// 一码一上午
// 不吐不舒服
// bug 一直出
// 我积极对付
// 可对手威武
// 我脑子鱼木
// 想要rush it thru
// 又花一下午
// 可惜没进度
// 一切白辛苦
// 我编程之路
// 真含辛茹苦
// 日夜拼学术
// 却班级倒数
// 我投降认输
// 求放我生路
// 其实还不如
// 每个星期五
// 写诗跳跳舞
// GPA 2.5
// 又有谁在乎
// 把觉睡睡足
// 还没到25
// 就头顶狂秃
// 毛还剩几簇
// 我来数一数
// 一二三四五.....)}




/* 
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first-fit placement, and boundary tag coalescing, as described
 * in the CS:APP3e text. Blocks must be aligned to doubleword (8 byte) 
 * boundaries. Minimum block size is 16 bytes. 
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/*
 * If NEXT_FIT defined use next fit search, else use first-fit search 
 */
#define NEXT_FITx

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define TSIZE 		12  	/* Triple word size (bytes) */
#define QSIZE       16       /* Quad word size (bytes) = minimum block size*/
#define FIFTEENSIZE 120       /* 15 word size (bytes)*/
#define CHUNKSIZE  (1<<8)   /* Extend heap by this amount (bytes) */  
#define SEG_LIST_LEN 15     /*the length of seg_list*/

#define MAX(x, y) ((x) > (y)? (x) : (y))  

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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Given a pointer,computes its offset*/
#define GET_OFFSET(bp) (bp ==NULL? 0 : ((unsigned int)((void*)bp - heap_start)))

//pointer + WSIZE
#define PWSIZE(bp) (bp+WSIZE) 
// just to make it cleaner
#define GET1(fbp) (GET(PWSIZE(fbp))) 


/* Given block ptr fbp, compute address of next and previous free blocks */
#define NEXT_FREE_BLKP(fbp) ((GET1(fbp)==0)?NULL:(void*)(GET1(fbp)+heap_start))
#define PREV_FREE_BLKP(fbp) ((GET(fbp)==0)?NULL:((void*)(GET(fbp)+heap_start)))  

/* given two pointers ,set the next of the first pointer
to be another pointer */
#define SET_NEXT(fbp,next) (PUT(fbp+WSIZE,GET_OFFSET(next)))
#define SET_PREV(fbp,prev) (PUT(fbp,GET_OFFSET(prev)))






/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */ 
static char **seg_listp = 0; /* root pointer to the first free list*/ 
static void *heap_start = 0;/* heap_start =  mem_heap_lo()*/




/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static unsigned int get_group(size_t asize);
static void insert(void *bp,size_t groupNum);
static void delete(void *bp,size_t groupNum);
static void checkblock(void * bp, int lineno);
static void checkfreelistcount(int lineno);
static void checkfreelist(void *fb, size_t groupNum, int lineno);

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
    /* Initialize the segregated list array */
    if ((seg_listp = mem_sbrk(FIFTEENSIZE)) == (void *)-1)
        return -1;

    /* Create the initial empty heap*/
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    /* Initialize the segregated list array to NULL */
    for (size_t num = 0; num < SEG_LIST_LEN; num++) {
        seg_listp[num] = NULL;
    }

    heap_start = mem_heap_lo();
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (DSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (QSIZE);     

    //mm_checkheap(__LINE__);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

/* 
 * malloc - Allocate a block with at least size bytes of payload 
 */
void *malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          
        asize = QSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

    //mm_checkheap(__LINE__);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) { 
        place(bp, asize);    

        //mm_checkheap(__LINE__);

        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);


    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;    
    //mm_checkheap(__LINE__);
                         
    place(bp, asize);                                 
    return bp;
}

/* 
 * ffree - Free a block 
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
    insert(bp,get_group(size));
    coalesce(bp);
    //mm_checkheap(__LINE__);
}

/*
 * realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}


/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *newptr;
    newptr = malloc(bytes);
    if (newptr == NULL) return NULL;
    memset(newptr, 0, bytes);
    return newptr;
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
    {
    	printf("allocation error\n");
        return NULL;                                        
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    insert(bp,get_group(size));

  	
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
    

    if (prev_alloc && next_alloc) return bp;   /* Case 1 */ 
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
    	//next is a free block
    	delete(bp,get_group(size));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        void* next = NEXT_BLKP(bp);
        delete(next,get_group(GET_SIZE(HDRP(next))));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
        insert(bp,get_group(size));
    }

    else if (!prev_alloc && next_alloc) {    /* Case 3  prev is free block */
    	//prev is a free block
        delete(bp,get_group(size));
        void* prev = PREV_BLKP(bp);
        delete(prev,get_group(GET_SIZE(HDRP(prev))));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = prev;
        insert(bp,get_group(size));
    }

    else {/* Case 4 */
    	
    	//prev and next both are free blocks 
    	void* prev = PREV_BLKP(bp);
    	void* next = NEXT_BLKP(bp);
    	delete(bp,get_group(size));
    	delete(prev,get_group(GET_SIZE(HDRP(prev))));
    	delete(next,get_group(GET_SIZE(HDRP(next))));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = prev;
        insert(bp,get_group(size));
        
    }
    //mm_checkheap(__LINE__);
    return bp;
}


//insert a free block to the seglist according to the groupNum
static void insert(void *bp , size_t groupNum){
	void* front = seg_listp[groupNum];
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
	if (front == NULL){
		seg_listp[groupNum] = bp;
		SET_PREV(bp,NULL);
		SET_NEXT(bp,NULL);
	}
	else{
		SET_NEXT(bp,front);
		SET_PREV(front,bp);
		SET_PREV(bp,NULL);
		seg_listp[groupNum] = bp;
	}
	
}

// delete the free block denoted by bp.
static void delete(void *bp ,size_t groupNum){
	size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 1));
    PUT(FTRP(bp), PACK(size, 1));
	if (GET(bp) == 0) // first one
	{	
		size_t tem = GET(bp+WSIZE);
		if (tem ==0) seg_listp[groupNum] = NULL; // the only one 
		else
		{
			//the first but not the only one 
			void* next = NEXT_FREE_BLKP(bp);
			seg_listp[groupNum] = next;
			SET_PREV(next,NULL);
		}
	}
	else if (GET(bp+WSIZE) == 0) SET_NEXT(PREV_FREE_BLKP(bp),NULL);
		//not the only one but the last one 
	else{
		//in the middle
		void* prev = PREV_FREE_BLKP(bp);
		void* next = NEXT_FREE_BLKP(bp);
		SET_NEXT(prev,next);
		SET_PREV(next,prev);
	}
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   
    PUT(HDRP(bp), PACK(csize, 0));
    PUT(FTRP(bp), PACK(csize, 0));

    if ((csize - asize) >= (QSIZE)) {
    	// split into two blocks
    	size_t groupNum = get_group(csize);
    	delete(bp,groupNum);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void *nbp = NEXT_BLKP(bp);
        PUT(HDRP(nbp), PACK(csize-asize, 0));
        PUT(FTRP(nbp), PACK(csize-asize, 0));
        insert(nbp,get_group(csize-asize));    }
    else { 
    	// no need to split
    	delete(bp,get_group(csize));
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
	//mm_checkheap(__LINE__);
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    void *fbp; /* free block pointer */
    int group = get_group(asize);
    for (size_t groupNum = group;groupNum < SEG_LIST_LEN;groupNum++)
    {
        for(fbp = seg_listp[groupNum];fbp!=NULL; fbp = NEXT_FREE_BLKP(fbp)) 
        {
    		if (GET_SIZE(HDRP(fbp))>= asize) {
    			return fbp;
    		}
     	}	
    }
    return NULL;
}

/*get the group number for the free block */
static unsigned int get_group(size_t asize){
	if (asize <= 32)return 0;
	else if (asize <= 64) return 1;
	else if (asize <= 128) return 2;
	else if (asize <= 256) return 3;
	else if (asize <= 512) return 4;
	else if (asize <= 1024) return 5;
	else if (asize <= 2048) return 6;
	else if (asize <= 4096) return 7;
	else if (asize <= 8192) return 8;
	else if (asize <= 16384) return 9;
	else if (asize <= 18384) return 10;
	else if (asize <= 20384) return 11;
	else if (asize <= 22384) return 12;
	else if (asize <= 24384) return 13;
	else  return 14;
}




/* check a block on the heap */
static void checkblock(void * bp, int lineno) {
    /* check if size >= MINIMUMSIZE */
    if (GET_SIZE(HDRP(bp)) < QSIZE) {
        printf("block size error at line %d\n", lineno);
        exit(1);
    }

    /*  header should be euqal to the footer */
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("block header error at line %d\n",lineno);
        exit(1);
    }

    /* Check coalescing */
    if (GET_ALLOC(HDRP(bp)) == 0 && GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0) {
        printf("consective free blocks error at line %d\n", lineno);
        exit(1);
    }
}

/*
 * checkfreelist - Check all the free blocks in this free list
 */
static void checkfreelist(void *fb, size_t groupNum, int lineno) {
    
    if (fb == NULL)return;//empty
    else {
        char *curr = fb;
        for (;NEXT_FREE_BLKP(curr) != NULL;curr = NEXT_FREE_BLKP(curr)){
            if (GET_ALLOC(HDRP(curr)) != 0) {
                printf("Alloc bit error at line %d\n", lineno);
                exit(1);
            }

            /* Check if the free block belongs to this groupNum */
            if (get_group(GET_SIZE(HDRP(curr))) != groupNum) {
                printf("wrong groupNum at line %d\n", lineno);
                exit(1);
            }
        }

        /* take care of the last block in the free list */
        if (GET_ALLOC(HDRP(curr)) != 0) {
            printf("alloc bit error at line %d\n", lineno);
            exit(1);
        }
        if (get_group(GET_SIZE(HDRP(curr))) != groupNum) {
            printf("last block wrong groupNum at line %d,%d,%d\n", lineno,
            	get_group(GET_SIZE(HDRP(curr))),(int)groupNum);
            exit(1);
        }
    }
}


/*
 * check if the number of free lists on the heap agrees with the number of
 * free lists on the seg list.
 */
static void checkfreelist2(int lineno) {
    lineno++;
    size_t HEAPfb = 0;
    size_t SEGfb = 0;
    char *bp;
    /* go through the segregated free list */
    for (size_t num = 0; num < SEG_LIST_LEN; num++) {
        for (char *current =seg_listp[num];current != NULL;current = 
        	NEXT_FREE_BLKP(current)){
        	SEGfb ++;
        }   
    }

    /* go through blocks on the heap */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if (GET_ALLOC(HDRP(bp)) == 0) {
            HEAPfb++;   
        }
    }	

    if (HEAPfb != SEGfb) {
        printf("free blocks error %d\n", lineno);
        exit(1);
    }
}

/* 
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
void mm_checkheap(int lineno) {


    /*Check all the free lists */
    for (size_t num = 0; num < SEG_LIST_LEN; num++) {  
        checkfreelist(seg_listp[num],num,lineno);
    }
    /* checks all the blocks on the heap*/
    char *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        checkblock(bp,lineno);
    }
    checkfreelist2(lineno);
    return;
}






