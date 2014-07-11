/*
 * mm.c
 * jdbrando - Jeff Brandon
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a full description of your solution.
 * Power of 2 size allocations.
 * first fit.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

#define ALLOC (1<<30)
#define NALLOC 1
#define PALLOC (1<<31)
#define WORD 4
#define DUB (WORD << 1)
void coalesce(void);
void combine(uint32_t*, uint32_t*);
void* found(uint32_t*, size_t);
void carve(uint32_t*, size_t);
static inline uint32_t* block_next(uint32_t* const);
static inline uint32_t* block_prev(uint32_t* const);
static inline void mark_prev(uint32_t*, int);
static inline void mark_next(uint32_t*, int);
static void* prolog;
static void* epilog;
static uint32_t* last_allocated;
size_t incr = 1<<11;

struct fnode{
    struct fnode *prev;
    struct fnode *next;
    void* val;
};
typedef struct fnode fnode;

fnode *freelist = NULL;

/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

// Return the size of the given block in multiples of the word size
// returns least significant 30 bits which are used to represent size
// of the block in multiples of 4
// if 2 is returned block size is 8 bytes
static inline unsigned int block_size(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (block[0] & 0x3FFFFFFE);
}

// Return true if the block is free, false otherwise
// Checks 30th (counting from 0) bit, if it is set the block is allocated 
static inline int block_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(block[0] & 0x40000000);
}

static inline int next_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    //REQUIRES(in_heap((void*)block_next(block)));

    return !(block[0] & 0x1);
}

static inline int prev_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    //REQUIRES(in_heap((void*)block_prev(block)));

    return !(block[0] & 0x80000000);
}

// Mark the given block as free(0)/alloced(1) by marking the header and footer.
// set 30th bit according to weather block is being marked as free or allocated
// set header and footer
static inline void block_mark(uint32_t* block, int free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    unsigned int next = block_size(block) + 1;
    block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
    block[next] = block[0];
    uint32_t* tmp = block_next(block);
    if(in_heap((void*)tmp)){
        mark_prev(tmp, free);
    }
    if(in_heap(block_prev(block))){
        mark_next(block_prev(block), free);
    }
}

static inline void mark_next(uint32_t* block, int free){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(in_heap((void*)block_next(block)));
    
    unsigned next = block_size(block) + 1;
    block[0] = free ? block[0] & 0xfffffffe : block[0] | 0x1;
    block[next] = block[0];
}

static inline void mark_prev(uint32_t* block, int free){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(in_heap((void*)block_prev(block)));
    
    unsigned next = block_size(block) + 1;
    block[0] = free ? block[0] & 0x7fffffff : block[0] | 0x80000000;
    block[next] = block[0];
}

// Return a pointer to the memory malloc should return
// using pointer arithmatic
static inline uint32_t* block_mem(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block + 1));

    return block + 1;
}

// Return the header to the previous block
// subtract size of previous block from current block and then 2 
// to account for header and footer
static inline uint32_t* block_prev(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block - block_size(block - 1) - 2;
}

// Return the header to the next block
// similarly add the size of the current block plus 2 to 
// account for header and footer
static inline uint32_t* block_next(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block + block_size(block) + 2;
}


/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    //alocate some blocks so they are ready for the first malloc
    void *res;
    uint32_t *tmp, t;
    res = mem_sbrk(incr);
    if((long)res == -1){
        fprintf(stderr,"mem_sbrk failed\n");
        exit(1);
    }
    prolog = (void*)((long)mem_heap_lo()+4);
    epilog = (void*)((long)mem_heap_hi()-3);
    //init prolog and epilog
    tmp = (uint32_t*)prolog;
    *(tmp-1) = 0x0;                     //4 byte padding
    *tmp = (uint32_t)0x0 | ALLOC;	//allocate prolog header forever
    *(tmp+1) = (uint32_t)0x0 | ALLOC;	//prolog footer
    t = ((mem_heapsize()>>2)-6) & ~ALLOC; //calculate size of initial block
    t = t | NALLOC | PALLOC;            //mark previous and next blocks alloced
    *(tmp+2) = t;			//set block header
    tmp = (uint32_t*)epilog;
    *tmp = 0x0 | ALLOC;			//epilog is header only
    *(tmp-1) = t; 			//set block footer
    //TODO:figure out if any thing else needs to be done here
    last_allocated = (uint32_t*)prolog;
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    uint32_t *p;
    checkheap(1);  // Let's make sure the heap is ok!
    
    size = (size + 7) & ~7; //align size to next 8 byte slot

    p = last_allocated;
    p = block_next((uint32_t* const)p);
    while(in_heap((void*)p)){
        if(block_size(p) >= size && block_free(p)){
            return found(p, size);
        }
        p = block_next(p);
    }
    p = block_next((uint32_t*)prolog);
    while(p != last_allocated && in_heap((void*)p)){
        if(block_size(p) >= size && block_free(p)){
            return found(p, size);
        }
        p = block_next(p);
    }
    
    //no suitable block found in current heap call sbrk
    if(mem_sbrk(incr)==(void*)-1){
        fprintf(stderr,"mem_sbrk failed\n");
        exit(1);
    }
    //update Epilog
    *((uint32_t*)epilog)=incr-2;
    free((void*)((long)epilog+4));
    epilog = (void*)((long)mem_heap_hi()-3);
    ((uint32_t*)epilog)[0] = 0;
    block_mark((uint32_t*)epilog, 0);

    if(mem_heapsize() <= -1u)
        return malloc(size);
    else return NULL;

    //search free list for a block that will satisfy size
    
    //if block found carve out unused portion of block 
    //and place back in the free list then return pointer
    
    //if suitable block is not found in free list call
    //sbreak to increase the size of the heap
    //(somewhere we need to make sure that sizeof(heap) < 2^32)
    //After more memory is alocated get the pointer, carve the
    //chunk remaining out, and place back on free list 
    //and return the pointer
}

void* found(uint32_t *p, size_t size){
    //suitable block found
    size_t oldBlockSize;
    oldBlockSize = block_size(p);
    p[0] = size >> 2;
    if(p[0] != oldBlockSize){
        //carve out remaining part of block
        carve(p, oldBlockSize);
    }
    block_mark(p, 0);
    //allocate and return
    last_allocated = p;
    checkheap(1); //make sure things are okay after allocation
    return block_mem(p);
}
void carve(uint32_t *p, size_t oldBlockSize){
    uint32_t *tmp;
    tmp = block_next(p);
    tmp[0] = oldBlockSize - p[0] - 2;
    block_mark(tmp, 1);
}
/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL) {
        return;
    }
    uint32_t *head = ((uint32_t*)ptr)-1;
    block_mark(head,1);

    if(in_heap(block_prev(head)))    
        if(prev_free(head))
            combine(block_prev(head), head);

    if(in_heap(block_next(head)))
        if(next_free(head))
            combine(head, block_next(head));
    //Use the header to free the block
    //and place the block in the free list
}

void coalesce(){
    uint32_t *p, *next;
    p = block_next((uint32_t*)prolog);
    next = block_next(p);
    while(next != epilog){
        //traverse heap inline
        //if p is free and next is free
        //combine them into one block
        //set next from new block and continue
        if(block_free(p) && block_free(next)){
            combine(p,next);
            next = block_next(p);
            continue;
        }
        p = next;
        next = block_next(next);
    }
}

void combine(uint32_t *p, uint32_t *n){
    size_t newSize;
    newSize = block_size(p)+block_size(n)+2;
    p[0] = newSize | (p[0] & 0x80000000) | (n[0] & 0x1);
    block_mark(p,1);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    void *newPtr;
    size_t oldSize, i;
    uint32_t *oPtr, *nPtr;
    if(size == 0){
        free(oldptr);
        return 0;
    }
    if(oldptr == NULL)
        return malloc(size);
    oldSize = block_size(oldptr);
    if(oldSize == size)
        return oldptr; 

    newPtr = malloc(size);
    oPtr = (uint32_t*) oldptr;
    nPtr = (uint32_t*) newPtr;
    if(oldSize > size){
        //copy first size ints of oldptr to newptr
        for(i=0; i<size; i++)
            nPtr[i] = oPtr[i];
    } else {
        //copy first oldSize ints of oldptr to newptr
        for(i=0; i<oldSize; i++)
            nPtr[i] = oPtr[i];
    }
    free(oldptr);
    return newPtr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    void* newptr;
    newptr = malloc(nmemb * size);
    memset(newptr, 0, nmemb * size);
    return newptr;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    uint32_t *p;
    if(prolog != (void*)((long)mem_heap_lo()+4)){
        if(verbose) fprintf(stderr,"prolog corrupt\n");
        return 1;
    }
    if(epilog != (void*)((long)mem_heap_hi()-3)){
        if(verbose) fprintf(stderr,"epilog corrupt\n");
        return 1;
    }
    
    p = (uint32_t*)prolog;
    while(p != epilog){
        if(!aligned((void*)p)){
            if(verbose) fprintf(stderr,"block not aligned\n");
            return 1;
        }
        if(p[0]!=p[block_size(p)+1]){
            if(verbose) fprintf(stderr,"header footer mismatch\n");
        }
        p = block_next(p);
    }
    
    return 0;
}
