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

#define LIMIT (0x6400000u)
struct node {
    size_t head; //larger than necessary for size but keeps alignment correct
    struct node *prev;
    struct node *next;
};
typedef struct node node;

void printheap(void);
void printflist(void);
static inline void flist_insert(node*, node**);
static inline void flist_update(const node*, node*, node**);
static inline void flist_delete(const node*, node**);
static inline size_t block_size(const node*);
static inline char block_class(const node*);
static inline void add(node*);
const char pow = 12;
const size_t incr = 1 << pow;

#define SIZEN 7
#define SIZE11 6
#define SIZE10 5
#define SIZE9 4
#define SIZE8 3
#define SIZE7 2
#define SIZE6 1
#define SIZE5 0

static node* flist5 = NULL;
static node* flist6 = NULL;
static node* flist7 = NULL;
static node* flist8 = NULL;
static node* flist9 = NULL;
static node* flist10 = NULL;
static node* flist11 = NULL;

static n_node* flistn = NULL;

static inline void flist_insert(node* n, node** list){
    if(*list){
        n->next = *list;
        n->prev = NULL;
        (*list)->prev = n;
        *list = n;
    } else {
        n->next = NULL;
        n->prev = NULL;
        *list = n;
    }
}

static inline void flist_update(const node* old, node* new, node** list){
    if(new==old){
        flist_delete(new,list);
        flist_insert(new,list);
    } else {
        flist_insert(new,list);
        flist_delete(old,list);
    }
}

static inline void flist_delete(const node* n, node** list){
    if(n){
        if(n->next)
            n->next->prev = n->prev;
        if(n->prev)
            n->prev->next = n->next;
        else *list = n->next; //n equals list head, so update list
    }
}

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

static inline size_t block_size(const node* n){
    return n->head & 0xfffffff8; 
}

static inline char block_class(const node* n){
    return (char) (n->head & 0x7);
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
    node* n;
    size_t size = incr;
    char p = pow;
    long addr = (long) mem_sbrk(size);
    while(size != 0x20){
        size >>= 1;
        n = (node*) (addr + size);
        n->head = (size-8) | ((--p)-5); //(--p)-5 calculates size class 
        add(n);
    }
    n = (node*) addr;
    n->head = size - 8;
    flist_insert(n);
    
    return 0;
}

/* 
 */
static inline void add(node* n){
    char s = block_class(n);
    switch(s){
    case SIZE5:
        flist_insert(n, &flist5);
        break;
    case SIZE6:
        flist_insert(n, &flist6);
        break;
    case SIZE7:
        flist_insert(n, &flist7);
        break;
    case SIZE8:
        flist_insert(n, &flist8);
        break;
    case SIZE9:
        flist_insert(n, &flist9);
        break;
    case SIZE10:
        flist_insert(n, &flist10);
        break;
    case SIZE11:
        flist_insert(n, &flist11);
        break;
    case SIZEN:
        flist_insert(n, &flistn);
        break;
    }
}


//TODO:Write Malloc free and such under new scheme

/*
 * malloc
 */
void *malloc (size_t size) {
    node *n;
    checkheap(1);  // Let's make sure the heap is ok!
    size_t s = 64i, p=0;
    while(s<size+8){
        s<<=1;
        p++;
    }
    size = s>>2;
    n = flist;
    while(n){
        if(block_size((uint32_t*)n) >= size+(8<<p)){
            return found((uint32_t*)n, size+((8<<p)-8));
        }
        n = n->next; 
    }
    
    //no suitable block found in current heap call sbrk
    size_t up;
    up = (size<<2) + 8;//change to 8 to 24 if this fails ever
    if((up + mem_heapsize()) > LIMIT){
        fprintf(stderr,"out of mem\n");
        return NULL;
    }
    if(mem_sbrk(up)==(void*)-1){
        fprintf(stderr,"mem_sbrk failed\n");
        fprintf(stderr,"%zx\n",mem_heapsize()+up);
        exit(1);
    }
    //update Epilog
    node *tmp = (node*)epilog;
    tmp->head = ((up>>2)-2) | (tmp->head & PACKMASK);//this is correct
    epilog = (void*)((long)mem_heap_hi()-3);
    ((uint32_t*)epilog)[0] = 0;
    block_mark((uint32_t*)tmp,1);
    block_mark((uint32_t*)epilog, 0);
    n = (node*) coalesce((uint32_t*)tmp, NULL);//wants the pointer to the free block

    while(n){
        if(block_size((uint32_t*)n) >= size+8){
            return found((uint32_t*)n, size);
        }
        n = n->next;
    }

    //search free list for a block that will satisfy size
    
    //if block found carve out unused portion of block 
    //and place back in the free list then return pointer
    
    //if suitable block is not found in free list call
    //sbreak to increase the size of the heap
    //(somewhere we need to make sure that sizeof(heap) < 2^32)
    //After more memory is alocated get the pointer, carve the
    //chunk remaining out, and place back on free list 
    //and return the pointer
    return NULL; //shouldn't ever reach here
}

void* found(uint32_t *p, const size_t size){
    //suitable block found
    size_t oldBlockSize;
    oldBlockSize = block_size(p);
    if(size != oldBlockSize){
        //split out remaining part of block
        p[0] = size | (p[0] & PACKMASK);
        carve(p, oldBlockSize);
        p[0]&=~NALLOC;
    } else {
        flist_delete((node*)p);
        block_mark(p, 0);
    }
    //allocate and return
    checkheap(1); //make sure things are okay after allocation
    return block_mem(p);
}
/* p - header of a block in memory
 * oldBlockSize - size p used to be
 *
 * context: P has had its value set to a new size so temp is
 * the header of a new block that follows p.
 *
 * returns - pointer to the free block
 * */
void* carve(uint32_t *p, const size_t oldBlockSize){
    node *tmp, *pnode;
    tmp = (node*) block_next(p);
    tmp->head = (oldBlockSize - block_size(p) - 2) | (p[0] & NALLOC);
    if(block_free(p)){
        pnode = (node*)p;
        flist_update(pnode, tmp);
    } else {
        flist_insert(tmp);
    }
    block_mark(p, 0);
    block_mark((uint32_t*)tmp, 1);
    return tmp;
}
/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL) {
        return;
    }
    uint32_t *head = ((uint32_t*)ptr)-1;
    int insert;
    checkheap(1);
    block_mark(head,1);
    node* n = (node*) coalesce(head, &insert);//wants pointer to insert in free list
    if(insert)
        flist_insert(n);
    checkheap(1);
    //Use the header to free the block
    //and place the block in the free list
}

/* Returns - pointer to the newly combined block
 */
void* coalesce(uint32_t* head, int* needToInsert){
    uint32_t* prev;
    int new = 1;
    if(needToInsert)
        *needToInsert = 1;
    if(next_free(head)){
        combine(head, block_next(head), new++);
        if(needToInsert)
            *needToInsert = 0;
    }
    else{new =0;}
    if(prev_free(head)){
        combine(prev = block_prev(head), head, new);
        if(needToInsert)
            *needToInsert = 0;
        return prev;
    }
    return head;
}

void combine(uint32_t *p, uint32_t *n, int flag){
    size_t newSize;
    node* prev = (node*)p;
    node* next = (node*)n;
    newSize = block_size(p)+block_size(n)+2;
    prev->head = newSize | (prev->head & PALLOC) | (next->head & NALLOC);
    if(flag == 1){
        flist_update(next, prev); //removes next inserts prev at front
    } else {
        if(flag == 2)
            flist_delete(next);   //next and prev both need to be removed
        flist_update(prev, prev); //moves prev to front of list
    }
    block_mark(p,1);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    void *newptr;
    size_t oldsize, newsize;
    uint32_t *oldhead;
    checkheap(1);
    size = (size + 0x7) & ~0x7;
    if(size == 0){
        free(oldptr);
        return 0;
    }
    if(oldptr == NULL)
        return malloc(size);
    if(size<24) size = 24;
    newsize = size>>2;
    oldhead = (uint32_t*)oldptr - 1;
    oldsize = block_size(oldhead);
    if(oldsize == newsize)
        return oldptr; 

    /*
    //figure out if this is actually better than the the method
    //in the given naieve source.

    if(oldsize > newsize){
        //copy first size bytes of oldptr to newptr
        oldhead[0] = newsize | (oldhead[0] & (PALLOC|ALLOC));
        node* n = (node*) carve(oldhead, oldsize);
        coalesce((uint32_t*)n, &insert);
        if(insert)
            flist_insert(n);
        checkheap(1);
        return oldptr;
    }*/
    newptr = malloc(size);
    //copy first oldSize bytes of oldptr to newptr
    oldsize = newsize < oldsize ? newsize<<2 : oldsize<<2;
    memcpy(newptr,oldptr, oldsize);
    free(oldptr);
    checkheap(1);
    return newptr;
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
    uint32_t *p, *prev, *next;
    int count = 0;
    if(prolog != (void*)((long)mem_heap_lo()+4)){
        if(verbose) fprintf(stderr,"prolog corrupt\n");
        return 1;
    }
    if(block_size(prolog)!=0){
        fprintf(stderr,"prolog value corrupt\n");
        fprintf(stderr,"prolog:%p, sz:%d\n",prolog,block_size(prolog));
        return 1;
    }
    if(epilog != (void*)((long)mem_heap_hi()-3)){
        if(verbose) fprintf(stderr,"epilog corrupt\n");
        return 1;
    }
    if(block_size(epilog)!=0){
        fprintf(stderr,"epilog value corrupt\n");
        return 1;
    }
    
    p = (uint32_t*)prolog;
    while(p != epilog && in_heap(p)){
        if(block_free(p)) 
            count++;
        if(!aligned(p+1)){
            if(verbose) fprintf(stderr,"block not aligned\n");
            fprintf(stderr,"p+1:%p\n",(void*)(p+1));
            return 1;
        }
        if(p[0]!=p[block_size(p)+1]){
            if(verbose) fprintf(stderr,"header footer mismatch\n");
            fprintf(stderr,"hs:%d fs:%d\n",block_size(&p[0]), block_size(&p[block_size(p)+1]));
            return 1;
        }
        next = block_next(p);
        prev = block_prev(p);
        if(in_heap(next) && (next_free(p) ^ block_free(next))){
            if(verbose) fprintf(stderr,"bitpack: NALLOC incorrect\n");
            fprintf(stderr,"bitpack:%d, actual:%d\n",next_free(p),block_free(next));
            return 1;
        }
        if(in_heap(prev) && (prev_free(p) ^ block_free(prev))){
            if(verbose) fprintf(stderr,"bitpack: PALLOC incorrect\n");
            return 1;
        }
        if(in_heap(next) && block_free(p) && next_free(p)){
            if(verbose) fprintf(stderr,"coalesce error: 2 adjacent free blocks\n");
            fprintf(stderr,"psz:%d, nsz:%d\n",block_size(p), block_size(next));
            return 1;
        }
        p = block_next(p);
    }
    node* n = flist;
    while(n){
        if(n->next){
            if(n->next->prev != n){
                fprintf(stderr,"next elements previous element isn't this element\n");
                return 1;
            }
        }
        if(n->prev){
            if(n->prev->next != n){
                fprintf(stderr,"previous elements next element isn't this element\n");
                return 1;
            }
        }
        if(!block_free((uint32_t*)n)){
            fprintf(stderr,"allocated block on the free list\n");
            return 1;
        }
        if(!in_heap((uint32_t*)n)){
            fprintf(stderr,"you dun goofed real good\n");
            return 1;
        }
        n = n->next;
        count--;
    }
    if(count){
        fprintf(stderr,"Uh oh, %d free blocks not on free list\n",count);
        return 1;
    }
    return 0;
}
void printheap(){
    uint32_t *p = (uint32_t*)prolog;
    while(p != epilog){
        fprintf(stdout,"[%p %d %c]",(void*)p,block_size(p), block_free(p)?'f':'a');
        p = block_next(p);
    }
    fprintf(stdout,"\n");
}
void printflist(){
    node* n = flist;
    while(n){
        fprintf(stdout,"{h:%p s:%d p:%p n:%p}",(void*)n, block_size((uint32_t*)n), (void*)n->prev, (void*)n->next);
        n = n->next;
    }
    fprintf(stdout,"\n");
}
