/*
 * mm.c
 * jdbrando - Jeff Brandon
 *
 * This implementation of a dynamic memory allocator uses segregated
 * free lists with sizes equal to exactly 2^n for n in [5,11]. Smaller sizes
 * are allocated to a block of 32 to bytes (n=5) and larger blocks are 
 * maintained on an 8th free list for blocks greater than size 2040.
 * Allocations are of exactly 2^n bytes and headers are stored inside
 * those allocations so payloads are equal to (2^n - 8) where 8 is the size
 * of the block header for blocks of size 2^5 and 2^11. For larger blocks
 * the size is exactly what is requested. 
 *
 * The free lists are not sorted, insertion is simply done at the head of the 
 * list. 
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
/* this struct is used for referencing data in an organized way
 * head represents the block header
 * a serves as a boolean flag representing weather the block
 * is allocated or free
 * prev and next point to the next and previous free blocks in the
 * appropriate list repectively
 * prev_alloc, next_alloc, and b are unused and serve as padding
 * to ensure correct allignment.
 */
struct node {
    uint32_t head;
    char prev_alloc; //in order to utilise all space use 4 unused bytes for 
    char next_alloc; //additonal metadata. Not sure exactly what that is yet
    char a;          //Right now I'm thinking data on adjacent blocks in the heap
    char b;          //Bitmaps may be useful also
    struct node *prev;
    struct node *next;
};
typedef struct node node;

void printheap(void);
void printflist(char);
void printallflist(void);
static inline void flist_insert(node*, node**);
static inline void flist_update(const node*, node*, node**);
static inline void flist_delete(const node*, node**);
static inline size_t block_size(const node*);
static inline char block_class(const node*);
static inline char block_free(const node*);
static inline node* block_next(const node*);
static inline void add(node*);
static inline void delete(node*);
static inline void* found(node*, const char);
static inline node* get_list(char);
static inline node** get_list_addr(char);
static inline char get_class(size_t);
int check_flist(node*, char, int*);
node* split(char);
int combine(char, node**);
static inline void do_split(node*, const char);
const char power = 12;
const size_t incr = 1 << 12;

/* The following definitions represent size classes
 * the number represents the n in 2^n and the value
 * SIZEN is unique in that it is the only list with variable
 * size blocks
 */
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
static node* flistn = NULL;

/* Insert a node into a list, if the list is NULL
 * set list to n.
 * n - The node to insert
 * list - the address of the list to insert into
 */
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

/* Update a list
 */
static inline void flist_update(const node* old, node* new, node** list){
    if(new==old){
        flist_delete(new,list);
        flist_insert(new,list);
    } else {
        flist_insert(new,list);
        flist_delete(old,list);
    }
}

/* Delete a node from a list
 * n - the node to delete
 * list - the address of the list n is an element of
 * to perform the delete update the predecessor of n to
 * point to the successor of n as its next element and likewise 
 * update the successor of n to point to the predecessor of n as 
 * its previous element. 
 * One special case is when n has no previous element, signifying
 * n is the head of the list. If this is the case it is important to update
 * the list to set it to the node located at n->next.   
 */
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

/* For classes 0-6 return the appropriate (2^n)-8
 * for class 7 return the size portion of n->head
 */
static inline size_t block_size(const node* n){
    switch(block_class(n)){
    case SIZE5:
        return 0x20 - 8;
    case SIZE6:
        return 0x40 - 8;
    case SIZE7:
        return 0x80 - 8;
    case SIZE8:
        return 0x100 - 8;
    case SIZE9:
        return 0x200 - 8;
    case SIZE10:
        return 0x400 - 8;
    case SIZE11:
        return 0x800 - 8;
    default:
        return n->head & 0xfffffff8; 
    }
}

//return least significant 3 bits that store block class information
static inline char block_class(const node* n){
    return (char) (n->head & 0x7);
}

//Calculate next block location using size of current block
static inline node* block_next(const node* n){
    if(block_class(n) < SIZEN)
        return (node*)((size_t)n + (1<<(block_class(n)+5)));
    return (node*)((long) n + block_size(n) + 8);
    
}

//check the allocated flag
static inline char block_free(const node* n){
    return !(n->a);
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
    char p = power;
    long addr = (long) mem_sbrk(size);
    //init free lists to NULL
    flist5 = flist6 = flist7 = flist8 = flist9 = flist10 = flist11 = flistn = NULL;
    if(addr == -1){
        fprintf(stderr,"mm_init failed calling mem_sbrk\n");
        return -1;
    }
    //Start with block of size 2^12
    //split it and add one block to the free list
    //then split the other and repeat until there is
    //one block of each class in each free list
    //except the smallest which will have 2 blocks
    while(size != 0x20){
        size >>= 1;
        n = (node*) (addr + size);
        n->head =(--p)-5; //(--p)-5 calculates size class 
        n->prev_alloc = 0;
        n->next_alloc = 0;
        n->a = 0;
        n->b = 0;
        add(n);
    }
    n = (node*) addr;
    n->head = 0;
    n->prev_alloc = 0;
    n->next_alloc = 0;
    n->a = 0;
    n->b = 0;
    flist_insert(n, &flist5);
    
    checkheap(1);
    return 0;
}

/* Extract the class of the block and add to the appropriate
 * free list based on that.
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

/* Determine class of the block and delete from appropriate 
 * free list
 */
static inline void delete(node* n){
    switch(block_class(n)){
    case SIZE5:
        flist_delete(n, &flist5);
        break;
    case SIZE6:
        flist_delete(n, &flist6);
        break;
    case SIZE7:
        flist_delete(n, &flist7);
        break;
    case SIZE8:
        flist_delete(n, &flist8);
        break;
    case SIZE9:
        flist_delete(n, &flist9);
        break;
    case SIZE10:
        flist_delete(n, &flist10);
        break;
    case SIZE11:
        flist_delete(n, &flist11);
        break;
    default:
        flist_delete(n, &flistn);
    }
}

/*
 * malloc
 */
void *malloc (size_t size) {
    node *n;
    char p;
    checkheap(1);  // Let's make sure the heap is ok!
    p = get_class(size);
    n = get_list(p);
    if(p<7){
        //allocate any block on the list because it is the best size
        //for that request
        if(n) //there exists a block of the size we're looking for already
            return found(n, p);
        if(combine(p-1, &n)){ //try and combine 2 blocks of the class below
            n->a = 1;
            return (void*) &n->prev;
        }
        //if the above fails split a larger block
        n = split(p+1);
        n->a = 1;
        checkheap(1);
        return (void*) &n->prev;
    }
    else{
        //search flistn for a free block that will suit our needs
        n = flistn;
        while(n){
            if(block_size(n) >= size+8) //found a block
                return found(n, SIZEN);
            n = n->next;
        }
        //Requested size is larger than blocks we keep on hand under
        //normal circumstances, call sbrk for a variable
        //size block, store its size in its header so that it can be
        //accurately measured when it is freed.
        size_t up = (size + 0x7 ) & ~0x7; //align size to 8
        up += 8; //account for metadata
        if((up + mem_heapsize()) > LIMIT){
            fprintf(stderr,"out of mem\n");
            return NULL;
        }
        n = (node*) mem_sbrk(up+24);//firefox-reddit.rep breaks if i dont add 24 here
        if(n == (node*) -1){
            fprintf(stderr,"mem_sbrk failed\n");
            return NULL;
        }
        n->head = (up-8) | SIZEN; //dont acount for metadata when accounting for
        n->a = 1;                 //size of the allocation
        checkheap(1);
        return (void*) &n->prev;
    }
    return NULL; //shouldn't ever reach here
}

/* Based on a requested size of allocation, get
 * the class of block we will allocate for that request
 */
static inline char get_class(const size_t size){
    size_t s = 1<<5;
    char  p = 0;
    while((s<<p) < size+8)
        p++;
    return p;
}

//based on a class get the appropriate flist
static inline node* get_list(const char p){
    switch(p){
    case SIZE5:
        return flist5;
    case SIZE6:
        return flist6;
    case SIZE7:
        return flist7;
    case SIZE8:
        return flist8;
    case SIZE9:
        return flist9;
    case SIZE10:
        return flist10;
    case SIZE11:
        return flist11;
    default:
        return flistn; 
    }
}

//based on class get appropriate flist address
static inline node** get_list_addr(const char p){
    switch(p){
    case SIZE5:
        return &flist5;
    case SIZE6:
        return &flist6;
    case SIZE7:
        return &flist7;
    case SIZE8:
        return &flist8;
    case SIZE9:
        return &flist9;
    case SIZE10:
        return &flist10;
    case SIZE11:
        return &flist11;
    default:
        return &flistn; 
    }
}

/* Get a block of size class specified by p
 * (call recursively if necessary)
 * Remove it from it's respective list
 * split it in half
 * add the second half to the appropriate free list
 * return the first half
 */
node* split(char class){
    node** listptr, *n;
    if(class < 1){
        fprintf(stderr,"\n\n\nsplit should never be called with a value less than 1!!\n\n\n");
        return NULL;
    }
    if(class > 6){
        //Call sbrk
        //similar to mm_init, get block of size 2^12 and split it
        if((mem_heapsize()+incr) > LIMIT){
            fprintf(stderr, "Uh oh what do we do here?\n");
            return NULL;
        }
        n = (node*) mem_sbrk(incr);
        if(n == (node*)-1){
            fprintf(stderr,"mem_sbrk failed!!\n");
            return NULL;
        }
        do_split(n, SIZEN); 
        return n;
    }
    listptr = get_list_addr(class);
    if((n = *listptr)){ //list is not empty
        //we've found a block to split!
        delete(n);
        do_split(n, class);
        return n;
    }
    if(class<7){
        n = split(class+1); //call split recursively
        do_split(n, class);
        //TODO: consider coalescing here
        return n;
    }
    else{
        fprintf(stderr, "I didn't think the code could get here initially... interesting\n");
        return NULL;
    }
}

/* Given a node of a class, break it into two nodes of
 * class (class-1). Add the second node to the appropriate
 * free list. At the end of this function n will be half the size it
 * was previously. 
 */
static inline void do_split(node* n, const char class){
    node* m;
    n->head = class-1;
    m = block_next(n);
    m->head = class-1;
    m->a = 0;
    add(m);
}

/* Remove the block from it's list
 * mark the header to indicate size class
 * return a pointer to the 8 byte aligned address just beyond the nodes metadata
 */
static inline void* found(node *n, const char class){
    //suitable block found
    flist_delete(n, get_list_addr(class));
    n->a = 1;
    //TODO: see about marking next block
    checkheap(1);
    return (void*) &n->prev;
}

/* Attempts to combine two blocks of size class into one block of size class+1
 * returns 0 if the combine fails. On success, returns 1 and res points to the
 * combined block.
 * under current implementation free lists are not sorted so iterate through the
 * appropriate free list and check if the next block in the heap is both free and
 * also the appropriate size class. If it is remove both block from the free list
 * combine them, set res and return. If we reach the end of the list  combine 
 * fails.
 */
int combine(char class, node** res){
    node *m, *n;
    if(class > 5 || class < 0) 
        return 0;
    n = get_list(class);
    while(n){
        m = block_next(n);
        if(in_heap(m) && block_free(m) && (block_class(m) == class)){
            delete(m); delete(n);
            n->head = (class+1) | (n->head & 0xfffffff8);
            *res = n;
            return 1;
        }
        n = n->next;
    }
    return 0;
}

/*
 * free
 */
void free (void *ptr) {
    char class;
    if (ptr == NULL) {
        return;
    }
    checkheap(1);
    node *n = (node*)(((long)ptr)-8);
    //Use the header to free the block
    //and place the block in the free list
    n->a = 0;
    add(n);
    class = block_class(n);
    //while(class<6){
        //combine blocks of the returned blocks size class until we fail
        while(combine(class,&n)){
            add(n);
        }
        //class++;
    //}
    checkheap(1);
}
/*
 * realloc 
 */
void *realloc(void *oldptr, size_t size) {
    void *newptr;
    size_t oldsize;
    node* old;
    if(size == 0){
        free(oldptr);
        return 0;
    }
    if(oldptr == NULL)
        return malloc(size);
    checkheap(1);
    old = (node*)((long)oldptr - 8);
    if(block_class(old) == get_class(size))
        return oldptr; 

    oldsize = block_size(old);
    newptr = malloc(size);
    //copy first oldSize bytes of oldptr to newptr
    //TODO: update to inplace reallocation if possible
    oldsize = size < oldsize ? size : oldsize;
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
    checkheap(1);
    newptr = malloc(nmemb * size);
    memset(newptr, 0, nmemb * size);
    checkheap(1);
    return newptr;
}
// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    node *p;
    int count = 0;
    
    p = (node*) mem_heap_lo();
    while(in_heap(p)){
        if(!aligned(p)){
            if(verbose) fprintf(stderr,"block not aligned\n");
            fprintf(stderr,"p:%p\n",(void*)(p));
            printheap();
            return 1;
        }
        if(block_free(p))
            count++;
        p = block_next(p);
    }
    int r;
    r = check_flist(flist5,SIZE5, &count);
    if(r){
        fprintf(stderr,"flist5 failed\n");
        return 1;
    }
    r = check_flist(flist6,SIZE6, &count);
    if(r){
        fprintf(stderr,"flist6 failed\n");
        return 1;
    }
    r = check_flist(flist7,SIZE7, &count);
    if(r){
        fprintf(stderr,"flist7 failed\n");
        return 1;
    }
    r = check_flist(flist8,SIZE8, &count);
    if(r){
        fprintf(stderr,"flist8 failed\n");
        return 1;
    }
    r = check_flist(flist9,SIZE9, &count);
    if(r){
        fprintf(stderr,"flist9 failed\n");
        return 1;
    }
    r = check_flist(flist10,SIZE10, &count);
    if(r){
        fprintf(stderr,"flist10 failed\n");
        return 1;
    }
    r = check_flist(flist11,SIZE11, &count);
    if(r){
        fprintf(stderr,"flist11 failed\n");
        return 1;
    }
    r = check_flist(flistn,SIZEN, &count);
    if(r){
       fprintf(stderr,"flistn failed\n");
       return 1;
    }
    if(count){
        fprintf(stderr, "Uh oh %d free blocks in heap not on a list\n", count);
        printheap();
        printallflist();
        return 1;
    }
    return 0;
}

//checks a free node list for errors / discrepancies
// returns 0 if everything is okay 
int check_flist(node* flist, char class, int* countptr){
    node* n = flist;
    class = class;
    int count = *countptr;
    while(n){
        if(n->next){
            if(n->next->prev != n){
                fprintf(stderr,"next elements previous element isn't this element\n");
                printheap();
                printflist(class);
                return 1;
            }
            if(n->next == n){
                fprintf(stderr,"blocks next element is its self\n");
                return 1;
            }
        }
        if(n->prev){
            if(n->prev->next != n){
                fprintf(stderr,"previous elements next element isn't this element\n");
                printheap();
                printflist(class);
                return 1;
            }
        }
        if(!block_free(n)){
            fprintf(stderr,"allocated block on the free list\n");
            printheap();
            printflist(class);
            return 1;
        }
        if(!in_heap((uint32_t*)n)){
            fprintf(stderr,"you dun goofed real good\n");
            printheap();
            printflist(class);
            return 1;
        }
        n = n->next;
        count--;
    }
    *countptr = count;
    return 0;
}

//Used in debugging to print the heap
void printheap(){
    node* n = (node*) mem_heap_lo();
    while(in_heap(n)){
        printf("%p[%zd %c]", (void*)n, block_size(n), block_free(n) ? 'f' : 'a');
        n = block_next(n);
    }
    printf("\n");
}

//Used in debugging to print a freelist
void printflist(char class){
    node* list = get_list(class);
    while(list){
        printf("{%zd %c %d}",block_size(list), block_free(list)? 'f':'a', class+5);
        if(list->next != list)
            list = list->next;
        else {printf("!!fail!!");break;}
    }
    printf("\n");
}

//used in debugging to print all free lists
void printallflist(){
    int i;
    for(i=0; i<8; i++){
        printflist(i);
    }
}
