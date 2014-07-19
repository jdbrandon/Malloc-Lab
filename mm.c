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
    uint32_t head;
    uint32_t prev;
    uint32_t next;
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
static inline void* found(node*);
static inline node* get_list(int);
static inline node** get_list_addr(int);
static inline char get_class(size_t);
int check_flist(node*, char, int*);
static inline node* next(const node*);
static inline void setnext(node*, node*);
static inline node* prev(const node*);
static inline void setprev(node*, node*);
void *carve(node*, size_t, size_t);
void *relocate(void*, size_t, size_t);
void *searchlist(node**, size_t);

#define WSIZE 4
#define DSIZE 8
#define ALLOC 1
#define NALLOC 2
#define PALLOC 4
#define LISTBOUND 10
#define LOOKAHEAD 5

#define SIZEN 12
#define SIZE15 11
#define SIZE14 10 
#define SIZE13 9
#define SIZE12 8
#define SIZE11 7
#define SIZE10 6
#define SIZE9 5
#define SIZE8 4
#define SIZE7 3
#define SIZE6 2
#define SIZE5 1
#define SIZE4 0

static node* flist4 = NULL;
static node* flist5 = NULL;
static node* flist6 = NULL;
static node* flist7 = NULL;
static node* flist8 = NULL;
static node* flist9 = NULL;
static node* flist10 = NULL;
static node* flist11 = NULL;
static node* flist12 = NULL;
static node* flist13 = NULL;
static node* flist14 = NULL;
static node* flist15 = NULL;
static node* flistn = NULL;

static node** lists = &flist4;
static node* prolog;
static node* epilog;
static void* lbound;

static inline void flist_insert(node* n, node** list){
    if(*list){
        setnext(n, *list);
        setprev(n, prev(*list));
        setprev(*list, n);
        setnext(prev(n), n);
        *list = n;
    } else {
        setnext(n, n);
        setprev(n, n);
        *list = n;
    }
}

static inline void flist_update(const node* old, node* new, node** list){
    flist_delete(old,list);
    flist_insert(new,list);
}

static inline void flist_delete(const node* n, node** list){
    if(n){
        if(next(n) == n) {*list = NULL; return;}
        setprev(next(n), prev(n));
        setnext(prev(n), next(n));
        if(n == *list) *list = next(n); //n equals list head, so update list
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
    return p <= mem_heap_hi() && p >= lbound;
}

static inline node* next(const node* n){
    return n->next ? (node*)((long)lbound + n->next) : NULL;
}

static inline void setnext(node* n, node* val){
    n->next = (uint32_t)(long)val;
}

static inline node* prev(const node* n){
    return n->prev ? (node*)((long)lbound + n->prev) : NULL;
}

static inline void setprev(node* n, node* val){
    n->prev = (uint32_t)(long)val;
}

static inline size_t block_size(const node* n){
    return n->head & 0xfffffff8; 
}

static inline char block_class(const node* n){
    return get_class(block_size(n));
}

static inline node* block_next(const node* n){
    return (n == epilog)? NULL : (node*)((long) n + block_size(n) + DSIZE);
}

static inline node* block_prev(const node* n){
    return (n  == prolog) ? NULL : (node*)((long)n - (block_size((node*)(((uint32_t*)n)-1))+8));
}

static inline void block_mark(node* n){
    char free = block_free(n);
    node* m;
    ((node*)((long)n +block_size(n)+WSIZE))->head = n->head;
    m = block_next(n);
    if(m)
        m->head = free ? m->head & ~PALLOC : m->head | PALLOC;
    m = block_prev(n);
    if(m)
        m->head = free ? m->head & ~NALLOC : m->head | NALLOC;
}
static inline char next_free(const node* n){
    return !(n->head & NALLOC);
}
static inline char prev_free(const node* n){
    return !(n->head & PALLOC);
}
static inline char block_free(const node* n){
    return !(n->head & ALLOC);
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
    long addr = (long) mem_sbrk(4*WSIZE);
    flist4 = flist5 = flist6 = flist7 = flist8 = flist9 = flist10 = flist11 = \
        flist12 = flist13 = flist14 = flist15 = flistn = NULL;
    if(addr == -1){
        fprintf(stderr,"mm_init failed calling mem_sbrk\n");
        return -1;
    }
    
    uint32_t* p = (uint32_t*) addr;
    p[0] = 0;
    p[1] = ALLOC | NALLOC;
    p[2] = ALLOC | NALLOC;
    p[3] = ALLOC | PALLOC;
    
    prolog = (node*) &p[1];
    epilog = (node*) &p[3];
    lbound = mem_heap_lo();
    checkheap(1);
    return 0;
}

/* 
 */
static inline void add(node* n){
    flist_insert(n, lists + block_class(n));
}

static inline void delete(node* n){
    flist_delete(n, lists + block_class(n));
}


/*
 * malloc
 */
void *malloc (size_t size) {
    node *n;
    char p;
    checkheap(1);  // Let's make sure the heap is ok!
    size = (size + 7) & ~7; //align size
    if(size<8)return NULL;
    p = get_class(size);
    n = searchlist(get_list_addr(p), size);
    if(n!=NULL) 
        return n;
    //carve out a chunk of a large block and allocate it if possible
    if(p != SIZEN){
        n = searchlist(get_list_addr(SIZEN), size);
        if(n != NULL) return n;
    }
    //Requested size is not found on a free list call sbrk for a variable
    //size block, store its size in its header so that it can be
    //placed accurately measured when it is freed.
    size_t up = size;
    up += DSIZE; //account for metadata
    if((up + mem_heapsize()) > LIMIT){
        fprintf(stderr,"out of mem\n");
printheap();
        return NULL;
    }
    n = (node*) ((long)mem_sbrk(up)-WSIZE);//firefox-reddit.rep breaks if i dont add 24 here
    if(n == (node*) -1){
        fprintf(stderr,"mem_sbrk failed\n");
        return NULL;
    }
    char prevalloc = epilog->head & PALLOC;
    n->head = (up-DSIZE); //dont acount for metadata when accounting for
    n->head |= ALLOC|NALLOC|prevalloc;                 //size of the allocation
    block_mark(n);
    epilog = (node*)((long)mem_heap_hi()-3);
    epilog->head = ALLOC|PALLOC;
    checkheap(1);
    return (void*) &n->prev;
}

void* searchlist(node** list, size_t size){
    node* n, *m, *start;
    size_t best, tmp;
    char count;
    start = n = *list;
    if(n && (block_class(n) < SIZE8)) return found(n);
    while(n){
        if((best = block_size(n)) >= size+DSIZE){
            count = 0;
            m = next(n);
            while((count++ < LOOKAHEAD) && m && (m != start)){
                if(((tmp = block_size(m)) < best) && (tmp >= size+DSIZE) ){
                    best = tmp;
                    n = m;
                }
                m = next(m);
            }
//            *list = next(n);
            if((best - size) >= 16)
                return carve(n, size, best - size - 8);
            return found(n);
        }
        n = next(n);
        if(n == start)
            break;
    }
    return NULL;
}

void* carve(node* n, size_t s0, size_t s1){
     node* m;
     char nextAlloc;
     delete(n);
     nextAlloc = n->head & NALLOC;
     n->head = s0 | (n->head & PALLOC) | ALLOC;
     block_mark(n);
     m = block_next(n);
     m->head = s1 | PALLOC | nextAlloc;
     block_mark(m);
     add(m);
     return &n->prev;
}

static inline char get_class(const size_t size){
    if(size == 8)
        return SIZE4;
    else if(size == 16)
        return SIZE5;
    else if(size == 24)
        return SIZE6;
    else if(size == 32)
        return SIZE7;
    else if(size <= 56)
        return SIZE8;
    else if(size <= 80)
        return SIZE9;
    else if(size <= 104)
        return SIZE10;
    else if(size <= 300)
        return SIZE11;
    else if(size <= 500)
        return SIZE12;
    else if(size <= 700)
        return SIZE13;
    else if(size <= 900)
        return SIZE14;
    else if(size <= 1100)
        return SIZE15;
    else return SIZEN;
}

static inline node* get_list(const int p){
    return lists[p];
}

static inline node** get_list_addr(const int p){
    return &lists[p];
}

/* Remove the block from it's list
 * mark the header to indicate size class
 * mark next block to let it know this blocks size?
 * return a pointer to the 8 byte aligned address just beyond the nodes metadata
 */
static inline void* found(node *n){
    //suitable block found
    delete(n);
    n->head |= ALLOC;
    block_mark(n);
    //TODO: see about marking next block
    checkheap(1);
    return (void*) &n->prev;
}

/*
 * free
 */
void free (void *ptr) {
    size_t size;
    node *next, *prev;
    if (ptr == NULL) {
        return;
    }
    checkheap(1);
    node *n = (node*)(((long)ptr)-WSIZE);
    //Use the header to free the block
    //and place the block in the free list
    n->head = n->head & ~ALLOC;
    next = block_next(n);
    prev = block_prev(n);
    if(block_free(next)){
        delete(next);
        if(block_free(prev)){
            delete(prev);
            size = block_size(prev) + block_size(n) + block_size(next) + 2*DSIZE;
            prev->head = size | PALLOC | NALLOC;
            block_mark(prev);
            add(prev);
        } else {
            size = block_size(n) + block_size(next) + DSIZE;
            n->head = size | PALLOC | NALLOC;
            block_mark(n);
            add(n);
        }
    } else {
        if(block_free(prev)){
            delete(prev);
            size = block_size(prev) + block_size(n) + DSIZE;
            prev->head = size | PALLOC | NALLOC;
            block_mark(prev);
            add(prev);
        }
        else{
            add(n);
        }
    }
    checkheap(1);
}
/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    void* newptr;
    size_t oldsize;
    node* old, *ret;
    if(size == 0){
        free(oldptr);
        return 0;
    }
    if(oldptr == NULL)
        return malloc(size);
    checkheap(1);
    old = (node*)((long)oldptr - WSIZE);
    size = (size + 7) & ~7;
    if(block_size(old) == size)
        return oldptr;

    oldsize = block_size(old);
    if(next_free(old)){
        if(prev_free(old)){
            if((oldsize + block_size(block_prev(old)) + block_size(block_next(old)) + 16) \
              >= size){
                ret = block_prev(old);
                delete(ret);
                delete(block_next(old));
                ret->head = block_size(ret) + block_size(old) + block_size(block_next(old)) + 16;
            }
            else{
                return relocate(oldptr, oldsize, size);
            }
        }
        else if((oldsize + block_size(block_next(old)) +8) >= size){
            ret = block_next(old);
            delete(ret);
            old->head = oldsize + block_size(ret) + 8;
            old->head |= ALLOC|PALLOC|NALLOC;
            block_mark(old);
            return &old->prev;
        }
        else return relocate(oldptr, oldsize, size);
    }
    else if(prev_free(old)){
        if((block_size(block_prev(old)) + oldsize +8) >= size){
            ret = block_prev(old);
            delete(ret);
            ret->head = block_size(ret) + oldsize + 8;
        }
        else return relocate(oldptr, oldsize, size);
    } else return relocate(oldptr, oldsize, size);
    ret->head |= ALLOC|PALLOC|NALLOC;
    block_mark(ret);
    oldsize = size < oldsize ? size : oldsize;
    newptr = (void*)&ret->prev;
    memcpy(newptr,oldptr, oldsize);
    checkheap(1);
    return newptr;
}

void* relocate(void* oldptr, size_t oldsize, size_t size){
    void* newptr = malloc(size);
    //copy first oldSize bytes of oldptr to newptr
    oldsize = size < oldsize ? size : oldsize;
    memcpy(newptr,oldptr, oldsize);
    free(oldptr);
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
    node *p, **listptr;
    int count = 0, r;
    size_t size, offset = 0;
    uint32_t* iptr;
    char class;

    p = prolog;
    while(p != epilog){
        if(!aligned((uint32_t*)p+1)){
            if(verbose) fprintf(stderr,"block not aligned\n");
            fprintf(stderr,"p:%p\n",(void*)(p));
            fprintf(stderr,"prolog+%zd\n",offset);
            printheap();
            return 1;
        }
        if(block_next(p)){
            if(block_prev(block_next(p)) != p){
                fprintf(stderr,"Next adjacent blocks previous block isnt this block\n");
                fprintf(stderr,"prolog+%zd\n",offset);
                printheap();
                return 1;
            }
            if(next_free(p) && !block_free(block_next(p))){
                fprintf(stderr, "bitpacking error: NALLOC incorrect\n");
                return 1;
            }
        }
        if(block_prev(p)){
            if(block_next(block_prev(p)) != p){
                fprintf(stderr,"prev adjacent blocks next block isnt this block\n");
                fprintf(stderr,"prolog+%zd\n",offset);
                printheap();
                return 1;
            }
            if(prev_free(p) && !block_free(block_prev(p))){
                fprintf(stderr,"bitpacking error: PALLOC incorrect");
                return 1;
            }
        }
        size = block_size(p) >> 2;
        iptr = (uint32_t*) p;
        if(block_size((node*)&iptr[0]) != block_size((node*)&iptr[size+1])){
            fprintf(stderr,"header footer mismatch\n");
            fprintf(stderr,"prolog+%zd\n",offset);
            printheap();
            return 1;
        }
        if(block_free(p))
            count++;
        p = block_next(p);
        offset++;
    }
    for(class = 0; class < LISTBOUND; class++){
        listptr = get_list_addr(class);
        r = check_flist(*listptr, class, &count);
        if(r){
            fprintf(stderr,"flist%d failed\n",class+4);
            printflist(class);
            return 1;
        }
    }
    if(count){
        fprintf(stderr, "Uh oh %d free blocks in heap not on a list\n", count);
        return 1;
    }
    return 0;
}

int check_flist(node* flist, char class, int* countptr){
    node* n, *start;
    n = start  = flist;
    int count = *countptr;
    while(n){
        if(prev(next(n)) != n){
            fprintf(stderr,"next elements previous element isn't this element\n");
            return 1;
        }
        if(next(prev(n)) != n){
            fprintf(stderr,"previous elements next element isn't this element\n");
            return 1;
        }
        if(!block_free(n)){
            fprintf(stderr,"allocated block on the free list\n");
            printflist(class);
            return 1;
        }
        if(!in_heap(n)){
            fprintf(stderr,"you dun goofed real good\n");
            return 1;
        }
        n = next(n);
        count--;
        if(n == start)
            break;
    }
    *countptr = count;
    return 0;
}

void printheap(){
    node* n = prolog;
    while(in_heap(n)){
        printf("%p[%zd %c]", (void*)n, block_size(n), block_free(n) ? 'f' : 'a');
        n = block_next(n);
    }
    printf("\n");
}
void printflist(char class){
    node* start, *list = get_list(class);
    start = list;
    while(list){
        printf("%p{%zd %c %d}",(void*)list,block_size(list), block_free(list)? 'f':'a', class+4);
        list = next(list);
        if(list == start)
            break;
    }
    printf("\n");
}
void printallflist(){
    int i;
    for(i=0; i<LISTBOUND; i++){
        printflist(i);
    }
}
