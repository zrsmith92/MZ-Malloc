/*
 * mm.c - A custom memory allocator by Zachary Smith and Matthew Hlavacek
 *
 * OVERVIEW
 * Anatomy of a block: Each block has a header and footer that wrap the actual
 * block data. There are each 8 bytes in length. A block pointer (referred as bp
 * in the code below), always points to the beginning of the actual payload, NOT
 * the header preceding it.
 *
 * BLOCK LAYOUT
 *
 * hdr  ssssssss ssssssss ssssssss ssssssss ssssssss ssssssss ssssssss sssssxxa
 * bp-> pppppppp pppppppp pppppppp pppppppp pppppppp pppppppp pppppppp pppppppp
 *      pppppppp pppppppp pppppppp pppppppp pppppppp pppppppp pppppppp pppppppp
 * ftr  ssssssss ssssssss ssssssss ssssssss ssssssss ssssssss ssssssss sssssxxa
 *
 * Each character is one bit, with each character standing for:
 * s - size of block (including header + footer)
 * x - unused (should always be zero, since size is always divisible by 8)
 * p - payload
 * 
 * The block pointer for this block is designated by the "bp->" in symbol. To
 * get to the header of block, you would subtract 8 (WSIZE) from bp. To get to
 * the footer of the previous block (blocks are always contiguous), you would
 * subtract 16 (DSIZE or 2*WSIZE) from bp. In the above example, the size bits
 * would be set to 32 (16 bytes for the payload, 16 bytes for header + footer),
 * and a would presumably be set to 1 if this block is allocated.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <assert.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Zachary Smith",
    /* First member's email address */
    "zacharysmith2014@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Matthew Hlavacek",
    /* Second member's email address (leave blank if none) */
    "matthewhlavacek2014@u.northwestern.edu"
};

// Set this to 0 to remove the check_heap function and all calls to it.
#define DEBUG 0

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define MAX(a, b) ((a) > (b) ? (a) : (b))

#define WSIZE 4
#define DSIZE 8
#define CHUNK_SIZE (1<<12)

#define PACK(size, alloc)   (size | alloc)
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// Writes both the header and footer for a given block pointer
#define PUT_HDR_FTR(bp, size, alloc) \
PUT(HDRP(bp), PACK(size, alloc)); \
PUT(FTRP(bp), PACK(size, alloc));

static void *extend_heap();
static inline void *coalesce();

static void *find_fit(size_t size);
static inline void place(void *bp, size_t size);

#if DEBUG
#define CHECK_HEAP(s, ...) check_heap(s, ##__VA_ARGS__)
static void check_heap(const char *title, ...);
#else
#define CHECK_HEAP(s, ...)
#endif


static char * heap_listp;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                             // Alignment Padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // Prologue Header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // Prologue Footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // Epilogue header
    heap_listp += (2*WSIZE);

    CHECK_HEAP("PRE-INIT");

    if (extend_heap(CHUNK_SIZE/WSIZE) == NULL)
        return -1;

    CHECK_HEAP("INITIAL HEAP");

    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // Allocate even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    #if DEBUG
    printf("\n########################\nHEAP EXTENSION\n########################\n");
    printf("New area: %p, Size: %zu\n", bp, size);
    #endif

    // Initialize free block header/footer and the epilogue header
    // PUT_HDR_FTR(bp, size, 0);
    PUT_HDR_FTR(bp, size, 0);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    #if DEBUG
    printf("########################\n\n");
    #endif

    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t adj_size;    // adjusted size for header/footer and alignment
    size_t extend_size; // amount to extend if no fit
    char *bp;

    // ignore pointless calls
    if ( size == 0 ) return NULL;

    if ( size <= DSIZE )
        adj_size = 2 * DSIZE;
    else
        adj_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(adj_size)) != NULL)
    {
        place(bp, adj_size);
        CHECK_HEAP("Malloc size: %zu(%zu), bp: %p", size, adj_size, bp);
        return bp;
    }

    extend_size = MAX(adj_size, CHUNK_SIZE);
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL)
        return NULL;

    place(bp, adj_size);
    CHECK_HEAP("Malloc size: %zu(%zu), bp: %p", size, adj_size, bp);
    return bp;
}

static void *find_fit(size_t size)
{
    void *bp = NEXT_BLKP(heap_listp);
    while(!(GET_SIZE(HDRP(bp)) >= size && GET_ALLOC(HDRP(bp)) == 0))
    {
        if ( GET(HDRP(bp)) == 0x1 )
            // We've reached the epilogue, no fit found
            return NULL;

        bp = NEXT_BLKP(bp);
    }

    return bp;
}

inline static void place(void *bp, size_t size)
{
    size_t curr_size = GET_SIZE(HDRP(bp)); // current size

    // If there is enough room for another block, we need to split.
    if ((curr_size - size) > DSIZE)
    {
        PUT_HDR_FTR(bp, size, 1);
        PUT_HDR_FTR(NEXT_BLKP(bp), (curr_size - size), 0);
    }
    else
    {
        PUT_HDR_FTR(bp, curr_size, 1);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size;
    // slight optimization. If it's already freed, skip the coalescing
    if ( GET_ALLOC(HDRP(bp)) == 0 )
        return;

    size = GET_SIZE(HDRP(bp));

    PUT_HDR_FTR(bp, size, 0);
    coalesce(bp);

    CHECK_HEAP("Freed bp: %p", bp);
}


inline static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // both previous and next blocks are allocated; nothing to do
    if (prev_alloc && next_alloc) 
    {
        return bp;
    }
    // previous is allocated but next is free
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT_HDR_FTR(bp, size, 0);
    }
    // previous is free but next is allocated
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // both are free
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *new_bp;
    size_t adj_size;
    size_t old_size = GET_SIZE(HDRP(bp));

    // Edge cases
    if (bp == NULL)
        return mm_malloc(size);

    if (size == 0)
    {
        mm_free(bp);
        return NULL;
    }

    // Adjust size to be word aligned and at least big enough for header/footer
    if ( size <= DSIZE )
        adj_size = 2 * DSIZE;
    else
        adj_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // don't do anything if the old size is the same as the new size
    if ( adj_size == old_size )
        return bp;

    // Free current block
    PUT_HDR_FTR(bp, old_size, 0);

    new_bp = coalesce(bp);
    if ( GET_SIZE(HDRP(new_bp)) < adj_size)
    {
        // not enough free space around block, need to find new block
        if ((new_bp = find_fit(adj_size)) == NULL)
        {
            // Still can't find big enough block. Need to expand the heap
            if ((new_bp = extend_heap(MAX(adj_size, CHUNK_SIZE)/WSIZE)) == NULL)
                return NULL;
        }
    }

    memmove(new_bp, bp, old_size);
    place(new_bp, adj_size);
    CHECK_HEAP(
        "Realloc from %p to %p\n"
        "old size:\t%zu\n"
        "new size:\t%zu(%zu)", 
        bp, new_bp,
        old_size,
        size,
        adj_size
    );
    return new_bp;
}

#if DEBUG
void check_heap(const char *title, ...)
{
    int i = 0;                      // block counter;
    void *bp = NEXT_BLKP(heap_listp);
    void *heap_lo = mem_heap_lo();
    void *heap_hi = mem_heap_hi();

    if ( title != NULL )
    {
        va_list args;
        va_start(args, title);
        vprintf(title, args);
        printf("\n=======================\n");
    }

    // printf("heap_listp:\t%p\n", (void *)((void *)heap_listp - mem_heap_lo()));
    printf(
        "Heap Lo:\t%p\n"
        "Heap Hi:\t%p\n"
        "Heap Size:\t%zu\n"
        "heap_listp:\t%p\n"
        heap_lo,
        heap_hi,
        mem_heapsize(),
        (void *)((void *)heap_listp - mem_heap_lo()));

    printf(
        "0x%#.8x\n"
        "%#.8x\n"
        "%#.8x\n\n", 
        GET(heap_lo), 
        GET(heap_lo + 1*WSIZE),
        GET(heap_lo + 2*WSIZE)
    );

    printf("blk #\tbp\tHDR\t\t...\tSIZE(ALLOC)\t...\tFTR\n"
        "-----------------------------------------------------------------\n");
    printf(
        "prlg\t%p\t%#.8x\t...\t%8u(%d)\t...\tN/A\n",
        heap_listp,
        GET(HDRP(heap_listp)),
        GET_SIZE(heap_listp),
        GET_ALLOC(heap_listp));
    while( GET_SIZE(HDRP(bp)) != 0 )
    {
        printf(
            "%d\t%p\t%#.8x\t...\t%8u(%d)\t...\t%#.8x\n",
            i,
            bp,
            GET(HDRP(bp)),
            GET_SIZE(HDRP(bp)),
            GET_ALLOC(HDRP(bp)),
            GET(FTRP(bp)));

        // Header equals footer
        assert(GET(HDRP(bp)) == GET(FTRP(bp)));

        i++;
        bp = NEXT_BLKP(bp);
    }
    printf(
        "eplg\t%p\t%#.8x\t...\t%8u(%d)\t...\tN/A\n",
        bp,
        GET(HDRP(bp)),
        GET_SIZE(bp),
        GET_ALLOC(bp));

    printf("\n\n");
}
#endif