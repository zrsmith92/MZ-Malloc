/*
 * mm.c - A custom memory allocator by Zachary Smith and Matthew Hlavacek
 *
 * OVERVIEW
 * Anatomy of a block: Each block has a header and footer that wrap the actual
 * block data. There are each 8 bytes in length. A block pointer (referred as bp
 * in the code below), always points to the beginning of the actual payload, NOT
 * the header preceding it.
 *
 * In a free block, the first four bytes point to the next block in the list, and the
 * next four bytes point to the previous.
 *
 * INITIAL HEAP LAYOUT
 *
 * bin1ptr bin1ptr bin1ptr bin1ptr bin2ptr bin2ptr bin2ptr bin2ptr
 * bin3ptr bin3ptr bin3ptr bin3ptr bin4ptr bin4ptr bin4ptr bin4ptr
 * ...                             bin8ptr bin8ptr bin8ptr bin8ptr
 * 0000000 0000000 0000000 0000000 FIRST BLOCK HEADER.............
 * Free block of maximum size for each bin.
 *
 * BINS
 * 0 - 32
 * 33 - 64
 * 65 - 128
 * 129 - 256
 * 257 - 512
 * 513 - 1024
 * 1025 - 2048
 * 2049+
 *
 *
 * FREE BLOCK LAYOUT
 *
 * hdr  ssssssss ssssssss ssssssss ssssssss ssssssss ssssssss ssssssss sssssxxa
 * bp-> nnnnnnnn nnnnnnnn nnnnnnnn nnnnnnnn pppppppp pppppppp pppppppp pppppppp
 *      xxxxxxxx xxxxxxxx xxxxxxxx xxxxxxxx xxxxxxxx xxxxxxxx xxxxxxxx xxxxxxxx
 *      ...
 *      ...
 * ftr  ssssssss ssssssss ssssssss ssssssss ssssssss ssssssss ssssssss sssssxxa
 *
 *
 * s = bits indicating block size (multiple of eight, so least significant 3 bits are always 0)
 * a = allocated bit (0 in this case of a free block)
 * n = pointer to next block in free list bin
 * p = pointer to previous block in free list bin
 *
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

#define MAX(a, b) ((a) > (b) ? (a) : (b))

#define WSIZE 4
#define DSIZE 8

/* single word (4) or double word (8) alignment */
#define ALIGNMENT DSIZE

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define CHUNK_SIZE (1<<12)
#define PTR_SIZE sizeof(void *)
#define LIST_OVERHEAD (2 * PTR_SIZE)

#define PACK(size, alloc)   (size | alloc)
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (unsigned int)(val))
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define GET_NEXT(bp)        ((void *)GET(bp))
#define GET_PREV(bp)        ((void *)GET((char *)(bp) + PTR_SIZE))
#define PUT_NEXT(bp1, bp2)  PUT((char *)(bp1), bp2)
#define PUT_PREV(bp1, bp2)  PUT(((char *)(bp1) + PTR_SIZE), bp2)

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
static void *find_bin_for_size(size_t size);
static inline void prepend_block(void *bp, size_t size);
static inline void remove_block(void *bp);

#if DEBUG
#define CHECK_HEAP(s, ...) check_heap(s, ##__VA_ARGS__)
// printf, but only prints if in debugging mode
#define DPRINTF(...) printf(__VA_ARGS__)
static void check_heap(const char *title, ...);
#else
#define CHECK_HEAP(s, ...)
#define DPRINTF(...)
#endif


// Bottom of heap, beginning of bin pointers list
static void * heap_lo;

// Bottom of blocks, just after bin pointers and padding
static void * block_lo;

// Last item in list of bin pointers
static void * bin_hi;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int i;
    // expand the heap to 9 words for 8 list pointers + 1 word of padding + 1 word for first block's header
    if ((heap_lo = mem_sbrk(12*PTR_SIZE)) == (void *)-1)
        return -1;

    // zero out all values for now;
    for ( i = 0; i < 9; i++ )
        PUT((heap_lo + i * PTR_SIZE), 0);

    bin_hi = (void *)((unsigned int)heap_lo + (7 * PTR_SIZE));
    block_lo = (void *)((unsigned int)heap_lo + (10 * PTR_SIZE));

    PUT_HDR_FTR(block_lo, DSIZE, 1);
    PUT(HDRP(NEXT_BLKP(block_lo)), PACK(0, 1));

    CHECK_HEAP("Initial Heap");

    return 0;
}

static void *find_bin_for_size(size_t size)
{
    if ( size <= 32 )
        return heap_lo;
    else if ( size <= 64 )
        return (void *)((unsigned int)heap_lo + (WSIZE));
    else if ( size <= 128 )
        return (void *)((unsigned int)heap_lo + (2 * WSIZE));
    else if ( size <= 256 )
        return (void *)((unsigned int)heap_lo + (3 * WSIZE));
    else if ( size <= 512 )
        return (void *)((unsigned int)heap_lo + (4 * WSIZE));
    else if ( size <= 1024 )
        return (void *)((unsigned int)heap_lo + (5 * WSIZE));
    else if ( size <= 2048 )
        return (void *)((unsigned int)heap_lo + (6 * WSIZE));
    else
        return (void *)((unsigned int)heap_lo + (7 * WSIZE));
}

static inline void prepend_block(void *bp, size_t size)
{
    DPRINTF("Begin prepend_block, %p\n", bp);

    void * bin = find_bin_for_size(size);
    if ( (void *)GET(bin) == NULL )
    {
        // no elements in list currently
        PUT(bin, bp);
        PUT_PREV(bp, NULL);
        PUT_NEXT(bp, NULL);
    }
    else
    {
        PUT_PREV(bp, NULL);
        PUT_PREV(GET(bin), bp);
        PUT_NEXT(bp, GET(bin));
        PUT(bin, bp);
    }
}

static inline void remove_block(void *bp)
{
    DPRINTF("Removing block: %p, Next: %p, Prev: %p\n", bp, GET_NEXT(bp), GET_PREV(bp));

    if ( (void *)GET_PREV(bp) == NULL && (void *)GET_NEXT(bp) == NULL )
    {
        // block is only block in list. list will now be empty.
        void * bin = find_bin_for_size(GET_SIZE(HDRP(bp)));
        PUT(bin, NULL);
    }
    else if ( (void *)GET_PREV(bp) == NULL )
    {
        // block is the first block in list, but not the only block.
        void * bin = find_bin_for_size(GET_SIZE(HDRP(bp)));
        PUT(bin, GET_NEXT(bp));
        PUT_PREV(GET_NEXT(bp), NULL);
        DPRINTF(
            "Replacement block: %p, Next: %p, Prev: %p\n", 
            GET_NEXT(bp), GET_NEXT(GET_NEXT(bp)), GET_PREV(GET_NEXT(bp)));
    }
    else if ( (void *)GET_NEXT(bp) == NULL )
    {
        // at the end of the list. just set the previous to be the end
        PUT_NEXT(GET_PREV(bp), NULL);
    }
    else
    {
        PUT_NEXT(GET_PREV(bp), GET_NEXT(bp));
        PUT_PREV(GET_NEXT(bp), GET_PREV(bp));
    }
}

static void *extend_heap(size_t words)
{
    DPRINTF("Begin extend_heap\n");

    char *bp;
    size_t size;

    // Allocate even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // Initialize free block header/footer and the epilogue header
    PUT_HDR_FTR(bp, size, 0);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    // Attach to the appropriate bin's free list.
    // prepend_block(bp, size);

    bp = coalesce(bp);
    CHECK_HEAP("Heap Extension, Size: %zu", mem_heapsize());
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    DPRINTF("Begin mm_malloc\n");

    size_t adj_size;    // adjusted size for header/footer and alignment
    size_t extend_size; // amount to extend if no fit
    char *bp;

    // ignore pointless calls
    if ( size == 0 ) return NULL;

    if ( size <= LIST_OVERHEAD )
        adj_size = LIST_OVERHEAD + DSIZE; // List overhead + header/footer space
    else
        adj_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(adj_size)) == NULL)
    {
        extend_size = MAX(adj_size, CHUNK_SIZE);
        if ( (bp = extend_heap(extend_size/WSIZE)) == NULL)
            return NULL;
    } 

    place(bp, adj_size);
    CHECK_HEAP("Malloc size: %zu(%zu), bp: %p", size, adj_size, bp);
    return bp;
}

static void *find_fit(size_t size)
{
    DPRINTF("Begin find_fit\n");

    void * bin;
    void * bp;

    for (bin = find_bin_for_size(size); bin <= bin_hi; bin += WSIZE )
    {
        if ( (void *)GET(bin) == NULL )
        {
            // bin is empty or we're at end of bin. next bin;
            continue;
        }

        for ( bp = (void *)GET(bin); bp != NULL; bp = (void *)GET_NEXT(bp) )
        {
            if ( GET_SIZE(HDRP(bp)) >= size )
                return bp;
        }
    }

    return NULL;
}

inline static void place(void *bp, size_t size)
{
    DPRINTF("Begin place\n");

    size_t curr_size = GET_SIZE(HDRP(bp)); // current size
    size_t leftover = curr_size - size;

    remove_block(bp);

    // If there is enough room for another block, we need to split.
    if (leftover >= LIST_OVERHEAD + DSIZE)
    {
        PUT_HDR_FTR(bp, size, 1);
        PUT_HDR_FTR(NEXT_BLKP(bp), leftover, 0);
        prepend_block(NEXT_BLKP(bp), leftover);
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
    DPRINTF("Begin mm_free\n");

    size_t size;
    // slight optimization. If it's already freed, skip the coalescing
    if ( GET_ALLOC(HDRP(bp)) == 0 )
        return;

    size = GET_SIZE(HDRP(bp));

    PUT_HDR_FTR(bp, size, 0);
    coalesce(bp);

    CHECK_HEAP("Freed bp: %p", bp);
}


static inline void *coalesce(void *bp)
{
    DPRINTF("Begin coalesce\n");

    int prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // both previous and next blocks are allocated; nothing to do
    if (prev_alloc && next_alloc)
    {
        prepend_block(bp, size);
        return bp;
    }
    // previous is allocated but next is free
    else if (prev_alloc && !next_alloc)
    {
        // remove_block(bp);

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        remove_block(NEXT_BLKP(bp));
        prepend_block(bp, size);

        PUT_HDR_FTR(bp, size, 0);
    }
    // previous is free but next is allocated
    else if (!prev_alloc && next_alloc)
    {
        // remove_block(bp);
        remove_block(PREV_BLKP(bp));

        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        prepend_block(bp, size);
    }
    // both are free
    else
    {
        // remove_block(bp);
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        prepend_block(bp, size);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    DPRINTF("Begin mm_realloc\n");

    void *new_bp;
    size_t adj_size;
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t leftover;

    // Edge cases
    if (bp == NULL)
        return mm_malloc(size);

    if (size == 0)
    {
        mm_free(bp);
        return NULL;
    }

    // Adjust size to be word aligned and at least big enough for header/footer
    if ( size <= LIST_OVERHEAD )
        adj_size = LIST_OVERHEAD + DSIZE; // List overhead + header/footer space
    else
        adj_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // don't do anything if the old size is the same as the new size
    if ( adj_size == old_size )
        return bp;


    if ( 
        !GET_ALLOC(HDRP(NEXT_BLKP(bp))) && 
        (old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)))) >= adj_size 
    )
    {
        // next block is unallocated and big enough to hold the new block size.
        remove_block(NEXT_BLKP(bp));
        new_bp = bp;
        PUT_HDR_FTR(new_bp, (old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)))), 1);
    }
    else
    {
        if ( (new_bp = find_fit(adj_size)) == NULL )
        {
            if ((new_bp = extend_heap(MAX(adj_size, CHUNK_SIZE)/WSIZE)) == NULL)
                return NULL;
        }

        PUT_HDR_FTR(new_bp, GET_SIZE(HDRP(new_bp)), 1);
        remove_block(new_bp);

        PUT_HDR_FTR(bp, old_size, 0);
        memcpy(new_bp, bp, old_size - DSIZE);

        assert(memcmp(new_bp, bp, old_size - DSIZE) == 0);

        coalesce(bp);
    }

    leftover = GET_SIZE(HDRP(new_bp)) - adj_size;
    
    // Modified Place
    // If there is enough room for another block, we need to split.
    if (leftover >= LIST_OVERHEAD + DSIZE)
    {
        PUT_HDR_FTR(new_bp, adj_size, 1);
        PUT_HDR_FTR(NEXT_BLKP(new_bp), leftover, 0);
        coalesce(NEXT_BLKP(new_bp));
    }


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
    void *bp;
    void *heap_hi = mem_heap_hi();

    if ( title != NULL )
    {
        va_list args;
        va_start(args, title);
        vprintf(title, args);
        printf("\n=======================\n");
    }

    printf(
        "Heap Lo:\t%p\n"
        "Heap Hi:\t%p\n"
        "Heap Size:\t%zu\n"
        "Bin hi:\t\t%p\n"
        "Block Lo:\t%p\n\n",
        heap_lo,
        heap_hi,
        mem_heapsize(),
        bin_hi,
        block_lo);

    printf(
        "Bin Pointers\n"
        "------------\n"
        "%#.8x\t"
        "%#.8x\t"
        "%#.8x\t"
        "%#.8x\n"
        "%#.8x\t"
        "%#.8x\t"
        "%#.8x\t"
        "%#.8x\n\n",
        GET(heap_lo),
        GET(heap_lo + 1*PTR_SIZE),
        GET(heap_lo + 2*PTR_SIZE),
        GET(heap_lo + 3*PTR_SIZE),
        GET(heap_lo + 4*PTR_SIZE),
        GET(heap_lo + 5*PTR_SIZE),
        GET(heap_lo + 6*PTR_SIZE),
        GET(heap_lo + 7*PTR_SIZE)
    );

    printf("blk #\tbp\t\tHDR\t\tSize\t\tAlloc\tNext\tPrev\tFTR\n"
        "-----------------------------------------------------------------\n");
    
    printf(
        "prlg\t%8p\t%#.8x\t%.8zu\t%d\t\t(N/A)\t\t(N/A)\t%#.8x\n",
        block_lo, GET(HDRP(block_lo)), (size_t)GET_SIZE(HDRP(block_lo)), 
        GET_ALLOC(HDRP(block_lo)), GET(FTRP(block_lo)));

    for ( bp = NEXT_BLKP(block_lo); bp < heap_hi; bp = NEXT_BLKP(bp) )
    {
        if ( GET_ALLOC(HDRP(bp)) )
        {
            printf(
                "%d\t%8p\t%#.8x\t%.8zu\t%d\t\t(N/A)\t\t(N/A)\t%#.8x\n",
                i, bp, GET(HDRP(bp)), (size_t)GET_SIZE(HDRP(bp)), 
                GET_ALLOC(HDRP(bp)), GET(FTRP(bp))
            );
        }
        else
        {
            printf(
                "%d\t%8p\t%#.8x\t%.8zu\t%d\t%8p\t%8p\t%#.8x\n",
                i, bp, GET(HDRP(bp)),
                (size_t)GET_SIZE(HDRP(bp)), 
                GET_ALLOC(HDRP(bp)),
                (void *)GET_NEXT(bp), 
                (void *)GET_PREV(bp), 
                GET(FTRP(bp))
            );

            // ensure link list pointers are valid
            assert(
                (GET_NEXT(bp) < heap_hi && GET_NEXT(bp) > heap_lo) ||
                GET_NEXT(bp) == NULL
            );
            assert(
                (GET_PREV(bp) < heap_hi && GET_PREV(bp) > heap_lo) ||
                GET_PREV(bp) == NULL
            );

            if ( GET_NEXT(bp) != NULL )
                assert(GET_PREV(GET_NEXT(bp)) == bp);
        }

        // Block is aligned to 8 byte boundary
        assert((unsigned int)bp % ALIGNMENT == 0);
        
        // Header equals footer
        assert(GET(HDRP(bp)) == GET(FTRP(bp)));

        i++;
    }

    printf(
        "eplg\t%8p\t%#.8x\t%.8zu\t%d\t\t(N/A)\t\t(N/A)\t%#.8x\n",
        bp, GET(HDRP(bp)), (size_t)GET_SIZE(HDRP(bp)), 
        GET_ALLOC(HDRP(bp)), GET(FTRP(bp))
    );


    printf("\n\n");
}
#endif
