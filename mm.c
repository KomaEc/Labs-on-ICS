/*
 * 张汉樑 1500015975
 * 这个动态分配器采用了分离的空闲链表来组织各个动态分配的内存块，使用了分离适配方法
 * 动态分配内存块BLOCK的分配：
 * 较小的块(SIZE <= 2*DSIZE)使用一个双向链表连接。
 * 由于WRITEUP中明确堆最大长度为4字节,因此HEADER,FOOTER,PRED,SUCC四个指针都可以4字节表示，只需加上堆初始偏移量即可
 * 所以该分配器准许的最小块大小为2*DSIZ，最小块由一个单独的双向链表连接
 * 对于较大的块(SIZE >= 2*DSIZE + WSIZE,大小向WSIZE对齐)，为了实现快速的best_fit查找，使用
 * Binary Search Tree来记录各个节点，对于大小相同的块，只需要悬挂在某一块之下即可(Hanger)
 * 这样这棵二叉树首先是BST,其次每个节点实际上是一个分离的空闲链表，里面存储着对应节点块大小的所有空闲块。
*/
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif
/* def DRIVER */
#define WSIZE 4
#define DSIZE 8


#define ALIGNMENT 8
#define MIN_BST_NODE_SIZE (2 * DSIZE + WSIZE)
#define MIN_BLOCK_SIZE (2 * DSIZE)
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Statement bit,在HEADER中保存，分别记录当前块以及前一块是否被分配
 * 优化：只有在当前块FREE状态时才会用到footer，所以可以多一个WORD的存储
 */
#define STAT_ALLOC 0x1
#define STAT_PREV_ALLOC 0x2

/* size of a block*/
#define GET_SIZE(bp) ((GET(HDRP(bp))) & ~0x7)
#define GET_ALLOC(bp) ((GET(HDRP(bp))) & 0x1)
#define SIZE(p) (GET(p) & (~0x7))
#define ALLOC(p) (GET(p) & (0x1))

/* address of header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + SIZE(HDRP(bp)) - DSIZE)

/* address of previous and next block */
#define NEXT_BLKP(bp)  ((char *)(bp) + SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - SIZE(((char *)(bp) - DSIZE)))

/* address of both children, parent, hanger*/
#define LCHILD(bp) ((char *)(bp))
#define RCHILD(bp) ((char *)(bp) + WSIZE)
#define PARENT(bp) ((char *)(bp) + 2 * WSIZE)
#define HANGER(bp) ((char *)(bp) + 3 * WSIZE)

/* get and set previous allocate information*/
#define PREV_ALLOC_R(p) (GET(p) & (0x2))
#define PREV_ALLOC(bp) ((GET(HDRP(bp))) & 0x2)
#define SET_PREV_ALLOC(bp) (GET(HDRP(bp)) |= 0x2)
#define CLEAR_PREV_ALLOC(bp) (GET(HDRP(bp)) &= ~0x2)

/* get the pointers which point to children, parent and hanger*/
#define LCHILD_BLKP(bp) ((unsigned long)GET(LCHILD(bp)) + (virtual_NULL))
#define RCHILD_BLKP(bp) ((unsigned long)GET(RCHILD(bp)) + (virtual_NULL))
#define PARENT_BLKP(bp) ((unsigned long)GET(PARENT(bp)) + (virtual_NULL))
#define HANGER_BLKP(bp) ((unsigned long)GET(HANGER(bp)) + (virtual_NULL))

/* pred and succ for small block free list */
#define S_PRED_BLKP(bp) LCHILD_BLKP(bp)
#define S_SUCC_BLKP(bp) RCHILD_BLKP(bp)


/* change the value */
#define PUT_HDRP(bp, val) (PUT(HDRP(bp), val))
#define PUT_FTRP(bp, val) (PUT(FTRP(bp), val))
#define TRUNCATE(val) ((unsigned int)(unsigned long)(val)) //convert 4_byte_addr to addr
#define PUT_LCHILD(bp, val) (PUT(LCHILD(bp), TRUNCATE(val)))
#define PUT_RCHILD(bp, val) (PUT(RCHILD(bp), TRUNCATE(val)))
#define PUT_PARENT(bp, val) (PUT(PARENT(bp), TRUNCATE(val)))
#define PUT_HANGER(bp, val) (PUT(HANGER(bp), TRUNCATE(val)))

/* S refers to 'small' */
#define PUT_S_PRED(bp, val) PUT_LCHILD(bp, val)
#define PUT_S_SUCC(bp, val) PUT_RCHILD(bp, val)


/* Global variables and functions */

static void *coalesce (void *bp);
static void *extend_heap (size_t size);
static void place (void *ptr, size_t asize);
static void insert_node (void *bp);
static int judge_child(void * bp);
static void delete(void *bp);
static void delete_node (void *bp);
static void delete_first_node(void * bp, int direction);
static void *find_fit (size_t asize);
static void printBlock(void *bp);
static void small_free_block_list_checker();
static void BST_checker(void * bp);
void mm_checkheap(int verbose);


static char *heap_listp = 0;//header of all the blocks in heap
static unsigned long virtual_NULL = 0;//used to point to mem_heap_lo(), the initial offsets for each ptr
static void *root = 0;//root of the BST
static void *small_free_block_list = 0;//header of byside linklists with 16-byte blocks

/*
 * 初始化分配器，将virtual_NULL指向mem_heap_lo() (0x800000000)
 * 并不直接拓展heap，而是采取demang-extending，在需要的时候再拓展
 * root和header初始化为virtual_NULL，可以理解为空NULL
*/

int mm_init(void) {
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *) -1)
        return -1;
    PUT(heap_listp + (2 * WSIZE), 0); /* Alignment padding */
    PUT(heap_listp + (3 * WSIZE), PACK(DSIZE, STAT_ALLOC)); /* Prologue header */
    PUT(heap_listp + (4 * WSIZE), PACK(DSIZE, STAT_ALLOC)); /* Prologue footer */
    PUT(heap_listp + (5 * WSIZE), PACK(0, STAT_ALLOC | STAT_PREV_ALLOC)); /* Epilogue header */
    heap_listp += (4 * WSIZE);
    /*init the global variables*/
    virtual_NULL = (unsigned long)(mem_heap_lo());
    root = (void *) virtual_NULL;
    small_free_block_list = (void *) virtual_NULL;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    //delay,demand-extending
    return 0;
}

/*
 * 这里是采用demand-extending的方式，需要多少空间申请多少空间
 * 先越过结尾块找到现有堆中最后一块，如果这一块是free的，那么就
 * 申请size-GET_SIZE(last_block)的空间，然后再合并就可以得到
 * size大小的空间
 */
void *extend_heap(size_t words) {
    void *bp;
    void *last_block = mem_heap_hi() - 3;

    size_t size = words;
    if (!PREV_ALLOC_R(last_block) && size - GET_SIZE(last_block) >= MIN_BLOCK_SIZE) {
        size -= GET_SIZE(last_block);
    }
    if (size <= 0) return NULL;

    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    size_t flag = 0 | PREV_ALLOC(bp);
    PUT_HDRP(bp, PACK(size, flag));
    PUT_FTRP(bp, PACK(size, flag));
    PUT_HDRP(NEXT_BLKP(bp), PACK(0, STAT_ALLOC));

    void *temp = coalesce(bp);
    insert_node(temp);
    return temp;
}

/*
 * 分配算法，分配的块大小向WSIZE对齐，注意最小块是2*DSIZE的，所以不足时需要补齐
 * 如果没有能从heap中找到合适的块，再对堆扩展
 */

void *malloc(size_t size) {
    size_t asize;      /* Adjusted block size */
    char *bp;

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /*  Adjust block size to include overhead and alignment reqs. */
    //plus WSIZE for we omit the footer of allocated block
    asize = ALIGN(size + WSIZE);
    asize = MAX(asize, MIN_BLOCK_SIZE);
    if ((bp = find_fit(asize)) == (void *) virtual_NULL) {
        /* No fit found. Get more memory and place the block */
        extend_heap(asize);
        if ((bp = find_fit(asize)) == (void *) virtual_NULL)
            return NULL;
    }
    place(bp, asize);
    return bp;
}

/* 释放之前申请的内存空间，合并之后再插入合适的链表中*/
void free(void *bp) {
    if (bp == 0)
        return;

    size_t size = GET_SIZE(bp);
    size_t checkalloc = GET_ALLOC(bp);
    if (checkalloc == 0) return;
    size_t flag = 0 | PREV_ALLOC(bp);
    PUT_HDRP(bp, PACK(size, flag));
    PUT_FTRP(bp, PACK(size, flag));

    insert_node(coalesce(bp));
}

/*
 * 重新分配
 * 如果重新分配的空间比较小，则将原来的块做分割
 * 若不然则重新分配
 */
void *realloc(void *ptr, size_t size) {
    size_t oldsize;
    void *newptr;
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        free(ptr);
        return 0;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL) {
        return malloc(size);
    }
    newptr = malloc(size);
    /* If realloc() fails the original block is left untouched  */
    if (!newptr) {
        return 0;
    }
    oldsize = GET_SIZE(ptr);
    if (size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);
    free(ptr);
    return newptr;
}

/*
 * 合并函数，与书中描述的隐式链表模式相近，也是分为四种情况
 * 但是要注意要保存PREV_ALLOC_INFO
 * 可能需要在链表中删除前后节点，注意到每次调用合并函数时bp都已经被删除了
 * 并且调用完之后还会再插入，因不需要额外对bp进行插入和删除
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = PREV_ALLOC(bp);
    size_t next_alloc = GET_ALLOC(NEXT_BLKP(bp));
    size_t size = GET_SIZE(bp);

    if (prev_alloc && next_alloc) { /* Case 0 */
        return bp;
    }
    else if (prev_alloc && !next_alloc) { /* Case 1 */
        size += GET_SIZE(NEXT_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size_t flag = PREV_ALLOC(bp);
        PUT_HDRP(bp, PACK(size, flag));
        PUT_FTRP(bp, PACK(size, flag));
        return bp;
    }
    else if (!prev_alloc && next_alloc) { /* Case 2*/
        void *prev = (void *) PREV_BLKP(bp);
        size_t flag = PREV_ALLOC(prev);
        delete_node(prev);
        size += GET_SIZE(prev);
        PUT_HDRP(prev, PACK(size, flag));
        PUT_FTRP(prev, PACK(size, flag));
        return prev;
    }
    else { /* Case 3 */
        void *prev = (void *) PREV_BLKP(bp);
        void *next = (void *) NEXT_BLKP(bp);
        size += GET_SIZE(prev) + GET_SIZE(next);
        delete_node(prev);
        delete_node(next);
        size_t flag = PREV_ALLOC(bp);
        PUT_HDRP(prev, PACK(size, flag));
        PUT_FTRP(prev, PACK(size, flag));
        return prev;
    }
}

/*
 * 分割函数，将一个块分成两份，减少内部碎片
 * 需要维护最小块大小以及PREV_ALLOC_INFO
 */
static void place(void *bp, size_t asize) {

    size_t csize = GET_SIZE(bp);
    delete_node(bp);

    if ((csize - asize) >= MIN_BLOCK_SIZE) {
        size_t flag = STAT_ALLOC | PREV_ALLOC(bp);
        PUT_HDRP(bp, PACK(asize, flag));

        void *temp = NEXT_BLKP(bp);
        PUT_HDRP(temp, PACK(csize - asize, STAT_PREV_ALLOC));
        PUT_FTRP(temp, PACK(csize - asize, STAT_PREV_ALLOC));

        insert_node(coalesce(temp));
    }
    else {
        size_t flag = STAT_ALLOC | PREV_ALLOC(bp);
        PUT_HDRP(bp, PACK(csize, flag));
    }
}

/*
 * 对于给定的size在堆中寻找合适的块，分为两种情况
 * 1.size为最小块大小，则在最小块的空闲链表中查询，取第一个即可，因为大小都是相同的
 * 2.size较大时，在BST中查询
 */
static void *find_fit(size_t asize) {
    if (asize <= MIN_BLOCK_SIZE && small_free_block_list != (void *) virtual_NULL) return small_free_block_list;

    //best-fit policy
    void *bp = (void *) virtual_NULL;
    void *temp = root;

    while (temp != (void *) virtual_NULL) {
        if (GET_SIZE(temp) >= asize) {
            bp = temp;
            temp = (void *) LCHILD_BLKP(temp);
        }
        else
            temp = (void *) RCHILD_BLKP(temp);
    }
    return bp;
}

/* 判断左儿子还是右儿子 */
inline static int judge_child(void * bp) {
    void *parent = (void *) PARENT_BLKP(bp);
    if (parent == (void *) virtual_NULL) {
        return 0;
    }
    if ((void *) LCHILD_BLKP(parent) == bp) {
        return 1;
    }
    if ((void *) RCHILD_BLKP(parent) == bp) {
        return 2;
    }

    return -1;
}


/* 向合适的链表中插入一个新的空闲块，分为两种情况
 * 1.size较小，直接插入双向链表的开头
 * 2.size较大，则需要插入BST，先查找这个节点
 * 如果找到了，那么需要将节点插入找到的这个节点对应的空闲链表的开头
 * 如果没有找到，则创建一个新的节点
 */
inline static void insert_node( void *bp ) {

    CLEAR_PREV_ALLOC(NEXT_BLKP(bp)); //reset the second bit of the HDRPer of the next block

    if (GET_SIZE(bp) == MIN_BLOCK_SIZE) {
        if (small_free_block_list == (void *) virtual_NULL) {
            PUT_S_SUCC(bp, small_free_block_list);
            PUT_S_PRED(bp, (void *) virtual_NULL);
            small_free_block_list = bp;
            return;
        }
        PUT_S_SUCC(bp, small_free_block_list);
        PUT_S_PRED(small_free_block_list, bp);
        PUT_S_PRED(bp, (void *) virtual_NULL);
        small_free_block_list = bp;
        return;
    }
    if (root == (void *) virtual_NULL) {
        PUT_LCHILD(bp, (void *) virtual_NULL);
        PUT_RCHILD(bp, (void *) virtual_NULL);
        PUT_PARENT(bp, (void *) virtual_NULL);
        PUT_HANGER(bp, (void *) virtual_NULL);
        root = bp;   //root is also an address.
        return;
    }
    void *parent = root;
    void *temp = root;
    int flag = 0;
    /*flag = 0 : the root itself; flag = 1 : left; flag = 2 : right*/
    while (temp != (void *) virtual_NULL) {
        /*when finding the free block in BST with the same size*/
        if (GET_SIZE(temp) == GET_SIZE(bp)) {

            PUT_LCHILD(bp, (void *) LCHILD_BLKP(temp));
            PUT_RCHILD(bp, (void *) RCHILD_BLKP(temp));
            PUT_PARENT(bp, (void *) PARENT_BLKP(temp));
            if (LCHILD_BLKP(temp) != virtual_NULL)
                PUT_PARENT(LCHILD_BLKP(temp), bp);
            if (RCHILD_BLKP(temp) != virtual_NULL)
                PUT_PARENT(RCHILD_BLKP(temp), bp);
            if (PARENT_BLKP(temp) != virtual_NULL) {
                int direction = judge_child(temp);
                if (direction == 1)
                    PUT_LCHILD(PARENT_BLKP(temp), bp);
                else if (direction == 2)
                    PUT_RCHILD(PARENT_BLKP(temp), bp);
            }
            PUT_HANGER(bp, temp);
            PUT_PARENT(temp, bp);
            PUT_LCHILD(temp, (void *) virtual_NULL);
            PUT_RCHILD(temp, (void *) virtual_NULL);
            if (root == temp) root = bp;
            return;
            /*SEARCH RIGHT CHILD*/
        } else if (GET_SIZE(temp) < GET_SIZE(bp)) {
            parent = temp;
            temp = (void *) RCHILD_BLKP(temp);
            flag = 2;
            /*SEARCH LEFT CHILD*/
        } else {
            parent = temp;
            temp = (void *) LCHILD_BLKP(temp);
            flag = 1;
        }
    }
    /*insert new node*/
    if (flag == 1) {
        PUT_LCHILD(parent, bp);
    } else {
        PUT_RCHILD(parent, bp);
    }
    PUT_LCHILD(bp, (void *) virtual_NULL);
    PUT_RCHILD(bp, (void *) virtual_NULL);
    PUT_PARENT(bp, parent);
    PUT_HANGER(bp, (void *) virtual_NULL);
}


/* 删除链表，还是分为两种情况
 * 1.size小时，直接删除双向链表的第一个元素
 * 2.size较大，则调用函数来进行BST的节点删除*/
inline static void delete_node(void *bp) {
    SET_PREV_ALLOC(NEXT_BLKP(bp));

    if (GET_SIZE(bp) == MIN_BLOCK_SIZE) {
        if (bp == small_free_block_list) {
            small_free_block_list = (void *) S_SUCC_BLKP(bp);
            PUT_S_PRED(small_free_block_list, (void *) virtual_NULL);
            return;
        }

        void *bpleft = (void *) S_PRED_BLKP(bp);
        void *bpright = (void *) S_SUCC_BLKP(bp);

        PUT_S_SUCC(LCHILD_BLKP(bp), bpright);
        PUT_S_PRED(RCHILD_BLKP(bp), bpleft);

        return;
    }
    delete(bp);
}

/*在BST中的删除分为三种情况
 * 1.节点有悬挂节点，则用悬挂节点替代该节点
 * 2.节点无悬挂节点，但是是某一个节点的悬挂节点，则直接删掉
 * 3.节点是BST中的节点，则调用BST中删除节点的函数*/
inline static void delete(void *bp) {

    if (root == (void *) virtual_NULL) {
        return ;
    }

    if ((void *) HANGER_BLKP(bp) != (void *) virtual_NULL) {
        void *temp = (void *) HANGER_BLKP(bp);
        PUT_LCHILD(temp, LCHILD_BLKP(bp));
        PUT_RCHILD(temp, RCHILD_BLKP(bp));
        PUT_PARENT(temp, PARENT_BLKP(bp));
        if ((void *) LCHILD_BLKP(bp) != (void *) virtual_NULL)
            PUT_PARENT((void *) LCHILD_BLKP(bp), temp);
        if ((void *) RCHILD_BLKP(bp) != (void *) virtual_NULL)
            PUT_PARENT((void *) RCHILD_BLKP(bp), temp);

        if ((void *)PARENT_BLKP(bp) != (void *) virtual_NULL) {
            void *parent = (void *) PARENT_BLKP(bp);
            if ((void *)HANGER_BLKP(parent) != bp){
                int direction = judge_child(bp);
                if (direction == 1)
                    PUT_LCHILD(parent, temp);
                else if (direction == 2)
                    PUT_RCHILD(parent, temp);
                else {
                    printf("error in ptr\n");
                }
            }
            else PUT_HANGER(parent, (void *) HANGER_BLKP(bp));

        }
        if (root == bp) root = temp;
        return ;
    }

    if ((void *)PARENT_BLKP(bp) != (void *)virtual_NULL && (void *) HANGER_BLKP(PARENT_BLKP(bp)) == bp) {
        PUT_HANGER((void *)PARENT_BLKP(bp), virtual_NULL);
        return ;
    }

    delete_first_node(bp, judge_child(bp));
}

/* 删除BST节点，只需将其替换为左子树的最大节点 */
inline static void delete_first_node(void * bp, int direction) {

    void *replpointer, *replparent = (void *) virtual_NULL, *delparent = (void *) PARENT_BLKP(bp);

    //带删除节点左子树为空，则直接用右子树代替
    if ((void *) LCHILD_BLKP(bp) == (void *) virtual_NULL)
        replpointer = (void *) RCHILD_BLKP(bp);
    //若不为空，在在左子树中寻找最大节点
    else {
        replpointer = (void *) LCHILD_BLKP(bp);
        while ((void *) RCHILD_BLKP(replpointer) != (void *) virtual_NULL) {
            replparent = replpointer;
            replpointer = (void *) RCHILD_BLKP(replpointer);
        }
        //替换节点就是被删节点左子节点
        if (replparent == (void *) virtual_NULL) {
            PUT_LCHILD(bp, LCHILD_BLKP(replpointer));
            if ((void *) LCHILD_BLKP(replpointer) != (void *) virtual_NULL)
                PUT_PARENT(LCHILD_BLKP(replpointer), bp);
        } else {
            PUT_RCHILD(replparent, LCHILD_BLKP(replpointer));
            if ((void *) LCHILD_BLKP(replpointer) != (void *) virtual_NULL)
                PUT_PARENT(LCHILD_BLKP(replpointer), replparent);
        }
        PUT_LCHILD(replpointer, LCHILD_BLKP(bp));
        if ((void *) LCHILD_BLKP(bp) != (void *) virtual_NULL)
            PUT_PARENT(LCHILD_BLKP(bp), replpointer);
        PUT_RCHILD(replpointer, RCHILD_BLKP(bp));
        if ((void *) RCHILD_BLKP(bp) != (void *) virtual_NULL)
            PUT_PARENT(RCHILD_BLKP(bp), replpointer);
    }

    if (delparent == (void *) virtual_NULL)
        root = replpointer;
    else if ((void *) LCHILD_BLKP(delparent) == bp)
        PUT_LCHILD(delparent, replpointer);
    else
        PUT_RCHILD(delparent, replpointer);
    PUT_PARENT(replpointer, delparent);
}
/*
 * lineno = 0时打印小内存块空闲链表中的所有块，并排错
 * lineno = 1时打印BST中所有块，并排错
 */
void mm_checkheap(int lineno)
{
    if (lineno == 0) {
        small_free_block_list_checker();
        return ;
    }
    if (lineno == 1) {
        BST_checker(root);
        return ;
    }
}

/*打印块的信息，将所有指针信息打印出，由于两种块的组织不同，所以分情况打印*/
static inline void printBlock(void *bp) {

    size_t alloc_flag = GET_ALLOC(bp);
    if (!alloc_flag) {
        if (SIZE(HDRP(bp)) != SIZE(FTRP(bp)) || ALLOC(HDRP(bp)) != ALLOC(FTRP(bp))) {
            printf("Header and footer inconsistency!\n");
            printf("block_ptr = %p, header = %u, footer = %u\n",
                   bp, *(unsigned int*) HDRP(bp), *(unsigned int*) FTRP(bp));
            exit(0);
        }
    }
    size_t blocksize = GET_SIZE(bp);
    if (blocksize <= MIN_BLOCK_SIZE) {
        printf("Ptr_addr = %p, PRED = %p, SUCC = %p\n",
               bp, (void *) S_PRED_BLKP(bp), (void *) S_SUCC_BLKP(bp));
    }
    else {
        printf("Ptr_addr = %p, LCHILD = %p, RCHILD = %p, PARENT = %p, HANGER = %p\n",
               bp, (void *) LCHILD_BLKP(bp), (void *) RCHILD_BLKP(bp), (void *) PARENT_BLKP(bp),
               (void *) HANGER_BLKP(bp));
    }

}

/*遍历小内存块空闲链表，如果后继指针与前驱指针不对应则报错
 * 如果header footer不对应则报错
 * */
static inline void small_free_block_list_checker() {
    void *temp = small_free_block_list;
    while (temp != (void *)virtual_NULL) {
        if (((*(unsigned int *) HDRP(temp)) & ~0x7) != ((*(unsigned int *) FTRP(temp)) & ~0x7)) {
            printf("Header and footer inconsistency!\n");
            printf("block_ptr = %p, header = %x, footer = %x\n",
                   temp, *(unsigned int*) HDRP(temp), *(unsigned int*) FTRP(temp));
            exit(0);
        }
        printf("Block:\n:");
        printBlock(temp);
        printf("\n");
        if (S_SUCC_BLKP(temp) != virtual_NULL) {
            if (temp != (void *) S_PRED_BLKP(S_SUCC_BLKP(temp))) {
                printf("PRED and SUCC inconsistency!\n");
                printf("block_ptr = %p, pred_of_succ = %p\n", temp, (void *) S_PRED_BLKP(S_SUCC_BLKP(temp)));
                exit(0);
            }
        }
        temp = (void *) S_SUCC_BLKP(temp);
    }
}

/*遍历BST树，先序遍历逐次打印
 * 如果后继指针与前驱指针不对应则报错
 * 如果header footer不对应则报错*/
static inline void BST_checker(void *bp) {
    if (bp == (void *) virtual_NULL) return;
    void *temp = bp;
    printf("BST node and its hangers:\n");
    while (HANGER_BLKP(temp) != virtual_NULL) {
        printBlock(temp);
        temp = (void *) HANGER_BLKP(temp);
    }
    printf("\n");
    BST_checker((void *) LCHILD_BLKP(bp));
    BST_checker((void *) RCHILD_BLKP(bp));
}

