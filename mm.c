/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define WSIZE 4			//Words are int-sized
#define DSIZE 8
#define CNKSIZE (1<<12) 	//The amount of heap extention (as a chunk) 
#define ALIGNMENT 8

#define MAXSIZE 16		//Max size of the segregated free list

#define MAX(x,y) ((x) > (y) ? (x) : (y))
#define MIN(x,y) ((x) < (y) ? (x) : (y))
// Pack a size and allocate bit into a word (size : DSIZE)
#define PACK(size,alloc) ((size)|(alloc))

// Read/Write a word at p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)	//size at p
#define GET_ALLOC(p) (GET(p) & 0x1)	//allocation at p

// Set given block point bp as list pointer lp 
#define SET(bp,lp) ((*(unsigned int *)(bp)) = ((unsigned int)(lp)))

//Given block ptr bp, compute address of its header and footer
#define HEAD(bp) ((char *)(bp) - WSIZE)
#define FOOT(bp) ((char *)(bp)+ GET_SIZE(HEAD(bp)) - DSIZE)	//consider WSIZE as a unit

//Given block ptr bp, compute address if the next/prev 'block'
#define NEXT(bp) ((char *)(bp) + GET_SIZE((char*)(bp)-WSIZE))	//use the present header
#define PREV(bp) ((char *)(bp) - GET_SIZE((char*)(bp)-DSIZE))	//use the prev footer

//Given blcok ptr bp, compute address of its next/prev 'link' for seg_lists
//REfer to exlpcit lists section in ppt
#define NEXT_LINK(bp) ((char *)(bp))
#define PREV_LINK(bp) ((char *)(bp) +WSIZE)

//Given list ptr lp, compute the address of its next/prev 'block on list' in seg_lists
#define NEXT_BOL(lp) (*(char **)(lp))
#define PREV_BOL(lp) (*(char **)((char*)(lp)+WSIZE))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) 	// = ALIGN(8)


//Helper function prototypes
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_block(void *bp, size_t size);
static void delete_block(void *lp);


//Global varaible
static char **seg_lists;
static char *heap_listp;


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  int i;
 
	
  //Create init empty heap
  if ((heap_listp = mem_sbrk((MAXSIZE+4)*WSIZE)) == (void *)-1)	// +3 includes prlg header/footer, eplg header
	return -1;	//invalid


  seg_lists = (char **) heap_listp;  

  PUT(heap_listp,0);	//Alignment padding
  PUT(heap_listp + WSIZE ,  PACK(DSIZE+MAXSIZE*WSIZE,1));		//Prologue header
 
  for (i=2; i<=MAXSIZE+1; i++){
	PUT(heap_listp + (i*WSIZE),0);
  }
 
  PUT(heap_listp + ((MAXSIZE+2)*WSIZE), PACK(DSIZE+MAXSIZE*WSIZE,1));		//Prologue footer
  PUT(heap_listp + ((MAXSIZE+3)*WSIZE), PACK(0,1));		//Epilogue header
  heap_listp += (2*WSIZE); //point to the prologue

  seg_lists = heap_listp;

  //Extend the empty heap w/ a free block of CNKSIZE bytes 
  if (!extend_heap(CNKSIZE/WSIZE))
	return -1;	//invalid
  
  return 0;	//valid
}


/*Invoked when  (1) the heap is initialized
		(2) mm_malloc is unable to find a suitable fit*/
static void *extend_heap(size_t words)
{
   char *bp;
   size_t size;

   //Allocate an even number of words to maintain alignment
   size = (words % 2) ? (words+1)*WSIZE : words*WSIZE;
   //size=ALIGN(words);

   if ((long)(bp=mem_sbrk(size)) == -1)	 //request additional heap space
	return NULL;			//invalid

   //Initialize free block header/footer and the epilogue header
   PUT(HEAD(bp), PACK(size,0));
   PUT(FOOT(bp), PACK(size,0));		//free header/footer
   PUT(HEAD(NEXT(bp)), PACK(0,1));	//New epilogue header

   insert_block(bp,size); 

   return coalesce(bp);	//Coalesce if the prev one was free;
} 


static void *coalesce(void *bp)
{
   size_t prev_alloc=GET_ALLOC(HEAD(PREV(bp)));
   size_t next_alloc = GET_ALLOC(HEAD(NEXT(bp)));
   size_t size = GET_SIZE(HEAD(bp));

   //if (!GET_REALC(HEAD(PREV(ptr))))
//	prev_alloc=GET_ALLOC(HEAD(NEXT(bp)));
   //else
 //	prev_alloc=1;	//set occupied



   if (prev_alloc && next_alloc){		//both are occupied
 	return bp;
   }
   else{
   // now we have free blocks needed to be discarded in seg_lists due to coalescing 
   // otherwise, there occurs overlapped links
	delete_block(bp); //at first we remove the requested one	

	if (prev_alloc && !next_alloc){		//only the next block is free in a row
	   delete_block(NEXT(bp));

	   size += GET_SIZE(HEAD(NEXT(bp)));
	   PUT(HEAD(bp), PACK(size,0));
	   PUT(FOOT(bp), PACK(size,0));
	
	 }
	else if (!prev_alloc && next_alloc){		//only the prev block is free in a row
	   delete_block(PREV(bp));
		
	   size += GET_SIZE(HEAD(PREV(bp)));
	   
	   bp=PREV(bp);
	   PUT(HEAD(bp), PACK(size,0));
	   PUT(FOOT(bp), PACK(size,0));		//we don't need to consider the old (in the middle) one
	}
	else{					//both sides are free
	   delete_block(PREV(bp));
	   delete_block(NEXT(bp));

	   size +=GET_SIZE(HEAD(PREV(bp)))+GET_SIZE(HEAD(NEXT(bp)));
	   bp=PREV(bp);
 	   PUT(HEAD(bp), PACK(size,0));
   	   PUT(FOOT(bp), PACK(size,0));
   	}
	//finally, we update new (bigger) free block into the seg_lists
	insert_block(bp,size);

   }

   return bp;
}



static void *find_fit(size_t asize)
{
   //First_fit search; we return proper lp we found

   void *lp=NULL;		//list : pointer for list itself; lp : block pointer in list 
   int lev;
   size_t tsize=asize;		//temp size
   

   for (lev=0; lev<MAXSIZE-1; lev++){ //find lev
	if (tsize<=1)
	   break;
	tsize >>=1;
   }
   
   for (; lev<= MAXSIZE-1; lev++){

	lp = seg_lists[lev];

	if (lp){	// not empty list
	  
	   //Find the block whose size is the smallest on the list (Note again: list is monot. decreasing)
	   while ((lp) && (asize > GET_SIZE(HEAD(lp)) )){	
		lp = NEXT_BOL(lp);
	   }
	   
	   if(lp)		//lp still exists; i.e. we found properly-sized block 
		break;
	
	   //=> no block is found; try the next larger class	
	   
	}	

	 	
   }//if we failed to find lp, then it should be lp=NULL; 
  	
   return lp;

   /*
   bp=heap_listp;
   
   for (bp=heap_listp; GET_SIZE(HEAD(bp));bp=NEXT(bp)){
	if (!GET_ALLOC(HEAD(bp)) && (asize <= GET_SIZE(HEAD(bp))))
	   return bp; 		//not allocated + proper size
   }

   return NULL;			//NO flt
  */

}

//place the requested block at the begenning of the free block ,
//spliting only if the size of the remainder(csize-asize) would equal or exeed the 16B(min block size) 
static void place(void *bp, size_t asize)
{ 
   //bp is already properly chosen one

   size_t csize = GET_SIZE(HEAD(bp));	//original size
   size_t rmd = csize-asize;
 
   if ((csize-asize) >= (2*DSIZE)){	//Note that the min block size is 16B, here
	PUT(HEAD(bp), PACK(asize,1));
	PUT(FOOT(bp), PACK(asize,1));
	bp=NEXT(bp);			//split
	PUT(HEAD(bp), PACK(rmd,0));
	PUT(FOOT(bp), PACK(rmd,0));
	
	insert_block(bp,rmd);		//insert new free block
   }
  /*else if (asize >= (1<<8)){
	PUT(HEAD(bp),PACK(rmd,0));
	PUT(FOOT(bp),PACK(rmd,0));
	bp=NEXT(bp);
	PUT(HEAD(bp),PACK(asize,1));
	PUT(FOOT(bp),PACK(asize,1));

	insert_block(bp,rmd);
   }*/
   else {
	PUT(HEAD(bp), PACK(csize,1));
	PUT(FOOT(bp), PACK(csize,1));
   }



} 

 
   
static void insert_block(void *bp, size_t size)
{
 //insert free block into the seg_list w/ LIFO policy

   int lev;		// ith lev : 2^i <= size < 2^(i+1)
   size_t tsize=size;	// temp size
   //char **list; 	// for the seg_lists
   void *next;
   void *prev=NULL;  

   //unsigned int bp_addr =(unsigned int) bp;

   // Note that my seg_list is classified by level, which is related to the size of lists

   // determine a proper level from given size
   for (lev=0; lev<MAXSIZE-1; lev++){
	if (tsize<=1)
	   break;
	tsize>>=1;	//halve 
   }
  
   //list = seg_lists+lev;	//Note that this is initialized as NULL
   //next = GET(list);   
  
   next=seg_lists[lev]; //at first 

   //find a proper position to input the given node 
   //size ~ monotone decreasing for the ease of managing big blocks
   while((next) && (size <= GET_SIZE(HEAD(next)))){	//size ~ monotone decreasing 
	//propagate
	prev = next;
	next = NEXT_BOL(next);
   			
   }

   //Refer to the exlicit free list part in the ppt
   //Insertion as DLL w/ LIFO in levelwise
/*
   if (!next){ 
	
	PUT(list, bp_addr);
	PUT(NEXT_LINK(bp), (unsigned int) list);
	PUT(PREV_LINK(bp),0);

   }
   else{
	
	PUT(NEXT_LINK(bp), (unsigned int) list);
	PUT(PREV_LINK(bp), GET(bp));
	
	PUT(NEXT_LINK(next), bp_addr);

	PUT(list, bp_addr);	//save 

   }
*/
   if (!next){	//clearly end of the seg_lists

	if(!prev){	//but also start of the level
	   seg_lists[lev]= bp;		//Newly initialize the root
	   SET(NEXT_LINK(bp),NULL);
	   SET(PREV_LINK(bp),NULL);
	}
	else{		//not the starting one
	   SET(NEXT_LINK(bp),NULL); 
	   SET(PREV_LINK(bp),prev);

	   SET(NEXT_LINK(prev), bp);	//grow the list
	}
   }
   else{		//Size difference occurs => the next one has smaller size 
	if ((!prev)){	//but starting one
	   seg_lists[lev] = bp;	//initiate the root
	   SET(NEXT_LINK(bp),next);
	   SET(PREV_LINK(bp),NULL);
	   
	   SET(PREV_LINK(next),bp);	//connect across size
 	}
	else{			// nested
	   SET(NEXT_LINK(bp), next);
	   SET(PREV_LINK(bp), prev);

	   SET(PREV_LINK(next),bp);	//connect accross size
	   
	   SET(NEXT_LINK(prev),bp);	//grow the list
	}
   }
   
   return;
} 

static void delete_block(void *lp)
{
   // we shall delete the block on the list for given list block pointer lp
   size_t size = GET_SIZE(HEAD(lp));
   size_t tsize=size;
   int lev;
   

   //find the proper level;
   for (lev=0; lev<MAXSIZE-1; lev++){
	if (tsize<=1)
	   break;
	tsize>>=1;
   }
   //now the level for given lp is determined;
   //Note that organiing links of the survived lists is enough for deleting	
    
   //list += seg_lists+lev;

   if(!NEXT_BOL(lp)){		//end of the corr. list
 	if (!PREV_BOL(lp)){	// but also the first one on the list; i.e.are unique
	   seg_lists[lev]=NULL;
	}
	else{			// exists predecessor
	   SET(NEXT_LINK(PREV_BOL(lp)),NULL);
	}
   }
   else{		//not the end of the corr. list
	if (!PREV_BOL(lp)){	//first one
	   seg_lists[lev]=NEXT_BOL(lp);
	
	   SET(PREV_LINK(NEXT_BOL(lp)),NULL);	 //new start
	}
	else{		//nested
	   SET(NEXT_LINK(PREV_BOL(lp)),NEXT_BOL(lp));
	

	   SET(PREV_LINK(NEXT_BOL(lp)),PREV_BOL(lp));
	}
   }
   
   return;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

    int newsize = ALIGN(size + SIZE_T_SIZE);		//SIZE_T_SIZE=8
    //void *p = mem_sbrk(newsize);
   
    size_t asize;  //Adjusted block size
    size_t extended;	//amount to extend heap if no fit
    char *bp;   

    if (size ==0)
	return NULL;
   /*
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }*/
   
   //Adjust block size to include overhead and alignment requires
   if (size<=DSIZE)
	asize=2*DSIZE;	//min block size
   else
	asize=newsize;
	//asize= DSIZE*((size +DSIZE+ (DSIZE-1))/DSIZE);		//textbook ver

   //Search the free list for a list 
   if ((bp=find_fit(asize))!=NULL){
	
   	delete_block(bp);	// we need to use the corr free block; so delete it 
	place(bp,asize);
   	 
	return bp;
    
    }    

   //If no fit found
   extended=MAX(asize,CNKSIZE);
   if (!(bp=extend_heap(extended/WSIZE))){
	return NULL;	
   }
 
   delete_block(bp);	// we need to use the corr free block; so delete it 
   place(bp,asize);

   return bp;
   

}

/*
 * mm_free - Freeing a block.
 */
void mm_free(void *ptr)
{

   size_t size = GET_SIZE(HEAD(ptr));

   PUT(HEAD(ptr), PACK(size,0));
   PUT(FOOT(ptr), PACK(size,0));

   //now the corr block is freed
   insert_block(ptr,size);

   coalesce(ptr);

   return;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);		//SIZE_T_SIZE=8
    void *new_bp, *next_p;
    size_t given_size= GET_SIZE(HEAD(ptr));
    size_t extended;
    size_t asize, tsize, ttsize;	//adjusted/temp/temp of temp   

    size_t copySize;
    void *newptr;
    void *oldptr=ptr;


   if (!ptr)
	return mm_malloc(size);

   if (!size){
	mm_free(ptr);
	return NULL;
   }
   //align
   asize= newsize;
   
  
   //The core of realloc
 
   new_bp =ptr;

   if (asize == given_size)
   {
	return ptr;
   }  
   if (asize < given_size)		// requested size is smaller
   {
	tsize= given_size-asize;

	if (tsize <= 2*DSIZE) 	// diff is less than minimum block size
	   return new_bp;		// don't need to split

	//rearrange the size
	PUT(HEAD(new_bp),PACK(asize,1));	
	PUT(FOOT(new_bp),PACK(asize,1));

	//if (!tsize){
	new_bp = NEXT(new_bp);		//cuz now we splited blcok; new small block is redefined above
	
	PUT(HEAD(new_bp),PACK(tsize,0));
	PUT(FOOT(new_bp),PACK(tsize,0));
	insert_block(new_bp,tsize);
	coalesce(new_bp);	//temp
	//}

	return ptr;
   }
   else{
	//note that we may lack of space

	tsize = asize-given_size;

	next_p=NEXT(new_bp);

	if (((ttsize=GET_SIZE(HEAD(next_p)))>tsize) && !GET_ALLOC(HEAD(next_p))){

	   delete_block(next_p);
	   tsize = ttsize - tsize;
	  
	  if (tsize <=DSIZE)
		asize+=tsize;

	   PUT(HEAD(new_bp),PACK(asize,1));
	   PUT(FOOT(new_bp),PACK(asize,1));

	  if (tsize > DSIZE){
	   next_p=NEXT(new_bp);

	   PUT(HEAD(next_p),PACK(tsize,0));
	   PUT(FOOT(next_p),PACK(tsize,0));
	   insert_block(next_p,tsize);
	  }

	   return new_bp;

	}
	else{
	   
	   

	   new_bp=mm_malloc(size);
	   memcpy(new_bp,ptr,given_size-WSIZE);
	   mm_free(ptr);

	   return new_bp;


	}
	/*if (!(ttsize=GET_SIZE(HEAD(next_p)))){	//next one is an epilogue block

	   extended=MAX(asize,CNKSIZE);
	   if(!(extend_heap(extended)))
		 return NULL;
	   
	   tsize = given_size + extended -asize;

	   PUT(HEAD(next_p),PACK(tsize,0));	//split
	   PUT(FOOT(next_p),PACK(tsize,0));
	   insert_block(next_p,tsize);

	   return new_bp;
	}

	if (!GET_ALLOC(HEAD(next_p))){		//next one is a free block

	   tsize= asize-(given_size + ttsize);
	   extended=0;

	   if (tsize>0 && !GET_SIZE(HEAD(NEXT(next_p)))){	//but we don't have enough space to merge
	   	extended=MAX(asize,CNKSIZE);
	   	if (!(extend_heap(extended)))
		   return NULL;
		
	  	tsize=extended-tsize;	//redefine tsize : remainder size
		
		PUT(HEAD(new_bp),PACK(asize,1));
		PUT(FOOT(new_bp),PACK(asize,1));

		next_p=NEXT(new_bp);
		PUT(HEAD(next_p),PACK(tsize,0));  //split
		PUT(FOOT(next_p),PACK(tsize,0));
		insert_block(next_p,tsize);
		
		return new_bp;


	    }
	}
	   
	tsize=given_size-DSIZE;

	new_bp=mm_malloc(size);
	memcpy(new_bp,ptr,tsize);
	mm_free(ptr);
	  */ 
	

   }
    
  
 /*
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - WSIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;	//old ver/.
*/
  return new_bp;
}














