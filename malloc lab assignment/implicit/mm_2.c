// Implicit Linked List - Next fit

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/////// 워드, 헤더, 푸터 / 더블 워드 / 힙 확장 기본 바이트
#define WSIZE       4           
#define DSIZE       8           
#define CHUNKSIZE   (1 << 12)   

#define MAX(x, y)   ((x) > (y) ? (x) : (y))   

// 정보 (블록 사이즈와 할당 여부에 대한 정보를 헤더와 풋터에 넣어야 함)
#define PACK(size, alloc)   ((size) | (alloc))

#define GETTER(p)  (*(unsigned int *)(p))
#define PUTTER(p, val)  (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)    (GETTER(p) & ~0x7)   // 블록 크기
#define IS_ALLOCATED(p)   (GETTER(p) & 0x1)  // 블록 할당 여부

#define HDPT(bp)    ((char *)(bp) - WSIZE)  // 헤더 포인터
#define FTPT(bp)    ((char *)(bp) + GET_SIZE(HDPT(bp)) - DSIZE)  // 풋터 포인터

#define NEXT_BLKP(bp)   (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)))   // 다음 블록 포인터 
#define PREV_BLKP(bp)   (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)))   // 이전 블록 포인터

static void* heap_list = NULL;
static char* last_bp; // 마지막 블록 포인터

static int mm_init(void);
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
void* mm_malloc(size_t size);
static void* first_fit(size_t a_size);
static void place(void* bp, size_t a_size);
void mm_free(void* bp);
void* mm_realloc(void* bp, size_t size);

////////
// mm_init 
int mm_init(void)
{
    // 메모리 확장 실패
    if ((heap_list = mem_sbrk(4 * WSIZE)) == (void*)-1) {  
        return -1;
    }

    PUTTER(heap_list, 0);                            // 시작 부분
    PUTTER(heap_list + (1 * WSIZE), PACK(DSIZE, 1));    // 맨 앞 헤더 할당된 것
    PUTTER(heap_list + (2 * WSIZE), PACK(DSIZE, 1));    // 풋터
    PUTTER(heap_list + (3 * WSIZE), PACK(0, 1));        // 뒷부분 에필로그 헤더

    heap_list += (2 * WSIZE); // 힙 리스트의 포인터를 맨 앞 블록의 끝으로 , 블록 관리

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) { // 청크 사이즈만큼 힙 확장 -> 실패하면 -1
        return -1;
    }
    return 0;
}

// extend_heap
static void* extend_heap(size_t words) { // 힙 확장
    char* bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 짝수 크기로 할당

    // 힙 확장에 실패하면
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    PUTTER(HDPT(bp), PACK(size, 0));   // 프리 블록 헤더
    PUTTER(FTPT(bp), PACK(size, 0));   // 프리 블록 풋터
    PUTTER(HDPT(NEXT_BLKP(bp)), PACK(0, 1));   // 새 에필로그 헤더

    return coalesce(bp); // 이전 블록이 프리블록이면 합쳐 !
}

// coalesce
static void* coalesce(void* bp) { // 프리 블록끼리 합치기
    // 할당 상태 저장
    size_t prev_alloc = IS_ALLOCATED(FTPT(PREV_BLKP(bp))); // 할당 여부 확인
    size_t next_alloc = IS_ALLOCATED(HDPT(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDPT(bp)); // 크기 값 저장

    // 모두 할당된 경우
    if (prev_alloc && next_alloc) {
        return bp;
    }

    // 다음이 프리블록이면
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDPT(NEXT_BLKP(bp))); // 현재 블록의 크기에 다음 블록 크기 더해
        PUTTER(HDPT(bp), PACK(size, 0)); // 헤더와 풋터 업데이트
        PUTTER(FTPT(bp), PACK(size, 0));
    }

    // 이전이 프리블록이면 
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDPT(PREV_BLKP(bp))); // 현재 블록의 크기에 이전 블록 크기 더해
        PUTTER(FTPT(bp), PACK(size, 0));   // 헤더와 풋터 업데이트
        PUTTER(HDPT(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // 앞뒤 모두 프리블록이면
    else {
        size += GET_SIZE(HDPT(PREV_BLKP(bp))) + GET_SIZE(FTPT(NEXT_BLKP(bp))); // 현재 블록의 크기에 다음과 이전 블록 크기 더해
        PUTTER(HDPT(PREV_BLKP(bp)), PACK(size, 0)); // 헤더와 풋터 업데이트
        PUTTER(FTPT(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    last_bp = bp;  // 마지막 할당 블록 포인터 저장
    return bp; // 합쳐진 블록의 시작 주소 리턴
}

// mm_malloc 
void* mm_malloc(size_t size) {
    size_t a_size; // 실제로 할당할 블록 크기
    size_t extend_size; // 힙을 확장할 크기
    char* bp; // 찾은 프리 블록의 시작 주소

    if (size == 0) { // 요청하는 크기가 0이면 할당 불필요
        return NULL;
    }

    // 할당할 프리블록 찾기
    if (size <= DSIZE) { // 최소 블록 크기 이하로 요청 받은 경우 최소 크기 블록으로 할당
        a_size = 2 * DSIZE;
    }
    else { // 요청보다 더 크게 할당
        // 헤더와 풋터를 위한 size + DSIZE
        a_size = ((size + DSIZE - 1 + DSIZE) / DSIZE) * DSIZE;
    }

    // 적절한 프리 블록 탐색
    if ((bp = next_fit(a_size)) != NULL) {  
        place(bp, a_size);                  
        last_bp = bp; // 마지막 할당한 블록 포인터로 저장
        return bp;  // 프리 블록 적절한 것 발견했다면 return 후 종료
    }
    // 적절한 프리블록을 못 찾았다면
    extend_size = MAX(a_size, CHUNKSIZE);  // 요청 크기와 기본 크기 중 큰 값으로 확장
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL) { // 정해진 크기로 힙 확장 
        return NULL; // 실패하면 -1 NULL
    }
    place(bp, a_size);  // bp 에는 함수를 통해 프리 블록 할당
    last_bp = bp; // 마지막 할당한 블록 포인터로 저장
    return bp;  // 성공하면 블록 시작 주소 리턴
}

// next fit
static void* next_fit(size_t a_size) {
    char* bp;  // 현재 탐색 중인 블록을 가리키는 포인터

    // 마지막 할당한 블록 포인터부터 하나씩 , 블록 크기가 0보다 클 때까지 (=힙 끝까지)
    for (bp = last_bp; GET_SIZE(HDPT(bp)) > 0; bp = NEXT_BLKP(bp)) { 
        if (!IS_ALLOCATED(HDPT(bp)) && GET_SIZE(HDPT(bp)) >= a_size) {
            // 프리 블록이면서 요청 크기보다 크거나 같은 공간이면 만족
            return bp; // 시작 주소 반환
        }
    }

    return NULL; // 찾지 못했다면 NULL
}
 
// place
static void place(void* bp, size_t a_size) { 
    static void place(void* bp, size_t a_size) {  // 블록 포인터와 할당할 크기
        size_t c_size = GET_SIZE(HDPT(bp)); // 현재 블록의 크기

        if ((c_size - a_size) >= (2 * (DSIZE))) { // 요청된 크기를 최소 크기로 쪼갤 수 있다면

            PUTTER(HDPT(bp), PACK(a_size, 1)); // 현재 헤더와 풋터에 할당 정보와 크기 업데이트
            PUTTER(FTPT(bp), PACK(a_size, 1));

            bp = NEXT_BLKP(bp); // 다음 블록으로 이동

            // 남은 공간의 헤더와 풋터는 할당되지 않은 상태 0
            PUTTER(HDPT(bp), PACK(c_size - a_size, 0));
            PUTTER(FTPT(bp), PACK(c_size - a_size, 0));
        }
        else { // 블록 크기 불충분해서 분할 불가 (남은 공간이 최소보다 작아서)
            PUTTER(HDPT(bp), PACK(c_size, 1));  // 할당 상태 1
            PUTTER(FTPT(bp), PACK(c_size, 1));
        }
    }

}

// mm_free
void mm_free(void* bp)
{
    size_t size = GET_SIZE(HDPT(bp)); // 블록 해제를 위해 매개변수 받기

    PUTTER(HDPT(bp), PACK(size, 0)); // 프리블록으로 상태 변경
    PUTTER(FTPT(bp), PACK(size, 0));
    coalesce(bp); // 프리 블록 병합
}

// mm_realloc
void* mm_realloc(void* bp, size_t size)
{
    void* old_bp = bp; // 기존 블록 포인터
    void* new_bp;  // 새로 할당되는 블록 할당 포인터
    size_t copySize; // 복사 데이터 크기

    new_bp = mm_malloc(size); // 새 블록 할당 

    if (new_bp == NULL) return NULL;

    copySize = GET_SIZE(HDPT(old_bp)); // 기존 블록 크기

    if (size < copySize) // 재할당할 크기가 기존보다 작으면
        copySize = size; // 원래 size만큼조정

    // 데이터 복사
    memcpy(new_bp, old_bp, copySize);

    mm_free(old_bp); // 기존 블록 해제

    return new_bp; // 실패시 블록 할당 역할
}
