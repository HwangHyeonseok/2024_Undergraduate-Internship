// Explicit Linked List - First fit

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include <sys/mman.h>
#include <errno.h>

#include "mm.h"
#include "memlib.h"

// 이미 있던 !
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

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

#define PRED_FREEPT(bp) (*(void**)(bp)) // 이전 프리블록 포인터
#define SUCC_FREEPT(bp) (*(void**)(bp + WSIZE)) // 다음 프리블록 포인터

static void* heap_list = NULL; // 힙 리스트 시작 포인터
static void* free_list = NULL; // 프리블록 리스트 시작 포인터

static int mm_init(void);
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
void* mm_malloc(size_t size);
static void* first_fit(size_t a_size);
static void place(void* bp, size_t a_size);
void mm_free(void* bp);
void* mm_realloc(void* bp, size_t size);

void putFreeBlock(void* bp); // 프리블록 리스트에 블록 추가
void rmFreeBlock(void* bp); // 프리블록 리스트에서 블록 삭제

///////
// mm_init 
int mm_init(void)
{   
    // 메모리 확장 실패
    if ((heap_list = mem_sbrk(6 * WSIZE)) == (void*)-1) {
        return -1;
    }

    PUTTER(heap_list, 0);                             // 시작 부분
    PUTTER(heap_list + (1 * WSIZE), PACK(2 * DSIZE, 1)); // 맨 앞 헤더 할당된 것
    PUTTER(heap_list + (2 * WSIZE), NULL);            // 이전 포인터 null
    PUTTER(heap_list + (3 * WSIZE), NULL);            // 이후 포인터 null
    PUTTER(heap_list + (4 * WSIZE), PACK(2 * DSIZE, 1));  // 풋터 
    PUTTER(heap_list + (5 * WSIZE), PACK(0, 1));      // 뒷부분 헤더

    free_list = heap_list + (2 * WSIZE); // 프리 블록 리스트의 시작을 맨 앞 다음 첫 프리블록으로

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) // 확장 ~
        return -1;

    return 0;
}

// Coalesce
static void* coalesce(void* bp) 
{
    size_t prev_alloc = IS_ALLOCATED(FTPT(PREV_BLKP(bp))); // 이전 할당 여부
    size_t next_alloc = IS_ALLOCATED(HDPT(NEXT_BLKP(bp))); // 이후 할당 여부
    size_t size = GET_SIZE(HDPT(bp));

    if (prev_alloc && !next_alloc) { // 다음 블록이 프리
        rmFreeBlock(NEXT_BLKP(bp)); // 프리 블록 리스트에서 다음 블록 제거

        size += GET_SIZE(HDPT(NEXT_BLKP(bp))); // 다음 블록의 크기 추가
        PUTTER(HDPT(bp), PACK(size, 0));   // 헤더와 풋터 업데이트
        PUTTER(FTPT(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {   // 이전 블록이 프리
        rmFreeBlock(PREV_BLKP(bp)); // 프리 블록 리스트에서 이전 블록 제거

        size += GET_SIZE(HDPT(PREV_BLKP(bp))); // 이전 블록의 크기 추가

        PUTTER(FTPT(bp), PACK(size, 0)); // 현재 블록 풋터 업데이트
        PUTTER(HDPT(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 업데이트

        bp = PREV_BLKP(bp); // 블록 포인터를 이전 블록으로 이동
    }
    else if (!prev_alloc && !next_alloc) { // 이전 블록과 다음 블록 모두 프리
        rmFreeBlock(PREV_BLKP(bp)); // 프리 블록 리스트에서 이전 블록 제거
        rmFreeBlock(NEXT_BLKP(bp)); // 프리 블록 리스트에서 다음 블록 제거

        size += GET_SIZE(HDPT(PREV_BLKP(bp))) + GET_SIZE(FTPT(NEXT_BLKP(bp))); // 이전 블록과 다음 블록의 크기 추가

        PUTTER(HDPT(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 업데이트
        PUTTER(FTPT(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 풋터 업데이트

        bp = PREV_BLKP(bp); // 블록 포인터를 이전 블록으로 이동
    }
    putFreeBlock(bp); // 병합된 블록을 프리 리스트에 추가

    return bp; // 병합된 블록의 포인터 반환
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
    if ((bp = worst_fit(a_size)) != NULL) {
        place(bp, a_size);
        return bp;  // 프리 블록 적절한 것 발견했다면 return 후 종료
    }
    // 적절한 프리블록을 못 찾았다면
    extend_size = MAX(a_size, CHUNKSIZE);  // 요청 크기와 기본 크기 중 큰 값으로 확장
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL) { // 정해진 크기로 힙 확장 
        return NULL; // 실패하면 -1 NULL
    }
    place(bp, a_size);  // bp 에는 함수를 통해 프리 블록 할당
    return bp;  // 성공하면 블록 시작 주소 리턴
}

// first_fit
static void* first_fit(size_t a_size) {
    void* bp;  // 블록 리스트를 순회할 포인터

    // End when the only allocated block in the free list (end of list) is found
    for (bp = free_list; IS_ALLOCATED(HDPT(bp)) != 1; bp = SUCC_FREEPT(bp)) {
        // 프리 블록 리스트 시작부터 리스트 끝까지 (할당된 블록이 리스트의 끝)
        if (GET_SIZE(HDPT(bp)) >= a_size) {
            // 현재 블록 사이즈가 요청 사이즈보다 크거나 같은 경우 !
            return bp;
        }
    }

    // fit한 블록 못 찾았다면
    return NULL;
}

// place
static void place(void* bp, size_t a_size) { // 블록 포인터와 할당할 크기
    size_t c_size = GET_SIZE(HDPT(bp)); // 현재 블록 크기

    rmFreeBlock(bp); // 할당된 블록이므로 자유 블록 리스트에서 제거

    if ((c_size - a_size) >= (2 * DSIZE)) { // 블록을 분할할 충분한 공간이 있는 경우
        PUTTER(HDPT(bp), PACK(a_size, 1)); // 헤더에 할당 정보와 크기 기록
        PUTTER(FTPT(bp), PACK(a_size, 1)); // 풋터에 할당 정보와 크기 기록

        bp = NEXT_BLKP(bp); // 다음 블록으로 포인터 이동

        PUTTER(HDPT(bp), PACK(c_size - a_size, 0)); // 남은 공간을 자유 블록으로 만듦
        PUTTER(FTPT(bp), PACK(c_size - a_size, 0)); // 풋터에도 기록

        putFreeBlock(bp); // 분할된 자유 블록을 자유 블록 리스트에 추가
    }
    else { // 블록을 분할할 충분한 공간이 없는 경우
        PUTTER(HDPT(bp), PACK(c_size, 1)); // 헤더에 할당 정보와 크기 기록
        PUTTER(FTPT(bp), PACK(c_size, 1)); // 풋터에 할당 정보와 크기 기록
    }
}

// putFreeBlock
void putFreeBlock(void* bp) { // 프리 블록을 프리 블록 리스트에 추가
    SUCC_FREEPT(bp) = free_list; // 프리 블록 리스트의 시작 블록을 다음 블록으로 설정
    PRED_FREEPT(bp) = NULL; // 이전 블록 포인터 NULL로
    if (free_list != NULL) { // 프리 블록 리스트가 비어있지 않으면
        PRED_FREEPT(free_list) = bp; // 원래의 프리 블록 리스트의 시작 블록의 이전 블록 포인터를 현재 블록으로 설정
    }
    free_list = bp; // 프리 블록 리스트의 시작 포인터를 현재 블록으로 설정
}

// rmFreeBlock
void rmFreeBlock(void* bp) { // 프리 블록 리스트에서 주어진 블록 제거
    if (bp == free_list) { // 주어진 블록이 프리 블록 리스트의 첫 번째 블록인 경우
        free_list = SUCC_FREEPT(bp); // 프리 블록 리스트의 시작 포인터를 다음 블록으로 설정
        if (free_list != NULL) { // 프리 블록 리스트가 비어있지 않으면
            PRED_FREEPT(free_list) = NULL; // 다음 블록의 이전 블록 포인터를 NULL로 설정
        }
    }
    else { // 주어진 블록이 리스트의 중간에 있는 경우
        SUCC_FREEPT(PRED_FREEPT(bp)) = SUCC_FREEPT(bp); // 이전 블록의 다음 블록 포인터를 현재 블록의 다음 블록으로 설정
        if (SUCC_FREEPT(bp) != NULL) { // 다음 블록이 NULL이 아니면
            PRED_FREEPT(SUCC_FREEPT(bp)) = PRED_FREEPT(bp); // 다음 블록의 이전 블록 포인터를 현재 블록의 이전 블록으로 설정
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
