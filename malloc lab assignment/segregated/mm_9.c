// Segregated List - best fit

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
static void* segregation_list[LISTLIMIT];

static int mm_init(void);
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
void* mm_malloc(size_t size);
static void* best_fit(size_t a_size);
static void place(void* bp, size_t a_size);
void mm_free(void* bp);
void* mm_realloc(void* bp, size_t size);


static void remove_block(void* bp);
static void insert_block(void* bp, size_t size);

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

// extend_heap
static void* extend_heap(size_t words) {
    char* bp; // 새로운 블록의 포인터
    size_t size; // 요청된 크기

    // 짝수 개의 단어로 크기 조정
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) // 메모리 할당 실패 시
        return NULL;

    // 프리 블록 헤더/풋터와 새로운 에필로그 헤더 초기화
    PUTTER(HDPT(bp), PACK(size, 0)); // 프리 블록 헤더
    PUTTER(FTPT(bp), PACK(size, 0)); // 프리 블록 풋터
    PUTTER(HDPT(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 에필로그 헤더

    // 이전 블록이 프리 상태라면 통합
    return coalesce(bp); // 블록 통합 후 반환
}

// coalesce
static void* coalesce(void* bp) {
    size_t prev_alloc = IS_ALLOCATED(FTPT(PREV_BLKP(bp))); // 이전 블록 할당 여부
    size_t next_alloc = IS_ALLOCATED(HDPT(NEXT_BLKP(bp))); // 다음 블록 할당 여부
    size_t size = GET_SIZE(HDPT(bp)); // 현재 블록 크기

    if (prev_alloc && next_alloc) { // 이전과 다음 블록 모두 할당된 경우
        return bp;
    }

    else if (prev_alloc && !next_alloc) { // 다음 블록만 프리 상태인 경우
        size += GET_SIZE(HDPT(NEXT_BLKP(bp))); // 다음 블록 크기 추가
        PUTTER(HDPT(bp), PACK(size, 0)); // 현재 블록 헤더 갱신
        PUTTER(FTPT(bp), PACK(size, 0)); // 현재 블록 풋터 갱신
    }

    else if (!prev_alloc && next_alloc) { // 이전 블록만 프리 상태인 경우
        size += GET_SIZE(HDPT(PREV_BLKP(bp))); // 이전 블록 크기 추가
        PUTTER(FTPT(bp), PACK(size, 0)); // 현재 블록 풋터 갱신
        PUTTER(HDPT(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 갱신
        bp = PREV_BLKP(bp); // 블록 포인터 이전 블록으로 이동
    }

    else { // 이전과 다음 블록 모두 프리 상태인 경우
        size += GET_SIZE(HDPT(PREV_BLKP(bp))) + GET_SIZE(HDPT(NEXT_BLKP(bp))); // 이전과 다음 블록 크기 추가
        PUTTER(HDPT(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 갱신
        PUTTER(FTPT(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 풋터 갱신
        bp = PREV_BLKP(bp); // 블록 포인터 이전 블록으로 이동
    }

    return bp; // 통합된 블록 반환
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

// best_fit
static void* best_fit(size_t a_size) {
    void* bp; // 블록 포인터
    void* best_bp = NULL; // 최적 블록 포인터
    size_t best_size = (size_t)-1; // 최적 크기를 최대 값으로 초기화

    for (int i = 0; i < LISTLIMIT; i++) { // 각 리스트 탐색
        for (bp = segregation_list[i]; bp != NULL; bp = SUCC_FREEPT(bp)) { // 각 블록 탐색
            size_t size = GET_SIZE(HDPT(bp)); // 현재 블록 크기
            if (a_size <= size && size < best_size) { // 요청 크기에 맞고 현재 최적 크기보다 작은 경우
                best_size = size; // 최적 크기 갱신
                best_bp = bp; // 최적 블록 포인터 갱신
            }
        }
    }
    return best_bp; // 최적 블록 포인터 반환
}

// place
static void place(void* bp, size_t a_size) {
    size_t csize = GET_SIZE(HDPT(bp)); // 현재 블록 크기

    if ((csize - a_size) >= (2 * DSIZE)) { // 블록 분할 가능한 경우
        PUTTER(HDPT(bp), PACK(a_size, 1)); // 블록 할당 헤더 설정
        PUTTER(FTPT(bp), PACK(a_size, 1)); // 블록 할당 풋터 설정
        bp = NEXT_BLKP(bp); // 블록 포인터 이동
        PUTTER(HDPT(bp), PACK(csize - a_size, 0)); // 분할된 프리 블록 헤더 설정
        PUTTER(FTPT(bp), PACK(csize - a_size, 0)); // 분할된 프리 블록 풋터 설정
        insert_block(bp, csize - a_size); // 프리 블록 리스트에 추가
    }
    else { // 블록 분할 불가능한 경우
        PUTTER(HDPT(bp), PACK(csize, 1)); // 전체 블록 할당 헤더 설정
        PUTTER(FTPT(bp), PACK(csize, 1)); // 전체 블록 할당 풋터 설정
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

// remove_block
static void remove_block(void* bp) {
    int i = 0; // 리스트 인덱스
    size_t size = GET_SIZE(HDPT(bp)); // 블록 크기

    while ((i < LISTLIMIT - 1) && (size > 1)) { // 적절한 리스트 인덱스 찾기
        size >>= 1;
        i++;
    }

    if (SUCC_FREEPT(bp) != NULL) { // 다음 블록이 존재하는 경우
        PRED_FREEPT(SUCC_FREEPT(bp)) = PRED_FREEPT(bp); // 이전 블록 연결 갱신
    }
    if (PRED_FREEPT(bp) != NULL) { // 이전 블록이 존재하는 경우
        SUCC_FREEPT(PRED_FREEPT(bp)) = SUCC_FREEPT(bp); // 다음 블록 연결 갱신
    }
    else { // 현재 블록이 리스트의 첫 블록인 경우
        segregation_list[i] = SUCC_FREEPT(bp); // 리스트 헤더 갱신
    }
}


// insert_block
static void insert_block(void* bp, size_t size) {
    int i = 0; // 리스트 인덱스
    void* search_bp = NULL; // 검색 블록 포인터
    void* insert_bp = NULL; // 삽입 위치 블록 포인터

    while ((i < LISTLIMIT - 1) && (size > 1)) { // 적절한 리스트 인덱스 찾기
        size >>= 1;
        i++;
    }

    search_bp = segregation_list[i]; // 리스트 헤더로부터 검색 시작
    while ((search_bp != NULL) && (size > GET_SIZE(HDPT(search_bp)))) { // 적절한 위치 찾기
        insert_bp = search_bp;
        search_bp = SUCC_FREEPT(search_bp);
    }

    if (search_bp != NULL) { // 삽입 위치가 리스트 중간인 경우
        if (insert_bp != NULL) { // 삽입 위치가 리스트 중간인 경우
            SUCC_FREEPT(insert_bp) = bp;
            PRED_FREEPT(search_bp) = bp;
            SUCC_FREEPT(bp) = search_bp;
            PRED_FREEPT(bp) = insert_bp;
        }
        else { // 삽입 위치가 리스트의 첫 블록인 경우
            SUCC_FREEPT(bp) = search_bp;
            PRED_FREEPT(search_bp) = bp;
            PRED_FREEPT(bp) = NULL;
            segregation_list[i] = bp;
        }
    }
    else { // 삽입 위치가 리스트의 끝인 경우
        if (insert_bp != NULL) { // 삽입 위치가 리스트 중간인 경우
            SUCC_FREEPT(insert_bp) = bp;
            PRED_FREEPT(bp) = insert_bp;
            SUCC_FREEPT(bp) = NULL;
        }
        else { // 삽입 위치가 리스트의 첫 블록인 경우
            SUCC_FREEPT(bp) = NULL;
            PRED_FREEPT(bp) = NULL;
            segregation_list[i] = bp;
        }
    }
}
