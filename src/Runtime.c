// HVM3-Strict Core: parallel, polarized, LAM/APP & DUP/SUP only

#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define DEBUG_LOG(fmt, ...) fprintf(stderr, "[DEBUG] " fmt "\n", ##__VA_ARGS__)

typedef pthread_t thread_t;

int get_num_threads() {
  long nprocs = sysconf(_SC_NPROCESSORS_ONLN);
  return (nprocs <= 1) ? 1 : 1 << (int)log2(nprocs);
}

int thread_create(pthread_t *thread, const pthread_attr_t *attr,
                  void *(*start_routine)(void *), void *arg) {
  return pthread_create(thread, attr, start_routine, arg);
}

int thread_join(pthread_t thread, void **retval) {
  return pthread_join(thread, retval);
}

// Constants
#define VAR 0x01
#define SUB 0x02
#define NUL 0x03
#define ERA 0x04
#define LAM 0x05
#define APP 0x06
#define SUP 0x07
#define DUP 0x08
#define REF 0x09
#define OPX 0x0A
#define OPY 0x0B
#define U32 0x0C
#define I32 0x0D
#define F32 0x0E
#define MAT 0x0F

// Operators
#define OP_ADD 0x00
#define OP_SUB 0x01
#define OP_MUL 0x02
#define OP_DIV 0x03
#define OP_MOD 0x04
#define OP_EQ  0x05
#define OP_NE  0x06
#define OP_LT  0x07
#define OP_GT  0x08
#define OP_LTE 0x09
#define OP_GTE 0x0A
#define OP_AND 0x0B
#define OP_OR  0x0C
#define OP_XOR 0x0D
#define OP_LSH 0x0E
#define OP_RSH 0x0F

// Types
typedef int32_t i32;
typedef uint32_t u32;
typedef _Atomic(u32) a32;
typedef float f32;
typedef int64_t i64;
typedef uint64_t u64;
typedef _Atomic(u64) a64;
// NOTE alignment is gcc/clang specific
typedef unsigned __int128 u128 __attribute__((aligned(16)));

typedef uint8_t Tag; //  8 bits
typedef u32 Lab;     // 24 bits
typedef u32 Loc;     // 32 bits
typedef u64 Term;    // Loc | Lab | Tag
typedef u128 Pair;   // Term | Term

// Using union for type punning (safer in C)
typedef union {
  u32 u;
  i32 i;
  f32 f;
} TypeConverter;

// Global heap
static u64 *BUFF = NULL;

// Heap configuration options
enum : u64 {
  // 1GiB heap
  HEAP_1GB = (1ULL << 27) * sizeof(u64),  // 128Mi * 8 bytes = 1GiB

  //////////////////////////
  // Choose a heap size here
  //////////////////////////
  HEAP_SIZE = HEAP_1GB * 4,

  // Cache line size
  CACH_SIZ = 64,
  CACH_U64 = CACH_SIZ / sizeof(u64),
  VOID = 0,

  // Threads per CPU
  TPC = 10,

  // Various redex bag sizes within the heap to choose from. The remaining
  // percentage is used for node storage. Named for the % of heap used.
  RBAG_12_PCT = (HEAP_SIZE / 8),
  RBAG_25_PCT = (HEAP_SIZE / 4),
  RBAG_50_PCT = (HEAP_SIZE / 2),
  RBAG_75_PCT = (HEAP_SIZE - (HEAP_SIZE / 4)),
  // TODO: something like: RBAG_1024_DEX, for 1024 redex per thread

  //////////////////////////
  // Choose a RBAG size here
  //////////////////////////
  RBAG_SIZE = RBAG_25_PCT,
};

enum : u32 {
  // Final calculated RBAG index
  RBAG = ((HEAP_SIZE - RBAG_SIZE) / sizeof(u64)) & ~7U, // CACH_U64 - 1

  // Calculate RBAG_LEN and NODE_LEN: number of u64 elements *per thread*
  // RBAG_LEN MUST be 16-byte aligned. 64-byte alignment might be preferable
  RBAG_LEN = (RBAG_SIZE / (TPC * sizeof(u64))) & ~7U, // CACH_U64 - 1
  NODE_LEN = (HEAP_SIZE - RBAG_SIZE) / (TPC * sizeof(u64)),

  // Booty-bag length in u64 elements
  BBAG_LEN = 8
};

typedef struct Net {
  a64 nods;
  a64 itrs;
  a32 idle;
} Net;

// Global book
typedef struct Def {
  char *name;
  Term *nodes;
  u64  nodes_len;
  Term *rbag;
  u64  rbag_len;
} Def;

typedef struct Book {
  Def *defs;
  u32 len;
  u32 cap;
} Book;

// TODO: net_reset()
static Net net = {
  .nods = 0,
  .itrs = 0,
  .idle = 0
};

static Book BOOK = {
  .defs = NULL,
  .len = 0,
  .cap = 0,
};

#define MBUF_SIZ 10

// Local Thread Memory
typedef struct TM {
  u32 tid;  // thread id
  Loc nput; // next node allocation attempt index
  Loc rput; // next rbag push index
  Loc bput; // next (owned) bbag push index
  Loc bpop; // next (stolen) bbag pop index
  u32 btid; // tid from which bbag was stolen
  u32 sgud; // successful steals
  u32 sbad; // failed steals

  // debugging
  u32 mput;
  u32 itid;
  u32 i1_tag;
  u32 i2_tag;

  u64 itrs; // interaction count
  bool buse; // use booty bag
  bool muse; // use mlog
} TM;

//static_assert(sizeof(TM) <= CACH_SIZ, "TM struct getting big");

// Booty bag control word values
enum : u32 {
  EMPTY = 0,
  FULL = 1,
  STOLEN = 2
};

// Booty bag state
typedef struct BB {
  a32 ctrl; // control word
} BB;

static TM *tms[TPC];
static BB *bbs[TPC];
static thread_t threads[TPC];
static uint8_t unprocessed_itrs[255] = { 0 };

static _Thread_local int thread_id = 0;

// Debugging
static char *tag_to_str(Tag tag);
static char *bty_ctrl_str(u32 ctrl);
void dump_term(Loc loc);
void dump_buff(TM *tm);

#define TERMSTR_BUFSIZ 128

static Term pair_pos(Pair pair);
static Term pair_neg(Pair pair);
static const char* term_str(char* buf, Term term);
Tag term_tag(Term term) { return term & 0xFF; }
Loc term_loc(Term term);

#define MEMLOG // comment out to disable
//#define LOCLOG

#if defined(MEMLOG) && defined(LOCLOG)
#error "define MEMLOG -or- LOCLOG not both"
#endif

#ifdef MEMLOG

// Memory operations log
static u64 *MEMBUFF = NULL;
enum : u32 {
  MLOG_SIZ = (1U << 26) * sizeof(u64) * 3,
  MLOG_LEN = MLOG_SIZ / (TPC * sizeof(u64))
};

//static _Thread_local u64 rbag_loc = 0;
#define MLOG(mop, loc, t1, t2)          mlog((u32)thread_id, mop, loc, t1, t2, 0)
#define MLOG_PAIR(mop, loc, pair)       mlog((u32)thread_id, mop, loc, pair_neg(pair), pair_pos(pair), 0)
#define MLOG_LVL(mop, loc, lvl, t1, t2) mlog((u32)thread_id, mop, loc, t1, t2, lvl)
#else
#define MLOG(mop, loc, t1, t2)
#define MLOG_PAIR(mop, loc, pair)
#define MLOG_LVL(mop, loc, lvl, t1, t2)
#endif

// Memory operations
#define MOP_EXCH 0x01
#define MOP_LOAD 0x02
#define MOP_STOR 0x03

static const char* mop_str(u32 mop) {
  switch (mop) {
  case MOP_EXCH: return "EXCH";
  case MOP_LOAD: return "LOAD";
  case MOP_STOR: return "STOR";
  default: return "????";
  }
}

static bool is_log_loc(Loc loc) {
  return (loc == 80) || (loc == 81); //|| (loc == 111)) {
}

static const char* other_term_str(char* buf, Term term) {
  char term_buf[128];
  if (term != 0) {
    sprintf(buf, "other: %s", term_str(term_buf, term));
    return buf;
  }
  return "";
}

static void log_term_loc_other(u32 mop, Term term, Loc loc, Term other) {
  Loc tloc = term_loc(term);
  if (is_log_loc(tloc) || is_log_loc(loc)) {
    TM *tm = tms[thread_id];
    char buf[128];
    char other_buf[128];
    fprintf(stderr, "%d %s%s %s %s %s @ %u %s\n", thread_id,
            tag_to_str(tm->i1_tag), tag_to_str(tm->i2_tag),
            (loc < RBAG) ? "RNOD" : "RBAG",
            mop_str(mop), term_str(buf, term), loc,
            other_term_str(other_buf, other));
  }
}

static void log_term_loc(u32 mop, Term term, Loc loc) {
#ifdef LOC_LOG
  log_term_loc_other(mop, term, loc, 0);
#endif
}

static void log_pair_loc(u32 mop, Pair pair, Loc loc) {
#ifdef LOC_LOG
  Term neg = pair_neg(pair);
  Term pos = pair_pos(pair);
  log_term_loc_other(mop, neg, loc, pos);
  log_term_loc_other(mop, pos, loc+1, neg);
#endif
}

#ifdef MEMLOG
static void mlog_init() {
  if (MEMBUFF == NULL) {
    MEMBUFF = aligned_alloc(CACH_SIZ, MLOG_SIZ);
  }
}

static void mlog_free() {
  if (MEMBUFF != NULL) {
    free(MEMBUFF);
    MEMBUFF = NULL;
  }
}

// i1_tag: 4, i2_tag: 4, lvl: 5, op:2, t1_tag: 4, t2_tag: 4, tid: 4, sid: 4

static u64 mlog_entry(u32 tid, u32 mop, u32 sid, u32 loc, u32 lvl,
                      u32 i1_tag, u32 i2_tag, u32 t1_tag, u32 t2_tag) {
  u64 hi = (i1_tag << 27) | ((i2_tag & 0xF) << 23) |
    ((lvl & 0x1F) << 18) | ((mop & 0x3) << 16) |
    ((t1_tag & 0xF) << 12) | ((t2_tag & 0xF) << 8) |
    ((tid & 0xF) << 4) | (sid & 0xF);
  return hi << 32 | loc;
}

static u32 mlog_hi(u64 e) {
  return e >> 32;
}

static u32 mlog_lo(u64 e) {
  return e & 0xFFFFFFFF;
}

static u32 mlog_i1_tag(u64 e) {
  return (mlog_hi(e) >> 27);
}

static u32 mlog_i2_tag(u64 e) {
  return (mlog_hi(e) >> 23) & 0xF;
}

static u32 mlog_lvl(u64 e) {
  return (mlog_hi(e) >> 18) & 0x1F;
}

static u32 mlog_mop(u64 e) {
  return (mlog_hi(e) >> 16) & 0x3;
}

static u32 mlog_t1_tag(u64 e) {
  return (mlog_hi(e) >> 12) & 0xF;
}

static u32 mlog_t2_tag(u64 e) {
  return (mlog_hi(e) >> 8) & 0xF;
}

static u32 mlog_tid(u64 e) {
  return (mlog_hi(e) >> 4) & 0xF;
}

static u32 mlog_sid(u64 e) {
  return mlog_hi(e) & 0xF;
}

static u32 mlog_loc(u64 e) {
  return mlog_lo(e);
}

static void mlog_dump_term(FILE* fp, u64 cnt, u64 e, u32 tag, Loc loc, u32 loc_offset) {
  fprintf(fp, "%" PRIu64 ",%u,%s%s,%s,%u,%s,%u,%u\n", cnt, mlog_tid(e),
          tag_to_str(mlog_i1_tag(e)), tag_to_str(mlog_i2_tag(e)),
          mop_str(mlog_mop(e)), mlog_lvl(e),
          tag_to_str(tag), loc, mlog_loc(e) + loc_offset);
}

static void mlog_dump(const char* fn) {
  FILE *fp = fopen(fn, "w");
  if (fp == NULL) {
    perror("mlog_dump: Error opening file");
    return;
  }

  u32 ops = 0;
  for (u64 t = 0; t < TPC; t++) {
    TM *tm = tms[t];
    for (u32 i = 0; i < tm->mput; i += 3) {
      u32 pos = t * MLOG_LEN + i;
      u64 cnt =  MEMBUFF[pos]; 
      u64 e =    MEMBUFF[pos+1]; // entry
      u64 locs = MEMBUFF[pos+2]; // locs
      u32 mop = mlog_mop(e);
      if ((mop == MOP_LOAD) || (mop == MOP_STOR)) {
        // T1 
        Loc t1_loc = mlog_hi(locs);
        mlog_dump_term(fp, cnt, e, mlog_t1_tag(e), t1_loc, 0);
        Loc t2_loc = mlog_lo(locs);
        if ((mlog_t2_tag(e) != 0) || (t2_loc != 0)) {
          // T2
          mlog_dump_term(fp, cnt, e, mlog_t2_tag(e), t2_loc, 1);
        }
      } else {
        fprintf(fp, "%" PRIu64 ",%u,%s%s,%s,%u,%s,%u,%s,%u,%u\n", cnt, mlog_tid(e),
                tag_to_str(mlog_i1_tag(e)), tag_to_str(mlog_i2_tag(e)),
                /*mlog_sid(e),*/ mop_str(mlog_mop(e)), mlog_lvl(e),
                tag_to_str(mlog_t1_tag(e)), mlog_hi(locs),
                tag_to_str(mlog_t2_tag(e)), mlog_lo(locs), mlog_loc(e));
      }
    }
  }
  fclose(fp);
}

#ifdef __APPLE__
// Use explicit file-scope assembly to define the function
extern uint64_t read_cntvct(void);
__asm__(
    ".global _read_cntvct\n"
    ".global read_cntvct\n"
    "_read_cntvct:\n"
    "read_cntvct:\n"
    //"   isb\n"
    "   mrs x0, cntvct_el0\n"
    "   ret\n"
);
#endif

static void mlog(u32 tid, u32 mop, Loc loc, Term t1, Term t2, u32 lvl) {
  static bool at_end = false;

  TM *tm = tms[tid];
  if (tm->mput + 3 < MLOG_LEN) {
    u32 pos = tid * MLOG_LEN + tm->mput;

    MEMBUFF[pos] = read_cntvct();
    MEMBUFF[pos+1] = mlog_entry(tid, mop, tm->itid, loc, lvl, tm->i1_tag,
                                tm->i2_tag, term_tag(t1), term_tag(t2));

#if 1
    MEMBUFF[pos+2] = (u64)term_loc(t1) << 32 | term_loc(t2);
#endif

    tm->mput += 3;
  } else if (!at_end) {
    fprintf(stderr, "%u end of MLOG reached\n", tid);
    at_end = true;
  }
}

#endif // MEMLOG

void mlog_exit() {
#ifdef MEMLOG
  mlog_dump("memlog.txt");
#endif
  exit(1);
}


// TM/BS operations
void tm_reset(TM *tm) {
  tm->rput = 0;
  tm->nput = 0;
  tm->itrs = 0;

  tm->mput = 0;
}

TM *tm_new(u64 tid) {
  // make size a multiple of alignment
  size_t tm_siz = (sizeof(TM) + CACH_SIZ - 1) & ~(CACH_SIZ - 1);
  TM *tm = aligned_alloc(CACH_SIZ, tm_siz);
  if (tm == NULL) {
    fprintf(stderr, "TM memory allocation failed\n");
    exit(EXIT_FAILURE);
  }
  tm_reset(tm);
  tm->tid = tid;
  tm->bput = 0;
  tm->bpop = 0;
  tm->btid = 0;
  tm->sgud = 0;
  tm->sbad = 0;
  tm->buse = false;

  tm->muse = false;
  return tm;
}

BB *bb_new() {
  size_t bb_siz = (sizeof(BB) + CACH_SIZ - 1) & ~(CACH_SIZ - 1);
  BB *bb = aligned_alloc(CACH_SIZ, bb_siz);
  if (bb == NULL) {
    fprintf(stderr, "BB memory allocation failed\n");
    exit(EXIT_FAILURE);
  }
  bb->ctrl = EMPTY;
  return bb;
}

void alloc_static_data() {
  for (u64 t = 0; t < TPC; ++t) {
    tms[t] = tm_new(t);
    bbs[t] = bb_new();
  }
}

void free_static_data() {
  for (u64 t = 0; t < TPC; ++t) {
    if (tms[t] != NULL) {
      free(tms[t]);
      tms[t] = NULL;
    }
    if (bbs[t] != NULL) {
      free(bbs[t]);
      bbs[t] = NULL;
    }
  }
}

// Pair operations
static Pair pair_new(Term neg, Term pos) {
  return ((Pair)pos << 64) | neg;
}

static Term pair_pos(Pair pair) {
  return (pair >> 64) & 0xFFFFFFFFFFFFFFFF;
}

static Term pair_neg(Pair pair) {
  return pair & 0xFFFFFFFFFFFFFFFF;
}

// Term operations
Term term_new(Tag tag, Lab lab, Loc loc) {
  return ((Term)loc << 32) | ((Term)lab << 8) | tag;
}

Lab term_lab(Term term) { return (term >> 8) & 0xFFFFFF; }

Loc term_loc(Term term) { return (term >> 32) & 0xFFFFFFFF; }

static Term term_with_loc(Term term, Loc loc) {
  return (((Term)loc) << 32) | (term & 0xFFFFFFFF);
}

static bool term_has_loc(Term term) {
  Tag tag = term_tag(term);
  return !(tag == SUB || tag == NUL || tag == ERA || tag == REF || tag == U32);
}

static Term term_offset_loc(Term term, Loc offset) {
  if (!term_has_loc(term)) { return term; }
  Loc loc = term_loc(term) + offset;
  return term_with_loc(term, loc);
}

static Term term_offset_loc2(Term term, Loc offset) {
  Tag tag = term_tag(term);
  if (tag == SUB || tag == NUL || tag == ERA || tag == REF || tag == U32) {
    return term;
  } else {
    Loc loc = term_loc(term) + offset;
    return (((Term)loc) << 32) | (term & 0xFFFFFFFF);
  }
}

//#define DEBUG
static int mop_debug = 0; // memory operations
static int thd_debug = 0; // threading
static int bty_debug = 0; // booty bag

static const char* term_str(char* buf, Term term) {
  sprintf(buf, "%s lab:%u loc:%u", tag_to_str(term_tag(term)),
          (u32)term_lab(term), (u32)term_loc(term));
  return buf;
}

// Memory operations
Term swap_lvl(Loc loc, Term term, u32 lvl) {
  Term got = atomic_exchange_explicit((a64*)&BUFF[loc], term, memory_order_relaxed);
  MLOG_LVL(MOP_EXCH, loc, lvl, got, term);
  log_term_loc(MOP_STOR, term, loc);
  log_term_loc(MOP_LOAD, got, loc);
  return got;
}

Term swap(Loc loc, Term term) {
  return swap_lvl(loc, term, 0);
}

Term get(Loc loc) {
  Term term = atomic_load_explicit((a64*)&BUFF[loc], memory_order_relaxed);
  MLOG(MOP_LOAD, loc, term, 0);
  log_term_loc(MOP_LOAD, term, loc);
  return term;
}

Term take(Loc loc) {
  Term term = atomic_exchange_explicit((a64*)&BUFF[loc], VOID, memory_order_relaxed);
  MLOG(MOP_EXCH, loc, term, 0);
  log_term_loc(MOP_LOAD, term, loc);
  return term;
}

void set(Loc loc, Term term) {
  atomic_store_explicit((a64*)&BUFF[loc], term, memory_order_relaxed);
  MLOG(MOP_STOR, loc, term, 0);
  log_term_loc(MOP_STOR, term, loc);
}

static Pair take_pair(Loc loc, bool bty) {
  Pair pair = *(Pair*)&BUFF[loc];
  
  // Debugging
#if defined(MEMLOG) || defined(LOCLOG)
  Term neg = pair_neg(pair);
  Term pos = pair_pos(pair);

  TM *tm = tms[thread_id];
  tm->i1_tag = term_tag(neg);
  tm->i2_tag = term_tag(pos);
  tm->itid = bty ? tm->btid : tm->tid;

  MLOG(MOP_LOAD, loc, neg, pos);

#ifdef LOCLOC
  log_pair_loc(MOP_LOAD, pair, loc);
#endif
#endif

//#define VOID_TEST
#ifdef VOID_TEST
  *(Pair*)&BUFF[loc] = (Pair)VOID;
  if (pair == 0) {
    fprintf(stderr, "%d VOID term taken\n", thread_id);
    exit(1);
  }
#endif
  
  return pair;
}

static void atomic_set_pair(Loc loc, Pair pair) {
  __atomic_store_n((Pair*)&BUFF[loc], pair, __ATOMIC_RELAXED);
  MLOG_PAIR(MOP_STOR, loc, pair);
}

static void set_pair(Loc loc, Pair pair) {
  *((Pair*)&BUFF[loc]) = pair;
  MLOG_PAIR(MOP_STOR, loc, pair);
}

static Loc port(u64 n, Loc loc) { return n + loc - 1; }

// Allocator
// ---------

static Loc node_alloc(TM *tm, u32 num) {
  if ((num & 1) == 1) {
    num += 1;
  }

  if (tm->nput + num >= NODE_LEN) {
    fprintf(stderr, "node space exhausted\n");
    exit(1);
  }

  Loc loc = tm->tid * NODE_LEN + tm->nput;
  tm->nput += num;
  return loc;
}

static bool bty_time(TM* tm) {
  return (tm->bpop == 0) && tm->buse;
}
 
static bool bbag_compare_swap(u32 tid, u32 expect, u32 desire,
                              memory_order success_order) {
  u32 orig = expect;
  bool res = atomic_compare_exchange_strong_explicit(&bbs[tid]->ctrl, &expect,
                 desire, success_order, memory_order_relaxed);
  return res;
}

static void bbag_set(u32 tid, u32 val, memory_order order) {
  atomic_store_explicit(&bbs[tid]->ctrl, val, order);
}

static u32 bbag_get(u32 tid) {
  u32 got = atomic_load_explicit(&bbs[tid]->ctrl, memory_order_relaxed);
  return got;
}

static Loc get_push_offset(TM *tm) {
  if (bty_time(tm)) {
    // Consider pushing to booty bag
    if (tm->bput >= BBAG_LEN) {
      // BBAG is full, last we checked. But maybe it's empty now
      if (bbag_get(tm->tid) == EMPTY) {
        tm->bput = 0;
        return tm->bput;
      }        
    } else {
      // BBAG isn't full, use it
      return tm->bput;
    }
  }
  // Push to RBAG
  return BBAG_LEN + tm->rput;
}

//static void redex_push(TM *tm, Pair pair) {
static Loc rbag_push(TM *tm, Term neg, Term pos) {
  Loc off = get_push_offset(tm);
  bool bty = off < BBAG_LEN;
  Loc loc = RBAG + tm->tid * RBAG_LEN + off;

  Pair pair = pair_new(neg, pos);
  set_pair(loc, pair);

  log_pair_loc(MOP_STOR, pair, loc);

  if (bty) {
    tm->bput += 2;
    if (tm->bput == BBAG_LEN) {
      bbag_set(tm->tid, FULL, memory_order_release);
    }
  } else {
    //#ifdef DEBUG
    bool free_global = tm->rput < RBAG_LEN - BBAG_LEN - 1;
    if (!free_global) {
      fprintf(stderr, "rbag space exhausted\n");
      exit(1);
    }
    //#endif

    tm->rput += 2;
  }
  return loc;
}

static Pair rbag_pop(TM* tm) {
  if (tm->bpop > 0) {
    // We stole a booty bag, use it
    tm->bpop -= 2;

    // If stealing from own booty bag, adjust push index as well
    if (tm->btid == tm->tid) {
      tm->bput -= 2;
    }

    return RBAG + tm->btid * RBAG_LEN + tm->bpop;
  } else if (tm->rput > 0) {
    // RBAG isn't empty, use it
    tm->rput -= 2;
    return RBAG + tm->tid * RBAG_LEN + BBAG_LEN + tm->rput;
  } else {
    return 0;
  }
}

// FFI functions
void hvm_init() {
  if (BUFF == NULL) {
    BUFF = aligned_alloc(CACH_SIZ, HEAP_SIZE);
    if (BUFF == NULL) {
      fprintf(stderr, "Heap memory allocation failed\n");
      exit(EXIT_FAILURE);
    }
  }
  memset(BUFF, 0, HEAP_SIZE);

  alloc_static_data();

#ifdef MEMLOG
  mlog_init();
#endif

  #if 0 
  fprintf(stderr, "HEAP_SIZE = %" PRIu64 "\n", HEAP_SIZE);
  fprintf(stderr, "RBAG_SIZE = %" PRIu64 "\n", RBAG_SIZE);
  fprintf(stderr, "RBAG      = %u\n", RBAG);
  fprintf(stderr, "RBAG_LEN  = %u\n", RBAG_LEN);
  fprintf(stderr, "NODE_LEN  = %u\n", NODE_LEN);
  #endif
}

void hvm_free() {
  if (BUFF != NULL) {
    free(BUFF);
    BUFF = NULL;
  }
  free_static_data();

#ifdef MEMLOG
  mlog_free();
#endif

}

Loc ffi_alloc_node(u64 arity) {
  TM *tm = tms[0];
#if 1
  Loc loc = tm->nput;
  //if ((arity & 1) == 1) {
  //  arity += 1;
  //}
  tm->nput += arity;
  return loc;
#else
  return node_alloc(tm, arity);
#endif
}

void ffi_rbag_push(Term neg, Term pos) {
  rbag_push(tms[0], neg, pos);
}

u64 inc_itr() {
  return atomic_load(&net.itrs);
} 

Loc rbag_ini() {
  // TODO
  return RBAG;
}

Loc rbag_end() {
  // TODO
  return RBAG;
}

Loc rnod_end() {
  return net.nods;
}

// Moves the global buffer and redex bag into a new def and resets
// the global buffer and redex bag.
void def_new(char *name) {
  if (BOOK.len == BOOK.cap) {
    if (BOOK.cap == 0) {
      BOOK.cap = 32;
    } else {
      BOOK.cap *= 2;
    }

    BOOK.defs = realloc(BOOK.defs, sizeof(Def) * BOOK.cap);
  }

  TM *tm = tms[0];

  Loc rbag_end = tm->rput;
  Loc rnod_end = tm->nput;
  size_t rbag_siz = ((sizeof(Term) * rbag_end) + CACH_SIZ - 1) & ~(CACH_SIZ - 1);
  size_t rnod_siz = ((sizeof(Term) * rnod_end) + CACH_SIZ - 1) & ~(CACH_SIZ - 1);

  Def def = {
      .name = name,
      .nodes = aligned_alloc(CACH_SIZ, rnod_siz),
      .nodes_len = rnod_end,
      .rbag = aligned_alloc(CACH_SIZ, rbag_siz),
      .rbag_len = rbag_end,
  };

  if (def.nodes == NULL || def.rbag == NULL) {
    fprintf(stderr, "DEF memory allocation failed\n");
  }

  u64 *rbag = BUFF + RBAG + BBAG_LEN;

  memcpy(def.nodes, BUFF, sizeof(Term) * def.nodes_len);
  memcpy(def.rbag, rbag, sizeof(Term) * def.rbag_len);

  // printf("NEW DEF '%s':\n", def.name);
  // dump_buff();
  // printf("\n");

  memset(BUFF, 0, sizeof(Term) * def.nodes_len);
  memset(rbag, 0, sizeof(Term) * def.rbag_len);

  tm_reset(tm);

  BOOK.defs[BOOK.len] = def;
  BOOK.len++;
}

char *def_name(Loc def_idx) { return BOOK.defs[def_idx].name; }

// Expands a ref's data into a linear block of nodes with its nodes' locs
// offset by the index where in the BUFF it was expanded.
//
// Returns the ref's root, the first node in its data.
static Term expand_ref(TM *tm, Loc def_idx) {
  // Get definition data
  const Def* def = &BOOK.defs[def_idx];
  const u32 nodes_len = def->nodes_len;
  const Term *nodes = def->nodes;
  const Term *rbag = def->rbag;
  const u32 rbag_len = def->rbag_len;

  // offset calculation must occur before node_alloc() call
  Loc offset = (tm->tid * NODE_LEN) + tm->nput - 1;
  node_alloc(tm, nodes_len - 1);

  Term root = term_offset_loc(nodes[0], offset);

  u32 n = 1;
  for (; n + 1 < nodes_len; n += 2) {
    // 128-bit load & store
    Pair orig = *(Pair*)&nodes[n];
    Term neg = term_offset_loc(pair_neg(orig), offset);
    Term pos = term_offset_loc(pair_pos(orig), offset);
    Loc loc = offset + n;
    // What if we add these without atomics, then release on first
    // rbag_push, and acquire on take_pair?
    //*(Pair*)&BUFF[loc] = pair_new(neg, pos);
    atomic_set_pair(loc, pair_new(neg, pos));
    MLOG_LVL(MOP_STOR, loc, def_idx, neg, pos);
    log_term_loc(MOP_STOR, neg, loc);
    log_term_loc(MOP_STOR, pos, loc+1);
  }
  if (n < nodes_len) {
    Term term = term_offset_loc(nodes[n], offset);
    BUFF[offset + n] = term;
    MLOG_LVL(MOP_STOR, offset+n, def_idx, term, 0);
  }

  for (u32 i = 0; i < rbag_len; i += 2) {
    // 128-bit load
    Pair pair = *(Pair*)&rbag[i];
    Loc loc = rbag_push(tm, term_offset_loc(pair_neg(pair), offset),
                        term_offset_loc(pair_pos(pair), offset));
  }

  return root;
}

static void boot(Loc def_idx) {
  TM *tm = tms[0];
  if (tm->nput > 0 || tm->rput > 0) {
    fprintf(stderr, "booting on non-empty state\n");
    exit(1);
  }
  node_alloc(tm, 1);
  set(0, expand_ref(tm, def_idx));
}

// Atomic Linker
static inline void move(TM *tm, Loc neg_loc, Term pos);
static inline void move_lvl(TM *tm, Loc neg_loc, Term pos, u32 lvl, Term exp_neg);

static inline void link_lvl(TM *tm, Term neg, Term pos, u32 lvl) {
  if (term_tag(pos) == VAR) {
    Loc loc = term_loc(pos);
    Term far = swap_lvl(loc, neg, lvl);
    if (term_tag(far) != SUB) {
      move_lvl(tm, term_loc(pos), far, lvl + 1, neg);
    }
  } else {
    rbag_push(tm, neg, pos);
  }
}

static inline void move_lvl(TM *tm, Loc neg_loc, Term pos, u32 lvl, Term exp_neg) {
  Term neg = swap_lvl(neg_loc, pos, lvl);
#if 0
  if ((lvl > 0) && (exp_neg != neg)) {
    fprintf(stderr, "OOF\n");
  }
#endif
  if (term_tag(neg) != SUB) {
    // No need to take() since we already swapped
    link_lvl(tm, neg, pos, lvl + 1);
  }
}

static inline void link_terms(TM *tm, Term neg, Term pos) {
  link_lvl(tm, neg, pos, 0);
}

static inline void move(TM *tm, Loc neg_loc, Term pos) {
  move_lvl(tm, neg_loc, pos, 0, 0);
}

// Interactions
static void interact_applam(TM *tm, Loc a_loc, Loc b_loc) {
  Term arg = take(port(1, a_loc));
  Loc ret = port(2, a_loc);
  Loc var = port(1, b_loc);
  Term bod = take(port(2, b_loc));

  // Magic to make race condition appear more frequently
  bool buse = tm->buse;
  tm->buse = false;

  move(tm, var, arg);
  move(tm, ret, bod);

  tm->buse = buse;
}

static void interact_appsup(TM *tm, Loc a_loc, Loc b_loc) {
  Loc nloc = node_alloc(tm, 8);
  Term arg = take(port(1, a_loc));
  Loc ret = port(2, a_loc);
  Term tm1 = take(port(1, b_loc));
  Term tm2 = take(port(2, b_loc));
  Loc dp1 = nloc;
  Loc dp2 = nloc + 2;
  Loc cn1 = nloc + 4;
  Loc cn2 = nloc + 6;
  set(port(1, dp1), term_new(SUB, 0, 0));
  set(port(2, dp1), term_new(SUB, 0, 0));
  set(port(1, dp2), term_new(VAR, 0, port(2, cn1)));
  set(port(2, dp2), term_new(VAR, 0, port(2, cn2)));
  set(port(1, cn1), term_new(VAR, 0, port(1, dp1)));
  set(port(2, cn1), term_new(SUB, 0, 0));
  set(port(1, cn2), term_new(VAR, 0, port(2, dp1)));
  set(port(2, cn2), term_new(SUB, 0, 0));
  link_terms(tm, term_new(DUP, 0, dp1), arg);
  move(tm, ret, term_new(SUP, 0, dp2));
  link_terms(tm, term_new(APP, 0, cn1), tm1);
  link_terms(tm, term_new(APP, 0, cn2), tm2);
}

static void interact_appnul(TM *tm, Loc a_loc) {
  Term arg = take(port(1, a_loc));
  Loc ret = port(2, a_loc);
  link_terms(tm, term_new(ERA, 0, 0), arg);
  move(tm, ret, term_new(NUL, 0, 0));
}

static void interact_appu32(TM *tm, Loc a_loc, u32 num) {
  Term arg = take(port(1, a_loc));
  Loc ret = port(2, a_loc);
  link_terms(tm, term_new(U32, 0, num), arg);
  move(tm, ret, term_new(U32, 0, num));
}

static void interact_opxnul(TM *tm, Loc a_loc) {
  Term arg = take(port(1, a_loc));
  Loc ret = port(2, a_loc);
  link_terms(tm, term_new(ERA, 0, 0), arg);
  move(tm, ret, term_new(NUL, 0, 0));
}

static void interact_opxnum(TM *tm, Loc loc, Lab op, u32 num, Tag num_type) {
  Term arg = swap(port(1, loc), term_new(num_type, 0, num));
  link_terms(tm, term_new(OPY, op, loc), arg);
}

static void interact_opxsup(TM *tm, Loc a_loc, Lab op, Loc b_loc) {
  Loc nloc = node_alloc(tm, 8);
  Term arg = take(port(1, a_loc));
  Loc ret = port(2, a_loc);
  Term tm1 = take(port(1, b_loc));
  Term tm2 = take(port(2, b_loc));
  Loc dp1 = nloc;
  Loc dp2 = nloc + 2;
  Loc cn1 = nloc + 4;
  Loc cn2 = nloc + 6;
  set(port(1, dp1), term_new(SUB, 0, 0));
  set(port(2, dp1), term_new(SUB, 0, 0));
  set(port(1, dp2), term_new(VAR, 0, port(2, cn1)));
  set(port(2, dp2), term_new(VAR, 0, port(2, cn2)));
  set(port(1, cn1), term_new(VAR, 0, port(1, dp1)));
  set(port(2, cn1), term_new(SUB, 0, 0));
  set(port(1, cn2), term_new(VAR, 0, port(2, dp1)));
  set(port(2, cn2), term_new(SUB, 0, 0));
  link_terms(tm, term_new(DUP, 0, dp1), arg);
  move(tm, ret, term_new(SUP, 0, dp2));
  link_terms(tm, term_new(OPX, op, cn1), tm1);
  link_terms(tm, term_new(OPX, op, cn2), tm2);
}

static void interact_opynul(TM *tm, Loc a_loc) {
  Term arg = take(port(1, a_loc));
  Loc ret = port(2, a_loc);
  link_terms(tm, term_new(ERA, 0, 0), arg);
  move(tm, ret, term_new(NUL, 0, 0));
}

// Safer Utilities
u32 u32_to_u32(u32 u) { return u; }

i32 u32_to_i32(u32 u) {
  TypeConverter converter;
  converter.u = u;
  return converter.i;
}

f32 u32_to_f32(u32 u) {
  TypeConverter converter;
  converter.u = u;
  return converter.f;
}

u32 i32_to_u32(i32 i) {
  TypeConverter converter;
  converter.i = i;
  return converter.u;
}

u32 f32_to_u32(f32 f) {
  TypeConverter converter;
  converter.f = f;
  return converter.u;
}

static void interact_opynum(TM *tm, Loc a_loc, Lab op, u32 y, Tag y_type) {
  u32 x = term_loc(take(port(1, a_loc)));
  Loc ret = port(2, a_loc);
  u32 res = 0;

  // Optimized path using jump table & direct compute
  if (y_type == U32) {
    // Faster operation dispatch
    static void *op_jumptable[] = {
        [OP_ADD] = &&do_add, [OP_SUB] = &&do_sub, [OP_MUL] = &&do_mul,
        [OP_DIV] = &&do_div, [OP_EQ] = &&do_eq,   [OP_NE] = &&do_ne,
        [OP_LT] = &&do_lt,   [OP_GT] = &&do_gt,   [OP_LTE] = &&do_lte,
        [OP_GTE] = &&do_gte, [OP_MOD] = &&do_mod, [OP_AND] = &&do_and,
        [OP_OR] = &&do_or,   [OP_XOR] = &&do_xor, [OP_LSH] = &&do_lsh,
        [OP_RSH] = &&do_rsh};

    // Faster branching
    goto *op_jumptable[op];

  do_add:
    res = x + y;
    goto done;
  do_sub:
    res = x - y;
    goto done;
  do_mul:
    res = x * y;
    goto done;
  do_div:
    res = x / y;
    goto done;
  do_eq:
    res = x == y;
    goto done;
  do_ne:
    res = x != y;
    goto done;
  do_lt:
    res = x < y;
    goto done;
  do_gt:
    res = x > y;
    goto done;
  do_lte:
    res = x <= y;
    goto done;
  do_gte:
    res = x >= y;
    goto done;
  do_mod:
    res = x % y;
    goto done;
  do_and:
    res = x & y;
    goto done;
  do_or:
    res = x | y;
    goto done;
  do_xor:
    res = x ^ y;
    goto done;
  do_lsh:
    res = x << y;
    goto done;
  do_rsh:
    res = x >> y;
    goto done;

  done:;
  } else {
    // Inlined type conversion and operation for i32 and f32
    switch (y_type) {
    case I32: {
      i32 a = u32_to_i32(x);
      i32 b = u32_to_i32(y);
      i32 val;
      switch (op) {
      case OP_ADD:
        val = a + b;
        break;
      case OP_SUB:
        val = a - b;
        break;
      case OP_MUL:
        val = a * b;
        break;
      case OP_DIV:
        val = a / b;
        break;
      case OP_EQ:
        val = a == b;
        break;
      case OP_NE:
        val = a != b;
        break;
      case OP_LT:
        val = a < b;
        break;
      case OP_GT:
        val = a > b;
        break;
      case OP_LTE:
        val = a <= b;
        break;
      case OP_GTE:
        val = a >= b;
        break;
      case OP_MOD:
        val = a % b;
        break;
      case OP_AND:
        val = a & b;
        break;
      case OP_OR:
        val = a | b;
        break;
      case OP_XOR:
        val = a ^ b;
        break;
      case OP_LSH:
        val = a << b;
        break;
      case OP_RSH:
        val = a >> b;
        break;
      default:
        val = 0;
      }
      res = i32_to_u32(val);
      break;
    }
    case F32: {
      f32 a = u32_to_f32(x);
      f32 b = u32_to_f32(y);
      f32 val;
      switch (op) {
      case OP_ADD:
        val = a + b;
        break;
      case OP_SUB:
        val = a - b;
        break;
      case OP_MUL:
        val = a * b;
        break;
      case OP_DIV:
        val = a / b;
        break;
      case OP_EQ:
        val = a == b;
        break;
      case OP_NE:
        val = a != b;
        break;
      case OP_LT:
        val = a < b;
        break;
      case OP_GT:
        val = a > b;
        break;
      case OP_LTE:
        val = a <= b;
        break;
      case OP_GTE:
        val = a >= b;
        break;
      default:
        val = 0;
      }
      res = f32_to_u32(val);
      break;
    }
    }
  }
  move(tm, ret, term_new(y_type, 0, res));
}

static void interact_opysup(TM *tm, Loc a_loc, Loc b_loc) {
  Loc nloc = node_alloc(tm, 8);
  Term arg = take(port(1, a_loc));
  Loc ret = port(2, a_loc);
  Term tm1 = take(port(1, b_loc));
  Term tm2 = take(port(2, b_loc));
  Loc dp1 = nloc;
  Loc dp2 = nloc + 2;
  Loc cn1 = nloc + 4;
  Loc cn2 = nloc + 6;
  set(port(1, dp1), term_new(SUB, 0, 0));
  set(port(2, dp1), term_new(SUB, 0, 0));
  set(port(1, dp2), term_new(VAR, 0, port(2, cn1)));
  set(port(2, dp2), term_new(VAR, 0, port(2, cn2)));
  set(port(1, cn1), term_new(VAR, 0, port(1, dp1)));
  set(port(2, cn1), term_new(SUB, 0, 0));
  set(port(1, cn2), term_new(VAR, 0, port(2, dp1)));
  set(port(2, cn2), term_new(SUB, 0, 0));
  link_terms(tm, term_new(DUP, 0, dp1), arg);
  move(tm, ret, term_new(SUP, 0, dp2));
  link_terms(tm, term_new(OPY, 0, cn1), tm1);
  link_terms(tm, term_new(OPY, 0, cn2), tm2);
}

static void interact_dupsup(TM *tm, Loc a_loc, Loc b_loc) {
  Loc dp1 = port(1, a_loc);
  Loc dp2 = port(2, a_loc);
  Term tm1 = take(port(1, b_loc));
  Term tm2 = take(port(2, b_loc));
  move(tm, dp1, tm1);
  move(tm, dp2, tm2);
}

static void interact_duplam(TM *tm, Loc a_loc, Loc b_loc) {
  Loc nloc = node_alloc(tm, 8);
  Loc dp1 = port(1, a_loc);
  Loc dp2 = port(2, a_loc);
  Loc var = port(1, b_loc);
  // TODO(enricozb): why is this the only take?
  Term bod = take(port(2, b_loc));
  Loc co1 = nloc;
  Loc co2 = nloc + 2;
  Loc du1 = nloc + 4;
  Loc du2 = nloc + 6;
  set(port(1, co1), term_new(SUB, 0, 0));
  set(port(2, co1), term_new(VAR, 0, port(1, du2)));
  set(port(1, co2), term_new(SUB, 0, 0));
  set(port(2, co2), term_new(VAR, 0, port(2, du2)));
  set(port(1, du1), term_new(VAR, 0, port(1, co1)));
  set(port(2, du1), term_new(VAR, 0, port(1, co2)));
  set(port(1, du2), term_new(SUB, 0, 0));
  set(port(2, du2), term_new(SUB, 0, 0));
  move(tm, dp1, term_new(LAM, 0, co1));
  move(tm, dp2, term_new(LAM, 0, co2));
  move(tm, var, term_new(SUP, 0, du1));
  link_terms(tm, term_new(DUP, 0, du2), bod);
}

static void interact_dupnul(TM *tm, Loc a_loc) {
  Loc dp1 = port(1, a_loc);
  Loc dp2 = port(2, a_loc);
  move(tm, dp1, term_new(NUL, 0, a_loc));
  move(tm, dp2, term_new(NUL, 0, a_loc));
}

static void interact_dupnum(TM *tm, Loc a_loc, u32 n, Tag n_type) {
  Loc dp1 = port(1, a_loc);
  Loc dp2 = port(2, a_loc);
  move(tm, dp1, term_new(n_type, 0, n));
  move(tm, dp2, term_new(n_type, 0, n));
}

static void interact_dupref(TM *tm, Loc a_loc, Loc b_loc) {
  move(tm, port(1, a_loc), term_new(REF, 0, b_loc));
  move(tm, port(2, a_loc), term_new(REF, 0, b_loc));
}

static void interact_matnul(TM *tm, Loc a_loc, Lab mat_len) {
  fprintf(stderr, "interact_matnul not supported (yet)\n");
  exit(1);
  move(tm, port(1, a_loc), term_new(NUL, 0, 0));
  for (u32 i = 0; i < mat_len; i++) {
    link_terms(tm, term_new(ERA, 0, 0), take(port(i + 2, a_loc)));
  }
}

static void interact_matnum(TM *tm, Loc mat_loc, Lab mat_len, u32 n, Tag n_type) {
  if (n_type != U32) {
    fprintf(stderr, "match with non-U32\n");
    exit(1);
  }

  u32 i_arm = (n < mat_len - 1) ? n : (mat_len - 1);
  for (u32 i = 0; i < mat_len; i++) {
    if (i != i_arm) {
      link_terms(tm, term_new(ERA, 0, 0), take(port(2 + i, mat_loc)));
    }
  }

  Loc ret = port(1, mat_loc);
  Term arm = take(port(2 + i_arm, mat_loc));

  if (i_arm < mat_len - 1) {
    move(tm, ret, arm);
  } else {
    Loc app = node_alloc(tm, 2);
    set(app + 0, term_new(U32, 0, n - (mat_len - 1)));
    set(app + 1, term_new(SUB, 0, 0));
    move(tm, ret, term_new(VAR, 0, port(2, app)));

    link_terms(tm, term_new(APP, 0, app), arm);
  }
}

static void interact_matsup(TM *tm, Loc mat_loc, Lab mat_len, Loc sup_loc) {
  fprintf(stderr, "interact_matsup not supported (yet)\n");
  exit(1);
  // TODO: convert to get_resources()

  /*
  // TODO: recoverable
  if (!get_resources(tm, 0, 2 + mat_len * 3)) {
    fprintf(stderr, "i_appsup: Thread %u node space exhausted\n", tm->tid);
    exit(1);
  }
  Loc ma0 = alloc_node(1 + mat_len);
  Loc ma1 = alloc_node(1 + mat_len);

  Loc sup = alloc_node(2);

  set(port(1, sup), term_new(VAR, 0, port(1, ma1)));
  set(port(2, sup), term_new(VAR, 0, port(1, ma0)));
  set(port(1, ma0), term_new(SUB, 0, 0));
  set(port(1, ma1), term_new(SUB, 0, 0));

  for (u64 i = 0; i < mat_len; i++) {
    Loc dui = alloc_node(2);
    set(port(1, dui), term_new(SUB, 0, 0));
    set(port(2, dui), term_new(SUB, 0, 0));
    // TODO: problematic port() usage with recycled nodes
    set(port(2 + i, ma0), term_new(VAR, 0, port(2, dui)));
    set(port(2 + i, ma1), term_new(VAR, 0, port(1, dui)));

    link_terms(tm, term_new(DUP, 0, dui), take(port(2 + i, mat_loc)));
  }

  move(tm, port(1, mat_loc), term_new(SUP, 0, sup));
  link_terms(tm, term_new(MAT, mat_len, ma0), take(port(2, sup_loc)));
  link_terms(tm, term_new(MAT, mat_len, ma1), take(port(1, sup_loc)));
  */
}

static void interact_eralam(TM *tm, Loc b_loc) {
  Loc var = port(1, b_loc);
  Term bod = take(port(2, b_loc));
  move(tm, var, term_new(NUL, 0, 0));
  link_terms(tm, term_new(ERA, 0, 0), bod);
}

static void interact_erasup(TM *tm, Loc b_loc) {
  Term tm1 = take(port(1, b_loc));
  Term tm2 = take(port(2, b_loc));
  link_terms(tm, term_new(ERA, 0, 0), tm1);
  link_terms(tm, term_new(ERA, 0, 0), tm2);
}

static char *tag_to_str(Tag tag);

static void interact(TM *tm, Term neg, Term pos) {
  Tag neg_tag = term_tag(neg);
  Tag pos_tag = term_tag(pos);
  Loc neg_loc = term_loc(neg);
  Loc pos_loc = term_loc(pos);

  bool processed = true;

  switch (neg_tag) {
  case APP:
    switch (pos_tag) {
    case LAM:
      interact_applam(tm, neg_loc, pos_loc);
      break;
    case NUL:
      interact_appnul(tm, neg_loc);
      break;
    case U32:
      interact_appu32(tm, neg_loc, pos_loc);
      break;
    case REF:
      link_terms(tm, neg, expand_ref(tm, pos_loc));
      break;
    case SUP:
      interact_appsup(tm, neg_loc, pos_loc);
      break;
    default:
      processed = false;
      break;
    }
    break;
  case OPX:
    switch (pos_tag) {
    case NUL:
      interact_opxnul(tm, neg_loc);
      break;
    case U32:
    case I32:
    case F32:
      interact_opxnum(tm, neg_loc, term_lab(neg), pos_loc, pos_tag);
      break;
    case REF:
      link_terms(tm, neg, expand_ref(tm, pos_loc));
      break;
    case SUP:
      interact_opxsup(tm, neg_loc, term_lab(neg), pos_loc);
      break;
    case LAM:
    default:
      processed = false;
      break;
    }
    break;
  case OPY:
    switch (pos_tag) {
    case NUL:
      interact_opynul(tm, neg_loc);
      break;
    case U32:
    case I32:
    case F32:
      interact_opynum(tm, neg_loc, term_lab(neg), pos_loc, pos_tag);
      break;
    case REF:
      link_terms(tm, neg, expand_ref(tm, pos_loc));
      break;
    case SUP:
      interact_opysup(tm, neg_loc, pos_loc);
      break;
    case LAM:
    default:
      processed = false;
      break;
    }
    break;
  case DUP:
    switch (pos_tag) {
    case LAM:
      interact_duplam(tm, neg_loc, pos_loc);
      break;
    case NUL:
      interact_dupnul(tm, neg_loc);
      break;
    case U32:
    case I32:
    case F32:
      interact_dupnum(tm, neg_loc, pos_loc, pos_tag);
      break;
    // TODO(enricozb): dup-ref optimization
    case REF:
      interact_dupref(tm, neg_loc, pos_loc);
      break;
    // case REF: link_terms(tm, neg, expand_ref(pos_loc)); break;
    case SUP:
      interact_dupsup(tm, neg_loc, pos_loc);
      break;
    default:
      processed = false;
      break;
    }
    break;
  case MAT:
    switch (pos_tag) {
    case NUL:
      interact_matnul(tm, neg_loc, term_lab(neg));
      break;
    case U32:
    case I32:
    case F32:
      interact_matnum(tm, neg_loc, term_lab(neg), pos_loc, pos_tag);
      break;
    case REF:
      link_terms(tm, neg, expand_ref(tm, pos_loc));
      break;
    case SUP:
      interact_matsup(tm, neg_loc, term_lab(neg), pos_loc);
      break;
    case LAM:
    default:
      processed = false;
      break;
    }
    break;
  case ERA:
    switch (pos_tag) {
    case LAM:
      interact_eralam(tm, pos_loc);
      break;
    case SUP:
      interact_erasup(tm, pos_loc);
      break;
    case NUL:
    case U32:
    case REF:
    default:
      processed = false;
      break;
    }
    break;
  default:
    processed = false;
    break;
  }
  tm->itrs += 1;

  if (!processed) {
    unprocessed_itrs[neg_tag * 16 + pos_tag] = 1;
  }
}

static void show_unprocessed_itrs() {
  for (u32 i = 17; i <= 255; i++) {
    u32 pos_tag = i % 16;
    if (pos_tag < 1) continue;
    u32 neg_tag = i / 16;
    bool hdr = true;
    if (unprocessed_itrs[neg_tag*16 + pos_tag]) {
      if (hdr) {
        fprintf(stderr, "Unprocesed itrs:\n");
        hdr = false;
      }
      fprintf(stderr, "%s%s\n", tag_to_str(neg_tag), tag_to_str(pos_tag));
    }
  }
}

static inline bool sequential_step(TM* tm) {
  Loc loc = rbag_pop(tm);

  if (loc == 0) {
    return false;
  }

  Pair pair = take_pair(loc, false);
  interact(tm, pair_neg(pair), pair_pos(pair));
  return true;
}

static bool set_idle(bool was_busy) {
  if (was_busy) {
    u32 idle = atomic_fetch_add_explicit(&net.idle, 1, memory_order_relaxed);
  }
  return false;
}

static bool set_busy(bool was_busy) {
  if (!was_busy) {
    u32 idle = atomic_fetch_sub_explicit(&net.idle, 1, memory_order_relaxed);
  }
  return true;
}

static u32 get_victim(TM *tm) {
  return (tm->tid - 1) % TPC;
}

static bool try_steal(TM *tm) {
  if (!tm->buse) return false;

  if (tm->bput > 0) {
    // Our own booty bag has something in it
    if (tm->bput < BBAG_LEN) {
      // Booty bag isn't full, so we can steal without atomics
      tm->bpop = tm->bput;
      tm->btid = tm->tid;
      return true;
    } else {
      // To steal from our own full bag, we need to take back ownership
      if (bbag_compare_swap(tm->tid, FULL, EMPTY, memory_order_relaxed)) {
        tm->bpop = tm->bput; // BBAG_LEN, always
        tm->btid = tm->tid;
        return true;
      }
    }
  }

  // Our booty bag is either empty, or another thread stole it.
  // Try to steal another thread's full bag
  u32 vic = get_victim(tm);
  if (bbag_compare_swap(vic, FULL, STOLEN, memory_order_acquire)) {
    tm->bpop = BBAG_LEN;
    tm->btid = vic;
    tm->sgud += 1;
    return true;
  }

  tm->sbad += 1;
  return false;
}

static bool check_timeout(u32 tick) {
  if (tick % 256 == 0) {
    u32 idle = atomic_load_explicit(&net.idle, memory_order_relaxed);
    if (idle == TPC) {
     return true;
    }
  }
  return false;
}

static void* thread_func(void* arg) {
  thread_id = (u64)arg;
  TM *tm = tms[thread_id];

  // Wait until after injection to turn on booty bag usage
  // TODO: this could be a global net flag i think.
  tm->buse = true;

  u32  tick = 0;
  bool busy = tm->tid == 0;
  while (true) {
    tick += 1;
    bool bty = tm->bpop > 0; // haxor
    Loc loc = rbag_pop(tm);
    if (loc) {
      busy = set_busy(busy);

      Pair pair = take_pair(loc, bty);

      if (bty && (tm->bpop == 0) && (tm->btid != tm->tid)) {
        // Mark stolen booty bag empty
        bbag_set(tm->btid, EMPTY, memory_order_relaxed);
      }

      interact(tm, pair_neg(pair), pair_pos(pair));
    } else {
      busy = set_idle(busy);

      if (try_steal(tm)) continue;

      sched_yield();

      if (check_timeout(tick)) break;
    }
  }

  atomic_fetch_add(&net.nods, tm->nput);
  atomic_fetch_add(&net.itrs, tm->itrs);

  if (1) {
    fprintf(stderr, "t%u: %" PRIu64 " itrs, rput: %u, bput: %u, bpop: %u, steals: %u good %u bad\n",
            tm->tid, tm->itrs, tm->rput, tm->bput, tm->bpop, tm->sgud, tm->sbad);
  }

  return NULL;
}

static void parallel_normalize() {
  // Initialize the global idle counter
  atomic_store_explicit(&net.idle, TPC - 1, memory_order_relaxed);

  for (u64 i = 0; i < TPC; i++) {
    int rc = thread_create(&threads[i], NULL, thread_func, (void*)i);
  }

  for (u64 i = 0; i < TPC; i++) {
    thread_join(threads[i], NULL);
  }

  show_unprocessed_itrs();
}

Term normalize(Term term) {
  if (term_tag(term) != REF) {
    fprintf(stderr, "normalizing non-ref\n");
    exit(1);
  }

  boot(term_loc(term));

  if (TPC == 1) {
    TM *tm = tms[0];
    while (sequential_step(tm))
      ;
    net.nods = tm->nput;
    net.itrs = tm->itrs;
  } else {
    parallel_normalize();
  }

  return get(0);
}

void handle_failure() {
#ifdef MEMLOG
  mlog_dump("memlog.txt");
#endif
}

// Debugging
static char *tag_to_str(Tag tag) {
  switch (tag) {
  case VOID:
    return "___";
  case VAR:
    return "VAR";
  case SUB:
    return "SUB";
  case NUL:
    return "NUL";
  case ERA:
    return "ERA";
  case LAM:
    return "LAM";
  case APP:
    return "APP";
  case SUP:
    return "SUP";
  case DUP:
    return "DUP";
  case REF:
    return "REF";
  case OPX:
    return "OPX";
  case OPY:
    return "OPY";
  case U32:
    return "U32";
  case I32:
    return "I32";
  case F32:
    return "F32";
  case MAT:
    return "MAT";

  default:
    return "???";
  }
}

static char *bty_ctrl_str(u32 ctrl) {
  switch (ctrl) {
  case EMPTY:  return "EMPTY";
  case FULL:   return "FULL";
  case STOLEN: return "STOLEN";
  default:     return "???";
  }
}

void dump_term(Loc loc) {
  Term term = get(loc);
  printf("%06X %03X %03X %s\n", loc, term_loc(term), term_lab(term),
      tag_to_str(term_tag(term)));
}

// FILE VERSION: (or you can >> the stdio into a file)
/*void dump_buff() {*/
/*  FILE *file = fopen("multi.txt", "w");*/
/*  if (file == NULL) {*/
/*    perror("Error opening file");*/
/*    return;*/
/*  }*/
/**/
/*  fprintf(file, "------------------\n");*/
/*  fprintf(file, "      NODES\n");*/
/*  fprintf(file, "ADDR   LOC LAB TAG\n");*/
/*  fprintf(file, "------------------\n");*/
/*  for (Loc loc = RNOD_INI; loc < RNOD_END; loc++) {*/
/*    Term term = get(loc);*/
/*    Loc t_loc = term_loc(term);*/
/*    Lab t_lab = term_lab(term);*/
/*    Tag t_tag = term_tag(term);*/
/*    fprintf(file, "%06X %03X %03X %s\n", loc, term_loc(term),
 * term_lab(term),*/
/*            tag_to_str(term_tag(term)));*/
/*  }*/
/**/
/*  fprintf(file, "------------------\n");*/
/*  fprintf(file, "    REDEX BAG\n");*/
/*  fprintf(file, "ADDR   LOC LAB TAG\n");*/
/*  fprintf(file, "------------------\n");*/
/*  for (Loc loc = RBAG + RBAG_INI; loc < RBAG + RBAG_END; loc++) {*/
/*    Term term = get(loc);*/
/*    Loc t_loc = term_loc(term);*/
/*    Lab t_lab = term_lab(term);*/
/*    Tag t_tag = term_tag(term);*/
/*    fprintf(file, "%06X %03X %03X %s\n", loc, term_loc(term),
 * term_lab(term),*/
/*            tag_to_str(term_tag(term)));*/
/*  }*/
/**/
/*  fprintf(file, "------------------\n");*/
/**/
/*  fclose(file);*/
/*}*/
// STD VERSION
void dump_buff(TM *tm) {
  printf("------------------\n");
  printf("      NODES\n");
  printf("ADDR   LOC LAB TAG\n");
  printf("------------------\n");
  for (Loc idx = 0; idx < tm->nput; idx++) {
    Loc loc = tm->tid * NODE_LEN + idx;
    dump_term(loc);
/*
    Term term = get(loc);
    printf("%06X %03X %03X %s\n", loc, term_loc(term), term_lab(term),
        tag_to_str(term_tag(term)));
*/
  }
  printf("------------------\n");
  printf("    REDEX BAG\n");
  printf("ADDR   LOC LAB TAG\n");
  printf("------------------\n");
  for (Loc idx = 0; idx < tm->rput; idx++) {
    Loc loc = RBAG + tm->tid * RBAG_LEN + idx;
    dump_term(loc);
  }
  printf("------------------\n");
}
