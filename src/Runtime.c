// HVM3-Strict Core: parallel, polarized, LAM/APP & DUP/SUP only

#include <assert.h>
#include <execinfo.h>
#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <signal.h>
#include <stdalign.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

//#define DEBUG
//#define MEMLOG

#define DEBUG_LOG(fmt, ...) fprintf(stderr, "[DEBUG] " fmt "\n", ##__VA_ARGS__)

int get_num_threads() {
  long nprocs = sysconf(_SC_NPROCESSORS_ONLN);
  return (nprocs <= 1) ? 1 : 1 << (int)log2(nprocs);
}

void segv_handler(int sig) {
  void *array[10];
  size_t size;
  
  size = backtrace(array, 10);
  fprintf(stderr, "Error: signal %d:\n", sig);
  backtrace_symbols_fd(array, size, STDERR_FILENO);
  exit(1);
}

#ifdef __APPLE__
// Use explicit file-scope assembly to prevent compiler from optimizing out

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
typedef uint8_t      u8;
typedef int32_t      i32;
typedef uint32_t     u32;
typedef _Atomic(u32) a32;
typedef float        f32;
typedef int64_t      i64;
typedef uint64_t     u64;
typedef _Atomic(u64) a64;
// NOTE typedef alignment is gcc/clang specific
typedef unsigned __int128 u128 __attribute__((aligned(16)));

typedef u8   Tag;  //  8 bits
typedef u32  Lab;  // 24 bits
typedef u32  Loc;  // 32 bits
typedef u64  Term; // Loc | Lab | Tag
typedef u128 Pair; // Term | Term

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
  ZERO = 0,

  // Threads per CPU
  TPC = 4,

  // Number of terms *per thread* for each overflow bag. There are two of them,
  // and they (currently) steal space from each thread's RBAG space.
  // NB: These numbers are a bit aggresive. Overflow of overflow could happen.
  OFLW_LEN = 1 << 18,
  OFLW_SYNC = 1024,

  // Various redex bag sizes within the heap to choose from. The remaining
  // percentage is used for node storage. Assumes 10 threads.
  RBAG_TEST = (1 << 23) * TPC * sizeof(Pair),

  //////////////////////////
  // Choose a RBAG size here
  //////////////////////////
  RBAG_SIZE = RBAG_TEST,
};

enum : u32 {
  // Final calculated RBAG index
  RBAG = ((HEAP_SIZE - RBAG_SIZE) / sizeof(Term)) & ~7U, // CACH_U64 - 1

  // Calculate RBAG_LEN and NODE_LEN: number of u64 elements *per thread*
  // RBAG_LEN MUST be 16-byte aligned. 64-byte alignment might be preferable
  RBAG_LEN = (RBAG_SIZE / (TPC * sizeof(Term))) & ~7U, // CACH_U64 - 1
  NODE_LEN = (HEAP_SIZE - RBAG_SIZE) / (TPC * sizeof(Term)),

  // Booty-bag length in u64 elements
  BBAG_LEN = 96,

  // Offset in RBAG of overflow bags
  OFLW_INI = RBAG_LEN - (OFLW_LEN * 2),

  // Max terms allowed in RBAG, taking into account booty bag and overflow
  RPUT_MAX = OFLW_INI - BBAG_LEN
};

typedef struct Net {
  a64 nods;
  a64 itrs;
  a32 alignas(64) idle;  // TODO Probably should just make it a64
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
  u32 tid;   // thread id
  Loc nput;  // next node allocation attempt index
  Loc rput;  // next rbag push index
  u32 sid;   // tid from which bbag was stolen
  Loc bput;  // owned bbag push index
  Loc spop;  // stolen bbag pop index + 2

  u32 sgud;  // successful steal count
  u32 sbad;  // failed steal count

  Loc oput[2]; // next oflw bag push indices
  
#ifdef MEMLOG
  u32 mput;
  u32 itid;
  u8 i1_tag;
  u8 i2_tag;
  bool mwrp; // memlog wrapped
#endif

  bool buse; // can use booty bag
  bool bful; // ctrl word marked full
  u8   opid; // oput idx we are pushing into
  bool ouse; // can use overflow
  bool osyn; // overflow is sync'd
  //bool otak; // can take from overflow

  u64 itrs;  // interaction count
} TM;

static_assert(sizeof(TM) <= CACH_SIZ, "TM struct getting big");

// Booty bag control word values
enum : u32 {
  EMPTY = 0,
  FULL = 1,
  STOLEN = 2
};

typedef struct BB {
  a32 alignas(64) ctrl; // control word TODO: just make it a64
} BB;

static TM *tms[TPC];
static BB bbs[TPC];
static pthread_t threads[TPC];
static uint8_t unprocessed_itrs[255] = { 0 };

static _Thread_local int thread_id = 0;

// Debugging
static char *tag_to_str(Tag tag);
static char *bty_ctrl_str(u32 ctrl);
static void dump_term(Loc loc);
void dump_buff();

#define TERMSTR_BUFSIZ 128

static Term pair_pos(Pair pair);
static Term pair_neg(Pair pair);
static const char* term_str(char* buf, Term term);
Tag term_tag(Term term) { return term & 0xFF; }
Loc term_loc(Term term);

#ifdef MEMLOG
// Memory operations log
static u64 *MEMBUFF = NULL;
enum : u32 {
  MLOG_SIZ = 4096 * TPC * sizeof(u64) * 3,
  MLOG_LEN = MLOG_SIZ / (TPC * sizeof(u64))
};

//static _Thread_local u64 rbag_loc = 0;
#define MLOG(mop, loc, t1, t2)          mlog((u32)thread_id, mop, loc, t1, t2, 0)
#define MLOG_PAIR(mop, loc, pair)       mlog_pair((u32)thread_id, mop, loc, pair)
#define MLOG_LVL(mop, loc, lvl, t1, t2) mlog((u32)thread_id, mop, loc, t1, t2, lvl)
#else
#define MLOG(mop, loc, t1, t2)
#define MLOG_PAIR(mop, loc, pair)
#define MLOG_LVL(mop, loc, lvl, t1, t2)
#endif

static u32 u64_hi(u64 u) {
  return (u >> 32) & 0xFFFFFFFF;
}

__attribute__((unused))
static u32 u64_lo(u64 u) {
  return u & 0xFFFFFFFF;
}

// Memory operations
#define MOP_EXCH 0x01
#define MOP_LOAD 0x02
#define MOP_STOR 0x03

__attribute__((unused))
static const char* mop_str(u32 mop) {
  switch (mop) {
  case MOP_EXCH: return "EXCH";
  case MOP_LOAD: return "LOAD";
  case MOP_STOR: return "STOR";
  default: return "????";
  }
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

// i1_tag: 4, i2_tag: 4, lvl: 5, op: 2, t1_tag: 4, t2_tag: 4, tid: 4, sid: 4

static u64 mlog_entry(u32 tid, u32 mop, u32 sid, u32 loc, u32 lvl,
                      u32 i1_tag, u32 i2_tag, u32 t1_tag, u32 t2_tag) {
  u64 hi = (i1_tag << 27) | ((i2_tag & 0xF) << 23) |
    ((lvl & 0x1F) << 18) | ((mop & 0x3) << 16) |
    ((t1_tag & 0xF) << 12) | ((t2_tag & 0xF) << 8) |
    ((tid & 0xF) << 4) | (sid & 0xF);
  return hi << 32 | loc;
}

static u32 mlog_i1_tag(u64 e) {
  return (u64_hi(e) >> 27);
}

static u32 mlog_i2_tag(u64 e) {
  return (u64_hi(e) >> 23) & 0xF;
}

static u32 mlog_lvl(u64 e) {
  return (u64_hi(e) >> 18) & 0x1F;
}

static u32 mlog_mop(u64 e) {
  return (u64_hi(e) >> 16) & 0x3;
}

static u32 mlog_t1_tag(u64 e) {
  return (u64_hi(e) >> 12) & 0xF;
}

static u32 mlog_t2_tag(u64 e) {
  return (u64_hi(e) >> 8) & 0xF;
}

static u32 mlog_tid(u64 e) {
  return (u64_hi(e) >> 4) & 0xF;
}

__attribute__((unused))
static u32 mlog_sid(u64 e) {
  return u64_hi(e) & 0xF;
}

static u32 mlog_loc(u64 e) {
  return u64_lo(e);
}

static void mlog_dump_term(FILE* fp, u64 cntr, u64 e, u32 tag, Loc loc, u32 loc_offset) {
  fprintf(fp, "%" PRIu64 ",%u,%s%s,%s,%u,%s,%u,%u\n", cntr, mlog_tid(e),
          tag_to_str(mlog_i1_tag(e)), tag_to_str(mlog_i2_tag(e)),
          mop_str(mlog_mop(e)), mlog_lvl(e),
          tag_to_str(tag), loc, mlog_loc(e) + loc_offset);
}

static void mlog_dump_entry(FILE *fp, u64 cntr, u64 e, u64 locs) {
  u32 mop = mlog_mop(e);
  Loc t1_loc = u64_hi(locs);
  Loc t2_loc = u64_lo(locs);
  if ((mop == MOP_LOAD) || (mop == MOP_STOR)) {
    mlog_dump_term(fp, cntr, e, mlog_t1_tag(e), t1_loc, 0);   // T1 
    /*
    if ((mlog_t2_tag(e) != 0) || (t2_loc != 0)) {
      mlog_dump_term(fp, cntr, e, mlog_t2_tag(e), t2_loc, 1); // T2
    }
    */
  } else {
    fprintf(fp, "%" PRIu64 ",%u,%s%s,%s,%u,%s,%u,%s,%u,%u\n", cntr, mlog_tid(e),
            tag_to_str(mlog_i1_tag(e)), tag_to_str(mlog_i2_tag(e)),
            mop_str(mop), mlog_lvl(e), tag_to_str(mlog_t1_tag(e)), t1_loc, 
            tag_to_str(mlog_t2_tag(e)), t2_loc, mlog_loc(e));
  }
}

static u32 mlog_dump_range(FILE *fp, u32 ini, u32 off, u32 end, u32 *nlog) {
  for (; (off + 2) < end; off += 3) {
    u32 pos  = ini + off;
    u64 cntr = MEMBUFF[pos]; 
    u64 e    = MEMBUFF[pos+1]; // entry
    u64 locs = MEMBUFF[pos+2];
    mlog_dump_entry(fp, cntr, e, locs);
    if (nlog) (*nlog)++;
  }
  return off;
}

static void mlog_dump(const char* fn) {
  FILE *fp = fopen(fn, "w");
  if (fp == NULL) {
    perror("mlog_dump: Error opening file");
    return;
  }

  for (u32 tid = 0; tid < TPC; tid++) {
    TM *tm = tms[tid];
    u32 ini = tid * MLOG_LEN;
    u32 off = tm->mwrp ? tm->mput : 0;
    u32 end = tm->mwrp ? MLOG_LEN : tm->mput;
    u32 nlog = 0;

    off = mlog_dump_range(fp, ini, off, end, &nlog);
    if (tm->mwrp) {
      if (off < end) {
        u64 words[3];
        u32 idx = 0;
        for (; off < end; off++, idx++) {
          if (idx > 2) {
            fprintf(stderr, "idx %u!\n", idx);
            exit(1);
          }
          words[idx] = MEMBUFF[ini + off];
        }
        off = 0;
        end = tm->mput;
        for (; idx < 3; idx++, off++) {
          words[idx] = MEMBUFF[ini + off];
        }
        mlog_dump_entry(fp, words[0], words[1], words[2]);
        nlog += 1;
      } else {
        off = 0;
      }
      mlog_dump_range(fp, ini, off, end, &nlog);
    }
  }
  fclose(fp);
}

static u64 mlog_get_word(u32 idx, TM *tm, u32 mop, Loc loc, u32 lvl, Term t1, Term t2) {
  switch (idx) {
  case 0: return read_cntvct();
  case 1: return mlog_entry(tm->tid, mop, tm->itid, loc, lvl, tm->i1_tag,
                            tm->i2_tag, term_tag(t1), term_tag(t2));
  case 2: return (u64)term_loc(t1) << 32 | term_loc(t2); // TODO new_u64()
  default:
    break;
  }
  fprintf(stderr, "bad idx %u\n", idx);
  exit(1);
}

static void mlog(u32 tid, u32 mop, Loc loc, Term t1, Term t2, u32 lvl) {
  TM *tm = tms[tid];
  for (u32 i = 0; i < 3; i++, tm->mput++) {
    if (tm->mput == MLOG_LEN) {
      tm->mput = 0;
      tm->mwrp = true;
    }
    u32 pos = tid * MLOG_LEN + tm->mput;
    MEMBUFF[pos] = mlog_get_word(i, tm, mop, loc, lvl, t1, t2);
  }
}

static void mlog_pair(u32 tid, u32 mop, Loc loc, Pair pair) {
  mlog(tid, mop, loc, pair_neg(pair), 0, 0);
  mlog(tid, mop, loc, pair_pos(pair), 0, 0);
}

#endif // MEMLOG

void cancel_threads() {
  for (int i = 0; i < TPC; i++) {
    if (i != thread_id) {
      pthread_cancel(threads[i]);
    }
  }
  for (int i = 0; i < TPC; i++) {
    if (i != thread_id) {
      pthread_join(threads[i], NULL);
    }
  }
}

void mlog_exit() {
#ifdef MEMLOG
  fprintf(stderr, "%d mlog_exit() cancelling threads...", thread_id);
  cancel_threads();
  fprintf(stderr, "done\n");
  TM *tm = tms[0];
  fprintf(stderr, "%d mput %u of LEN %u\n", thread_id, tm->mput, MLOG_LEN);
  mlog_dump("memlog.txt");
#endif
  exit(1);
}

// TM/BB operations
void tm_reset(TM *tm) {
  tm->rput = 0;
  tm->nput = 0;
  tm->itrs = 0;

#ifdef MEMLOG
  tm->mput = 0;
  tm->mwrp = false;
#endif
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
  tm->spop = 0;
  tm->sid = TPC;
  tm->sgud = 0;
  tm->sbad = 0;
  tm->oput[0] = 0;
  tm->oput[1] = 0;
  tm->opid = 0;
  tm->bful = false;
  tm->buse = false;
  tm->ouse = false;
  //tm->otak = false;
  tm->osyn = false;

  return tm;
}

#if 0
static BB *bb_new() {
  size_t bb_siz = (sizeof(BB) + CACH_SIZ - 1) & ~(CACH_SIZ - 1);
  BB *bb = aligned_alloc(CACH_SIZ, bb_siz);
  if (bb == NULL) {
    fprintf(stderr, "BB memory allocation failed\n");
    exit(EXIT_FAILURE);
  }
  bb->ctrl = EMPTY;
  return bb;
}
#endif

static void alloc_static_data() {
  for (u64 t = 0; t < TPC; ++t) {
    tms[t] = tm_new(t);
    //bbs[t] = bb_new();
  }
}

static void free_static_data() {
  for (u64 t = 0; t < TPC; ++t) {
    if (tms[t] != NULL) {
      free(tms[t]);
      tms[t] = NULL;
    }
    #if 0
    if (bbs[t] != NULL) {
      free(bbs[t]);
      bbs[t] = NULL;
    }
    #endif
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

Loc term_loc(Term term) { return u64_hi(term); }

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

#ifdef DEBUG
static int mop_debug = 0; // memory operations
static int thd_debug = 0; // threading
static int bty_debug = 0; // booty bag
#endif
static int oflw_debug = 0; // overflow

__attribute__((unused))
static const char* term_str(char* buf, Term term) {
  sprintf(buf, "%s lab:%u loc:%u", tag_to_str(term_tag(term)),
          (u32)term_lab(term), (u32)term_loc(term));
  return buf;
}

// Memory operations
Term swap_lvl(Loc loc, Term term, u32 lvl) {
  Term got = atomic_exchange_explicit((a64*)&BUFF[loc], term, memory_order_relaxed);
  MLOG_LVL(MOP_EXCH, loc, lvl, got, term);
#ifdef MEMLOG
  if (got == 0) {
    fprintf(stderr, "%d swap got NULL @ %u\n", thread_id, loc);
    mlog_exit();
  }
#endif
  return got;
}

Term swap(Loc loc, Term term) {
  return swap_lvl(loc, term, 0);
}

Term take(Loc loc) {
  Term term = atomic_exchange_explicit((a64*)&BUFF[loc], ZERO, memory_order_relaxed);
  MLOG(MOP_EXCH, loc, term, 0);
#ifdef MEMLOG
  if (term == 0) {
    fprintf(stderr, "%d take got NULL @ %u\n", thread_id, loc);
    mlog_exit();
  }
#endif
  return term;
}

Term get(Loc loc) {
  Term term = atomic_load_explicit((a64*)&BUFF[loc], memory_order_relaxed);
  MLOG(MOP_LOAD, loc, term, 0);
  return term;
}

void set(Loc loc, Term term) {
  atomic_store_explicit((a64*)&BUFF[loc], term, memory_order_relaxed);
  MLOG(MOP_STOR, loc, term, 0);
}

static Pair take_pair(Loc loc, bool bty) {
  Pair pair = *(Pair*)&BUFF[loc];
  
  //#define VOID_TEST

  // Debugging
#if defined(MEMLOG) || defined(VOID_TEST)
  Term neg = pair_neg(pair);
  Term pos = pair_pos(pair);
#endif

#if defined(MEMLOG)
  TM *tm = tms[thread_id];
  tm->i1_tag = term_tag(neg);
  tm->i2_tag = term_tag(pos);
  tm->itid = bty ? tm->sid : tm->tid;
#endif
  MLOG_PAIR(MOP_LOAD, loc, pair);

#ifdef VOID_TEST
  //*(Pair*)&BUFF[loc] = (Pair)ZERO;
  if ((neg == 0) || (pos == 0)) {
    fprintf(stderr, "%d take_pair: void term taken\n", thread_id);
    mlog_exit();
  }
#endif
  
  return pair;
}

static void set_pair(Loc loc, Pair pair) {
  *((Pair*)&BUFF[loc]) = pair;
  MLOG_PAIR(MOP_STOR, loc, pair);
}

static Loc port(u64 n, Loc loc) { return n + loc - 1; }

static Loc bbag_offset(u32 tid) {
  return tid * RBAG_LEN;
}

static Loc bbag_ini(u32 tid) {
  return RBAG + bbag_offset(tid);
}

static Loc rbag_ini(u32 tid) {
  return bbag_ini(tid) + BBAG_LEN;
}

static Loc rnod_ini(u32 tid) {
  return tid * NODE_LEN;
}

static Loc oflw_offset(u32 oidx) {
  return OFLW_INI + OFLW_LEN * oidx;
}

static Loc oflw_ini(u32 tid, u32 oidx) {
  // maybe some tricky trick when we know odix can only be zero or one
  return bbag_ini(tid) + oflw_offset(oidx);
}

// Allocator
// ---------

static u64 align(u64 align, u64 val) {
  return (val + align - 1) & ~(align - 1);
}

static Loc node_alloc(TM *tm, u32 cnt) {
#ifdef DEBUG
  if (mop_debug) {
    fprintf(stderr, "%u node alloc cnt: %u, nput: %u\n", tm->tid, cnt,
            tm->nput);
  }
#endif

  if (tm->nput + cnt >= NODE_LEN) {
    fprintf(stderr, "%u node space exhausted, nput: %u, cnt: %u, LEN: %u\n",
            tm->tid, tm->nput, cnt, NODE_LEN);
    exit(1);
  }

  Loc loc = rnod_ini(tm->tid) + tm->nput;
  tm->nput += cnt;
  return loc;
}

static bool bbag_compare_swap(u32 tid, u32 expect, u32 desire,
                              memory_order success_order) {
  return atomic_compare_exchange_strong_explicit(&bbs[tid].ctrl, &expect,
      desire, success_order, memory_order_relaxed);
}

static void bbag_set(u32 tid, u32 val, memory_order order) {
  atomic_store_explicit(&bbs[tid].ctrl, val, order);
}

static u32 bbag_get(u32 tid) {
  return atomic_load_explicit(&bbs[tid].ctrl, memory_order_relaxed);
}

static Loc get_push_offset(TM *tm, bool force_oflw) {
  if (force_oflw && tm->ouse) {
    #if 0 || defined(DEBUG)
    if (oflw_debug) {
      fprintf(stderr, "%u pushing to overflow %u @ %u\n", tm->tid,
            0u+tm->opid, tm->oput[tm->opid]);
    }
    #endif

    return oflw_offset(tm->opid) + tm->oput[tm->opid];
  }

  // Only push to booty bag if we aren't stealing
  if (tm->buse && !tm->bful && (tm->bput < BBAG_LEN) && (tm->sid == TPC)) {
    #ifdef DEBUG
    fprintf(stderr, "%u pushing to booty bag @ %u\n", tm->tid, tm->bput);
    #endif

    return tm->bput;
  }

  #ifdef DEBUG
  fprintf(stderr, "%u pushing to RBAG @ %u\n", tm->tid, tm->rput);
  #endif
  // Push to RBAG
  return BBAG_LEN + tm->rput;
}

static void rbag_push(TM *tm, Term neg, Term pos, bool force_oflw) {
  Loc off = get_push_offset(tm, force_oflw);
  Loc loc = bbag_ini(tm->tid) + off;

  set_pair(loc, pair_new(neg, pos));

  // TODO: adjust_put_idx(tm, off);
  if (off < BBAG_LEN) {
    // pushed to booty bag
    tm->bput += 2;
  } else if (off >= OFLW_INI) {
    // pushed to overflow
    if (tm->oput[tm->opid] >= OFLW_LEN-1) {
      fprintf(stderr, "%u overflow %u space exhausted @ %u\n", tm->tid,
              tm->opid, tm->oput[tm->opid]);
      exit(1);
    }
    tm->oput[tm->opid] += 2;
  } else {
    // pushed to RBAG
    if (tm->rput >= RPUT_MAX-1) {
      fprintf(stderr, "%u rbag space exhausted\n", tm->tid);
      exit(1);
    }
    tm->rput += 2;
  }
}

_Thread_local u64 noflw = 0;

static Loc redex_pop_loc(TM* tm) {
  // Must check overflow bag first when sync'd
  if (tm->ouse) {

    if (tm->osyn) {
      // Overflow is sync'd so we can pop
      u32 oidx = 1u - tm->opid;
      u32 oput = tm->oput[oidx];
      if (oput > 0) {
        oput -= 2;
        tm->oput[oidx] = oput;
        
        #if 0 || defined(DEBUG)
        if (oflw_debug) {
          fprintf(stderr, "%u popping from overflow %u @ %u\n", tm->tid,
                  oidx, oput);
        }
        #endif

        ++noflw;
        
        return oflw_ini(tm->tid, oidx) + oput;
      }
    }

#if 0
    // If the overflow put bag is full, don't allow any pops from anywhere.
    // Overflow will empty on next sync.
    u32 oput = tm->oput[tm->opid];
    u32 opop = tm->oput[1-tm->opid] / 2;
    if (oput+opop >= OFLW_LEN) {
      //fprintf(stderr, "%u no pops overflow %u full\n", tm->tid, tm->opid);
      return 0;
    }
#endif
  }
    
  if (tm->spop > 0) {
    // Pop from stolen, non-empty booty bag
    tm->spop -= 2;

    // If we are stealing from our own booty bag, adjust push index as well
    if (tm->sid == tm->tid) {
      tm->bput -= 2;
    }
    return bbag_ini(tm->sid) + tm->spop;
  } else if (tm->rput > 0) {
    // Pop from non-empty RBAG
    tm->rput -= 2;
    return rbag_ini(tm->tid) + tm->rput;
  } else {
    // Steal from someone else
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

  #if 0 
  fprintf(stderr, "HEAP_SIZE = %" PRIu64 "\n", HEAP_SIZE);
  fprintf(stderr, "RBAG_SIZE = %" PRIu64 "\n", RBAG_SIZE);
  fprintf(stderr, "RBAG      = %u\n", RBAG);
  fprintf(stderr, "RBAG_LEN  = %u\n", RBAG_LEN);
  fprintf(stderr, "NODE_LEN  = %u\n", NODE_LEN);
  #endif

  signal(SIGSEGV, segv_handler);

#ifdef MEMLOG
  mlog_init();
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
  Loc loc = tm->nput;
  tm->nput += arity;
  return loc;
}

void ffi_rbag_push(Term neg, Term pos) {
  rbag_push(tms[0], neg, pos, false);
}

u64 inc_itr() {
  return atomic_load(&net.itrs);
} 

Loc ffi_rbag_ini() {
  // TODO
  return RBAG;
}

Loc ffi_rbag_end() {
  // TODO
  return RBAG;
}

Loc ffi_rnod_end() {
  return atomic_load(&net.nods);
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

  Loc rnod_cnt = tm->nput;
  Loc rbag_cnt = tm->rput;

  u64 rbag_siz = align(CACH_SIZ, sizeof(Term) * rbag_cnt);
  u64 rnod_siz = align(CACH_SIZ, sizeof(Term) * rnod_cnt);

  Def def = {
      .name = name,
      .nodes = aligned_alloc(CACH_SIZ, rnod_siz),
      .nodes_len = rnod_cnt,
      .rbag = aligned_alloc(CACH_SIZ, rbag_siz),
      .rbag_len = rbag_cnt,
  };

  if (def.nodes == NULL || def.rbag == NULL) {
    fprintf(stderr, "DEF memory allocation failed\n");
    exit(1);
  }

  Term *nodes = BUFF;
  Term *rbag = &BUFF[rbag_ini(0)];

  memcpy(def.nodes, nodes, sizeof(Term) * def.nodes_len);
  memcpy(def.rbag, rbag, sizeof(Term) * def.rbag_len);

#if 0
  printf("NEW DEF '%s':\n", def.name);
  dump_buff();
  printf("\n");
#endif

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
  // TODO: i think we can use the return value of node_alloc() here
  Loc offset = (tm->tid * NODE_LEN) + tm->nput - 1;
  node_alloc(tm, nodes_len - 1);

  Term root = term_offset_loc(nodes[0], offset);

  // No redexes reference these nodes yet; safe to add without atomics
  for (u32 n = 1; n < nodes_len; n++) {
    Loc loc = offset + n;
    Term term = term_offset_loc(nodes[n], offset);
    BUFF[loc] = term;
    MLOG_LVL(MOP_STOR, loc, def_idx, term, 0);
  }

  for (u32 i = 0; i < rbag_len; i += 2) {
    Term neg = term_offset_loc(rbag[i], offset);
    Term pos = term_offset_loc(rbag[i+1], offset);
    rbag_push(tm, neg, pos, false);
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

static inline void move(TM *tm, Loc neg_loc, u64 pos);
static inline void move_lvl(TM *tm, Loc neg_loc, Term pos, u32 lvl);

static inline void link_lvl(TM *tm, Term neg, Term pos, u32 lvl) {
  if (term_tag(pos) == VAR) {
    Term far = swap_lvl(term_loc(pos), neg, lvl);
    if (term_tag(far) != SUB) {
      move_lvl(tm, term_loc(pos), far, lvl + 1);
    }
  } else {
    rbag_push(tm, neg, pos, false);
  }
}

static inline void move_lvl(TM *tm, Loc neg_loc, Term pos, u32 lvl) {
  Term neg = swap_lvl(neg_loc, pos, lvl);
  if (term_tag(neg) != SUB) {
    // No need to take() since we already swapped
    link_lvl(tm, neg, pos, lvl + 1);
  }
}

static inline void link_terms(TM *tm, Term neg, Term pos) {
  link_lvl(tm, neg, pos, 0);
}

static inline void move(TM *tm, Loc neg_loc, Term pos) {
  move_lvl(tm, neg_loc, pos, 0);
}

// Interactions
static bool interact_applam(TM *tm, Loc a_loc, Loc b_loc) {
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
  return true;
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
  // TODO: convert to node_alloc( 2 + mat_len * 3)

  /*
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

static bool interact(TM *tm, Term neg, Term pos) {
  Tag neg_tag = term_tag(neg);
  Tag pos_tag = term_tag(pos);
  Loc neg_loc = term_loc(neg);
  Loc pos_loc = term_loc(pos);

  bool res = false;
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
#if 1
      {
        Term lam = expand_ref(tm, pos_loc);
        if (term_tag(lam) != LAM) {
          // Assumption broken. May not matter, but I want to know.
          fprintf(stderr, "APPREF root node is not a LAM, %s\n",
                  tag_to_str(term_tag(lam)));
          mlog_exit();
        }
        // force push to overflow buffer
        rbag_push(tm, neg, lam, true);
      }
#else
      link_terms(tm, neg, expand_ref(tm, pos_loc);
#endif
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

  return res;
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

static bool sequential_step(TM* tm) {
  Loc loc = redex_pop_loc(tm);
  if (loc == 0) {
    return false;
  }
  Pair pair = take_pair(loc, false);
  interact(tm, pair_neg(pair), pair_pos(pair));
  return true;
}
 
static bool can_idle(TM *tm) {
  return (tm->oput[0] == 0) && (tm->oput[1] == 0);
}
 
static bool set_idle(bool was_busy) {
  if (was_busy) {
    atomic_fetch_add_explicit(&net.idle, 1, memory_order_relaxed);
  }
  return false;
}

static bool set_busy(bool was_busy) {
  if (!was_busy) {
    atomic_fetch_sub_explicit(&net.idle, 1, memory_order_relaxed);
  }
  return true;
}

static u32 get_victim(TM *tm) {
  return (tm->tid - 1) % TPC;
}

static bool try_steal(TM *tm) {
  if (!tm->buse) return false;

  if (tm->bput > 0) {
    // Our booty bag has something in it
    // TODO: combine these two conditions into one compound condition
    if (tm->bput < BBAG_LEN) {
      // Booty bag isn't full, so we can steal without atomics
      tm->spop = tm->bput;
      tm->sid = tm->tid;

      #ifdef DEBUG
      fprintf(stderr, "%u stealing own non-empty booty bag\n", tm->tid);
      #endif
      return true;
    } else {
      // To steal from our own full bag, we need to atomic swap
      if (bbag_compare_swap(tm->tid, FULL, EMPTY, memory_order_relaxed)) {
        tm->bful = false;
        tm->spop = tm->bput; // will always be BBAG_LEN
        tm->sid = tm->tid;

        #ifdef DEBUG
        fprintf(stderr, "%u stole own full booty bag\n", tm->tid);
        #endif
        return true;
      }
    }
  }

  // Our booty bag is either empty, or another thread stole it.
  // Try to steal another thread's full bag
  u32 vic = get_victim(tm);
  if (bbag_compare_swap(vic, FULL, STOLEN, memory_order_acquire)) {
    tm->spop = BBAG_LEN;
    tm->sid = vic;
    tm->sgud += 1;

#ifdef DEBUG
    fprintf(stderr, "%u stole t%u's booty bag\n", tm->tid, tm->sid);
#endif

    return true;
  }

  tm->sbad += 1;
  return false;
}

#define IDLE 256

static bool timeout(u64 tick) {
  if (tick % IDLE == 0) {
    u32 idle = atomic_load_explicit(&net.idle, memory_order_relaxed);
    if (idle == TPC) {
      return true;
    }
  }
  return false;
}

static bool take_and_interact(TM *tm, Loc loc, bool from_bty) {
  Pair pair = take_pair(loc, from_bty);

  if (from_bty && (tm->spop == 0)) {
    // The booty bag we stole just became empty

    if (tm->sid != tm->tid) {
      // It was another threads bag - signal that it can be recovered now
      bbag_set(tm->sid, EMPTY, memory_order_relaxed);

#ifdef DEBUG
      fprintf(stderr, "%u emptied t%u's stolen booty bag\n", tm->tid, tm->sid);
#endif
    } else {
#ifdef DEBUG
      fprintf(stderr, "%u emptied own stolen booty bag\n", tm->tid);
#endif
    }

    // No longer stealing
    tm->sid = TPC;
  }

  return interact(tm, pair_neg(pair), pair_pos(pair));
}

#include <sys/sysctl.h>
#include <mach/mach.h>
#include <mach/thread_policy.h>

void setup_thread_for_pcore(int thread_id) {
    // Set high QoS first
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    
    // Then try to bind to specific P-core
    thread_affinity_policy_data_t policy;
    policy.affinity_tag = thread_id; // 0-3 for P-cores
    thread_policy_set(mach_thread_self(), THREAD_AFFINITY_POLICY,
                     (thread_policy_t)&policy, THREAD_AFFINITY_POLICY_COUNT);
}

void setup_thread_for_ecore(int thread_id) {
    // Set lower QoS
    pthread_set_qos_class_self_np(QOS_CLASS_UTILITY, 0);
    
    // Bind to E-core
    thread_affinity_policy_data_t policy;
    policy.affinity_tag = thread_id; // 4-9 for E-cores
    thread_policy_set(mach_thread_self(), THREAD_AFFINITY_POLICY,
                     (thread_policy_t)&policy, THREAD_AFFINITY_POLICY_COUNT);
}


struct SIMPLE_SYNC {
  a64 arrived;
  a64 departed;
} ss;

static bool sync_arrive(u32 tid) {
  u64 prev_arrived = atomic_fetch_add_explicit(&ss.arrived, 1, memory_order_relaxed);
  if (prev_arrived + 1 == TPC) {
    // Last to arrive
    atomic_store_explicit(&ss.departed, 1ULL, memory_order_release);
    atomic_store_explicit(&ss.arrived, ZERO, memory_order_relaxed);
    return true;
  }
  return false;
}

_Thread_local u32 nsync = 0;

static bool sync_depart(bool departed) {
  if (!departed) {
    if (atomic_load_explicit(&ss.arrived, memory_order_relaxed) > 0) {
      return false;
    }
    /*u64 dep_cnt = */atomic_fetch_add_explicit(&ss.departed, 1, memory_order_release);
    //technically a "sync done" shortcut for 1 person here, i just dont know
    // how to return it.
  }
  return true;
}

static bool sync_wait(bool departed) {
  if (departed) {
    u64 dep_cnt = atomic_load_explicit(&ss.departed, memory_order_relaxed);
    if ((dep_cnt % TPC) == 0) {
      nsync += 1;
      atomic_thread_fence(memory_order_acquire);
      return false;
    }
  }
  return true;
}

static u64 work_quantum(u64 time, bool ecore) {
  // 24000 = 1ms
  u64 work = 2400;
  if (ecore) {
    work = work / 2;
  }
  return time + work;
}

static void* thread_func(void* arg) {
  thread_id = (u64)arg;

  bool ecore = false;

  if (thread_id < 4) {
    setup_thread_for_pcore(thread_id);
  } else {
    setup_thread_for_ecore(thread_id);
    ecore = true;
  }
  
  TM *tm = tms[thread_id];

  // Wait until after injection to turn these on
  tm->buse = true;
  tm->ouse = true;
  //tm->otak = true;

  // Overflow synchronization
  // TODO: Could moving these to global to reduce code in this funciton
  bool syncing = false;
  bool departed = false;
  u64 do_nothing = 0;

  u64 time = read_cntvct();
  u64 next_time = work_quantum(time, ecore);
  
  u64  tick = 0;
  bool busy = tm->tid == 0;
  while (true) {
    #ifdef MEMLOG
    pthread_testcancel();
    #endif

    tick += 1;

    if (tm->ouse) {
      if (!syncing) {
        time = read_cntvct();
        if (time >= next_time) {
          //u64 tick_mod = tick % OFLW_SYNC;
          //if ((tick_mod == 0) && !syncing) {
          departed = sync_arrive(tm->tid);
          syncing = true;
          
          if (0 || oflw_debug) {
            fprintf(stderr, "%u syncing @ %u, stop taking from overflow %u len %u\n",
                    tm->tid, nsync+1, 1u-tm->opid, tm->oput[1u-tm->opid]/2);
            time = read_cntvct();
          }
          next_time = work_quantum(time, ecore);
          
          // TODO: assert(oput[oidx] == 0);
          tm->opid = 1 - tm->opid;
          // Just in case it's not empty (it should be)
          //tm->otak = false;
          tm->osyn = false;
        }
      } else { //if (syncing) {
        departed = sync_depart(departed);
        syncing = sync_wait(departed);
        if (!syncing) {
          tm->osyn = true;
          //tm->otak = true;
          // Reset tick count to ensure we empty oveflow before next sync point
          // TODO: could also try something like:
          //if ((tick % sync) < oput[1-oidx]) 
          // just enough rope to hang ourselves
          #if 0
          u32 oflw_len = (tm->oput[1-tm->opid] / 2);
          if (tick_mod < oflw_len) {
            tick = OFLW_SYNC - oflw_len;
          }
          #else
          //tick = 0;
          #endif
          if (0 || oflw_debug) {
            fprintf(stderr, "%u synched @ %u, can take from overflow %u len %u\n", // tick %" PRIu64 "\n",
                    tm->tid, nsync, 1u-tm->opid, tm->oput[1u-tm->opid]/2); // , tick);
          }
          u64 time = read_cntvct();
          next_time = work_quantum(time, ecore);
        }
      }
    }

    bool from_bty = tm->spop > 0; // haxor
    Loc loc = redex_pop_loc(tm);
    if (loc) {
      busy = set_busy(busy);

      // We *think* booty bag is full, but it may have been stolen and emptied
      if (tm->bful && (bbag_get(tm->tid) == EMPTY)) {
        tm->bful = false;
        tm->bput = 0;

        #ifdef DEBUG
        fprintf(stderr, "%u recovered stolen, empty booty bag\n", tm->tid);
        #endif
      }

      take_and_interact(tm, loc, from_bty);

      if (!tm->bful && (tm->bput == BBAG_LEN)) {
        // Booty bag was filled by the preceding interaction
        // Signal that it can be stolen aka drop()
        bbag_set(tm->tid, FULL, memory_order_release);
        tm->bful = true;
      }
    } else {
      do_nothing += 1;
      if (can_idle(tm)) {
        busy = set_idle(busy);
        if (!busy && !try_steal(tm)) {
          sched_yield();
          if (timeout(tick))
            break;
        }
      }
    }
  }

  atomic_fetch_add(&net.nods, tm->nput);
  atomic_fetch_add(&net.itrs, tm->itrs);

  if (1) {
    fprintf(stderr, "t%u itrs %" PRIu64 ", steals good %u bad %u oflw %" PRIu64 " do_nothing %" PRIu64 "\n",
            tm->tid, tm->itrs, tm->sgud, tm->sbad, noflw, do_nothing);
  }
  return NULL;
}

static void parallel_normalize() {
  atomic_store_explicit(&net.idle, TPC-1, memory_order_relaxed);
  atomic_store_explicit(&ss.arrived, ZERO, memory_order_relaxed);
  atomic_store_explicit(&ss.departed, ZERO, memory_order_relaxed);

  for (u64 i = 0; i < TPC; i++) {
    /*int rc = */pthread_create(&threads[i], NULL, thread_func, (void*)i);
  }

  for (u64 i = 0; i < TPC; i++) {
    pthread_join(threads[i], NULL);
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

#ifdef MEMLOG
  mlog_dump("memlog.txt");
#endif

  return get(0);
}

void handle_failure() {
}

// Debugging
static char *tag_to_str(Tag tag) {
  switch (tag) {
  case 0:
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

__attribute__((unused))
static char *bty_ctrl_str(u32 ctrl) {
  switch (ctrl) {
  case EMPTY:  return "EMPTY";
  case FULL:   return "FULL";
  case STOLEN: return "STOLEN";
  default:     return "???";
  }
}

static void dump_term(Loc loc) {
  Term term = get(loc);
  printf("%04u %03u %03u %s\n", loc, term_loc(term), term_lab(term),
      tag_to_str(term_tag(term)));
}

// FILE VERSION: (or you can >> the stdio into a file)
// NOTE: broken don't use without fixing.
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
void tm_dump_buff(TM *tm) {
  printf("------------------\n");
  printf("      NODES\n");
  printf("ADDR LOC LAB TAG\n");
  printf("------------------\n");
  for (Loc idx = 0; idx < tm->nput; idx++) {
    dump_term(rnod_ini(tm->tid) + idx);
  }
  printf("------------------\n");
  printf("    REDEX BAG\n");
  printf("ADDR   LOC LAB TAG\n");
  printf("------------------\n");
  for (Loc idx = 0; idx < tm->rput; idx++) {
    dump_term(rbag_ini(tm->tid) + idx);
  }
  printf("------------------\n");
  fflush(stdout);
}
 
void dump_buff() {
  tm_dump_buff(tms[0]);
}
