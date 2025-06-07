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

#include "../lib/hashmap.h"

#define SUMMARY
//#define DEBUG
//#define MEMLOG

#define DEBUG_LOG(fmt, ...) fprintf(stderr, "[DEBUG] " fmt "\n", ##__VA_ARGS__)

void bt_exit() {
  void *array[10];
  size_t size = backtrace(array, 10);
  backtrace_symbols_fd(array, size, STDERR_FILENO);
  exit(1);
}

void segv_handler(int sig) {
  fprintf(stderr, "Error: signal %d:\n", sig);
  bt_exit();
}

#ifdef __APPLE__
extern uint64_t read_cntvct(void);
__asm__(
    ".global read_cntvct\n"
    ".global _read_cntvct\n"
    "read_cntvct:\n"
    "_read_cntvct:\n"
    "   mrs x0, cntvct_el0\n"
    "   ret\n"
);

extern void dmb_ishst(void);
__asm__(
    ".global dmb_ishst\n"
    ".global _dmb_ishst\n"
    "dmb_ishst:\n"
    "_dmb_ishst:\n"
    "    dmb ishst\n"
    "    ret\n"
);
#endif // __APPLE__

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

// Heap configuration options
enum : u64 {
  // 1GiB heap
  HEAP_1GB = (1ULL << 27) * sizeof(u64),  // 128Mi * 8 bytes = 1GiB

  //////////////////////////
  // Choose a heap size here
  //////////////////////////
  HEAP_SIZ = HEAP_1GB * 6,

  // Cache line size
  CACH_SIZ = 64,
  CACH_U64 = CACH_SIZ / sizeof(u64),

  // Threads per CPU
  TPC = 10,

  #ifdef __APPLE__
  // PCores and ECores total, and in-use
  PCOR_TOT = 4,
  ECOR_TOT = TPC - PCOR_TOT,
  PCOR = TPC < PCOR_TOT ? TPC : PCOR_TOT,
  ECOR = TPC > PCOR_TOT ? (TPC - PCOR) : 1,
  #endif

  // Misc
  ZERO = 0ULL,
  ONE = 1ULL,
  IDLE = 256,

  // Deferred bag terms per thread (2 bags: twice this len used)
  DFER_LEN = 256,
  // When deferred bag gets this big, a memory sync occurs
  DFER_SYN = 32,

  // Includes booty and deferred bags
  RBAG_QED = 8192 * TPC * sizeof(Pair), // Demonstrated to work

  // Used in other calculations below
  RBAG_SIZ = RBAG_QED,
};

enum : u32 {
  // Most of these must be 16-byte aligned (even numbers).

  // Final calculated RBAG index
  RBAG = ((HEAP_SIZ - RBAG_SIZ) / sizeof(Term)) & ~1ULL,

  // Calculate RBAG_LEN and NODE_LEN as terms per thread
  RBAG_LEN = (RBAG_SIZ / (TPC * sizeof(Term))) & ~1ULL,

  // Total size of RNOD buffer in terms per thread
  NODE_TOT = (HEAP_SIZ - RBAG_SIZ) / (TPC * sizeof(Term)),
  
  // Free node bitmasks in u64 elements per thread
  // There is room for optimization of these FNOD/NODE lens
  FNOD_LEN = NODE_TOT / 128,

  // Actual RNOD terms per thread useable
  NODE_LEN = NODE_TOT - FNOD_LEN,

  // Booty bag terms per thread (also starting offset of RBAG)
  BBAG_LEN = 96,

  // Starting offset of deferred bags
  DFER_INI = (RBAG_LEN - (DFER_LEN * 2)) & ~1ULL,

  // Max terms allowed in RBAG, taking into account booty and deferred bags
  RPUT_MAX = DFER_INI - BBAG_LEN - 1
};

typedef struct Net {
  a64 idle;
} Net;

// Global book
typedef struct Def {
  char *name;
  Term *nodes;
  Term *rbag;
  u64  nodes_len;
  u64  rbag_len;
  u64  cnt;
} Def;

typedef struct Book {
  Def *defs;
  u32 len;
  u32 cap;
} Book;

// Local Thread Memory
typedef struct TM {
  u32 tid;   // thread id
  Loc nput;  // next node allocation attempt index
  Loc rput;  // next rbag push index
  Loc bput;  // owned bbag push index

  u32 sid;   // tid from which bbag was stolen (may be our own)
  Loc spop;  // stolen bbag pop index + 2

  Loc dput[2]; // next deferred bag push indices
  
  Loc fidx;  // Current free-node (FNOD) bitmask index
  u32 ffrd;  // free nodes freed
  u32 fusd;  // free nodes re-used/alloc'd

#if 1 || defined(MEMLOG)
  Loc mput;
  u32 itid;
  u8 i1_tag;
  u8 i2_tag;
  bool mwrp;
#endif

  bool buse; // can use booty bag
  bool bhld; // when we KNOW booty bag ctrl word is HELD
             // (in some cases it may be HELD but we don't know)

  u8   dpid; // deferred bag idx we are pushing into
  bool duse; // can use deferred bag
  bool dsyn; // deferred bag is sync'd

  bool nful; // nput has exceeded RNOD_LEN; RNOD space has filled

  bool bstp; // bootstrapping (injecting)

  u8   lvic; // last failed steal attempt victim

#ifdef __APPLE__
  u8   pvic; // round robin PCore victim
  u8   evic; // round robin ECore victim
#endif // __APPLE__

  u64 itrs;  // interaction count
} TM;

//static_assert(sizeof(TM) <= CACH_SIZ, "TM struct getting big");

// Booty bag control word values
enum : u64 {
  HELD = 1,    // held by owner, or "returned" by another thread
  DROPPED = 2, // dropped by owner. can be picked back up by owner or stolen
               // by another thread
  STOLEN = 3,  // stolen by another thread
};

typedef struct BB {
  a64 ctrl; // control word
} BB;

// Global heap, net, book
static u64 *BUFF = NULL;
static Net net;
static Book BOOK = {
  .defs = NULL,
  .len = 0,
  .cap = 0,
};

static TM *tms[TPC];
static BB bbs[TPC];
static pthread_t threads[TPC];

static _Thread_local int thread_id = 0;

// Debugging
static char *tag_to_str(Tag tag);
static const char* term_str(char* buf, Term term);

// FFI functions
void dump_buff();
static void dump_term(Loc loc);
Tag term_tag(Term term) { return term & 0xFF; }
Loc term_loc(Term term);

static u64 align(u64 align, u64 val) {
  return (val + align - 1) & ~(align - 1);
}

#ifdef MEMLOG
// Memory operations log
static u64 *MEMBUFF = NULL;
enum : u32 {
  MLOG_SIZ = 4096 * TPC * sizeof(u64) * 3,
  MLOG_LEN = MLOG_SIZ / (TPC * sizeof(u64))
};

#define MLOG(mop, loc, t1, t2)          mlog((u32)thread_id, mop, loc, t1, t2, 0)
#define MLOG_PAIR(mop, loc, pair)       mlog_pair((u32)thread_id, mop, loc, pair)
#define MLOG_LVL(mop, loc, lvl, t1, t2) mlog((u32)thread_id, mop, loc, t1, t2, lvl)
#else
#define MLOG(mop, loc, t1, t2)          // loggy(mop, loc, t1, t2, 0)
#define MLOG_PAIR(mop, loc, pair)       //loggy_pair(mop, loc, pair)
#define MLOG_LVL(mop, loc, lvl, t1, t2) //loggy(mop, loc, t1, t2, lvl)
#endif // MEMLOG 

__attribute__((unused))
static u32 u64_hi(u64 e) {
  return e >> 32;
}

__attribute__((unused))
static u32 u64_lo(u64 e) {
  return e & 0xFFFFFFFF;
}

// Memory operations
#define MOP_POP  0x00
#define MOP_EXCH 0x01
#define MOP_LOAD 0x02
#define MOP_STOR 0x03
#define MOP_TAKE 0x04

__attribute__((unused))
static const char* mop_str(u32 mop) {
  switch (mop) {
  case MOP_POP:  return "POP ";
  case MOP_EXCH: return "EXCH";
  case MOP_LOAD: return "LOAD";
  case MOP_STOR: return "STOR";
  case MOP_TAKE: return "TAKE";
  default: return "????";
  }
}

#ifdef MEMLOG

static Term pair_neg(Pair pair);
static Term pair_pos(Pair pair);

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

#endif

__attribute__((unused))
static u64 mlog_entry(u32 tid, u32 mop, u32 sid, u32 loc, u32 lvl,
                      u32 i1_tag, u32 i2_tag, u32 t1_tag, u32 t2_tag) {
  u64 hi = (i1_tag << 27) | ((i2_tag & 0xF) << 23) |
    ((lvl & 0x1F) << 18) | ((mop & 0x3) << 16) |
    ((t1_tag & 0xF) << 12) | ((t2_tag & 0xF) << 8) |
    ((tid & 0xF) << 4) | (sid & 0xF);
  return hi << 32 | loc;
}

__attribute__((unused))
static u32 mlog_i1_tag(u64 e) {
  return (u64_hi(e) >> 27);
}

__attribute__((unused))
static u32 mlog_i2_tag(u64 e) {
  return (u64_hi(e) >> 23) & 0xF;
}

__attribute__((unused))
static u32 mlog_lvl(u64 e) {
  return (u64_hi(e) >> 18) & 0x1F;
}

__attribute__((unused))
static u32 mlog_mop(u64 e) {
  return (u64_hi(e) >> 16) & 0x3;
}

__attribute__((unused))
static u32 mlog_t1_tag(u64 e) {
  return (u64_hi(e) >> 12) & 0xF;
}

__attribute__((unused))
static u32 mlog_t2_tag(u64 e) {
  return (u64_hi(e) >> 8) & 0xF;
}

__attribute__((unused))
static u32 mlog_tid(u64 e) {
  return (u64_hi(e) >> 4) & 0xF;
}

__attribute__((unused))
static u32 mlog_sid(u64 e) {
  return u64_hi(e) & 0xF;
}

__attribute__((unused))
static u32 mlog_loc(u64 e) {
  return u64_lo(e);
}

__attribute__((unused))
static void mlog_dump_term(FILE* fp, u64 cntr, u64 e, u32 tag, Loc loc, u32 loc_offset) {
  fprintf(fp, "%" PRIu64 ",%u,%s%s,%s,%u,%s,%u,%u\n", cntr, mlog_tid(e),
          tag_to_str(mlog_i1_tag(e)), tag_to_str(mlog_i2_tag(e)),
          mop_str(mlog_mop(e)), mlog_lvl(e),
          tag_to_str(tag), loc, mlog_loc(e) + loc_offset);
}

__attribute__((unused))
static void mlog_dump_entry(FILE *fp, u64 cntr, u64 e, u64 locs) {
  u32 mop = mlog_mop(e);
  Loc t1_loc = u64_hi(locs);
  Loc t2_loc = u64_lo(locs);
  if ((mop == MOP_POP) || (mop == MOP_LOAD) || (mop == MOP_STOR)) {
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

#ifdef MEMLOG
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
      //fprintf(stderr, "%u dumped %u wrapped entries, off %u end %u\n",
      //tid, wrapped, off, end);
    }
    //fprintf(stderr, "%u dumped %u %s\n", tid, nlog,
    //tm->mwrp ? "wrapped" : "no wrap");
  }
  fclose(fp);
}

static u64 mlog_get_word(u32 idx, TM *tm, u32 mop, Loc loc, u32 lvl, Term t1, Term t2) {
  switch (idx) {
  case 0: return read_cntvct();
  case 1: return mlog_entry(tm->tid, mop, tm->itid, loc, lvl, tm->i1_tag,
                            tm->i2_tag, term_tag(t1), term_tag(t2));
  case 2: return (u64)term_loc(t1) << 32 | term_loc(t2);
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
  mlog(tid, mop, loc+1, pair_pos(pair), 0, 0);
}

static void cancel_threads() {
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

#endif // MEMLOG

static u32 rnod_free_cnt(TM *tm);

static void show_def_cnts() {
  for (u32 i = 0; i < BOOK.len; i++) {
    Def *def = &BOOK.defs[i];
    fprintf(stderr, "%u %10s (n:%2u r:%2u) %u\n", i, def->name,
            ((u32)def->nodes_len - 1) / 2, (u32)def->rbag_len / 2,
            (u32)def->cnt);
  }    
}

static void mlog_exit(const char *msg) {
  TM *tm = tms[thread_id];
  u32 fcnt = rnod_free_cnt(tm);
  fprintf(stderr, "%d EXIT %s fidx %u of %u ffrd %u fusd %u free %u\n",
          thread_id, msg, tm->fidx, FNOD_LEN,
          tm->ffrd, tm->fusd, fcnt);

  show_def_cnts();

#ifdef MEMLOG
  fprintf(stderr, "%d mlog_exit() cancelling threads...", thread_id);
  cancel_threads();
  fprintf(stderr, "done\n");

  #if 0
  TM *tm = tms[0];
  fprintf(stderr, "%d mput %u of LEN %u\n", thread_id, tm->mput, MLOG_LEN);
  #endif

  mlog_dump("memlog.txt");
#endif
  exit(1);
}

// TM operations
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
  TM *tm = aligned_alloc(CACH_SIZ, align(CACH_SIZ, sizeof(TM)));
  if (tm == NULL) {
    fprintf(stderr, "tm_new() memory allocation failed\n");
    exit(1);
  }
  tm_reset(tm);

  tm->tid = tid;

  // Booty bag
  tm->bput = 0;
  tm->bhld = true;
  tm->buse = false;

  // Stolen booty bag
  tm->sid = TPC;
  tm->spop = 0;

  // Deferred bag
  tm->dput[0] = 0;
  tm->dput[1] = 0;
  tm->dpid = 0;
  tm->duse = false;
  tm->dsyn = false;
  tm->bstp = true;

  tm->fidx = 0;
  tm->ffrd = 0;
  tm->fusd = 0;
  tm->nful = false;

#ifdef MEMLOG
  tm->itid = TPC;
  tm->i1_tag = 0;
  tm->i2_tag = 0;
#endif

  // Last failed steal attempt thread ids
  tm->lvic = TPC;
#ifdef __APPLE__
  tm->pvic = tid % PCOR;
  tm->evic = PCOR + (tid % ECOR);
#endif // __APPLE__

  return tm;
}

static void alloc_static_data() {
  for (u64 t = 0; t < TPC; ++t) {
    tms[t] = tm_new(t);
  }
}

static void free_static_data() {
  for (u64 t = 0; t < TPC; ++t) {
    if (tms[t] != NULL) {
      free(tms[t]);
      tms[t] = NULL;
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

Loc term_loc(Term term) { return term >> 32; }

static Term term_with_loc(Term term, Loc loc) {
  return (((Term)loc) << 32) | (term & 0xFFFFFFFF);
}

static bool term_has_loc(Term term) {
  Tag tag = term_tag(term);
  return !(tag == SUB || tag == NUL || tag == ERA || tag == REF || tag == U32);
}

#if 0
static Term term_offset_loc(Term term, Loc offset) {
  if (!term_has_loc(term)) { return term; }
  Loc loc = term_loc(term) + offset;
  return term_with_loc(term, loc);
}
#endif

static Loc port(u32 n, Loc loc) { return n + loc - 1; }

__attribute__((unused))
static bool in_rng(Loc loc, Loc bgn, Loc end) {
  return (loc >= bgn && loc < end);
}

__attribute__((unused))
static bool look_loc(Loc loc) {
  return in_rng(loc, 32, 36) || in_rng(loc, 40, 42);
}

__attribute__((unused))
static bool look_tag(Tag tag) {
  return /*(tag == OPX) || */(tag == OPY);
}

__attribute__((unused))
static void loggy(u32 mop, Loc loc, Term t1, Term t2, u32 lvl) {
  TM *tm = tms[thread_id];
  if (mop == MOP_POP) {
    if (!look_tag(term_tag(t1))) return;
    //fprintf(stderr, "popped %s %u\n", tag_to_str(term_tag(t1)), term_loc(t1));
    if (!look_loc(term_loc(t1))) return;
  } else {
    if (!look_loc(loc)) return;
  }

  u64 e = mlog_entry(tm->tid, mop, tm->itid, loc, lvl, tm->i1_tag,
                     tm->i2_tag, term_tag(t1), term_tag(t2));
  u64 locs = (u64)term_loc(t1) << 32 | term_loc(t2);
  mlog_dump_entry(stderr, 0, e, locs);
}

__attribute__((unused))
static void loggy_pair(u32 mop, Loc loc, Pair pair) {
  loggy(mop, loc, pair_neg(pair), 0, 0);
  loggy(mop, loc+1, pair_pos(pair), 0, 0);
}

/*
static void loggy_pop(Loc loc, Pair pair) {
  Term neg = pair_neg(pair);
  Tag neg_tag = term_tag(neg);
  if (((neg_tag == OPX) || (neg_tag == OPY)) && look(term_loc(neg))) {
    loggy(MOP_POP, loc, neg, 0, 0);
  }
}
*/

//#define HALFNODES

#ifdef HALFNODES
typedef struct {
  Term got;
  Term other; // put for EXCH, other for TAKE
  Loc loc;
  u8 mop1;
  u8 mop2;
  u8 i1_tag;
  u8 i2_tag;
} HN;

#define HN_SIZ 1000000
HN half_nodes[HN_SIZ] = {0};
Loc hnput = 0;
u32 hn_takes = 0;
hashmap_t *hm = 0;


__attribute__((unused))
static HN *hn_get(Loc loc) {
#if 0
  for (u32 i = 0; i < hnput; i++) {
    if (half_nodes[i].loc == loc) {
      return i;
    }
  }
  return HN_SIZ;
#else
  return hashmap_lookup(hm, loc);
  //  void *e = hashmap_lookup(hm, loc);
  //  return (e == NULL) ? e : (HN*)e;
#endif
}

__attribute__((unused))
static bool hn_has(Loc loc) {
  return hn_get(loc) != NULL;
}

__attribute__((unused))
static bool hn_mark(u8 mop, Loc loc) {
  HN *hn = hn_get(loc);
  if (hn != NULL) {
    if (!hn->mop2) {
      hn->mop2 = mop;
    }
    /* else if (!hn->mop3) {
      hn->mop3 = mop;
    } else if (!hn->mop4) {
      hn->mop4 = mop;
      }*/
    //hn->loc = 0;
    return true;
  }
  return false;
}

__attribute__((unused))
static void hn_mon(u8 mop, Loc loc, Term got, Term other) {
  if (!hn_mark(mop, loc) && (hnput < HN_SIZ)) {
    HN *hn = &half_nodes[hnput++];
    hn->got = got;
    hn->other = other;
    hn->loc = loc;
    hn->mop1 = mop;

    TM *tm = tms[thread_id];
    hn->i1_tag = tm->i1_tag;
    hn->i2_tag = tm->i2_tag;

    hashmap_insert(hm, loc, hn);
  }
}

__attribute__((unused))
static void hn_stor(Loc loc, Term term) {
  hn_mark(MOP_STOR, loc);
}

__attribute__((unused))
static void hn_load(Loc loc) {
  hn_mark(MOP_LOAD, loc);
}

__attribute__((unused))
static void hn_dump() {
  u32 never_touched_cnt = 0;

  for (u32 i = 0; i < hnput; i++) {
    HN *hn = &half_nodes[i];
    char buf1[64];
    char buf2[64];
    if (hn->mop2 == 0) {
      if (hn->mop1 == MOP_TAKE) {
        Loc other_loc = ((hn->loc & 1) == 1) ? hn->loc-1 : hn->loc+1;
        fprintf(stderr, "%s%s %s %s @ %u other %s @ %u, then nothing\n",
                tag_to_str(hn->i1_tag), tag_to_str(hn->i2_tag), mop_str(hn->mop1),
                term_str(buf1, hn->got), hn->loc, term_str(buf2, hn->other), other_loc);
      } else {
        fprintf(stderr, "%s%s %s %s with %s @ %u, then nothing\n",
                tag_to_str(hn->i1_tag), tag_to_str(hn->i2_tag), mop_str(hn->mop1),
                term_str(buf1, hn->got), term_str(buf2, hn->other), hn->loc);
      }
      never_touched_cnt++;
    }
  }
  fprintf(stderr, "intital half-node-zero takes/swaps: %u\n", hn_takes);
  fprintf(stderr, "   no follow-up half-node accesses: %u\n", never_touched_cnt);
}

__attribute__((unused))
static void hn_init() {
  hm = hashmap_create();
}

__attribute__((unused))
static void hn_free() {
  hashmap_destroy(hm);
}
#endif // HALFNODES

// Memory operations
Term get(Loc loc) {
  Term term = atomic_load_explicit((a64*)&BUFF[loc], memory_order_relaxed);
  MLOG(MOP_LOAD, loc, term, 0);

  #ifdef HALFNODES
  hn_load(loc);
  #endif // HALFNODES

  return term;
}


Term swap_lvl(Loc loc, Term term, u32 lvl) {
  Term got = atomic_exchange_explicit((a64*)&BUFF[loc], term, memory_order_relaxed);
  MLOG_LVL(MOP_EXCH, loc, lvl, got, term);

  #ifdef HALFNODES
  Loc nod_loc = 0;
  if ((loc & 1) == 1) {
    nod_loc = loc - 1;
  } else {
    nod_loc = loc + 1;
  }
  Term nod = get(nod_loc);
  if (nod == 0) {
    hn_mon(MOP_EXCH, loc, got, term);
    //fprintf(stderr, "SWAP %s %u @ %u\n", tag_to_str(term_tag(term)), term_loc(term), loc);
  }
  #endif

  //hn_stor(loc, term);

  #ifdef VOIDTEST
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


Term take_lvl(Loc loc, u32 lvl) {
  Term term = atomic_exchange_explicit((a64*)&BUFF[loc], ZERO, memory_order_relaxed);
  MLOG_LVL(MOP_EXCH, loc, lvl, term, 0);
  
  #ifdef HALFNODES
  // or: hn_take(loc);
  Loc nod_loc = 0;
  if ((loc & 1) == 1) {
    nod_loc = loc - 1;
  } else {
    nod_loc = loc + 1;
  }
  Term nod = get(nod_loc);
  if (nod == 0) {
    fprintf(stderr, "free node @ %u\n", loc & ~1u);
  } else { //if (term_tag(nod) == VAR) {
    ++hn_takes;
    hn_mon(MOP_TAKE, loc, term, nod);
    //fprintf(stderr, "TAKE %s %u @ %u\n", tag_to_str(term_tag(nod)), term_loc(nod), nod_loc);
  }
  #endif

  #ifdef VOIDTEST
  if (term == 0) {
    fprintf(stderr, "%d take got NULL @ %u\n", thread_id, loc);
    mlog_exit();
  }
  #endif
  return term;
}

Term take(Loc loc) {
  return take_lvl(loc, 0);
}

u64 peek(Loc loc) {
  return BUFF[loc];
}

u64 poke(Loc loc, u64 val) {
  return BUFF[loc] = val;
}

void set(Loc loc, Term term) {
  atomic_store_explicit((a64*)&BUFF[loc], term, memory_order_relaxed);
  MLOG(MOP_STOR, loc, term, 0);

  #ifdef HALFNODES
  hn_stor(loc, term);
  #endif
}

static Pair take_pair(Loc loc) {
  Pair pair = *(Pair*)&BUFF[loc];
  
#define VOID_TEST

  // Debugging
#if defined(MEMLOG) || defined(VOID_TEST)
  Term neg = pair_neg(pair);
  Term pos = pair_pos(pair);
#endif

#if 1 || defined(MEMLOG)
  TM *tm = tms[thread_id];
  tm->i1_tag = term_tag(neg);
  tm->i2_tag = term_tag(pos);
  tm->itid = tm->sid; // bty ? tm->sid : tm->tid;
#endif
  MLOG_PAIR(MOP_POP, loc, pair);

  //loggy_pop(loc, pair);

  #ifdef VOID_TEST
  //*(Pair*)&BUFF[loc] = (Pair)ZERO;
  if ((neg == 0) || (pos == 0)) {
    mlog_exit("take_pair: void term taken");
  }
  #endif
  
  return pair;
}

static void set_pair(Loc loc, Pair pair) {
  *((Pair*)&BUFF[loc]) = pair;
  MLOG_PAIR(MOP_STOR, loc, pair);
}

static Loc bbag_offset(u32 tid) {
  return tid * RBAG_LEN;
}

static Loc bbag_ini(u32 tid) {
  return RBAG + bbag_offset(tid);
}

static bool bbag_empty(TM *tm) {
  return tm->bput == 0;
}

static bool bbag_full(TM *tm) {
  return tm->bput == BBAG_LEN;
}

static bool bbag_compare_swap(u32 tid, u64 expect, u32 desire,
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

// Drop a held, full booty bag (make it steal-able)
static void bbag_drop(TM *tm) {
  bbag_set(tm->tid, DROPPED, memory_order_release);
  tm->bhld = false;
}

// Attempt to recover a stolen and emptied booty bag
static bool bbag_recover(TM *tm) {
  bool held = bbag_get(tm->tid) == HELD;
  if (held) {
    tm->bhld = true;
    tm->bput = 0;
  }
  return held;
}

// Attempt to pick up our own dropped booty bag - this is treated as "stealing"
// from ourself - the only way to pop from our own bag
static bool bbag_pickup(TM *tm) {
  bool held = bbag_compare_swap(tm->tid, DROPPED, HELD, memory_order_relaxed);
  if (held) {
    tm->bhld = true;
    tm->spop = tm->bput; // will always be BBAG_LEN
    tm->sid = tm->tid;
  }
  return held;
}

// Attempt to steal another thread's dropped booty bag
static bool bbag_steal(TM *tm, u32 sid) {
  bool stole = bbag_compare_swap(sid, DROPPED, STOLEN, memory_order_acquire);
  if (stole) {
    tm->spop = BBAG_LEN;
    tm->sid = sid;
  }
  return stole;
}

// Return true if booty bag is stolen, and empty
static bool bbag_looted(TM *tm) {
  return (tm->sid < TPC) && (tm->spop == 0);
}

// Return a stolen, empty booty bag
static void bbag_return(TM *tm) {
  if (tm->sid != tm->tid) {
    // It was another thread's bag - reset state to HELD
    bbag_set(tm->sid, HELD, memory_order_relaxed);
  }
  // No longer stealing
  tm->sid = TPC;
}

static Loc rbag_ini(u32 tid) {
  return bbag_ini(tid) + BBAG_LEN;
}

static bool rbag_empty(TM *tm) {
  return tm->rput == 0;
}

static Loc rnod_ini(u32 tid) {
  return tid * NODE_TOT;
}

static Loc dfer_offset(u32 idx) {
  return DFER_INI + DFER_LEN * idx;
}

static Loc dfer_ini(u32 tid, u32 idx) {
  return bbag_ini(tid) + dfer_offset(idx);
}

// Check if the sync'd deferred bag we might pop from is empty
__attribute__((unused))
static bool dfer_empty(TM *tm) {
  return tm->dput[1u-tm->dpid] == 0;
}  

// Check if there are any items in either deferred bag
static bool dfer_any(TM *tm) {
  return (tm->dput[0] > 0) || (tm->dput[1] > 0);
}  

static Loc fnod_offset() {
  return NODE_LEN;
}

static Loc fnod_ini(u32 tid) {
  return rnod_ini(tid) + fnod_offset();
}

static void rnod_free(TM *tm, Loc loc) {
  Loc fidx = loc / 128;
  u32 bit = (loc % 128) / 2;
  Loc ini = fnod_ini(tm->tid);
  u64 mask = peek(ini + fidx);
#if 0
  fprintf(stderr, "%u freeing %u fidx %u bit %u\n", tm->tid,
          loc, fidx, bit);
#endif
  u64 bit_msk = ONE << bit;
  if (mask & bit_msk) {
    mlog_exit("rnod_free double-free");
  }
  poke(ini + fidx, mask | bit_msk);
  tm->ffrd += 1;
}

// could optimize this by using "0" as "free", and doing simple nput increment
// until we use all space and wrap to end, after which we check free mask
static Loc fnod_next(TM* tm) {
  Loc fidx = tm->fidx;
  Loc ini = fnod_ini(tm->tid);
  while (1) {
    u64 mask = peek(ini + tm->fidx);
    u64 fs = __builtin_ffsll(mask);  // find first set bit
    if (fs > 0) {
      fs -= 1;
      poke(ini + tm->fidx, mask & ~(ONE << fs));
      Loc nput = (tm->fidx * 128) + (fs * 2);
      tm->fusd += 1;
      return nput;
    } else {
      tm->fidx += 1;
      if (tm->fidx >= FNOD_LEN) {
        tm->fidx = 0;
      }
      if (tm->fidx == fidx) {
        mlog_exit("node space exhausted");
      }
    }
  }
}

// Debugging
__attribute__((unused))
static u32 rnod_free_cnt(TM *tm) {
  u32 cnt = 0;
  Loc ini = fnod_ini(tm->tid);
  for (u32 i = 0; i < FNOD_LEN; i++) {
    cnt += __builtin_popcountll(peek(ini + i));
  }
  return cnt;
}

// Allocator
// ---------

u32 alloc_cnt = 0;

static Loc node_alloc(TM *tm, u32 cnt) {
  if (TPC == 1) {
    ++alloc_cnt;
  }

  #if 0
  if (tm->nput + cnt >= NODE_LEN) {
    fprintf(stderr, "%u node space exhausted, nput: %u, cnt: %u, LEN: %u\n",
            tm->tid, tm->nput, cnt, NODE_LEN);
    exit(1);
  }
  #endif

  if (!tm->nful) {
    // Simple increment until we consume all node space
    if (tm->nput + cnt < NODE_LEN) {
      Loc nput = tm->nput;
      tm->nput += cnt;
      return rnod_ini(tm->tid) + nput;
    }
    tm->nful = true;
  }  
  return rnod_ini(tm->tid) + fnod_next(tm);
}

static Loc get_push_offset(TM *tm, bool dfer) {
  // Push to deferred bag
  if (dfer && tm->duse) {
    u32 dput = tm->dput[tm->dpid];
    tm->dput[tm->dpid] += 2;
    return dfer_offset(tm->dpid) + dput;
  }

  // Only push to booty bag if we aren't stealing
  if (tm->buse && tm->bhld && !bbag_full(tm) && (tm->sid == TPC)) {
    u32 bput = tm->bput;
    tm->bput += 2;
    return bput;
  }

  // Push to RBAG
  u32 rput = tm->rput;
  tm->rput += 2;
  return BBAG_LEN + rput;
}

static void redex_push(TM *tm, Term neg, Term pos, bool dfer) {
  Loc off = get_push_offset(tm, dfer);
  Loc loc = bbag_ini(tm->tid) + off;

  set_pair(loc, pair_new(neg, pos));

  if (off < BBAG_LEN) {
    // We pushed to booty bag
    if (bbag_full(tm)) {
      // We're holding a full, non-stolen booty bag - if there are terms in
      // other bags available to pop immediately, drop it
      if (!rbag_empty(tm) || dfer_any(tm)) {
        bbag_drop(tm);
      }
    }
  }

  #if 1
  if (off > BBAG_LEN) {
    // Pushed to RBAG
    if (tm->rput >= RPUT_MAX) {
      fprintf(stderr, "%u rbag space exhausted\n", tm->tid);
      exit(1);
    }
  }
  #endif
}

static Loc dfer_pop_loc(TM *tm) {
  if (tm->dsyn) {
    // Deferred bag is sync'd so we can pop
    u32 dpid = 1u - tm->dpid;
    if (tm->dput[dpid] > 0) {
      tm->dput[dpid] -= 2;
      return dfer_ini(tm->tid, dpid) + tm->dput[dpid];
    } else {
      tm->dsyn = false;
    }
  }
  return 0;
}

static void dfer_sync(TM *tm) {
#ifdef __APPLE__
  dmb_ishst();
#endif // __APPLE__
  tm->dpid = 1u - tm->dpid;
  tm->dsyn = true;
}

static Loc redex_pop_loc(TM* tm) {
  // Check deferred bags first
  if (tm->duse) {
    Loc loc = dfer_pop_loc(tm);
    if (loc > 0) return loc;

    // Flip & sync deferred bag if size has reached threshold
    if (tm->dput[tm->dpid] >= DFER_SYN) {
      dfer_sync(tm);
      Loc loc = dfer_pop_loc(tm);
      if (loc > 0) return loc;
    }
  }
    
  if ((tm->sid < TPC) && (tm->spop > 0)) {
    // Pop from stolen booty bag - it may be our HELD bag
    tm->spop -= 2;

    // If we are stealing from our own bag, adjust push index as well
    // NOTE shouldn't be necessary here as we are committed to emptying
    // the bag, thus could set bput=0 when bag becomes empty.
    if (tm->sid == tm->tid) {
      tm->bput -= 2;
    }
    return bbag_ini(tm->sid) + tm->spop;
  } else if (tm->rput > 0) {
    // Pop from RBAG
    tm->rput -= 2;
    return rbag_ini(tm->tid) + tm->rput;
  } else if (tm->duse) {
    // Finally, try flip & sync of deferred bag if size > 0
    if (tm->dput[tm->dpid] > 0) {
      dfer_sync(tm);
      return dfer_pop_loc(tm);
    }
  }
  // Steal from someone else
  return 0;
}

// FFI functions
void hvm_init() {
  if (BUFF == NULL) {
    BUFF = aligned_alloc(CACH_SIZ, HEAP_SIZ);
    if (BUFF == NULL) {
      fprintf(stderr, "Heap memory allocation failed\n");
      exit(1);
    }
  }
  memset(BUFF, 0, HEAP_SIZ);

  alloc_static_data();

  #ifdef SUMMARY
  fprintf(stderr, "HEAP_SIZ = %" PRIu64 "\n", HEAP_SIZ);
  fprintf(stderr, "RBAG_SIZ = %" PRIu64 "\n", RBAG_SIZ);
  fprintf(stderr, "RBAG     = %u\n", RBAG);
  fprintf(stderr, "RBAG_LEN = %u\n", RBAG_LEN);
  fprintf(stderr, "BBAG_LEN = %u\n", BBAG_LEN);
  fprintf(stderr, "DFER_INI = %u\n", DFER_INI);
  fprintf(stderr, "DFER_LEN = %" PRIu64 "\n", DFER_LEN);

  fprintf(stderr, "NODE_TOT = %u\n", NODE_TOT);
  fprintf(stderr, "NODE_LEN = %u\n", NODE_LEN);
  fprintf(stderr, "FNOD_LEN = %u\n", FNOD_LEN);
  #endif

  signal(SIGSEGV, segv_handler);

  #ifdef MEMLOG
  mlog_init();
  #endif

  #ifdef HALFNODES
  hn_init();
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

  #ifdef HALFNODES
  hn_free();
  #endif
}

void handle_failure() {
}

Loc ffi_alloc_node(u64 arity) {
  return node_alloc(tms[0], arity);
}

void ffi_rbag_push(Term neg, Term pos) {
  redex_push(tms[0], neg, pos, false);
}

u64 inc_itr() {
  u64 itrs = 0;
  for (u32 i = 0; i < TPC; i++) {
    itrs += tms[i]->itrs;
  }
  return itrs;
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
  u64 nods = 0;
  for (u32 i = 0; i < TPC; i++) {
    nods += tms[i]->nput;
  }
  return nods;
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

  u64 rbag_siz = sizeof(Term) * rbag_cnt;
  u64 rnod_siz = sizeof(Term) * rnod_cnt;

  Def def = {
      .name = name,
      .nodes = aligned_alloc(CACH_SIZ, align(CACH_SIZ, rnod_siz)),
      .nodes_len = rnod_cnt,
      .rbag = aligned_alloc(CACH_SIZ, align(CACH_SIZ, rbag_siz)),
      .rbag_len = rbag_cnt,
      .cnt = 0
  };

  if ((def.nodes == NULL) || (def.rbag == NULL)) {
    fprintf(stderr, "def_new() memory allocation failed\n");
    exit(1);
  }

  Term *rnod = BUFF;
  Term *rbag = &BUFF[rbag_ini(0)];

  memcpy(def.nodes, rnod, rnod_siz);
  memcpy(def.rbag, rbag, rbag_siz);

  #if 0
  printf("NEW DEF '%s':\n", def.name);
  dump_buff();
  printf("\n");
  #endif

  memset(rnod, 0, rnod_siz);
  memset(rbag, 0, rbag_siz);

  BOOK.defs[BOOK.len] = def;
  BOOK.len++;

  tm_reset(tm);
}

char *def_name(Loc def_idx) { return BOOK.defs[def_idx].name; }

static Term node_offset_loc(Term term, Loc* nod_locs) {
  if (!term_has_loc(term)) { return term; }
  Loc loc = term_loc(term) - 1;
  Loc nloc = loc / 2;
  Loc off = loc & 1;
  return term_with_loc(term, nod_locs[nloc] + off);
}

// Expands a ref's data into a linear block of nodes with its nodes' locs
// offset by the index where in the BUFF it was expanded.
//
// Returns the ref's root, the first node in its data.
static Term expand_ref(TM *tm, Loc def_idx) {
  // Get definition data
  Def *def = &BOOK.defs[def_idx];
  const u32 nodes_len = def->nodes_len;
  const Term *nodes = def->nodes;
  const Term *rbag = def->rbag;
  const u32 rbag_len = def->rbag_len;
  Loc node_locs[64];

  if (TPC == 1) {
    def->cnt++;
  }

  bool mat = term_tag(nodes[1]) == MAT;
  // loc_cnt == "number of term pairs"
  u32 loc_cnt = mat ? 1 + (nodes_len - 3) : (nodes_len - 1) / 2;
  for (u32 i = 0; i < loc_cnt; i++) {
    node_locs[i] = node_alloc(tm, 2);
  }

  Term root = node_offset_loc(nodes[0], node_locs);

  // No redexes reference these terms yet; safe to add without atomics
  if (!mat) {
    for (u32 i = 0; i < loc_cnt; i++) {
      Term neg = node_offset_loc(nodes[(i*2)+1], node_locs);
      Term pos = node_offset_loc(nodes[(i*2)+2], node_locs);
      Loc loc = node_locs[i];
      BUFF[loc] = neg;
      BUFF[loc+1] = pos;
      MLOG_PAIR(MOP_STOR, loc, pair_new(neg, pos));
    }
  } else { /* MAT */
    // First pair: store root LAM var, bod
    Term var = node_offset_loc(nodes[1], node_locs);
    Term bod = node_offset_loc(nodes[2], node_locs);
    Loc loc = node_locs[0];
    BUFF[loc] = var;
    BUFF[loc+1] = bod;
    MLOG_PAIR(MOP_STOR, loc, pair_new(var, bod));
    
    for (u32 i = 1; i < loc_cnt; i++) {
      Term trm = node_offset_loc(nodes[i+2], node_locs);
      // Add a "phony" SUB with Loc of next arm
      Term sub = term_new(SUB, 0, (i + 1 < loc_cnt) ? node_locs[i+1] : 0);
      Loc loc = node_locs[i];
      BUFF[loc] = trm;
      BUFF[loc+1] = sub;
      MLOG_PAIR(MOP_STOR, loc, pair_new(trm, sub));
    }
  }

  for (u32 i = 0; i < rbag_len; i += 2) {
    Term neg = node_offset_loc(rbag[i], node_locs);
    Term pos = node_offset_loc(rbag[i+1], node_locs);
    redex_push(tm, neg, pos, false);
  }
  return root;
}

static void boot(Loc def_idx) {
  TM *tm = tms[0];
  if (tm->nput > 0 || tm->rput > 0) {
    fprintf(stderr, "booting on non-empty state\n");
    exit(1);
  }
  tm->bstp = false;
  node_alloc(tm, 2);
  set(0, expand_ref(tm, def_idx));
}

// Atomic Linker
static inline void move(TM *tm, Loc neg_loc, u64 pos);
static inline void move_lvl(TM *tm, Loc neg_loc, Term pos, u32 lvl);

static inline void link_lvl(TM *tm, Term neg, Term pos, u32 lvl) {
  if (term_tag(pos) == VAR) {
    Term far = swap(term_loc(pos), neg);
    if (term_tag(far) != SUB) {
      move_lvl(tm, term_loc(pos), far, lvl);
    }
  } else {
    redex_push(tm, neg, pos, false);
  }
}

static inline void link_terms(TM *tm, Term neg, Term pos) {
  link_lvl(tm, neg, pos, 0);
}

static inline void move_lvl(TM *tm, Loc neg_loc, Term pos, u32 lvl) {
  Term neg = swap_lvl(neg_loc, pos, lvl);
  if (term_tag(neg) != SUB) {
    // No need to take() since we already swapped
    link_lvl(tm, neg, pos, lvl+1);
  }
}

static inline void move(TM *tm, Loc neg_loc, Term pos) {
  move_lvl(tm, neg_loc, pos, 0);
}

// Interactions
static void interact_appref(TM *tm, Term neg, Loc pos_loc) {
  Term lam = expand_ref(tm, pos_loc);
  // Force push to deferred bag
  redex_push(tm, neg, lam, true);
}

static void interact_applam(TM *tm, Loc a_loc, Loc b_loc) {
  Term arg = take(port(1, a_loc));
  Loc var = port(1, b_loc);
  Loc ret = port(2, a_loc);
  Term bod = take(port(2, b_loc));

  bool mat = term_tag(peek(var)) == MAT;

  move(tm, var, arg);
  move(tm, ret, bod);

  if (mat) {
    // !!!
    //rnod_free(tm, var);
  }
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
  u32 x = term_loc(take_lvl(port(1, a_loc), 1));
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
  move_lvl(tm, ret, term_new(y_type, 0, res), 2);

  // !!!
  //rnod_free(tm, a_loc);
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
  fprintf(stderr, "interact_matnul needs to support non-adjacent arms.\n");
  exit(1);
  
  move(tm, port(1, a_loc), term_new(NUL, 0, 0));
  for (u32 i = 0; i < mat_len; i++) {
    link_terms(tm, term_new(ERA, 0, 0), take(port(i + 2, a_loc)));
  }
}

static void interact_matnum(TM *tm, Loc ret, u32 mat_len, u32 n, Tag n_type) {
  if (n_type != U32) {
    fprintf(stderr, "match with non-U32\n");
    exit(1);
  }

  u32 i_arm = (n < mat_len - 1) ? n : (mat_len - 1);
  Loc arm_loc = 0;
  // First arm is in ret's phony SUB
  Loc sub = port(2, ret);
  for (u32 i = 0; i < mat_len; i++) {
    Loc arm = term_loc(peek(sub));
    if (i == i_arm) {
      arm_loc = arm;
    } else {
      link_terms(tm, term_new(ERA, 0, arm), take(arm));
    }
    // Next arm is in arm's phony SUB
    sub = port(2, arm);
  }

  Term arm = take(arm_loc);

  #if 0
  if (term_tag(arm) != REF) {
    fprintf(stderr, "non-REF arm @ %u i_arm %u n %u mat_len %u ret_loc %u\n",
            arm_loc, i_arm, n, mat_len, ret);
    exit(1);
  }
  #endif

  if (i_arm < mat_len - 1) {
    move(tm, ret, arm);
  } else {
    Loc app = node_alloc(tm, 2);
    set(app + 0, term_new(U32, 0, n - (mat_len - 1)));
    set(app + 1, term_new(SUB, 0, 0));
    move(tm, ret, term_new(VAR, 0, port(2, app)));

    // !!!
    //rnod_free(tm, ret);

    link_terms(tm, term_new(APP, 0, app), arm);
    
    // !!!
    //rnod_free(tm, arm_loc);
  }
}

static void interact_matsup(TM *tm, Loc mat_loc, Lab mat_len, Loc sup_loc) {
  fprintf(stderr, "interact_matsup needs to support non-adjacent arms.\n");
  exit(1);

  Loc ma0 = node_alloc(tm, mat_len + 1);
  Loc ma1 = node_alloc(tm, mat_len + 1);
  Loc sup = node_alloc(tm, 2);

  set(port(1, sup), term_new(VAR, 0, port(1, ma1)));
  set(port(2, sup), term_new(VAR, 0, port(1, ma0)));
  set(port(1, ma0), term_new(SUB, 0, 0));
  set(port(1, ma1), term_new(SUB, 0, 0));

  for (u32 i = 0; i < mat_len; i++) {
    Loc dui = node_alloc(tm, 2);
    set(port(1, dui), term_new(SUB, 0, 0));
    set(port(2, dui), term_new(SUB, 0, 0));
    set(port(2 + i, ma0), term_new(VAR, 0, port(2, dui)));
    set(port(2 + i, ma1), term_new(VAR, 0, port(1, dui)));

    link_terms(tm, term_new(DUP, 0, dui), take(port(2 + i, mat_loc)));
  }

  move(tm, port(1, mat_loc), term_new(SUP, 0, sup));
  link_terms(tm, term_new(MAT, mat_len, ma0), take(port(2, sup_loc)));
  link_terms(tm, term_new(MAT, mat_len, ma1), take(port(1, sup_loc)));
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

static void interact_eraref(TM *tm, Loc era_loc) {
  if (era_loc > 0) {
    //rnod_free(tm, era_loc);
  }
}

static bool interact(TM *tm, Term neg, Term pos) {
  Tag neg_tag = term_tag(neg);
  Tag pos_tag = term_tag(pos);
  Loc neg_loc = term_loc(neg);
  Loc pos_loc = term_loc(pos);

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
      interact_appref(tm, neg, pos_loc);
      break;
    case SUP:
      interact_appsup(tm, neg_loc, pos_loc);
      break;
    default:
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
    case REF:
      interact_dupref(tm, neg_loc, pos_loc);
      break;
    case SUP:
      interact_dupsup(tm, neg_loc, pos_loc);
      break;
    default:
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
      interact_matnum(tm, term_loc(neg), term_lab(neg), pos_loc, pos_tag);
      break;
    case REF:
      link_terms(tm, neg, expand_ref(tm, pos_loc));
      break;
    case SUP:
      interact_matsup(tm, neg_loc, term_lab(neg), pos_loc);
      break;
    case LAM:
    default:
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
      interact_eraref(tm, neg_loc);
    default:
      break;
    }
    break;
  default:
    break;
  }
  tm->itrs += 1;
  return true;
}

static bool sequential_step(TM* tm) {
  Loc loc = redex_pop_loc(tm);
  if (loc == 0) {
    return false;
  }
  Pair pair = take_pair(loc);
  interact(tm, pair_neg(pair), pair_pos(pair));
  return true;
}
 
static bool can_idle(TM *tm) {
  return rbag_empty(tm) && bbag_empty(tm) && !dfer_any(tm);
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

static u32 get_victim(TM* tm) {
#ifdef __APPLE__
  // PCore bias: if we didn't fail last attempt, or we failed on ECore, try PCore
  if ((tm->lvic == TPC) || (tm->lvic >= PCOR)) {
    tm->pvic = (tm->pvic - 1) % PCOR;
    return tm->pvic;
  } else {
    tm->evic = PCOR + (tm->evic - 1) % ECOR;
    return tm->evic;
  }
#else
  return (tm->tid - 1) % TPC;
#endif
}

static bool try_steal(TM *tm) {
  if (!tm->buse) return false;

  if (tm->bput > 0) {
    // Either our booty bag has something in it, or it had something in it
    // and we dropped it.
    if (tm->bhld) {
      // We're holding it, so we can "steal" (from) it without atomics
      tm->spop = tm->bput;
      tm->sid = tm->tid;
      return true;
    } else {
      // We dropped it - try to pick it up
      if (bbag_pickup(tm)) {
        return true;
      }
    }
  }
  // Our booty bag is either empty, or another thread stole it - try to steal
  // another thread's full bag
  u32 vic = get_victim(tm);
  if (bbag_steal(tm, vic)) {
    tm->lvic = TPC;
    return true;
  }
  tm->lvic = vic;
  return false;
}

static bool timeout(u64 tick) {
  if (tick % IDLE == 0) {
    u32 idle = atomic_load_explicit(&net.idle, memory_order_relaxed);
    if (idle == TPC) {
      return true;
    }
  }
  return false;
}

#ifdef __APPLE__
#include <mach/mach.h>
#include <mach/thread_policy.h>

void set_affinity(int tid) {
  thread_affinity_policy_data_t policy;
  policy.affinity_tag = tid; // 0-3 for P-cores, 4-9 for E-cores on base Mac Mini
  thread_policy_set(mach_thread_self(), THREAD_AFFINITY_POLICY,
                    (thread_policy_t)&policy, THREAD_AFFINITY_POLICY_COUNT);
}

void bind_pcore(int tid) {
    // Set high QoS
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    set_affinity(tid);
}

void bind_ecore(int tid) {
    // Set lower QoS
    pthread_set_qos_class_self_np(QOS_CLASS_UTILITY, 0);
    set_affinity(tid);
}

static void bind_core(int tid) {
  if (tid < PCOR) {
    bind_pcore(tid);
  } else {
    bind_ecore(tid);
  }
}
#endif // __APPLE__

__attribute__((unused))
static void disp_smry(TM *tm) {
  fprintf(stderr, "t%u itrs %" PRIu64 "\n", tm->tid,
          tm->itrs);
}

static void* thread_func(void* arg) {
  thread_id = (u64)arg;

#ifdef __APPLE__
  bind_core(thread_id);
#endif
  TM *tm = tms[thread_id];

  // Wait until after injection to turn these on
  tm->buse = true;
  tm->duse = true;
  tm->bstp = false;

  u64  tick = 0;
  bool busy = tm->tid == 0;
  while (true) {
    #ifdef MEMLOG
    pthread_testcancel();
    #endif
    
    tick += 1;

    // If we know we're not holding our own booty bag, it may have been stolen
    // and returned - try to recover it
    if (!tm->bhld) {
      bbag_recover(tm);
    }

    Loc loc = redex_pop_loc(tm);
    if (loc) {
      busy = set_busy(busy);
      
      Pair pair = take_pair(loc);
      
      // If we just emptied a stolen bag, return it
      if (bbag_looted(tm)) {
        bbag_return(tm);
      }

      interact(tm, pair_neg(pair), pair_pos(pair));
    } else {
      if (busy && can_idle(tm)) {
        busy = set_idle(busy);
      }
      if (!try_steal(tm)) {
        sched_yield();
        if (!busy && timeout(tick))
          break;
      }
    }
  }

  #ifdef SUMMARY
  disp_smry(tm);
  show_def_cnts();
  #endif

  return NULL;
}

static void parallel_normalize() {
  atomic_store_explicit(&net.idle, TPC-1, memory_order_relaxed);

  for (u64 i = 0; i < TPC; i++) {
    pthread_create(&threads[i], NULL, thread_func, (void*)i);
  }
  for (u64 i = 0; i < TPC; i++) {
    pthread_join(threads[i], NULL);
  }
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

    #ifdef SUMMARY
    disp_smry(tm);
    show_def_cnts();

    //hn_dump();
    //fprintf(stderr, "alloc_cnt: %u\n", alloc_cnt);

    #endif

  } else {
    parallel_normalize();
  }

#ifdef MEMLOG
  mlog_dump("memlog.txt");
#endif

  return get(0);
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
static const char* term_str(char* buf, Term term) {
  snprintf(buf, 64, "%s lab:%u loc:%u", tag_to_str(term_tag(term)),
           term_lab(term), term_loc(term));
  return buf;
}

static void dump_term(Loc loc) {
  Term term = get(loc);
  fprintf(stderr, "%04u %03u %03u %s\n", loc, term_loc(term), term_lab(term),
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
