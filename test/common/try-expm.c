#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <gmp.h>

#include "try-anything.h"

// ////////////////////////////////////////////////////////////////////////////

#if 0
void print(char *str1, uint64_t *array)
{
  int i;

  printf("%s", str1);

  for(i=0; i<(NLIMBS-1); i++)
  { printf("0x%016" PRIx64 "*2**%d + ", array[i], i*64); }
  printf("0x%016" PRIx64 "*2**%d\n", array[NLIMBS-1], (NLIMBS-1)*64);
}
#endif

// ////////////////////////////////////////////////////////////////////////////

typedef struct state {

  uint64_t *result;
  uint64_t *base;
  uint64_t *exp;
  uint64_t *mod;

  uint64_t *result2;
  uint64_t *base2;
  uint64_t *exp2;
  uint64_t *mod2;

  uint64_t len;

  void* free[8];
} state;

state* preallocate(void);
void allocate(state*);
void deallocate(state**);
void unalign(state*);
void realign(state*);
void test(unsigned char*,state *);

// ////////////////////////////////////////////////////////////////////////////

#define LOOPS 512

// ////////////////////////////////////////////////////////////////////////////

state* preallocate(void)
{
  state *s = calloc(sizeof(state), 1);
  return s;
}

// ////////////////////////////////////////////////////////////////////////////

void allocate(state *s)
{
  unsigned long long alloclen = (NLIMBS*sizeof(uint64_t)) + (CANARY_LENGTH*2) + sizeof(uint64_t);

  s->result  = alignedcalloc_u64(&(s->free[0]), alloclen);
  s->base    = alignedcalloc_u64(&(s->free[1]), alloclen);
  s->exp     = alignedcalloc_u64(&(s->free[2]), alloclen);
  s->mod     = alignedcalloc_u64(&(s->free[3]), alloclen);
  s->result2 = alignedcalloc_u64(&(s->free[4]), alloclen);
  s->base2   = alignedcalloc_u64(&(s->free[5]), alloclen);
  s->exp2    = alignedcalloc_u64(&(s->free[6]), alloclen);
  s->mod2    = alignedcalloc_u64(&(s->free[7]), alloclen);

  s->len     = (NLIMBS*sizeof(uint64_t));
}

void deallocate(state **_s)
{
  int i;
  state *s = *_s;

  for(i=0; i<8; i++)
  { free(s->free[i]); }
  free(s);
  *_s = NULL;
}

void unalign(state *s)
{
  s->result  = (uint64_t*) (((void*)(s->result)) + 1);
  s->base    = (uint64_t*) (((void*)(s->base)) + 1);
  s->exp     = (uint64_t*) (((void*)(s->exp)) + 1);
  s->mod     = (uint64_t*) (((void*)(s->mod)) + 1);
  s->result2 = (uint64_t*) (((void*)(s->result2)) + 1);
  s->base2   = (uint64_t*) (((void*)(s->base2)) + 1);
  s->exp2    = (uint64_t*) (((void*)(s->exp2)) + 1);
  s->mod2    = (uint64_t*) (((void*)(s->mod2)) + 1);
}

void realign(state *s)
{
  s->result  = (uint64_t*) (((void*)(s->result)) - 1);
  s->base    = (uint64_t*) (((void*)(s->base)) - 1);
  s->exp     = (uint64_t*) (((void*)(s->exp)) - 1);
  s->mod     = (uint64_t*) (((void*)(s->mod)) - 1);
  s->result2 = (uint64_t*) (((void*)(s->result2)) - 1);
  s->base2   = (uint64_t*) (((void*)(s->base2)) - 1);
  s->exp2    = (uint64_t*) (((void*)(s->exp2)) - 1);
  s->mod2    = (uint64_t*) (((void*)(s->mod2)) - 1);
}

extern void expm_test(uint64_t*,uint64_t*,uint64_t*,uint64_t*);

void reduce(uint64_t *base, uint64_t *mod)
{
  mpz_t m_base, m_mod;
  size_t base_count;

	mpz_init2(m_base, NLIMBS*64);
	mpz_init2(m_mod,  NLIMBS*64);

  mpz_import(m_base,  NLIMBS, -1, sizeof(uint64_t), 0, 0, base);
  mpz_import(m_mod,  NLIMBS, -1, sizeof(uint64_t), 0, 0, mod);

  mpz_mod(m_base, m_base, m_mod);

  memset(base, 0, NLIMBS*sizeof(uint64_t));
  mpz_export(base, &base_count, -1, sizeof(uint64_t), 0, 0, m_base);
  mpz_clears(m_base, m_mod,NULL);
}

void test(unsigned char *checksum_state, state *_s)
{
  unsigned long long loop;
  state s = *_s;
  
  for (loop = 0;loop < LOOPS;++loop)
  {
    //
    output_prepare_u64(s.result2, s.result, s.len);
    input_prepare_u64(s.base2, s.base, s.len);
    input_prepare_u64(s.exp2,  s.exp,  s.len);
    input_prepare_u64(s.mod2,  s.mod,  s.len);

    reduce(s.base,  s.mod);
    memcpy(s.base2, s.base, s.len);

   expm_test(s.result, s.base, s.exp, s.mod);

    checksum_u64(checksum_state, s.result, s.len);
    output_compare_u64(s.result2, s.result, s.len, "expm - result");
    input_compare_u64(s.base2, s.base, s.len, "expm - base");
    input_compare_u64(s.exp2,  s.exp,  s.len, "expm - exp");
    input_compare_u64(s.mod2,  s.mod,  s.len, "expm - mod");

    //
    double_canary_u64(s.result2, s.result, s.len);
    double_canary_u64(s.base2,   s.base,   s.len);
    double_canary_u64(s.exp2,    s.exp,    s.len);
    double_canary_u64(s.mod2,    s.mod,    s.len);

   expm_test(s.result2, s.base2, s.exp2, s.mod2);

    if (memcmp(s.result2, s.result, s.len) != 0) fail("expm is nondeterministic");
  }
}

#include "try-anything.c"

int main()
{
  return try_anything_main();
}

