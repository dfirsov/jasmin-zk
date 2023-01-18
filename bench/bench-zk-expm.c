#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>

//

#define OP 1

//

#include "config.h"
#include "cpucycles.c"
#include "median.c"
#include "alignedcalloc.c"
#include "randombytes.c"

#include "zk-expm.c"

//

int main(int argc, char**argv)
{
  int run, loop, i;
  uint64_t cycles[TIMINGS];
  uint64_t cycles_counts[OP][LOOPS];
  uint64_t cycles_expm[RUNS];

  uint8_t *_results,  *results;  uint8_t *result;
  uint8_t *_bases,    *bases;    uint8_t *base;
  uint8_t *_exps,     *exps;     uint8_t *exp;
  uint8_t *_barretts, *barretts; uint8_t *barrett;
  uint8_t *_mods,     *mods;     uint8_t *mod;
  size_t len, b_len;

  len   = alignedcalloc_step(   NLIMBS*sizeof(uint64_t) );
  b_len = alignedcalloc_step( 2*NLIMBS*sizeof(uint64_t) );

  results  = alignedcalloc(&_results,    len * TIMINGS);
  bases    = alignedcalloc(&_bases,      len * TIMINGS);
  exps     = alignedcalloc(&_exps,       len * TIMINGS);
  barretts = alignedcalloc(&_barretts, b_len * TIMINGS);
  mods     = alignedcalloc(&_mods,       len * TIMINGS);

  mpz_t m_base;
  mpz_t m_mod;
  size_t count;

  mpz_init2(m_base, NLIMBS*64);
  mpz_init2(m_mod, NLIMBS*64);

  // init with random
  result  = results;
  base    = bases;
  exp     = exps;
  barrett = barretts;
  mod     = mods;

  for(i=0; i<TIMINGS; i++, result += len, base += len, exp += len, barrett += b_len, mod += len)
  { randombytes(base, NLIMBS*sizeof(uint64_t));
    mpz_import(m_base, NLIMBS, -1, sizeof(uint64_t), 0, 0, base);

    randombytes(mod, NLIMBS*sizeof(uint64_t));
    mpz_import(m_mod, NLIMBS, -1, sizeof(uint64_t), 0, 0, mod);

    mpz_mod(m_base, m_base, m_mod); // ensure the ~same conditions for zk/gmp

    memset(base, 0, NLIMBS*sizeof(uint64_t));
    memset(mod, 0, NLIMBS*sizeof(uint64_t));
    mpz_export(base, &count, -1, sizeof(uint64_t), 0, 0, m_base);
    mpz_export(mod, &count, -1, sizeof(uint64_t), 0, 0, m_mod); // todo: assert and remove 

    expm_precompute_barrett((uint64_t*) barrett, (uint64_t*) mod);

    randombytes(exp, NLIMBS*sizeof(uint64_t));
  }

  mpz_clears(m_base, m_mod, NULL);

  // run
  for(run = 0; run < RUNS; run++)
  {
    for(loop = 0; loop < LOOPS; loop++)
    {
      result  = results;
      base    = bases;
      exp     = exps;
      barrett = barretts;
      mod     = mods;

      for (i = 0; i < TIMINGS; i++, result += len, base += len, exp += len, barrett += b_len, mod += len)
      { cycles[i] = cpucycles();
        zk_expm((uint64_t*)result, (uint64_t*)base, (uint64_t*)exp, (uint64_t*)barrett, (uint64_t*)mod); }
      cycles_counts[0][loop] = cpucycles_median(cycles, TIMINGS);
    }

    median_fr(cycles_counts);

    cycles_expm[run] = cycles_counts[0][0];
  }

  qsort(cycles_expm,RUNS,sizeof(uint64_t),cmp_uint64);

  for(run = 0; run < RUNS; run++)
  { printf("%" PRIu64 "\n", cycles_expm[run]); }

  free(_results);
  free(_bases);
  free(_exps);
  free(_barretts);
  free(_mods);

  return 0;
}

