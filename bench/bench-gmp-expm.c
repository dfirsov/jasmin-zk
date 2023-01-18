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
#include "randombytes.c"

//

int main(int argc, char**argv)
{
  int run, loop, i;
  uint64_t cycles[TIMINGS];
  uint64_t results[OP][LOOPS];

  uint64_t cycles_expm[RUNS];

  uint8_t buffer[NLIMBS*8];
  mpz_t m_result[TIMINGS];
  mpz_t m_base[TIMINGS];
  mpz_t m_exp[TIMINGS];
  mpz_t m_mod[TIMINGS];

  // alloc 
  for(i=0; i<TIMINGS; i++)
  { mpz_init2(m_result[i], NLIMBS*64);
    mpz_init2(m_base[i],   NLIMBS*64);
    mpz_init2(m_exp[i],    NLIMBS*64);
    mpz_init2(m_mod[i],    NLIMBS*64);
  }

  // init with random
  for(i=0; i<TIMINGS; i++)
  { randombytes(buffer, NLIMBS*8);
    mpz_import(m_base[i], NLIMBS, -1, sizeof(uint64_t), 0, 0, buffer);

    randombytes(buffer, NLIMBS*8);
    mpz_import(m_mod[i], NLIMBS, -1, sizeof(uint64_t), 0, 0, buffer);

    mpz_mod(m_base[i], m_base[i], m_mod[i]); // ensure the ~same conditions for zk/gmp

    randombytes(buffer, NLIMBS*8);
    mpz_import(m_exp[i], NLIMBS, -1, sizeof(uint64_t), 0, 0, buffer);

    //gmp_printf("0x%Zx \n 0x%Zx \n 0x%Zx \n\n", m_base[i], m_exp[i], m_mod[i]);
  }

  // run
  for(run = 0; run < RUNS; run++)
  {
    for(loop = 0; loop < LOOPS; loop++)
    {
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = cpucycles();
        mpz_powm(m_result[i], m_base[i], m_exp[i], m_mod[i]); }
      results[0][loop] = cpucycles_median(cycles, TIMINGS);

    }

    median_fr(results);

    cycles_expm[run] = results[0][0];
  }

  qsort(cycles_expm,RUNS,sizeof(uint64_t),cmp_uint64);

  for(run = 0; run < RUNS; run++)
  { printf("%" PRIu64 "\n", cycles_expm[run]); }

  for(i=0; i<TIMINGS; i++)
  { mpz_clears(m_result[i], m_base[i], m_exp[i], m_mod[i], NULL); }

  return 0;
}

