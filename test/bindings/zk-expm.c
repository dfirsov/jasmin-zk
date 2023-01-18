#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <gmp.h>

extern void zk_expm(
  uint64_t *result,  // NLIMBS
  uint64_t *mod,     // NLIMBS
  uint64_t *base,    // NLIMBS
  uint64_t *barrett, // NLIMBS * 2
  uint64_t *exp      // NLIMBS
);

void expm_precompute_barrett(uint64_t *barrett, uint64_t *mod)
{
  mpz_t m_barrett, m_k, m_mod;
  size_t barrett_count;

  //
  // compute r = floor( 4**k / mod ); export r to an array with 2*NLIMBS
  //

  // set m_k to 4**k
  mpz_init_set_ui(m_k, 1);
  mpz_mul_2exp(m_k, m_k, NLIMBS*64*2);

  // load m_mod
	mpz_init2(m_mod, NLIMBS*64);
  mpz_import(m_mod,  NLIMBS, -1, sizeof(uint64_t), 0, 0, mod);

  // init m_barrett
	mpz_init2(m_barrett, NLIMBS*64*2);

  // r = floor( 4**k / mod )
  mpz_fdiv_q(m_barrett, m_k, m_mod);

  // export barrett -- will be used as input for the jasmin implementation)
  memset(barrett, 0, sizeof(uint64_t)*NLIMBS*2);
  mpz_export(barrett, &barrett_count, -1, sizeof(uint64_t), 0, 0, m_barrett);

  mpz_clears(m_barrett,m_k,m_mod,NULL);
}

void expm_test(uint64_t *result, uint64_t *base, uint64_t *exp, uint64_t *mod)
{
  uint64_t barrett[NLIMBS*2];
  expm_precompute_barrett(barrett, mod);
  zk_expm(result, base, exp, barrett, mod);
}

