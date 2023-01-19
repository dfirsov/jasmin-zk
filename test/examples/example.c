#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <assert.h>

#include "example.h"

extern void expm_test(uint64_t *result, uint64_t *base, uint64_t *exp, uint64_t *mod);

#define NLIMBS 32

void load(uint64_t *dest, uint8_t *src)
{
  int i, j;
  for(i=0, j=(NLIMBS-1); i<NLIMBS; i++, j--)
  {
    dest[i] = (((uint64_t) src[(j*8)  ]) << 56) |
              (((uint64_t) src[(j*8)+1]) << 48) |
              (((uint64_t) src[(j*8)+2]) << 40) |
              (((uint64_t) src[(j*8)+3]) << 32) |
              (((uint64_t) src[(j*8)+4]) << 24) |
              (((uint64_t) src[(j*8)+5]) << 16) |
              (((uint64_t) src[(j*8)+6]) <<  8) |
              (((uint64_t) src[(j*8)+7])      ) ;
  }
}

void print(char *str1, char *str2, uint64_t *array)
{
  int i;

  printf("%s", str1);

  for(i=0; i<(NLIMBS-1); i++)
  { printf("0x%016" PRIx64 ", ", array[i]); }
  printf("0x%016" PRIx64 "\n", array[NLIMBS-1]);
  printf("%s\n", str2);
}

int main(void)
{
  int i;
  uint64_t result1[32], result2[32];
  uint64_t base[32], exp1[32], exp2[32], mod[32];

  base[0] = 0x1111111111111111;
  for(i=1; i<32; i++)
  { base[i] = base[i-1] + base[0]; }

  load(exp1, exp_e);
  load(exp2, exp_d);
  load(mod,  modulus);
  
  print("uint64_t base[32] = ", "};", base);
  print("uint64_t exp1[32] = ", "};", exp1);
  print("uint64_t exp2[32] = ", "};", exp2);
  print("uint64_t mod[32]  = ", "};", mod);

  expm_test(result1, base, exp1, mod);
  expm_test(result2, result1, exp2, mod);

  print("uint64_t result1[32] = ", "};", result1);
  print("uint64_t result2[32] = ", "};", result2);

  assert(memcmp(base,result2,sizeof(base)) == 0);

	return 0;
}


