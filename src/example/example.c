#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <assert.h>

#include "../schnorr_protocol.h"


void print(uint64_t *array)
{
  int i;

  for(i=0; i<(NLIMBS-1); i++)
  { printf("0x%016" PRIx64 ", ", array[i]); }
  printf("0x%016" PRIx64 "\n", array[NLIMBS-1]);
}

int main(void)
{
  bignum commitment_p, random_power_p, challenge_p, response_p;
  uint64_t result_p[1];

  printf("\n*** Prover commits: ***\n");
  __commitment(commitment_p, random_power_p);
  printf("\nCOMMITMENT:\n");  
  print(commitment_p);

  printf("\nSECRET POWER:\n");  
  print(random_power_p);

  printf("\n*** Verifier challenges: ***\n");
  __challenge(challenge_p);
  printf("\nCHALLENGE:\n");  
  print(challenge_p);

  printf("\n*** Prover responds: ***\n");
  __response(random_power_p, challenge_p, response_p);
  printf("\nRESPONSE:\n"); 
  print(response_p); 

  printf("\n*** Verifier decides: ***\n");
  __verify(commitment_p, challenge_p, response_p, result_p);

  printf("0x%016" PRIx64 "\n\n", result_p[0]);

  return 0;
}
