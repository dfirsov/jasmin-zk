#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <assert.h>

#include "../schnorr_protocol.h"

int main(void)
{
  bignum commitment_p, random_power_p, challenge_p, response_p;
  uint64_t result_p[1];
  
  __commitment(commitment_p, random_power_p);
  __challenge(challenge_p);
  __response(random_power_p, challenge_p, response_p);
  __verify(commitment_p, challenge_p, response_p, result_p);

  printf("0x%ld\n", result_p[0]);
  return 0;
}
