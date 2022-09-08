#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>

#include "api.h"

int main()
{
  int i;
  uint64_t t;
  uint8_t v;

  t = 0;
  for(i=0; i<64; i++)
  { v = randombit();
    assert(v == 0 || v == 1);
    t |= ( ((uint64_t) v) << i );
  }

  printf("%" PRIx64 "\n", t);

  return 0;
}
