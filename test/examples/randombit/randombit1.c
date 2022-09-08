#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>

#include "api.h"

int main()
{
  int l, i;
  uint64_t t;
  uint8_t v;

  for(l=0; l<1000; l++)
  {
    t = 0;
    for(i=0; i<64; i++)
    { v = randombit();
      assert(v == 0 || v == 1);
      t |= ( ((uint64_t) v) << i );
    }
  }

  return 0;
}
