#include <stdio.h>
#include <stdint.h>
#include <assert.h>


extern uint64_t* __addm(uint64_t* p, uint64_t* a, uint64_t* b);


int main() {
  uint64_t* r;

  uint64_t x[4] = { 5ull, 0ull, 0ull, 0ull };
  uint64_t y[4] = { 7ull, 0ull, 0ull, 0ull };
  uint64_t result[4];
 
  r = __addm(result, x, y);

  printf("%lu\n", (*result));
  printf("%lu\n", *(result + (sizeof(unsigned long)/sizeof(uint64_t))));

  return 0;
}


