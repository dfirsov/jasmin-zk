#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <string.h>

#define NLIMBS 32
void print_result(uint64_t* x);


extern void __expm(uint64_t* r, uint64_t* p, uint64_t* rr, uint64_t* a, uint64_t* b);



uint64_t texp[][5][64] =
 {
  {  { 13ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 4ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 5ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 1ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 5ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
   }
 };







int main(void) {
  uint64_t result[32]; 
  int i, b,a;
  __expm(result, texp[0][0], texp[0][1],texp[0][2], texp[0][3]);  
  return 0;
}




void print_result(uint64_t* x) {
  printf("echo: ");
  for(int i = 0; i < NLIMBS; i++){
    printf("%lu ", *(x+(i*sizeof(uint64_t)/sizeof(uint64_t))));
  }
  printf("\n");  
}
