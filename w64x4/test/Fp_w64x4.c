#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <string.h>

extern uint64_t* __addm(uint64_t* p, uint64_t* a, uint64_t* b);
extern uint64_t* __mulm(uint64_t* p, uint64_t* a, uint64_t* b);
extern uint64_t* __expm(uint64_t* p, uint64_t* a, uint64_t* b);


uint64_t tadd[][3][4] =
 {
   {  { 0ull , 0ull , 0ull , 0ull }
    , { 0ull , 0ull , 0ull , 0ull }
    , { 0ull , 0ull , 0ull , 0ull }
   }
 , {  { 1ull , 1ull , 1ull , 1ull }
    , { 1ull , 1ull , 1ull , 1ull }
    , { 2ull , 2ull , 2ull , 2ull }
   }
 };



uint64_t tmul[][3][4] =
 {
   {  { 0ull , 0ull , 0ull , 0ull }
    , { 0ull , 0ull , 0ull , 0ull }
    , { 0ull , 0ull , 0ull , 0ull }
   }
 , {  { 1ull , 0ull , 0ull , 0ull }
    , { 5ull , 5ull , 5ull , 5ull }
    , { 1ull , 0ull , 0ull , 0ull }
   }

 };


uint64_t texp[][3][4] =
 {
   {  { 2ull , 3ull , 0ull , 0ull }
    , { 2ull , 0ull , 0ull , 0ull }
    , { 96ull , 0ull , 0ull , 0ull }
   }

 };




int main() {
  uint64_t result[4]; 
  int i, b,a;

  /* printf("Testing ADDM: "); */
  /* b = 1; */
  /* for (i=0; i<2; i++) { */
  /*  __addm(result, tadd[i][0], tadd[i][1]); */
  /*  a = memcmp(result, tadd[i][2], sizeof(tadd[i][2])); */
  /*  b = b && !a; */
  /* } */
  /* if (b) printf("OK\n"); else printf("FAIL!\n"); */


  __expm(result, texp[0][0], texp[0][1]);
  printf("%lu\n", *(result+(0*sizeof(uint64_t)/sizeof(uint64_t))));

  
  /* printf("Testing MULM: "); */
  /* b = 1; */
  /* for (i=0; i<2; i++) { */
  /*  __mulm(result, tmul[i][0], tmul[i][1]); */
  /*  a = memcmp(result, tmul[i][2], sizeof(tmul[i][2])); */
  /*  b = b && !a; */
  /* } */
  /* if (b) printf("OK\n"); else printf("FAIL!\n"); */

  

  return 0;
}


