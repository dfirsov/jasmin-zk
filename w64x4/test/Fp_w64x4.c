#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <string.h>

#define NLIMBS 4
void print_result(uint64_t* x);


extern void __addm(uint64_t* p, uint64_t* a, uint64_t* b);
extern void __mulm(uint64_t* p, uint64_t* a, uint64_t* b);
extern void __expm(uint64_t* p, uint64_t* a, uint64_t* b);


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
    , { 5ull , 5ull , 5ull , 5ull }
   }
 , {  { 2ull , 0ull , 0ull , 0ull }
    , { 5ull , 0ull , 0ull , 0ull }
    , { 10ull , 0ull , 0ull , 0ull }
   }
 };


uint64_t texp[][3][4] =
 {
  {  { 2ull , 3ull , 0ull , 0ull }     // represents: (2*(2^64)^0 + 3 * (2^64)^1 )  
     , { 2ull , 0ull , 0ull , 0ull }   // represnets: 2
     , { 4ull , 12ull , 9ull , 0ull }  // represents: (4*(2^64)^0 + 12 * (2^64)^1 + 9 * (2^64)^2) %% (2^255 - 19)
   }
 , {  { 2ull , 3ull , 4ull , 5ull }
    , { 0ull , 0ull , 0ull , 0ull }
    , { 1ull , 0ull , 0ull , 0ull }
   }
 , {  { 9ull , 9ull , 9ull , 9ull }
    , { 1ull , 0ull , 0ull , 0ull }
    , { 9ull , 9ull , 9ull , 9ull }
   }
  , {  { 123123ull , 0ull , 0ull , 0ull } 
    , { 500ull , 0ull , 0ull , 0ull }
    , { 11117009174922751360ull , 13416253971750811784ull , 7609481284495345029ull , 5760204542479289991ull }
       /*  (123123^500) %% (2^255 - 19) = 11117009174922751360 * (2^64)^ 0 
	   + 13416253971750811784 * (2^64)^1  
	   + 7609481284495345029 * (2^64)^2 
	   + 5760204542479289991 * (2^64)^3 */
   }
 };




int main() {
  uint64_t result[4]; 
  int i, b,a;

  printf("Testing ADDM: ");
  b = 1;
  for (i=0; i<sizeof(tadd)/sizeof(tadd[0]); i++) {
   __addm(result, tadd[i][0], tadd[i][1]);
   a = memcmp(result, tadd[i][2], sizeof(tadd[i][2]));
   b =   b && !a;
  }
  if (b) printf("OK\n"); else printf("FAIL!\n");

  
  printf("Testing MULM: ");
  b = 1;
  for (i=0; i<sizeof(tmul)/sizeof(tmul[0]); i++) {
   __mulm(result, tmul[i][0], tmul[i][1]);
   a = memcmp(result, tmul[i][2], sizeof(tmul[i][2]));
   b =   b && !a;
  }
  if (b) printf("OK\n"); else printf("FAIL!\n");

  
  printf("Testing EXPM: ");
  b = 1;
  for (i=0; i<sizeof(texp)/sizeof(texp[0]); i++) {
   __expm(result, texp[i][0], texp[i][1]);
   a = memcmp(result, texp[i][2], sizeof(texp[i][2])/ sizeof(texp[i][2][0]));
   b =   b && !a;
  }
  if (b) printf("OK\n"); else printf("FAIL!\n");
  
  return 0;
}




void print_result(uint64_t* x) {
  printf("echo: ");
  for(int i = 0; i < NLIMBS; i++){
    printf("%lu ", *(x+(i*sizeof(uint64_t)/sizeof(uint64_t))));
  }
  printf("\n");  
}
