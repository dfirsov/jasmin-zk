#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <string.h>

#define NLIMBS 4
void print_result(uint64_t* x);


extern void __addm(uint64_t* r, uint64_t* p, uint64_t* a, uint64_t* b);
extern void __mulm(uint64_t* r, uint64_t* p, uint64_t* a, uint64_t* b);
extern void __expm(uint64_t* r, uint64_t* p, uint64_t* a, uint64_t* b);


/* uint64_t tadd[][4][64] = */
/*  { */
/*   {  { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull } */
/*      , { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull } */
/*      , { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull } */
/*      , { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull } */
/*    } */
/*  }; */

uint64_t tmul[][4][64] =
 {
  {  { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
   }
 };


uint64_t texp[][4][64] =
 {
  {  { 13ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 5ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 1ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 5ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
   }
 };





/* uint64_t tmul[][4][4] = */
/*  { */
/*    {  { 7ull , 0ull , 0ull , 0ull } */
/*     , { 0ull , 0ull , 0ull , 0ull } */
/*     , { 0ull , 0ull , 0ull , 0ull } */
/*     , { 0ull , 0ull , 0ull , 0ull } */
/*    } */
/*  , {  { 13ull , 13ull , 13ull , 13ull } */
/*     , { 1ull , 1ull , 1ull , 1ull } */
/*     , { 1ull , 1ull , 1ull , 1ull } */
/*     , { 1ull , 1ull , 1ull , 1ull } */
/*    } */
/*  , {  { 5ull , 0ull , 0ull , 0ull } */
/*     , { 3ull , 0ull , 0ull , 0ull } */
/*     , { 3ull , 0ull , 0ull , 0ull } */
/*     , { 4ull , 0ull , 0ull , 0ull } */
/*    } */
/*  , {  { 100ull , 0ull , 0ull , 0ull } */
/*     , { 50ull , 0ull , 0ull , 0ull } */
/*     , { 20ull , 0ull , 0ull , 0ull } */
/*     , { 0ull , 0ull , 0ull , 0ull } */
/*    } */
/*  }; */



/* uint64_t texp[][3][4] = */
/*  { */
/*   {  { 2ull , 3ull , 0ull , 0ull }     // represents: (2*(2^64)^0 + 3 * (2^64)^1 )   */
/*      , { 2ull , 0ull , 0ull , 0ull }   // represnets: 2 */
/*      , { 4ull , 12ull , 9ull , 0ull }  // represents: (4*(2^64)^0 + 12 * (2^64)^1 + 9 * (2^64)^2) %% (2^255 - 19) */
/*    } */
/*  , {  { 2ull , 3ull , 4ull , 5ull } */
/*     , { 0ull , 0ull , 0ull , 0ull } */
/*     , { 1ull , 0ull , 0ull , 0ull } */
/*    } */
/*  , {  { 9ull , 9ull , 9ull , 9ull } */
/*     , { 1ull , 0ull , 0ull , 0ull } */
/*     , { 9ull , 9ull , 9ull , 9ull } */
/*    } */
/*   , {  { 123123ull , 0ull , 0ull , 0ull }  */
/*     , { 500ull , 0ull , 0ull , 0ull } */
/*     , { 11117009174922751360ull , 13416253971750811784ull , 7609481284495345029ull , 5760204542479289991ull } */
/*        /\*  (123123^500) %% (2^255 - 19) = 11117009174922751360 * (2^64)^ 0  */
/* 	   + 13416253971750811784 * (2^64)^1   */
/* 	   + 7609481284495345029 * (2^64)^2  */
/* 	   + 5760204542479289991 * (2^64)^3 *\/ */
/*    } */
/*  }; */




int main(void) {
  uint64_t result[64]; 
  int i, b,a;

  /* printf("Testing ADDM: "); */
  /* b = 1; */
  /* for (i=0; i<sizeof(tadd)/sizeof(tadd[0]); i++) { */
  /*   __addm(result, tadd[i][0], tadd[i][1], tadd[i][2]); */
  /*  a = memcmp(result, tadd[i][3], sizeof(tadd[i][3])); */
  /*  b =   b && !a; */
  /* } */
  /* if (b) printf("OK\n"); else printf("FAIL!\n"); */


    /* __mulm(result, tmul[3][0], tmul[3][1],tmul[3][2]); */
    /* print_result(result); */
  
  /* printf("Testing MULM: "); */
  /* b = 1; */
  /* for (i=0; i<100000; i++) { */
  /*   __mulm(result, tmul[0][0], tmul[i][1],tmul[0][2]); */
  /*  a = memcmp(result, tmul[0][3], sizeof(tmul[0][3])); */
  /*  b =   b && !a; */
  /* } */
  /* if (b) printf("OK\n"); else printf("FAIL!\n"); */


  printf("Testing EXPM: ");
  b = 1;
  //  for (i=0; i<sizeof(texp)/sizeof(texp[0]); i++) {
  for (i=0; i<1; i++) {
    __expm(result, texp[0][0], texp[0][1],texp[0][2]);
   a = memcmp(result, texp[0][3], sizeof(texp[0][3]));
   b =   b && !a;
  }
  if (b) printf("OK\n"); else printf("FAIL!\n");

  
  print_result(result);  
  
  return 0;
}




void print_result(uint64_t* x) {
  printf("echo: ");
  for(int i = 0; i < NLIMBS; i++){
    printf("%lu ", *(x+(i*sizeof(uint64_t)/sizeof(uint64_t))));
  }
  printf("\n");  
}
