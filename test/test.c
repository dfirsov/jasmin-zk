#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <string.h>


extern void __addm(uint64_t* r, uint64_t* p, uint64_t* a, uint64_t* b);



uint64_t tadd[][4][64] =
 {
  {  { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
     , { 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull, 0ull , 0ull , 0ull , 0ull }
   }
 };


void func2()
{
   int count = 0;
   for(count=0; count < 0XFFFFF; count++);
 
   return;
}
 
void func1(void)
{
   int count = 0;
   for(count=0; count < 0XFF; count++)
       func2();
 
   return;
}
 
int main(void)
{
  uint64_t result[64]; 
  int i, b,a;

  printf("Testing ADDM: ");
  b = 1;
  for (i=0; i<sizeof(tadd)/sizeof(tadd[0]); i++) {
    __addm(result, tadd[i][0], tadd[i][1], tadd[i][2]);
   a = memcmp(result, tadd[i][3], sizeof(tadd[i][3]));
   b =   b && !a;
  }
  if (b) printf("OK\n"); else printf("FAIL!\n");

  
    printf("\n Hello World! \n");
    func1();
    func2();
    return 0;
}
