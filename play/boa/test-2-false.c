#include <stdio.h>
extern int nd ();

int main(int argc, char**argv) 
{
  int i;
  int a[10];
  for (i = 0; i < 10; i++)
  {
    a[i] = 9999;
  }


  // trick llvm so that it cannot detect overflow
  printf("%d\n", a[(nd()>0?i-1:i)]);
  return 42;

}
