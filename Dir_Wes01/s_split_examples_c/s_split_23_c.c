int main()
{
  int x=1000; int z=100;
  while(unknown()) {
    int tx = x-1;
    int tz=z+1;
    if((x/10)<z) tx=x+1;
    if((x/10)<z) tz=x-1;
    x=tx;
    z=tz;
  }
  assert(z<x);
}
