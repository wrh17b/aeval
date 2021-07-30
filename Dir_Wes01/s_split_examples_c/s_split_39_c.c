int main()
{
  int x=0;int z=0;
  while(z<=50) {
    int tx = x/10;
    int tz=z+1;
    if((x*5)<z) tx=x+1;
    if((x*5)<z) tz=z;
    x=tx;
    z=tz;
  }
  assert(z>x);
}
