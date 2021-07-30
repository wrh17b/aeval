int main()
{
  int x=-100; int z=-100;
  while(z<0) {
    int tx = (x+1)%5;
    int tz=z%4;
    if(z<4) tz=z+1;
    x=tx;
    z=tz;
  }
  assert(x==z);
}
