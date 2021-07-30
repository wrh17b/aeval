int main()
{
  int x=0; int y=10; int z=0;
  while(unknown()) {
    int tx = (x+1)%10;
    int ty = (y-1)%10;
    int tz=z+1;
    if(x==y) tz=0;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(z<=5);
}
