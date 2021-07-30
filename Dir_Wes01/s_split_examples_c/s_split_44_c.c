int main()
{
  int x=0;int y=1000; int z=2000;
  while(y<2000) {
    int tx=x+1;
    int ty=y;
    int tz=z;
    if(x>=1000) ty=y+1;
    if(y>=2000) tz=z+1;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(x==z);
}
