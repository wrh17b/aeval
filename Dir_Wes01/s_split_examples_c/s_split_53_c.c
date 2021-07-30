int main()
{
  int x=0;int y=0; int z=0; int w=500;
  while(y!=2250) {
    int tx=(x+1)%1000;
    int ty=y+1;
    int tz=z-1;
    int tw=w-1;
    if(x<500) tz=z+1;
    if(x>=500) tw=w+1;
    x=tx;
    y=ty;
    z=tz;
    w=tw;
  }
  assert(z==w);
}
