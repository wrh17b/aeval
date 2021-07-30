int main()
{
  int x=0;int y=0; int z=0; int w=0;
  while(y!=999000) {
    int tx=(x+1)%2000;
    int ty=y+1;
    int tz=z;
    int tw=w;
    if(x<1000) tz=z+1;
    if(x>=1000) tz=w+1;
    x=tx;
    y=ty;
    z=tz;
    w=tw;
  }
  assert(1000==z-w);
}
