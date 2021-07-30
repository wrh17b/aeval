int main()
{
  int x=0; int y=0; int z=0; int w=0;
  while(x<=100) {
    int tx = x+1;
    int ty=y+x;
    int tz=z;
    int tw=w+1;
    if((y-(10*x))>0) tz=z+1;
    if((y-(10*x))>0) tw=w;
    x=tx;
    y=ty
    z=tz;
    w=tw;
  }
  assert(z>w);
}
