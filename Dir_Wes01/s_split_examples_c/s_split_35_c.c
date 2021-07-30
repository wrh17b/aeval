int main()
{
  int x=0;int y=unknown(); int z=unknown(); int w=0;
  if(y<=z) return 0;
  while(x<=y) {
    int tx = x+5;
    int ty=y+3;
    int tz=z+1;
    int tw = w-1;
    if(x<z) tw=w+1;
    x=tx;
    y=ty;
    z=tz;
    w=tw;
  }
  assert(w<=0);
}
