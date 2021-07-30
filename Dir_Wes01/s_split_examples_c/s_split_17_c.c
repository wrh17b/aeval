int main()
{
  int x=unkown(); int z=unkown(); int v=0; int w=0;
  if(x<=z) return 0;
  while(v<=1000) {
    int tx = x+1;
    int tz=z+2;
    int tv = v;
    int tw=w+1;
    if(x<z) tv=v+1;
    if(x<z) tw=w;
    x=tx;
    v=tv;
    w=tw;
    z=tz;
  }
  assert(w>0);
}
