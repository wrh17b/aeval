int main()
{
  int x=unknown(); int y=unknown(); int z =unknown(); int v=0
  if(x<=y) return 0;
  if(y<=z) return 0;
  while((z-x)<=72531) {
    int tx = x+1;
    int ty=y+3;
    int tz=z+2;
    int tv=v;
    if(x<y) tv=v+1;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(v>0);
}
