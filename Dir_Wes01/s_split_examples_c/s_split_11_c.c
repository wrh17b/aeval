int main()
{
  int x=unknown(); int y=unknown(); int z=unknown();
  if(x>=0) return 0;
  if(y <= x) return 0;
  if(z!=0 && z!=1) return 0;
  while(x<=54932) {
    int tx = x+1;
    int ty=y;
    if(x$2==z) ty=y+2;
    x=tx;
    y=ty;
  }
  assert(y>54932);
}
