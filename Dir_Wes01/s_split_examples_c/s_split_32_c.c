int main()
{
  int x=unknown();int y=0; int z=unknown(); int w=1;
  if(z<!=0&&z!=1) return 0;
  if(x!=z) return 0;
  while(x<=10) {
    int tx = x+1;
    int ty=y+x-3;
    int tz=z-1;
    int tw=w-1;
    if(z==x%2) tw=w+y;
    x=tx;
    y=ty;
    z=tz;
    w=tw;
  }
  assert(w>=0);
}
