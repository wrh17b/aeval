int main()
{
  int x=0; int y=unknown(); int z=0;
  if(y<100) return 0;
  while(y!=0) {
    int tx = x+1;
    int ty=y-1;
    int tz=z;
    if(y<=(x/50)) tz=z+1;
    x=tx;
    y=ty
    z=tz;
  }
  assert(z>0);
}
