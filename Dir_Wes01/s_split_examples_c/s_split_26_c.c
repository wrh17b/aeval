int main()
{
  int x=0; int y=unknown(); int z=0;
  if(y<25) return 0;
  while(x<=(50*y)) {
    int tx = x+1;
    int tz=z;
    if(y>=(x/50)) tz=z+1;
    x=tx;
    z=tz;
  }
  assert(z>0);
}
