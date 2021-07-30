int main()
{
  int x=0; int y=unknown(); int z=0;
  if(y<0) return 0;
  while(x<=(1000*(y+1))) {
    int tx = x+1;
    int tz=z;
    if(y==(x/1000)) tz=z+1;
    x=tx;
    z=tz;
  }
  assert(z==1000);
}
