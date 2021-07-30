int main()
{
  int x=unknown(); int y=unknown(); int z=0;
  if(x!=0&&x!=1) return 0;
  if(y!=0&&y!=1) return 0;
  while(x<=400) {
    int tx = x+2;
    int ty = y+3;
    int tz=z;
    if((x%2)==(y%2)) tz=z+1;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(z>=100);
}
