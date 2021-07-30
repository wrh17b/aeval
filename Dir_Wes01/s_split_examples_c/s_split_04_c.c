int main()
{
  int x=0; int y=0; int z =0;
  while(x<3452365) {
    int tx = x + 1;
    int ty=y+x;
    int tz=z;
    if(y>x) tz=z+1;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(z>0);
}
