int main()
{
  int x=0; int y=200; int z =400;
  while(y<400) {
    int tx = x + 1;
    int ty=y;
    int tz=z;
    if(x<200) ty++;
    if(x<200) tz=z;
    else tz = z+2
    x=tx;
    y=ty;
    z=tz;
  }
  assert(z==(2*x));
}
