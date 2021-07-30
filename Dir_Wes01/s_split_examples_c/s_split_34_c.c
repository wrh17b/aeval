int main()
{
  int x=0;int y=1;
  while(unknown()) {
    int tx = x+y;
    int ty=-y;
    if((tx>-100)&&(tx<100)) ty=y;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(x>=-100 && x<=100);
}
