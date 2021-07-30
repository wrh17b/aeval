int main()
{
  int x=-10000;int y=0;
  while(x<0) {
    int tx = x;
    int ty=y+2;
    if(y>=x) tx=x+1;
    if(y>=x) ty=-1 * x;
    x=tx;
    y=ty;
  }
  assert(x>=(y-1));
}
