int main()
{
  int x=50000;int y=0;
  while(y<=50000) {
    int tx = x;
    int ty=y+1;
    if(y>=x) tx=x+5;
    if(y>=x) ty=y;
    x=tx;
    y=ty;
  }
  assert((x-y)<=5);
}
