int main()
{
  int x=0;int y=7500;
  while(x!=10000) {
    int tx = x+1;
    int ty=y;
    if(0==x%2) tx=x+2;
    if(x>=5000) ty=y+1;
    x=tx;
    y=ty;
  }
  assert(y==10000);
}
