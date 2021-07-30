int main()
{
  int x=0;int c=5000; int y=c;
  while(x!=2*c) {
    int tx=x+1;
    int ty=y-1;
    if(x>=c) ty=y+1;
    x=tx;
    y=ty;
  }
  assert(y==c);
}
