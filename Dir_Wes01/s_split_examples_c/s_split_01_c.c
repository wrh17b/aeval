int main()
{
  int x=0; int y=5000;
  while(x!=10000) {
    int tx = x + 1;
    int ty=y;
    if(x>=5000) ty++;
    x=tx;
    y=ty;
  }
  assert(y==x);
}
