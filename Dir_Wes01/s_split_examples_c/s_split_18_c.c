int main()
{
  int x=1; int y=1;
  while(x<=16) {
    int tx = x*2;
    int ty=x%16;
    if(y<16) ty=y*2;
    x=tx;
    y=ty;
  }
  assert(y==0);
}
