int main()
{
  int x=0; int y=1; int z=0; int w=1;
  while(x!=10) {
    int tx = x+1;
    int ty=y+2;
    int tw=1-w;
    int tz=0;
    if(((x+y)%2)==w) tz=z+1;
    x=tx;
    y=ty;
    z=tz;
    w=tw;
  }
  assert(x==z);
}
