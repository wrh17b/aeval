int main()
{
  int x=0; int y=0; int z=0; int w=0;
  while(y!=1000000) {
    int tx = (x+1)%2000;
    int ty=y+1;
    int tz=z;
    int tw=w+1;
    if(x<1000) tz=z+1;
    if(x<1000) tw=w;
    x=tx;
    z=tz;
    y=ty;
    w=tw;
  }
  assert(w==z);
}
