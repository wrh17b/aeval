int main()
{
  int x=0;int y=0; int z=0;
  while(x<=17650) {
    int tx=x+1;
    int ty=y+1;
    int tz=z+2;
    if(x>=1765) ty=y+2;
    if(y>=5765) tz=z+3;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(z>27650);
}
