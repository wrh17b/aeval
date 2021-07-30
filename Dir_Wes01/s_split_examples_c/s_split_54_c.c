int main()
{
  int x=0;int y=8000; int z=0;
  while(x!=16000) {
    int tx=x+1;
    int ty=y-1;
    int tz=z-1;
    if(x>=8000) ty=y+1;
    if(x<8000) tz=z+1;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(y==8000&&z==0);
}
