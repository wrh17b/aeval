int main()
{
  int x=0; int y=767976; int z=0;
  while(x<280275) {
    int tx = x+1;
    int ty=y-1;
    int tz=z;
    if((x-y)%3==1) tz=z+3;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(z>=280275);
}
