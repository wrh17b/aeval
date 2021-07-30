int main()
{
  int x=0;int y=0;int z=0;
  while(x<=100) {
    int tx = x+1;
    int ty=y;
    int tz=z+1;
    if(x>100||(x%10)<5) ty=y+1;
    if(x>100||(x%10)<5) tz=z;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(y>z);
}
