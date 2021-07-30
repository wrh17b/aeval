int main()
{
  int x=0;int y=0; int z=0;
  while(unknown()) {
    int tx = x+1;
    int ty=(y+1)%100;
    int tz=z+100;
    if((z/100)==(tx/100)) tz=z;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(x==z+y);
}
