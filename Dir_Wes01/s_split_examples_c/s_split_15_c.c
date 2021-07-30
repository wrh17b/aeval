int main()
{
  int x=0; int y=0; int z=0;
  do{
    int tx = (x+1)%1000;
    int ty=y+1;
    int tz=z;
    if(x<500) tz=z+2;
    x=tx;
    y=ty;
    z=tz;
  }while(x!=0);
  assert(y==z);
}
