int main()
{
  int x=1; int y=0; int z =0;
  while(y!=342341341) {
    int tx = x*-1;
    int ty=y;
    int tz=z;
    if(x>0) ty=y+1;
    if(x>0) tz=z;
    else tz=z+1;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(z==342341341);
}
