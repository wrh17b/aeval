int main()
{
  int x=0;int y=0;
  while(x<100000000) {
    int tx=x+1;
    int ty=0;
    if(x>=50000000){
      if(x>=100000000)
        ty=y;
      else
        y=y+1;
    }
    x=tx;
    y=ty;
  }
  assert(y=50000000);
}
