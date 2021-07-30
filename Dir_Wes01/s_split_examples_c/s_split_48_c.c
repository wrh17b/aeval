int main()
{
  int x=0;int y=0;
  while(x!=10000) {
    int tx=x+1;
    int ty=y-4;
    if(x<5000){
      if(x>=4000)
        ty=y+4;
      else
        ty=y+1;
    }
    else{
      if(x>=6000)
        ty=y-1;
      else
        ty=y-4;
    }
    x=tx;
    y=ty;
  }
  assert(y==0);
}
