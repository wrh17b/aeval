int main()
{
  int x=0;int y=0;
  while(x!=15000) {
    int tx=x+1;
    int ty=y-2;
    if(x>=7500){
      if(x>=12500)
        ty=y-2;
      else
        ty=y+1;
    }else{
      if(x>=2500)
        ty=y+1;
      else
        ty=y-2;
    }
    x=tx;
    y=ty;
  }
  assert(y==0);
}
