int main()
{
  int x=0;int y=unknown();
  while(x<2000) {
    int tx=x+5;
    int ty=y;
    if(x/5<200) tx=x+1;
    if(x==1000) ty=0;
    x=tx;
    y=ty;
  }
  assert(y==0);
}
