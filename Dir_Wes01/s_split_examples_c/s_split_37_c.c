int main()
{
  //Note: I am unsure about variable assignment for this specific
  //the smt file has "(rule (inv 0 0 0))" so I assumed that
  //X,y,z = 0
  int x=0;int y=0; int z=0;
  while(x<10) {
    int tx = x+1;
    int ty=y+z;
    int tz=250;
    if(x==0) ty=523;
    if(x==0) tz=z;
    x=tx;
    y=ty;
    z=tz;
  }
  assert(y>2500);
}
