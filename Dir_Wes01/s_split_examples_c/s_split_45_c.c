int main()
{
  int x=0;int y=unknown(); int z=unknown();
  while(x<965552) {
    int tx=x+1;
    int ty=0;
    int tz=0;
    if(x>=765552){
      if(x>=865552)
        ty=y;
      else
        ty=y+1
    }
    if(x>=663258){
      if(x>=763258)
        tz=z;
      else
        tz=z+1
    }
    x=tx;
    y=ty;
    z=tz;
  }
  assert(y==z);
}
