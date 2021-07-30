int main()
{
  int x=1; int z=-1;
  while(x<=5143523){
    int tx = -1*(x+x);
    int tz=z;
    if(x<0) tz=4*z;
    x=tx;
    z=tz;
  }
  assert((x+z)==0);
}
