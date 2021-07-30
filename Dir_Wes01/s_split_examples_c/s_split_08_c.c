int main()
{
  int x=0; int y=0;
  while(x!=(2*1351235)) {
    int tx = x+1;
    int ty=y;
    if(x%2 == 0) ty=y+1;
    x=tx;
    y=ty;
  }
  assert(y==1351235);
}
