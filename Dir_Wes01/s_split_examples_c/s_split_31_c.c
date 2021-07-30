int main()
{
  int x=0; int z=unknown(); int w=0;
  if(z<=53736239) return 0;
  while(x<=z) {
    int tx = x+1;
    int tw=w-1;
    if(x<z||(x%2)==0) tw=w+1;
    x=tx;
    w=tw;
  }
  assert(w>=0);
}
