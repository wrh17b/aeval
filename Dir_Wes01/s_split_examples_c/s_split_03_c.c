int main()
{
  int x=0; int y=unknown(); int z =unknown(); int w=0;
  if(y<=z) return 0;
  while(x<=(y+z)) {
    int tx = x + 1;
    int tw=w;
    if(x<z) tw=w+1;
    else tw=w-2;
    x=tx;
    w=tw;
  }
  assert(w<=0);
}
