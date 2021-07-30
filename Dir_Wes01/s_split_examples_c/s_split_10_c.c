int main()
{
  int x=0;
  while(x<2000) {
    int tx = x+5;
    if(x/5<200) tx=x+1;
    x=tx;
  }
  assert(x%5==0);
}
