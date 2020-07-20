#include "deep/SimAbs.hpp"

using namespace ufo;
using namespace std;

const char * getStrValue(const char * opt, const char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return atoi(argv[i+1]);
    }
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  const char *IN_FILE = "_invs.smt2";
  const char *OUT_FILE = "_invs_dst.smt2";
  const char * in = getStrValue("--in", IN_FILE, argc, argv);
  const char * out = getStrValue("--out", OUT_FILE, argc, argv);
  int str = getIntValue("--stren", 1, argc, argv);
  simAbs(argv[1], argv[2], in, out, str);
  return 0;
}
