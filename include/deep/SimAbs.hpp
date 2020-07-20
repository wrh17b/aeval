#ifndef SIMABS__HPP__
#define SIMABS__HPP__

#include "HornNonlin.hpp"
#include "NonlinCHCsolver.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  static string findClosestMatch(string str, set<string>& strs)
  {
    int maxNum = 0;
    string maxStr = "";
    for (auto & s : strs)
    {
      if (s == str)
      {
        strs.erase(s);
        return str;
      }
      int curNum = 0;
      while (curNum < s.size() && curNum < str.size() && s[curNum] == str[curNum]) curNum++;
      if (curNum > maxNum)
      {
        maxNum = curNum;
        maxStr = s;
      }
    }
    if (maxNum > 0)
    {
      strs.erase(maxStr);
    }
    return maxStr;
  }

  class SimAbs
  {
    private:

    ExprFactory &m_efac;
    SMTUtils u;
    CHCs& ruleManagerSrc;
    CHCs& ruleManagerDst;

    public:

    SimAbs (CHCs& r1, CHCs& r2) : m_efac(r1.m_efac), ruleManagerSrc(r1), ruleManagerDst(r2), u(m_efac) {}

    ExprMap relMatching;
    map<Expr, ExprMap> varMatching;

    void findMatching(Expr dSrc, Expr dDst)
    {
      relMatching[dSrc] = dDst;
      unsigned i, j;
      for (i = 0, j = 0;
           i < ruleManagerSrc.invVars[dSrc->left()].size() &&
           j < ruleManagerDst.invVars[dDst->left()].size();
           i++)
      {
        Expr vSrc = ruleManagerSrc.invVars[dSrc->left()][i];
        Expr vDst = ruleManagerDst.invVars[dDst->left()][j];
        if (bind::typeOf(vSrc) == bind::typeOf(vDst))
        {
          // TODO: proper variables matching
          varMatching[dSrc][vSrc] = vDst;
          j++;
        }
      }
    }

    void findMatching()
    {
      // corner case
      if (ruleManagerSrc.decls.size() == 1 && ruleManagerDst.decls.size() == 1)
      {
        Expr s = *ruleManagerSrc.decls.begin();
        Expr d = *ruleManagerDst.decls.begin();
        findMatching(s, d);
      }
      else // general case
      {
        map<string, Expr> rels;
        set<string> relNames;
        for (auto & s : ruleManagerDst.decls)
        {
          string str = lexical_cast<string>(*s->left());
          relNames.insert(str);
          rels[str] = s;
        }

        for (auto & s : ruleManagerSrc.decls)
        {
          string str1 = lexical_cast<string>(*s->left());
          string str2 = findClosestMatch(str1, relNames);
          if (str2 != "")
            findMatching(s, rels[str2]);
        }
      }
    }
  };

  inline void simAbs(const char * chcfileSrc, const char * chcfileDst, const char * invfileSrc, const char * invfileDst, int stren)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    Expr invTmp = z3_from_smtlib_file (z3, invfileSrc);

    // variable naming
    ExprSet av;
    filter (invTmp, bind::IsConst (), inserter (av, av.begin()));
    string pref = lexical_cast<string>(**av.begin());
    unsigned num = pref.find_last_of('_');
    pref = pref.substr(0, num+1);

    CHCs ruleManagerSrc(m_efac, z3, pref);
    ruleManagerSrc.parse(string(chcfileSrc));

    CHCs ruleManagerDst(m_efac, z3, pref + "dst_");
    ruleManagerDst.parse(string(chcfileDst));

    SimAbs sim(ruleManagerSrc, ruleManagerDst);
    sim.findMatching();

    NonlinCHCsolver nonlinDst(ruleManagerDst, stren);
    ExprSet invs;
    getConj(invTmp, invs);
    for (auto & a : invs)
    {
      assert (isOpX<EQ>(a));
      Expr relSrc = a->left()->left();
      Expr relDst = sim.relMatching[relSrc];
      if (relDst == NULL)
      {
        outs () << "cannot match " << *relSrc << "\n";
        continue;
      }

      ExprSet cands;
      getConj(a->right(), cands);
      ExprVector& iv = ruleManagerDst.invVars[relDst->left()];
      for (auto c : cands)
      {
        c = replaceAll(c, sim.varMatching[relSrc]);
        ExprSet cv;
        filter (c, bind::IsConst (), inserter (cv, cv.begin()));
        bool toCont = false;
        for (auto & v : cv)
        {
          if (find(iv.begin(), iv.end(), v) == iv.end())
          {
            toCont = true; // remove lemma candidates that have outer symbols
            break;
          }
        }
        if (toCont) continue;
        nonlinDst.addCandidate(relDst->left(), c);
      }
    }
    nonlinDst.repairCands(invfileDst);
  };
}

#endif
