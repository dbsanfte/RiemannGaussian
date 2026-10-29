#!/usr/bin/env python3
"""Exact sparse Z[multivariates] cleared-identity validation; standard library.
No modular fixtures, numerical factoring, rational division, or dependencies.
"""
import argparse,json
from pathlib import Path

NAMES=('A','D','W','s','Sw','S0','a','r','T','x','z','B','K','Kr','Kt','h',
       'p','l','m','l2','lm','kappa','b','w1','w2','p1','pw','p11','p1w')
NV=len(NAMES)
class P:
 def __init__(self,terms=None):self.t={e:c for e,c in (terms or {}).items() if c}
 @staticmethod
 def scalar(c):return P({(0,)*NV:c})
 @staticmethod
 def variable(name):
  e=[0]*NV;e[NAMES.index(name)]=1;return P({tuple(e):1})
 def __add__(self,q):
  if not isinstance(q,P):q=P.scalar(q)
  out=dict(self.t)
  for e,c in q.t.items():out[e]=out.get(e,0)+c
  return P(out)
 __radd__=__add__
 def __neg__(self):return P({e:-c for e,c in self.t.items()})
 def __sub__(self,q):return self+-q if isinstance(q,P) else self+(-q)
 def __rsub__(self,q):return -self+q
 def __mul__(self,q):
  if not isinstance(q,P):q=P.scalar(q)
  out={}
  for e,c in self.t.items():
   for f,d in q.t.items():
    g=tuple(a+b for a,b in zip(e,f));out[g]=out.get(g,0)+c*d
  return P(out)
 __rmul__=__mul__
 def __pow__(self,n):
  assert n>=0
  a=P.scalar(1);b=self
  while n:
   if n&1:a=a*b
   b=b*b;n//=2
  return a

v={n:P.variable(n) for n in NAMES}
globals().update(v)
checks=[]
def check(name,left,right=0,scope='universal cleared polynomial identity'):
 if not isinstance(right,P):right=P.scalar(right)
 diff=left-right
 checks.append(dict(name=name,passed=not diff.t,scope=scope,
                    lhs_monomials=len(left.t),rhs_monomials=len(right.t)))
 assert not diff.t,(name,diff.t)

def run():
 # Unregulated-mass covariance from packed-source (1).
 q11=Sw;q12=W-s*Sw;q21=D-s*S0;q22=A-s*D+s*s*S0
 check('Ward_unregulated_determinant',q11*q22-q12*q21,A*Sw-D*W+s*W*S0)
 # Regulated source, with Schur denominator cleared before specialization.
 det_reg=Sw*(A+s*D)-D*W
 check('Ward_regulated_Schur_numerator',det_reg+D*W,(A+s*D)*Sw)
 # Multiply the rational replica identity by 2(a+s)(a-s)(s^2-a^2).
 check('opposite_replica_sign',s*((a-s)-(a+s))*(s*s-a*a),
       2*s*s*(a+s)*(a-s))
 # Adjacent mass recurrence and the local Casoratian after clearing aa_next.
 an=r*a+(1-r)*A
 check('adjacent_Casoratian',an-r*a,(1-r)*A)
 # Three-step finite telescoping, with all four denominators cleared.
 masses=[A-T*r**i for i in range(4)]
 def prod(items):
  out=P.scalar(1)
  for x0 in items:out=out*x0
  return out
 telescoped=sum((r**i*prod([masses[k] for k in range(4)
                          if k not in (i,i+1)]) for i in range(3)),P.scalar(0))
 check('Casoratian_finite_h3', (1-r)*A*telescoped,
       (masses[3]-r**3*masses[0])*masses[1]*masses[2],
       'exact finite h=3 check in addition to universal adjacent rule')
 # Cone (8): z(1-x/z)=z-x; common D and squared denominators canceled.
 check('cone_Cayley_factorization_8',
       (1+x)**2*(z-1)**2-(1+z)**2*(1-x)**2,
       -4*(1-x*z)*(z-x))
 # z represents r^h, with D_r A=0, D_r B=-h*T*z, B_T=-z.
 PP=A*K;QQ=B*K;DP=A*Kr;DQ=-h*T*z*K+B*Kr;QT=-z*K+B*Kt
 check('full_q_Wronskian_1',PP*DQ-QQ*DP,-h*A*T*z*K*K)
 check('noncovariant_q_Wronskian_2',PP*(DQ-T*QT)-QQ*DP,
       A*T*z*(1-h)*K*K-A*B*T*K*Kt)
 # Universal log-jet substitutions, no physical leaf expansion.
 P1=p*l;PW=p*m;P11=p*(l*l-l2);P1W=p*(l*m-lm)
 check('DJ_log_jet_unweighted',P1*P1-p*P11,p*p*l2,
       'universal log-jet substitution; existence of physical log jets is paper proof')
 check('DJ_log_jet_weighted',P1*PW-p*P1W,p*p*lm,
       'universal log-jet substitution; no growing leaf expansion')
 # Direct two-leaf physical determinant and weighted adjugate diagnostic.
 physicalP=a*b;physicalP1=a+b;physicalPW=w1*b+w2*a
 detB=(a*a+kappa)*(b*b+kappa)-kappa*kappa
 check('DJ_physical_two_leaf_determinant',detB,
       physicalP**2+kappa*(physicalP1**2-2*physicalP),
       'finite two-leaf physical diagnostic, not arbitrary-dimension validation')
 selected=kappa*(w1*(b*b+kappa-kappa)+w2*(a*a+kappa-kappa))
 check('DJ_physical_two_leaf_selected_adjugate',selected,
       kappa*(physicalP1*physicalPW-physicalP*(w1+w2)),
       'finite two-leaf physical diagnostic')
 # Exact global-zero substitution p=0 in the general jet formulas.
 def at_p_zero(poly):
  index=NAMES.index('p')
  return P({e:c for e,c in poly.t.items() if e[index]==0})
 general_den=p*p+kappa*(p1*p1-p*p11)
 general_num=kappa*(p1*pw-p*p1w)
 check('DJ_gated_denominator',at_p_zero(general_den),kappa*p1**2,
       'formal P=0 substitution; unit/nonunit gate is not machine checked')
 check('DJ_gated_selected_numerator',at_p_zero(general_num),kappa*p1*pw,
       'formal P=0 substitution; ratio inversion remains an external gate')
 return dict(kind='exact symbolic cleared identities over integer polynomial ring',
             variables=list(NAMES),passed=len(checks),checks=checks,
             not_checked=['native coverage, orders, norm/unit guards and complexity',
               'general-rank determinant lemma or Wick theorem implementation',
               'arbitrary-h physical product expansion; local universal rules and h=3 checked',
               'Laurent principal parts on singular components and factor recovery'],
             dependencies='Python standard library only')

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output',default=str(
  Path(__file__).with_name('cancellation-identities.json')));args=parser.parse_args()
 result=run();Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(dict(passed=result['passed'],output=args.output)))
