"""Tiny exact algebra controls, not evidence of asymptotic speed."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from shared_layout import *
import unittest
from itertools import product

class LayoutTests(unittest.TestCase):
    def setUp(self):
        self.layout=build_layout(4,((0,1),(1,2),(2,3),()),2,2,2,0)
    def test_repeat_deterministic_and_history(self):
        a=self.layout;b=build_layout(4,a.scopes,2,2,2,0)
        self.assertEqual((a.av,a.df,a._forms),(b.av,b.df,b._forms))
        self.assertTrue(all(x>=y for x,y in zip(a.conditional_history,a.conditional_history[1:])))
        self.assertLessEqual(a.conditional_history[-1],2)
    def test_orthogonal_basis_and_swap_eigenvalues(self):
        a=self.layout;idx={u:i for i,u in enumerate(a.aux_labels)}
        for psi,j,eig in a.eigenbasis:
            self.assertTrue(any(psi))
            self.assertEqual(sum(sum(a.M0[i][k]*psi[k] for k in range(a.D))*psi[i] for i in range(a.D)),eig*sum(x*x for x in psi))
            for t in range(a.Q):
                transformed=[]
                for aa,dd in a.aux_labels:
                    aaa=list(aa);ddd=list(dd);aaa[t],ddd[t]=ddd[t],aaa[t]
                    transformed.append(psi[idx[tuple(aaa),tuple(ddd)]])
                self.assertTrue(tuple(transformed)==psi or tuple(-x for x in transformed)==psi)
        for i,(p,_,_) in enumerate(a.eigenbasis):
            for q,_,_ in a.eigenbasis[:i]:self.assertEqual(sum(x*y for x,y in zip(p,q)),0)
    def test_M0_polynomial_swap_independent(self):
        a=self.layout;idx={u:i for i,u in enumerate(a.aux_labels)}
        # I={0,1}: f=1-2W, so M=V*(1-Q)+sum V Pi_s.
        for u,(aa,dd) in enumerate(a.aux_labels):
            row=[F(0)]*a.D;row[idx[dd,aa]]+=1-a.Q
            for s in range(a.Q):
                x=list(dd);y=list(aa);x[s],y[s]=y[s],x[s]
                row[idx[tuple(x),tuple(y)]]+=1
            self.assertEqual(tuple(row),a.M0[u])
    def test_remark_44(self):
        a=self.layout;idx={u:i for i,u in enumerate(a.aux_labels)}
        u=idx[((0,0),(1,1))]
        self.assertEqual(a.aux_rows[u][u],(F(1),F(0)))
        self.assertEqual(a.aux_rows[u][idx[((1,0),(0,1))]],(F(0),F(-1,2)))
        self.assertEqual(a.aux_rows[u][idx[((0,1),(1,0))]],(F(0),F(-1)))
    def test_actual_kernel_restoration_integral(self):
        self.assertTrue(self.layout.validate(quantitative=False))
        a=self.layout
        for row in a._forms.values():
            for co in row.values():
                for x in co:self.assertEqual((a.denominator*x).denominator,1)
        # Independent direct row-space certificate via brute assignments with
        # matching assigned group and common measurements, avoiding rank checker.
        states=list(product(range(2),repeat=a.n))
        for t in range(1,a.Q+1):
            for f,scope in enumerate(a.scopes):
                group=a.groups(t)[a.factor_group(t,f)]
                bins={}
                for x in states:
                    key=(tuple(x[v] for v in group),tuple(sum(c*y for c,y in zip(row,x)) for row in a.common_measurements))
                    values=tuple(sum(_eval_public(co,t)*x[v] for v,co in a.form(f,v0).items()) for v0 in scope)
                    if key in bins:self.assertEqual(values,bins[key])
                    bins[key]=values
    def test_duplicate_variable_embeddings_and_empty_factor(self):
        a=self.layout
        self.assertEqual(a.factor_group(1,3),0)
        self.assertEqual(len(a.placement),6)
        self.assertEqual(len(set(a.placement.values())),6)
        self.assertEqual(len(a.groups(1)),2)
    def test_Q3_R2_and_R1(self):
        a=build_layout(2,((0,),(1,)),2,3,2,1)
        self.assertTrue(a.validate(False))
        b=build_layout(2,((0,),(1,)),2,2,1,0)
        self.assertTrue(b.validate(False))
    def test_supplied_labels_checked(self):
        a=self.layout
        b=build_layout(a.n,a.scopes,2,2,2,0,labels=(a.av,a.df))
        self.assertEqual(a._forms,b._forms)
        with self.assertRaises(ValueError):build_layout(2,((0,),),2,2,2,0)
        with self.assertRaises(ValueError):build_layout(2,((0,0),(1,)),2,2,2,0)
        with self.assertRaises(ValueError):build_layout(2,((0,),(1,)),2,2,2,0,labels=(((0,0),),((0,0),(0,0))))
    def test_tail_exact_enumeration_and_strict_guard(self):
        # Direct enumeration of all local eigenbasis sign choices weighted by
        # their multiplicities: r=2 => 3 plus choices, one minus choice.
        bad=sum(1 for choices in product(range(4),repeat=3) if not 1<=sum(c==3 for c in choices)<3)
        self.assertEqual(tail_probability(2,3,2,1),F(bad,4**3))
        with self.assertRaises(ValueError):construct_layout(4,((0,1),(1,2),(2,3)),r=2,Q=3,R=2,A0=1,tau=F(1,2))
    def test_conditional_history_against_independent_exhaustive_average(self):
        n=2;scopes=((0,),(1,));r=2;Q=1
        av,df,history=deterministic_labels(n,scopes,r,Q)
        chosen=list(av)+list(df);words=tuple(product(range(r),repeat=Q))
        def realized(labels):
            a=labels[:n];d=labels[n:]
            c=Counter((a[v],d[f]) for f,scope in enumerate(scopes) for v in scope)
            phi=sum((F(c.get(u,0))-F(2,4))**2 for u in product(words,repeat=2))
            xi=sum((F(sum(a[v][t]==g for v in range(n)))-F(n,r))**2 for t in range(Q) for g in range(r))
            return phi/4+xi/2
        for fixed in range(5):
            values=[realized(tuple(chosen[:fixed])+rest) for rest in product(words,repeat=4-fixed)]
            self.assertEqual(history[fixed],sum(values,F(0))/len(values))

    def test_scheduled_small_fallback(self):
        from shared_parameters import scheduled_guard
        self.assertFalse(scheduled_guard(64,128,2,2).accepted)


def _eval_public(co,t):
    return sum(x*t**i for i,x in enumerate(co))

if __name__=='__main__':
    import argparse,json,io
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'layout-checks.json')
    args=parser.parse_args()
    stream=io.StringIO()
    result=unittest.TextTestRunner(stream=stream,verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(LayoutTests))
    data={'description':'Tiny exact algebra controls; no asymptotic-speed evidence','tests':result.testsRun,'success':result.wasSuccessful(),
          'failures':[(str(t),msg) for t,msg in result.failures], 'errors':[(str(t),msg) for t,msg in result.errors],
          'stdout':stream.getvalue()}
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(stream.getvalue(),end='')
    raise SystemExit(not result.wasSuccessful())
