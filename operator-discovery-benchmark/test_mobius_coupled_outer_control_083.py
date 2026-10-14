"""Symbolic matched equality synthesis and full-program rejection guards."""
import unittest
from fractions import Fraction as Q
import mobius_coupled_outer_control_083 as P

def program():
    w=dict(kind='product',i=0,j=0,arithmetic='all')
    def term(comp):return dict(cut=dict(scale='1',n_exponent='1',u_exponent='0',complement=comp,unit_balance=True),weight=dict(w),theta='2')
    return dict(schema='coupled-divisor-completion-v1',kernel=[dict(divisor=d,weight=w) for d,w in [(4,'-1'),(5,'1'),(8,'1'),(10,'-1')]],memory=1,rays=[],drift_multiplier='3/2',coupled_terms=[term(False),term(True)],gram_weights=['0','0'])

class OuterControlTests(unittest.TestCase):
    def test_symbolic_equalities_and_achieved_proof(self):
        p=program();s=P.equality_constraints(p)
        self.assertEqual(s['status'],'OUTER_EQUALITY_SYSTEM');self.assertEqual(s['rows'],[['1','-1','0','0'],['1','0','-2','0'],['1','0','-2','0']]);self.assertEqual(s['rhs'],['0','2','2'])
        got=P.synthesize(p);self.assertEqual(got['status'],'PROPOSED_UNIFORM_WHOLE_OUTER_CONTROL');self.assertEqual(got['certificate']['uniform_bound_coefficient'],'1')
        p['coupled_terms'][0]['theta']='0';self.assertEqual(P.synthesize(p)['status'],'REJECTED')
    def test_gram_energy_and_class_closure(self):
        p=program();p['gram_weights'][0]='1/4'
        for t in p['coupled_terms']:t['theta']='5/2'
        self.assertEqual(P.synthesize(p)['certificate']['Astar'],'5/4')
        p=program();p['coupled_terms']=[dict(t,weight=dict(t['weight'],arithmetic='prime')) for t in p['coupled_terms']]
        self.assertEqual(P.synthesize(p)['status'],'REJECTED')
        p['coupled_terms'] += [dict(t,weight=dict(t['weight'],arithmetic='composite')) for t in p['coupled_terms']]
        self.assertEqual(P.synthesize(p)['status'],'PROPOSED_UNIFORM_WHOLE_OUTER_CONTROL')
    def test_zero_weights_and_whole_program_guards(self):
        p=program();extra=dict(cut=dict(scale='2',n_exponent='1',u_exponent='0',complement=False,unit_balance=False),weight=dict(kind='source',i=1,arithmetic='all'),theta='7');p['coupled_terms'].append(extra)
        self.assertEqual(P.synthesize(p)['certificate']['zero_outer_terms'],[2])
        extra['weight']=dict(kind='one',arithmetic='all');self.assertEqual(P.synthesize(p)['status'],'REJECTED')
        p=program();p['coupled_terms'][0]['weight']=dict(kind='band',left='1/6',right='2/9',arithmetic='all')
        self.assertEqual(P.equality_constraints(p)['status'],'REJECTED')
    def test_literal_outer_geometry_all_small_scales(self):
        p=program()
        for u in range(1,301):
            N=u//4;coords=[n for n in range(u//5+1,N+1) if all(n%(k*k) for k in range(2,int(n**.5)+1))];price=Q(0)
            def C(K,m):return Q(K//m-int(m==1)) if K else Q(0)
            def D(K,m):return C(K,m)-Q(max(K-1,0),N-1)*C(N,m) if N>=2 else C(K,m)
            for m in coords:
                for n in coords:
                    z=(D(n,m)+D(N-n,m)+D(m,n)+D(N-m,n))/2
                    a=1+2*z;price+=a if m==n else abs(a)
            self.assertLessEqual(price,u,(u,price))

if __name__=='__main__':unittest.main()
