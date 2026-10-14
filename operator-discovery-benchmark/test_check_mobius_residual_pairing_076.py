import unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_residual_pairing_076 as C
class Tests(unittest.TestCase):
    def test_prime_fold_signs_squares_and_boundary(self):
        before={1:{'a':'2'},2:{'a':'3','b':'-1'},3:{'b':'2'},4:{'a':'100'},6:{'a':'-2'},8:{'b':'4'},10:{'b':'1'}}
        after={1:{'a':'-1','b':'1'},3:{'a':'2','b':'2'},5:{'b':'-1'}}
        r=C.verify_fold(before,after,2);self.assertEqual(r['status'],'VERIFIED_IDENTITY');self.assertEqual(r['squareful_support_removed'],2);self.assertEqual(r['moved_support'],3);self.assertFalse(r['RH_proved']);self.assertFalse(r['uniform_bound_proved'])
        del after[5];self.assertEqual(C.verify_fold(before,after,2)['status'],'INVALID')
    def test_iterated_domains(self):
        a={1:{'x':'1'},3:{'x':'2'},5:{'x':'-1'},15:{'x':'3'},9:{'x':'8'}}
        b={1:{'x':'-1'},5:{'x':'-4'}}
        self.assertEqual(C.verify_fold(a,b,3,[2])['status'],'VERIFIED_IDENTITY')
        self.assertEqual(C.verify_fold(b,{1:{'x':'3'}},5,[2,3])['status'],'VERIFIED_IDENTITY')
        self.assertEqual(C.verify_fold({2:{'x':'1'}},{2:{'x':'1'}},3,[2])['status'],'INVALID')
    def test_prime_validation_and_canonical_support(self):
        for p,prior in [(4,()),(2,(2,)),(3,(2,2)),(3,(4,)),(100001,())]:self.assertEqual(C.verify_fold({}, {},p,prior)['status'],'INVALID')
        for bad in ({0:{'x':'1'}},{1:{}},{1:{'x':'0'}},{1:{'x':'2/4'}},{True:{'x':'1'}},{1:{'':'1'}}):self.assertEqual(C.verify_fold(bad,{},2)['status'],'INVALID')
        self.assertEqual(C.verify_fold({}, {},2)['status'],'VERIFIED_IDENTITY')
    def test_stencil_prefix_boundary_and_unit(self):
        # G(8)=M1-M0-M2+M1: coefficient mu1 is1; mu2 is-1.
        components=[{'parent':8,'weight':{'t':'1'}}]
        coefficients={1:{'t':'1'},2:{'t':'-1'}}
        self.assertEqual(C.verify_stencil(components,coefficients)['status'],'VERIFIED_IDENTITY')
        self.assertEqual(C.verify_stencil(components,{2:{'t':'-1'}})['status'],'INVALID')
        self.assertEqual(C.verify_stencil([{'parent':0,'weight':{'a':'1'}}],{})['status'],'VERIFIED_IDENTITY')
    def test_combined_stencil_cancellation(self):
        components=[{'parent':8,'weight':{'a':'1','b':'-2'}},{'parent':8,'weight':{'a':'-1','b':'2'}},{'parent':10,'weight':{'x':'-3/7'}}]
        # G10=M1-M1-M2+M2=0.
        self.assertEqual(C.verify_stencil(components,{})['status'],'VERIFIED_IDENTITY')
        self.assertEqual(C.verify_stencil([{'parent':-1,'weight':{}}],{})['status'],'INVALID')
    def test_actual_generic_mu_identity(self):
        def mu(n):
            s=1;d=2
            while d*d<=n:
                if n%d==0:
                    n//=d;s=-s
                    if n%d==0:return 0
                d+=1
            return -s if n>1 else s
        before={n:{'x':str((n%5)-2)} for n in range(1,31) if (n%5)-2}
        # Independent formula c(m)-c(pm), extending sparse map by zero.
        after={}
        for m in range(1,31):
            if m%3:
                a=Q(before.get(m,{}).get('x','0'))-Q(before.get(3*m,{}).get('x','0'))
                if a:after[m]={'x':str(a)}
        self.assertEqual(C.verify_fold(before,after,3)['status'],'VERIFIED_IDENTITY')
        self.assertEqual(sum(Q(v['x'])*mu(n) for n,v in before.items()),sum(Q(v['x'])*mu(n) for n,v in after.items()))
    def test_bound_signs_complete_intervals(self):
        coefficients={1:{'x':'2','y':'-3'},2:{'x':'-1'}}
        r=C.bound_coefficients(coefficients,{'x':['-1','2'],'y':['1','1']})
        self.assertEqual(r['status'],'VERIFIED_BOUND');self.assertEqual(r['bound'],'7');self.assertEqual(r['coefficient_intervals'][1]['lower'],'-5');self.assertEqual(r['coefficient_intervals'][1]['upper'],'1')
        self.assertFalse(r['uniform_bound_proved']);self.assertFalse(r['RH_proved'])
        self.assertEqual(C.bound_coefficients(coefficients,{'x':['0','0'],'y':['0','0']})['bound'],'0')
        self.assertEqual(C.bound_coefficients(coefficients,{'x':['0','1']})['status'],'INVALID')
        self.assertEqual(C.bound_coefficients(coefficients,{'x':['1','0'],'y':['0','0']})['status'],'INVALID')
    def test_memory_before_expansion(self):
        with patch.object(C,'_merge',side_effect=AssertionError('no expansion allowed')):
            r=C.verify_stencil([{'parent':4*C.MAX_N,'weight':{'x':'1'}}],{})
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit'])
        with patch.object(C,'_poly',side_effect=AssertionError('no parsed allocation allowed')):
            r=C.verify_fold({1:{str(i):'1' for i in range(17000)}},{},2)
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit'])
if __name__=='__main__':unittest.main()
