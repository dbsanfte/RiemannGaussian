import copy
import unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_residual_fold_077 as C

def I(l,r,w):return {'left':l,'right':r,'weight':w}
class Tests(unittest.TestCase):
    def test_stencil_floors_units_signs(self):
        components=[{'parent':8,'weight':{'x':'1','y':'-2'}}]
        intervals=[I(0,1,{'x':'1','y':'-2'}),I(1,2,{'x':'-1','y':'2'})]
        self.assertEqual(C.verify_stencil(components,intervals)['status'],'VERIFIED_IDENTITY')
        self.assertEqual(C.verify_stencil(components,intervals[1:])['status'],'INVALID')
        self.assertEqual(C.verify_stencil([{'parent':10,'weight':{'a':'1'}}],[])['status'],'VERIFIED_IDENTITY')
    def test_large_horizon_tiny_intervals(self):
        before=[I(3999999,4000000,{'x':'1'})]
        after=[I(1999999,2000000,{'x':'-1'}),I(3999999,4000000,{'x':'1'})]
        r=C.verify_fold(before,after,2);self.assertEqual(r['status'],'VERIFIED_IDENTITY');self.assertLess(r['peak_bytes'],1000000)
        self.assertEqual(C.bound_intervals(before,{'x':['1','1']},[2])['bound'],'0')
    def test_fold_full_function_excluded_primes(self):
        before=[I(0,6,{'x':'1'})];after=[I(2,6,{'x':'1'})]
        self.assertEqual(C.verify_fold(before,after,3,[2])['status'],'VERIFIED_IDENTITY')
        # m=4 remains part of coefficient FUNCTION even though 2 excludes it.
        self.assertEqual(C.verify_fold(before,[I(2,3,{'x':'1'}),I(4,5,{'x':'1'})],3,[2])['status'],'INVALID')
        self.assertEqual(C.verify_fold(before,after,3,[3])['status'],'INVALID')
    def test_coprime_counts_and_pruned_divisors(self):
        for primes in ([],[2],[2,3],[97,101],[2,3,5,7,11,13,17,19,23,29]):
            for l,r in ((0,1),(0,100),(17,39),(999,1040)):
                expected=sum(all(n%p for p in primes) for n in range(l+1,r+1))
                self.assertEqual(C.coprime_count(l,r,primes),expected)
        r=C.bound_intervals([I(0,10,{'x':'2','y':'-3'})],{'x':['-1','2'],'y':['1','1']},[2,3])
        self.assertEqual(r['counts'],[3]);self.assertEqual(r['l1_upper'],'15');self.assertEqual(r['l1_lower'],'0')
    def test_interval_and_token_tampering(self):
        for rows in ([I(0,3,{'x':'1'}),I(2,4,{'x':'1'})],[I(0,0,{'x':'1'})],[I(0,2,{'x':'0'})],[I(0,2,{'x':'2/4'})]):self.assertEqual(C.bound_intervals(rows,{'x':['1','1']})['status'],'INVALID')
        self.assertEqual(C.bound_intervals([I(0,2,{'x':'1'})],{})['status'],'INVALID')
        self.assertEqual(C.bound_intervals([I(0,2,{'x':'1'})],{'x':['0','0']})['bound'],'0')
        for primes in ([4],[2,2],list(range(2,13))):self.assertEqual(C.bound_intervals([],{ },primes)['status'],'INVALID')
    def test_compiled_binding_arbitrary_gamma(self):
        import check_mobius_count_control_076 as R
        spec={'grid':80,'theta':['1/2','3/4'],'multipliers':[2]}
        program={'spec':spec,'atoms':[{'column':0,'gamma':'17/31'},{'column':1,'gamma':'1001/1000'}],'operator':['1/3','-1/2']}
        row={'u':80,'X':20,'cuts':[4,9],'z':0,'components':[0,0],'moments':[0,0],'counts':[2,1]}
        token='count:2^(-17/31)';lo,hi=R.count_enclosure(2,Q(17,31),20)
        compiled={'components':[{'parent':80,'weight':{'1':'1'}},{'parent':11,'weight':{token:'-1/3'}},{'parent':16,'weight':{token:'-1/3'}},{'parent':40,'weight':{'1':'1/2'}}], 'token_intervals':{'1':['1','1'],token:[str(1/hi),str(1/lo)]},'token_definitions':{'1':{'kind':'constant','value':'1'},token:{'kind':'inverse_rational_count_power','count':2,'gamma':'17/31'}},'source_admission_supplied':False,'uniform_bound_proved':False,'RH_proved':False}
        groups=[{11:1,16:1}]
        r=C.verify_compiled(program,row,groups,compiled);self.assertEqual(r['status'],'VERIFIED_IDENTITY');self.assertTrue(r['source_data_admission_still_required'])
        bad=copy.deepcopy(compiled);bad['token_intervals'][token]=['1','1'];self.assertEqual(C.verify_compiled(program,row,groups,bad)['status'],'INVALID')
        bad=copy.deepcopy(compiled);bad['components'][1]['weight'][token]='1/3';self.assertEqual(C.verify_compiled(program,row,groups,bad)['status'],'INVALID')
        self.assertEqual(C.verify_compiled(program,row,[{11:2}],compiled)['status'],'INVALID')
        badrow=copy.deepcopy(row);badrow['counts'][0]=1;self.assertEqual(C.verify_compiled(program,badrow,groups,compiled)['status'],'INVALID')
    def test_signed_fold_independent_pointwise(self):
        before=[I(1,5,{'a':'2','b':'-1/3'}),I(7,13,{'a':'-3'})]
        def value(n):
            result={}
            for row in before:
                if row['left']<n<=row['right']:
                    for token,coefficient in row['weight'].items():result[token]=Q(coefficient)
            return result
        after=[];active=None;start=0
        for n in range(1,15):
            expected=value(n)
            for token,coefficient in value(3*n).items():expected[token]=expected.get(token,Q(0))-coefficient
            expected={token:str(v) for token,v in expected.items() if v}
            if expected!=active:
                if active:after.append(I(start,n-1,active))
                start=n-1;active=expected
        if active:after.append(I(start,14,active))
        self.assertEqual(C.verify_fold(before,after,3,[5])['status'],'VERIFIED_IDENTITY')
    def test_resource_gate_before_parsing(self):
        with patch.object(C,'_raw_cost',return_value=C.MEMORY_BUDGET),patch.object(C,'_poly',side_effect=AssertionError('reject before parsed allocation')):
            r=C.verify_fold([I(0,1,{'x':'1'})],[],2)
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit'])
    def test_generic_bulk_obstruction(self):
        kernel=[{'divisor':3,'weight':'2'},{'divisor':5,'weight':'-1'}]
        ps=[2,7];lo=Q(1,5);hi=Q(1,3);c=Q(2);delta=Q(3,7);A=c*delta*(hi-lo);E=c*4
        threshold=2*E/A;certificate={'lower':str(lo),'upper':str(hi),'coefficient':str(c),'delta':str(delta),'A':str(A),'E':str(E),'threshold_u':(threshold.numerator+threshold.denominator-1)//threshold.denominator,'q':'1001/1000'}
        r=C.verify_bulk_obstruction(kernel,2,ps,certificate);self.assertEqual(r['status'],'VERIFIED_UNIFORM_COEFFICIENT_OBSTRUCTION');self.assertFalse(r['arithmetic_residual_refuted']);self.assertFalse(r['RH_proved'])
        for key,value in [('lower','0'),('coefficient','1'),('A','1'),('threshold_u',0),('q','2')]:
            bad=copy.deepcopy(certificate);bad[key]=value;self.assertEqual(C.verify_bulk_obstruction(kernel,2,ps,bad)['status'],'INVALID')
        crossing=copy.deepcopy(certificate);crossing['lower']='1/6';self.assertEqual(C.verify_bulk_obstruction(kernel,2,ps,crossing)['status'],'INVALID')
if __name__=='__main__':unittest.main()
