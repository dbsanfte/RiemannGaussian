import copy
import math
import unittest
from fractions import Fraction as Q
import check_mobius_symbolic_cover_080 as C

def logspec(r):
    r=Q(r);z=(r-1)/(r+1);t=abs(z);lo=2*sum((t**(2*k+1)/Q(2*k+1) for k in range(32)),Q(0));hi=lo+2*t**65/(65*(1-t*t))
    if z<0:lo,hi=-hi,-lo
    return {'argument':str(r),'terms':32,'lower':str(lo),'upper':str(hi)}
def ray(i=1,c='1',l='0'):
    a=[['0','0'] for _ in range(10)];a[i]=[c,l];return a

def row(d=1,b=1,u=4):
    D=[{} for _ in range(10)];D[1]={'1':str(d)}
    B=[{'i':i,'j':j,'terms':([{'left_token':'1','right_token':'1','coefficient':str(b)}] if (i,j)==(1,1) and b else [])} for i in range(10) for j in range(i,10)]
    return {'u':u,'flux_features':D,'gram_upper':B,'token_intervals':{'1':['1','1']}}
def cells():
    return {'bands':[{'left':0,'right':1,'parent_weight':{'1':'1'},'child_weight':{}},{'left':1,'right':2,'parent_weight':{'1':'1'},'child_weight':{}}], 'cells':[{'band':0,'parent_category':1,'child_category':10,'count':1,'signed_count':1},{'band':1,'parent_category':2,'child_category':10,'count':1,'signed_count':-1}]}

class Tests(unittest.TestCase):
    def test_logs_sign_exact_and_tamper(self):
        for r in ['1','1/2','2','16','1/16','17/31']:
            s=logspec(r);self.assertEqual(C.verify_log(s)['status'],'VERIFIED_LOG_ENCLOSURE')
        for key,value in [('lower','0'),('terms',31),('argument','3')]:
            s=logspec('2');s[key]=value;self.assertEqual(C.verify_log(s)['status'],'INVALID')
        self.assertEqual(C.verify_log(logspec('17'))['status'],'INVALID')
    def test_shared_log_leaf_and_fractional_power(self):
        s=logspec('2');a=ray(1,'-1','1')
        result=C.verify_leaf(row(),a,'1','1',s)
        self.assertEqual(result['status'],'CERTIFIED_FINITE');self.assertEqual(result['difference_upper'],'0')
        self.assertEqual(C.verify_leaf(row(2,1),a,'1','1',s)['status'],'REFUTED_FINITE')
        self.assertEqual(C.verify_leaf(row(),ray(),'1','17/16',s)['status'],'CERTIFIED_FINITE')
        midpoint=(Q(s['lower'])+Q(s['upper']))/2
        # Constant S^2 vs a varying positive Q crosses at a rational midpoint.
        r=row();r['flux_features'][1]={'1':str(midpoint)}
        a=ray(1,'0','1')
        self.assertEqual(C.verify_leaf(r,a,str(midpoint**2),'1',s)['status'],'CERTIFIED_FINITE')
    def test_quadratic_vertex_and_genuine_ambiguity(self):
        meter=C.Meter();self.assertEqual(C._range((Q(1),Q(-2),Q(1)),Q(0),Q(2),meter),(Q(0),Q(1)))
        s=logspec('2');mid=(Q(s['lower'])+Q(s['upper']))/2
        r=row(1,0);r['gram_upper'][19]['terms']=[{'left_token':'1','right_token':'1','coefficient':'1'}]
        # entry19 is(2,2); S=L, Q=1, crossing at exact rational midpoint.
        a=ray(1,'0','1');a[2]=['1','0']
        v=C.verify_leaf(r,a,str(mid*mid),'1',s)
        self.assertEqual(v['status'],'UNRESOLVED_INTERVAL');self.assertLess(Q(v['difference_lower']),0);self.assertGreater(Q(v['difference_upper']),0)

    def test_tokens_zero_total_and_negative_gram(self):
        s=logspec('2');r=row();r['flux_features'][1]={'x':'1'};r['token_intervals']['x']=['1','1']
        self.assertEqual(C.verify_leaf(r,ray(),'1','1',s)['status'],'INVALID')
        for a in [[['0','0'] for _ in range(10)],[['1','2'] for _ in range(10)]]:
            self.assertEqual(C.verify_leaf(row(),a,'1','1',s)['status'],'INVALID')
        self.assertEqual(C.verify_leaf(row(1,-1),ray(),'1','1',s)['status'],'INVALID')
        self.assertEqual(C.verify_leaf(row(),ray(),'-1','1',s)['status'],'INVALID')
    def test_noncircularity_and_cross_sign(self):
        p=cells();s=logspec('2');a=ray(1,'-1','1')
        self.assertEqual(C.verify_noncircularity(p,a,s,0,1)['status'],'VERIFIED_NONCIRCULARITY')
        a=ray(1,str(-(Q(s['lower'])+Q(s['upper']))/2),'1')
        self.assertEqual(C.verify_noncircularity(p,a,s,0,1)['status'],'UNRESOLVED_INTERVAL')
        p['bands'][1]['parent_weight']={'x':'1'}
        self.assertEqual(C.verify_noncircularity(p,ray(),s,0,1)['status'],'INVALID')
    def test_cover_identity_price_and_scope(self):
        s=logspec('1');a=ray();b=[['1','0'] for _ in range(10)];b[1]=['0','0']
        # sqrt(3) upper at denominator2^24, independently calculated.
        root=math.isqrt(3*2**48);w=Q(root+1,2**24);price=(2*w)**2
        v=C.verify_cover([1]*10,[a,b],['1','1'],'1',s,{'price':str(price)})
        self.assertEqual(v['status'],'VERIFIED_CONDITIONAL_COVER');self.assertFalse(v['uniform_bound_proved']);self.assertTrue(v['uniform_leaves_still_required'])
        b[0]=['1','1'];self.assertEqual(C.verify_cover([1]*10,[a,b],['1','1'],'1',s,{'price':str(price)})['status'],'INVALID')
        self.assertEqual(C.verify_cover([1]*10,[a,ray()],['1','1'],'1',s,{'price':'0'})['status'],'INVALID')
    def test_mode_exact_identity_not_numerical_zero(self):
        s=logspec('7/5');a=ray(1,'0','1');a[9]=['1','0']
        v=C.verify_mode_annihilator('5/8',a,s);self.assertEqual(v['status'],'VERIFIED_LEADING_MODE_ANNIHILATION')
        a[2]=['1','0'];v=C.verify_mode_annihilator('5/8',a,s);self.assertFalse(v['whole_ray_mode_annihilated'])
        a[1]=[s['lower'],'0'];self.assertEqual(C.verify_mode_annihilator('5/8',a,s)['status'],'UNPAID')
        self.assertEqual(C.verify_mode_annihilator('5/8',a,logspec('3/2'))['status'],'INVALID')
        self.assertEqual(C.verify_mode_annihilator('1/2',a,s)['status'],'INVALID')
    def test_source_both_endpoints_and_kernel_binding(self):
        # Kernel1[n<=u], u4: M4=-1, M2=0. Unit-only bands.
        parent=[{'left':0,'right':4,'weight':{'1':'1'}}];child=[{'left':0,'right':2,'weight':{'1':'1'}}]
        p={'u':4,'child_u':2,'bands':[{'left':0,'right':2,'parent_weight':{'1':'1'},'child_weight':{'1':'1'}},{'left':2,'right':4,'parent_weight':{'1':'1'},'child_weight':{}}], 'cells':[{'band':0,'count':2,'signed_count':0},{'band':1,'count':1,'signed_count':-1}]}
        kernel=[{'divisor':1,'weight':'1'}]
        self.assertEqual(C.verify_source_pair(kernel,[],4,parent,child,p)['status'],'VERIFIED_SOURCE_PAIR')
        for ix in [0,1]:
            bad=copy.deepcopy(p);bad['cells'][ix]['signed_count']=1
            self.assertEqual(C.verify_source_pair(kernel,[],4,parent,child,bad)['status'],'INVALID')
        bad=copy.deepcopy(parent);bad[0]['right']=3
        self.assertEqual(C.verify_source_pair(kernel,[],4,bad,child,p)['status'],'INVALID')
    def test_source_excluded_prime_fold_domain(self):
        # f(n)-f(2n)=1 on(2,4]; retained odd n leaves n3, mu=-1.
        kernel=[{'divisor':1,'weight':'1'}]
        parent=[{'left':2,'right':4,'weight':{'1':'1'}}]
        child=[{'left':1,'right':2,'weight':{'1':'1'}}]
        payload={'u':4,'child_u':2,'bands':[{'left':1,'right':2,'parent_weight':{},'child_weight':{'1':'1'}},{'left':2,'right':4,'parent_weight':{'1':'1'},'child_weight':{}}], 'cells':[{'band':1,'count':1,'signed_count':-1}]}
        self.assertEqual(C.verify_source_pair(kernel,[2],4,parent,child,payload)['status'],'VERIFIED_SOURCE_PAIR')

    def test_symbolic_obstruction_pure_complement_and_coupled(self):
        kernel=[{'divisor':2,'weight':'1'}];s=logspec('7/5');meter=C.Meter()
        def certificate(a,scale=Q(1,4)):
            poly=(-Q(a[1][0]),-Q(a[1][1])+Q(a[9][0]),Q(a[9][1]))
            lo,hi=C._range(tuple(v*scale for v in poly),Q(s['lower']),Q(s['upper']),meter)
            return {'mass':'1/2','delta':'1','leading_lower':str(lo),'leading_upper':str(hi)}
        # Promoted complementary ray(1-L)e1 is nonzero and obstructed.
        a=ray(1,'1','-1');v=C.verify_mode_obstruction(kernel,[],'5/8',a,s,certificate(a))
        self.assertEqual(v['status'],'VERIFIED_SYMBOLIC_MODE_OBSTRUCTION');self.assertFalse(v['arithmetic_residual_refuted'])
        a=ray(1,'0','1');a[9]=['1','0'];self.assertEqual(C.verify_mode_obstruction(kernel,[],'5/8',a,s,certificate(a))['status'],'UNPAID')
        a[9]=['2','1'];self.assertEqual(C.verify_mode_obstruction(kernel,[],'5/8',a,s,certificate(a))['status'],'VERIFIED_SYMBOLIC_MODE_OBSTRUCTION')
        self.assertEqual(C.verify_mode_obstruction(kernel,[],'5/8',a,logspec('3/2'),certificate(a))['status'],'INVALID')
        a[2]=['1','0'];self.assertEqual(C.verify_mode_obstruction(kernel,[],'5/8',a,s,certificate(a))['status'],'UNSUPPORTED')
    def test_symbolic_obstruction_tamper_mass_and_zero(self):
        s=logspec('1');a=ray();cert={'mass':'1','delta':'1/2','leading_lower':'-1/4','leading_upper':'-1/4'}
        kernel=[{'divisor':1,'weight':'1'}]
        self.assertEqual(C.verify_mode_obstruction(kernel,[2],'1/3',a,s,cert)['status'],'VERIFIED_SYMBOLIC_MODE_OBSTRUCTION')
        bad=dict(cert);bad['leading_lower']='1/4';self.assertEqual(C.verify_mode_obstruction(kernel,[2],'1/3',a,s,bad)['status'],'INVALID')
        self.assertEqual(C.verify_mode_obstruction(kernel,[2],'1',a,s,cert)['status'],'UNSUPPORTED')
        zero={'mass':'0','delta':'1','leading_lower':'0','leading_upper':'0'}
        self.assertEqual(C.verify_mode_obstruction([],[],'1/3',a,s,zero)['status'],'UNPAID')

    def test_resource_and_noncanonical(self):
        m=C.Meter();m.reserve=lambda x: (_ for _ in ()).throw(C.ResourceLimit('synthetic cap'))
        self.assertEqual(C.verify_leaf(row(),ray(),'1','1',logspec('1'),m)['status'],'INVALID')
        a=ray();a[1][0]='2/2';self.assertEqual(C.verify_leaf(row(),a,'1','1',logspec('1'))['status'],'INVALID')
if __name__=='__main__':unittest.main()
