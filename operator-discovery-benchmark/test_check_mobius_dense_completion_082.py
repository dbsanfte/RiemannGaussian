import unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_dense_completion_082 as C

def program():return dict(schema='dense-divisor-completion-v1',kernel=[{'divisor':1,'weight':'1'},{'divisor':3,'weight':'-1/2'}],memory=2,rays=[{'a':['1','-1'],'weight':'1/4'}],drift_multiplier='3/2',profiles=[{'scale':'1','eta':'1/2'}],theta=[['1/2','-2','3/2']],gram_weights=['1/4','0','1/2','3/4'])
def squarefree(n):return all(n%(p*p) for p in range(2,n+1))
def mu(n):
    if not squarefree(n):return 0
    k=0;d=2
    while d*d<=n:
        if n%d==0:k+=1;n//=d
        else:d+=1
    return (-1)**(k+(n>1))
def independent(p,u):
    depth=p['memory'];dim=depth+1;H=[[Q(i==j==0)for j in range(depth)]for i in range(depth)]
    for ray in p['rays']:
        for i in range(depth):
            for j in range(depth):H[i][j]+=Q(ray['weight'])*Q(ray['a'][i])*Q(ray['a'][j])
    T=[[ (H[i][j]if i<depth and j<depth else 0)-(Q(p['drift_multiplier'])*H[i-1][j-1]if i and j else 0)for j in range(dim)]for i in range(dim)]
    N=u//min(k['divisor']for k in p['kernel']);cuts=[]
    for profile in p['profiles']:
        s=Q(profile['scale']);e=Q(profile['eta']);K=0
        while (K+1)**e.denominator*s.denominator**e.denominator<=s.numerator**e.denominator*u**e.numerator:K+=1
        cuts.append(min(N,K))
    groups={}
    for n in range(1,N+1):
        if not squarefree(n):continue
        f=tuple(sum(Q(k['weight'])for k in p['kernel']if n<=u//((1<<i)*k['divisor']))for i in range(dim))
        cs=tuple(Q(K//n-(n==1))if K else Q(0)for K in cuts)
        groups[f+cs]=groups.get(f+cs,0)+1
    keys=sorted(groups);A=[]
    for x in keys:
        row=[]
        for y in keys:
            v=sum(T[i][j]*x[i]*y[j]for i in range(dim)for j in range(dim))
            v+=sum(Q(t)*(x[dim+k]*y[i]+x[i]*y[dim+k])for k,ts in enumerate(p['theta'])for i,t in enumerate(ts))
            v+=sum(Q(w)*x[i]*y[i]for i,w in enumerate(p['gram_weights']))
            row.append(v*groups[x]*groups[y])
        A.append(row)
    prices=[max(Q(0),row[g]+sum(abs(x)for h,x in enumerate(row)if h!=g))for g,row in enumerate(A)]
    return dict(group_count=len(keys),squarefree_count=sum(groups.values()),price=str(sum(prices)),row_prices=list(map(str,prices))),keys,groups,T

class Tests(unittest.TestCase):
    def test_complete_model_and_exact_price(self):
        p=program();cert,keys,groups,T=independent(p,53);r=C.verify_certificate(p,53,cert)
        self.assertEqual(r['status'],'VERIFIED_FINITE_DENSE_UPPER_BOUND');m=C.build_model(p,53)
        self.assertEqual(list(m['features']),keys);self.assertEqual(list(m['counts']),[groups[k]for k in keys]);self.assertEqual(m['T'],T)
    def test_zero_identity_unit_and_actual_full_drift(self):
        p=program()
        for u in [1,2,11,37]:
            cert,keys,groups,T=independent(p,u);m=C.build_model(p,u);K=m['cuts'][0]
            self.assertEqual(sum(mu(n)*(K//n-(n==1))for n in range(1,K+1))if K else 0,0)
            states=[sum(mu(n)*sum(Q(k['weight'])for k in p['kernel']if n<=u//((1<<i)*k['divisor']))for n in range(1,m['N']+1))for i in range(3)]
            drift=sum(T[i][j]*states[i]*states[j]for i in range(3)for j in range(3))
            self.assertLessEqual(drift,Q(cert['price']));self.assertEqual(C.verify_certificate(p,u,cert)['status'],'VERIFIED_FINITE_DENSE_UPPER_BOUND')
    def test_fractional_scale_roots_and_zero_profile(self):
        p=program();p['profiles']=[{'scale':'2/3','eta':'17/31'}];cert,*_=independent(p,81)
        self.assertEqual(C.verify_certificate(p,81,cert)['status'],'VERIFIED_FINITE_DENSE_UPPER_BOUND')
        p['profiles']=[{'scale':'1/1000','eta':'1'}];self.assertEqual(C.build_model(p,9)['cuts'],(0,))
    def test_factor_two_and_count_normalization_mutations(self):
        p=program();cert,*_=independent(p,53)
        for key in ['squarefree_count','group_count']:
            bad=dict(cert);bad[key]+=1;self.assertEqual(C.verify_certificate(p,53,bad)['status'],'INVALID')
        bad=dict(cert);bad['row_prices']=list(cert['row_prices']);bad['row_prices'][0]=str(Q(bad['row_prices'][0])+Q(1,3));bad['price']=str(Q(cert['price'])+Q(1,3));self.assertEqual(C.verify_certificate(p,53,bad)['status'],'INVALID')
    def test_source_endpoint_and_positive_gram_tampering(self):
        p=program();cert,*_=independent(p,53)
        for mut in ['source','gram','theta']:
            q=program()
            if mut=='source':q['kernel'][1]['divisor']=4
            if mut=='gram':q['gram_weights'][0]='0'
            if mut=='theta':q['theta'][0][0]='-1/2'
            self.assertEqual(C.verify_certificate(q,53,cert)['status'],'INVALID')
    def test_grammar_and_false_proof_flags(self):
        for field,value in [('gram_weights',['-1','0','0','0']),('theta',[['17','0','0']]),('drift_multiplier','5/2')]:
            p=program();p[field]=value;self.assertEqual(C.verify_certificate(p,11,{})['status'],'INVALID')
        p=program();p['RH_proved']=True;self.assertEqual(C.verify_certificate(p,11,{})['status'],'INVALID')
    def test_empty_horizon(self):
        p=program();p['kernel']=[{'divisor':100,'weight':'1'}];cert,*_=independent(p,3)
        r=C.verify_certificate(p,3,cert);self.assertEqual(r['status'],'VERIFIED_FINITE_DENSE_UPPER_BOUND');self.assertEqual(r['price'],'0');self.assertFalse(r['unit_included'])
    def test_prime_edges_and_squarefree_support(self):
        p=program();m=C.build_model(p,53)
        self.assertEqual(m['squarefree_count'],sum(squarefree(n)for n in range(1,54)))
        cert,*_=independent(p,53);r=C.verify_certificate(p,53,cert)
        self.assertTrue(r['complete_target_admitted']);self.assertTrue(r['prime_edges_retained']);self.assertTrue(r['unit_included'])
        self.assertFalse(r['uniform_growth_proved']);self.assertFalse(r['uniform_original_source_bound_proved']);self.assertFalse(r['RH_proved'])
    def test_huge_horizon_before_allocation(self):
        with patch.object(C,'squarefree_prefix',side_effect=AssertionError('must not allocate'))as sieve:
            r=C.verify_certificate(program(),10**80,{})
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit']);sieve.assert_not_called()
    def test_prospective_power_gate(self):
        p=program();p['profiles'][0]['eta']='1/100001';p['profiles'][0]['scale']='2'
        with patch.object(C,'squarefree_prefix',side_effect=AssertionError('must not allocate'))as sieve:r=C.verify_certificate(p,100,{})
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit']);sieve.assert_not_called()
    def test_work_and_matrix_memory_gate(self):
        r=C.verify_certificate(program(),53,{},C.Meter(limit=1));self.assertTrue(r['resource_limit'])
        m=C.build_model(program(),53);meter=C.Meter()
        with patch.object(C,'MEMORY',1):
            with self.assertRaises(C.ResourceLimit):C.corrected_matrix(m,meter)
        self.assertGreater(meter.peak_bytes,1)
    def test_canonical_rationals_schema_and_boolean(self):
        p=program();p['theta'][0][0]='2/4';self.assertEqual(C.verify_certificate(p,11,{})['status'],'INVALID')
        self.assertEqual(C.verify_certificate(program(),True,{})['status'],'INVALID')
        p=program();p['kernel'].reverse();self.assertEqual(C.verify_certificate(p,11,{})['status'],'INVALID')
        p=program();p['profiles'][0]['eta']='0';self.assertEqual(C.verify_certificate(p,11,{})['status'],'INVALID')

def independent_dual(p,u,lam,nu):
    _,keys,counts,T=independent(p,u);dim=p['memory']+1;full=dim+len(p['profiles'])
    def functional(entry):
        result=sum(Q(lam[g])*counts[x]**2*entry(x,x)for g,x in enumerate(keys));index=0
        for g,x in enumerate(keys):
            for y in keys[g+1:]:result+=Q(nu[index])*counts[x]*counts[y]*entry(x,y);index+=1
        return result
    base=functional(lambda x,y:sum(T[i][j]*x[i]*y[j]for i in range(dim)for j in range(dim)))
    zs=[functional(lambda x,y,i=i,k=k:x[dim+k]*y[i]+x[i]*y[dim+k])for k in range(len(p['profiles']))for i in range(dim)]
    gs=[functional(lambda x,y,i=i:x[i]*y[i])for i in range(full)]
    return base-16*sum(abs(z)for z in zs)+16*sum(min(Q(0),z)for z in gs),base,zs,gs
class DualTests(unittest.TestCase):
    def fixture(self):
        p=program();_,keys,counts,T=independent(p,19);G=len(keys);lam=['1/3'if i%2 else '2/3'for i in range(G)]
        nu=[str(Q(-1,2)if (g+h)%2 else Q(1,2))for g in range(G)for h in range(g+1,G)]
        lower,*_=independent_dual(p,19,lam,nu)
        return p,dict(lambda_=lam,nu=nu,lower_bound=str(lower))
    def cert(self):
        p,c=self.fixture();c['lambda']=c.pop('lambda_');return p,c
    def test_independent_dual_offdiagonal_sign_factor_and_templates(self):
        p,c=self.cert();expected,base,zs,gs=independent_dual(p,19,c['lambda'],c['nu']);r=C.verify_price_dual(p,19,c)
        self.assertEqual(r['status'],'VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND');self.assertEqual(Q(r['lower_bound']),expected);self.assertEqual(Q(r['base_functional']),base)
        self.assertEqual(list(map(Q,r['zero_template_functionals'])),zs);self.assertEqual(list(map(Q,r['gram_template_functionals'])),gs)
        self.assertLess(expected,0);self.assertFalse(r['actual_signed_drift_lower_bound_proved']);self.assertFalse(r['uniform_growth_proved'])
    def test_dual_feasibility_and_shape(self):
        p,c=self.cert()
        for mutate in ['lambda','nu','shape','missing']:
            bad={k:list(v)if isinstance(v,list)else v for k,v in c.items()}
            if mutate=='lambda':bad['lambda'][0]='4/3'
            if mutate=='nu':bad['nu'][0]='2'
            if mutate=='shape':bad['nu'].pop()
            if mutate=='missing':bad.pop('lambda')
            self.assertEqual(C.verify_price_dual(p,19,bad)['status'],'INVALID')
    def test_dual_price_tampering_and_grammar_parameter_independence(self):
        p,c=self.cert();bad=dict(c,lower_bound=str(Q(c['lower_bound'])+1));self.assertEqual(C.verify_price_dual(p,19,bad)['status'],'INVALID')
        p['theta']=[['16','16','-16']];p['gram_weights']=['16','16','16','16']
        self.assertEqual(C.verify_price_dual(p,19,c)['status'],'VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND')
    def test_dual_lower_bounds_every_tiny_grammar_choice(self):
        p,c=self.cert();lower=Q(c['lower_bound'])
        for theta in [-16,0,16]:
            for w in [0,16]:
                p['theta']=[[str(theta)]*3];p['gram_weights']=[str(w)]*4
                cert,*_=independent(p,19);self.assertLessEqual(lower,Q(cert['price']))
    def test_dual_zero_and_empty_geometry(self):
        p=program();G=C.build_model(p,11)['group_count'];c={'lambda':['0']*G,'nu':['0']*(G*(G-1)//2),'lower_bound':'0'}
        self.assertEqual(C.verify_price_dual(p,11,c)['status'],'VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND')
        p['kernel']=[{'divisor':100,'weight':'1'}];c={'lambda':[],'nu':[],'lower_bound':'0'}
        self.assertEqual(C.verify_price_dual(p,1,c)['status'],'VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND')
    def test_dual_prospective_nu_memory_before_rational_parse(self):
        p,c=self.cert();real=C._rational
        def monitor(value,name,m):
            if name=='nu':raise AssertionError('nu parse must follow memory admission')
            return real(value,name,m)
        class Restrictive(C.Meter):
            def reserve(self,n):
                if n>100000:raise C.ResourceLimit('synthetic nu memory gate')
                self.peak_bytes=max(self.peak_bytes,n)
        # The independent setup peak is below this gate, whereas dual strings
        # are inflated (invalid too-long strings) to force admission first.
        c['nu']=['1'*3000]*len(c['nu'])
        with patch.object(C,'_rational',side_effect=monitor):r=C.verify_price_dual(p,19,c,Restrictive())
        self.assertEqual(r['status'],'INVALID');self.assertTrue(r['resource_limit'])
if __name__=='__main__':unittest.main()
