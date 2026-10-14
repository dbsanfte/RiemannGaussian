import unittest,copy
from fractions import Fraction as Q
from math import gcd
from unittest.mock import patch
import check_mobius_coupled_completion_083 as C

def fixture():
    def cut(a,ne,ue,complement=False,balance=False):return dict(scale=a,n_exponent=ne,u_exponent=ue,complement=complement,unit_balance=balance)
    terms=[dict(cut=cut('1/2','1/2','0'),weight=dict(kind='one',arithmetic='all'),theta='-1/3'),dict(cut=cut('1/3','-1','1',balance=True),weight=dict(kind='source',arithmetic='prime',i=0),theta='1/2'),dict(cut=cut('1','17/31','-3/7',True,True),weight=dict(kind='product',arithmetic='composite',i=0,j=1),theta='-1/2'),dict(cut=cut('1','0','1/2'),weight=dict(kind='band',arithmetic='all',left='1/5',right='3/5'),theta='2/3')]
    return dict(schema='coupled-divisor-completion-v1',kernel=[dict(divisor=1,weight='1'),dict(divisor=2,weight='-1')],memory=1,rays=[],drift_multiplier='3/2',coupled_terms=terms,gram_weights=['1/4','0'])
def sf(n):return all(n%(d*d)for d in range(2,n+1))
def prime(n):return n>=2 and all(n%d for d in range(2,n))
def mu(n):
    if not sf(n):return 0
    factors=sum(n%d==0 and prime(d)for d in range(2,n+1));return(-1)**factors

def independent(p,u):
    dim=p['memory']+1;N=u//min(k['divisor']for k in p['kernel']);ns=[n for n in range(1,N+1)if sf(n)]
    H=[[Q(i==j==0)for j in range(dim-1)]for i in range(dim-1)]
    for ray in p['rays']:
        for i in range(dim-1):
            for j in range(dim-1):H[i][j]+=Q(ray['weight'])*Q(ray['a'][i])*Q(ray['a'][j])
    T=[[ (H[i][j]if i<dim-1 and j<dim-1 else 0)-(Q(p['drift_multiplier'])*H[i-1][j-1]if i and j else 0)for j in range(dim)]for i in range(dim)]
    f=[[sum(Q(k['weight'])for k in p['kernel']if n<=u//(2**i*k['divisor']))for i in range(dim)]for n in ns]
    cuts=[];weights=[];templates=[]
    for term in p['coupled_terms']:
        ks=[];ws=[];cut=term['cut']
        for n,features in zip(ns,f):
            eta=Q(cut['n_exponent']);beta=Q(cut['u_exponent']);degree=eta.denominator*beta.denominator//gcd(eta.denominator,beta.denominator)
            target=Q(cut['scale'])**degree*Q(n)**int(eta*degree)*Q(u)**int(beta*degree)
            K=0
            while K<N and Q(K+1)**degree<=target:K+=1
            if cut['complement']:K=N-K
            ks.append(K);w=term['weight'];kind=w['kind'];arith=w['arithmetic']
            if arith=='prime'and not prime(n)or arith=='composite'and(n==1 or prime(n)):value=Q(0)
            elif kind=='one':value=Q(1)
            elif kind=='source':value=features[w['i']]
            elif kind=='product':value=features[w['i']]*features[w['j']]
            else:value=Q(Q(w['left'])*u<n<=Q(w['right'])*u)
            ws.append(value)
        def D(K,m):
            value=Q(K//m-(m==1))if K else Q(0)
            if cut['unit_balance']and N>=2:value-=Q(max(K-1,0),N-1)*(N//m-(m==1))
            return value
        Z=[[ (ws[h]*D(ks[h],n)+ws[g]*D(ks[g],v))/2 for h,v in enumerate(ns)]for g,n in enumerate(ns)]
        cuts.append(ks);weights.append(ws);templates.append(Z)
    A0=[[sum(T[i][j]*f[g][i]*f[h][j]for i in range(dim)for j in range(dim))for h in range(len(ns))]for g in range(len(ns))]
    grams=[[[f[g][i]*f[h][i]for h in range(len(ns))]for g in range(len(ns))]for i in range(dim)]
    A=[[A0[g][h]+sum(Q(t['theta'])*templates[k][g][h]for k,t in enumerate(p['coupled_terms']))+sum(Q(w)*grams[i][g][h]for i,w in enumerate(p['gram_weights']))for h in range(len(ns))]for g in range(len(ns))]
    rows=[row[g]+sum(abs(v)for h,v in enumerate(row)if h!=g)for g,row in enumerate(A)]
    cert=dict(squarefree_count=len(ns),price=str(sum(rows)),row_prices=list(map(str,rows)))
    return dict(ns=ns,f=f,cuts=cuts,weights=weights,Z=templates,A0=A0,grams=grams,A=A,cert=cert)
def dual(data,nu):
    def L(A):
        n=len(A);result=sum(A[i][i]for i in range(n));k=0
        for i in range(n):
            for j in range(i+1,n):result+=Q(nu[k])*A[i][j];k+=1
        return result
    base=L(data['A0']);zs=list(map(L,data['Z']));gs=list(map(L,data['grams']));lower=base-16*sum(abs(v)for v in zs)+16*sum(min(Q(0),v)for v in gs)
    return dict(nu=nu,lower_bound=str(lower)),base,zs,gs

class Tests(unittest.TestCase):
    def test_complete_physical_model_and_exact_upper(self):
        p=fixture();data=independent(p,19);m=C.build_model(p,19)
        self.assertEqual(list(m['coordinates']),data['ns']);self.assertEqual([list(r)for r in m['features']],data['f']);self.assertEqual([list(r)for r in m['cuts']],data['cuts']);self.assertEqual([list(r)for r in m['weights']],data['weights'])
        self.assertEqual(C.corrected_matrix(m),data['A']);r=C.verify_certificate(p,19,data['cert']);self.assertEqual(r['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND');self.assertTrue(r['prime_edges_retained']);self.assertTrue(r['Boolean_squarefree_diagonals_exact'])
    def test_coupled_zero_identity_and_actual_full_drift(self):
        p=fixture();data=independent(p,19);ns=data['ns'];signs=list(map(mu,ns))
        for Z in data['Z']:self.assertEqual(sum(signs[g]*Z[g][h]*signs[h]for g in range(len(ns))for h in range(len(ns))),0)
        drift=sum(signs[g]*data['A0'][g][h]*signs[h]for g in range(len(ns))for h in range(len(ns)))
        self.assertLessEqual(drift,Q(data['cert']['price']))
    def test_unit_balance_cancels_all_unit_columns_and_K0(self):
        p=fixture();p['coupled_terms']=[p['coupled_terms'][0]];p['coupled_terms'][0]['cut']['unit_balance']=True;m=C.build_model(p,19)
        for K in m['cuts'][0]:self.assertEqual(C._dvalue(m,0,K,1,C.Meter()),0)
        self.assertEqual(C._dvalue(m,0,0,1,C.Meter()),0)
        self.assertEqual(sum(mu(n)*C._dvalue(m,0,7,n,C.Meter())for n in m['coordinates']),0)
    def test_boolean_negative_rows_are_not_clamped(self):
        p=fixture();p['coupled_terms']=[];p['gram_weights']=['0','0'];data=independent(p,3)
        self.assertLess(Q(data['cert']['row_prices'][0]),0);r=C.verify_certificate(p,3,data['cert']);self.assertEqual(r['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
        bad=copy.deepcopy(data['cert']);bad['row_prices'][0]='0';bad['price']=str(sum(map(Q,bad['row_prices'])));self.assertEqual(C.verify_certificate(p,3,bad)['status'],'INVALID')
    def test_dual_offdiagonal_factor_half_sign_and_full_templates(self):
        p=fixture();data=independent(p,11);G=len(data['ns']);nu=['-2'if (g+h)%2 else '1/2'for g in range(G)for h in range(g+1,G)];cert,base,zs,gs=dual(data,nu)
        r=C.verify_price_dual(p,11,cert);self.assertEqual(r['status'],'VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND');self.assertEqual(Q(r['base_functional']),base);self.assertEqual(list(map(Q,r['coupled_template_functionals'])),zs);self.assertEqual(list(map(Q,r['gram_template_functionals'])),gs);self.assertLessEqual(Q(cert['lower_bound']),Q(data['cert']['price']))
    def test_dual_feasibility_shapes_negative_lower_and_parameter_independence(self):
        p=fixture();data=independent(p,7);G=len(data['ns']);cert,*_=dual(data,['-1']*(G*(G-1)//2));self.assertLess(Q(cert['lower_bound']),0)
        for term in p['coupled_terms']:term['theta']='16'
        p['gram_weights']=['16','16'];self.assertEqual(C.verify_price_dual(p,7,cert)['status'],'VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND')
        for bad in [dict(cert,nu=['3']*len(cert['nu'])),dict(cert,nu=[]),dict(cert,lower_bound=str(Q(cert['lower_bound'])+1))]:self.assertEqual(C.verify_price_dual(p,7,bad)['status'],'INVALID')
    def test_prime_composite_masks_and_unit(self):
        p=fixture();m=C.build_model(p,19)
        self.assertEqual(m['prime_count'],sum(prime(n)for n in m['coordinates']))
        unit=m['coordinates'].index(1);self.assertEqual(m['weights'][0][unit],1);self.assertEqual(m['weights'][1][unit],0);self.assertEqual(m['weights'][2][unit],0)
        for g,n in enumerate(m['coordinates']):
            if not prime(n):self.assertEqual(m['weights'][1][g],0)
            if n==1 or prime(n):self.assertEqual(m['weights'][2][g],0)
    def test_fractional_and_negative_exponents_exact_boundaries(self):
        for eta,beta in [('17/31','-19/37'),('-1001/1000','1'),('0','0'),('-1','-1')]:
            p=fixture();p['coupled_terms']=[p['coupled_terms'][0]];p['coupled_terms'][0]['cut'].update(scale='2/3',n_exponent=eta,u_exponent=beta)
            data=independent(p,9);self.assertEqual([list(r)for r in C.build_model(p,9)['cuts']],data['cuts'])
        self.assertEqual(C.floor_cut(Q(1),Q(0),Q(1,2),1,81,100),9)
        self.assertEqual(C.floor_cut(Q(1),Q(0),Q(1,2),1,80,100),8)
    def test_complement_zero_and_empty_horizon_unit(self):
        p=fixture();p['coupled_terms']=[p['coupled_terms'][0]];p['coupled_terms'][0]['cut'].update(scale='1/1000',n_exponent='0',u_exponent='0',unit_balance=True)
        self.assertTrue(all(K==0 for K in C.build_model(p,11)['cuts'][0]));p['coupled_terms'][0]['cut']['complement']=True;self.assertTrue(all(K==11 for K in C.build_model(p,11)['cuts'][0]))
        for u in [1,2]:data=independent(p,u);self.assertEqual(C.verify_certificate(p,u,data['cert'])['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
        p['kernel']=[dict(divisor=100,weight='1')];data=independent(p,1);self.assertEqual(C.verify_certificate(p,1,data['cert'])['price'],'0');self.assertEqual(C.verify_price_dual(p,1,dict(nu=[],lower_bound='0'))['status'],'VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND')
    def test_source_weight_cut_and_unit_balance_tampering(self):
        p=fixture();p['coupled_terms'][1]['cut'].update(scale='1/2',n_exponent='0',u_exponent='1',unit_balance=False);data=independent(p,19)
        for mode in ['source','arithmetic','balance','cut']:
            bad=copy.deepcopy(p)
            if mode=='source':bad['kernel'][1]['divisor']=3
            if mode=='arithmetic':bad['coupled_terms'][1]['weight']['arithmetic']='all'
            if mode=='balance':bad['coupled_terms'][0]['cut']['unit_balance']=True
            if mode=='cut':bad['coupled_terms'][0]['cut']['scale']='3'
            self.assertEqual(C.verify_certificate(bad,19,data['cert'])['status'],'INVALID')
    def test_discriminated_schema_booleans_and_canonical(self):
        for mode in ['missing_arithmetic','extra','product','bool','rational','gram','theta','scale','band']:
            p=fixture()
            if mode=='missing_arithmetic':p['coupled_terms'][0]['weight'].pop('arithmetic')
            if mode=='extra':p['RH_proved']=True
            if mode=='product':p['coupled_terms'][2]['weight'].update(i=1,j=0)
            if mode=='bool':p['coupled_terms'][0]['cut']['unit_balance']=1
            if mode=='rational':p['coupled_terms'][0]['cut']['scale']='2/4'
            if mode=='gram':p['gram_weights'][0]='-1'
            if mode=='theta':p['coupled_terms'][0]['theta']='17'
            if mode=='scale':p['coupled_terms'][0]['cut']['scale']='0'
            if mode=='band':p['coupled_terms'][3]['weight']['right']='3/2'
            self.assertEqual(C.verify_certificate(p,11,{})['status'],'INVALID')
    def test_huge_horizon_before_allocation_and_physical_count_gate(self):
        with patch.object(C.D,'squarefree_prefix',side_effect=AssertionError('must reject horizon before allocation'))as allocation:r=C.verify_certificate(fixture(),10**80,{})
        self.assertTrue(r['resource_limit']);allocation.assert_not_called()
        r=C.verify_certificate(fixture(),16384,{});self.assertTrue(r['resource_limit']);self.assertIn('4096',r['reason'])
    def test_prospective_matrix_power_and_work_gates(self):
        m=C.build_model(fixture(),11)
        with patch.object(C.D,'MEMORY',1):
            with self.assertRaises(C.ResourceLimit):C.corrected_matrix(m)
        p=fixture();p['coupled_terms'][0]['cut']['scale']='2';p['coupled_terms'][0]['cut']['n_exponent']='1/100001'
        self.assertTrue(C.verify_certificate(p,11,{})['resource_limit']);self.assertTrue(C.verify_certificate(fixture(),11,{},C.Meter(limit=1))['resource_limit'])
    def test_nu_prospective_memory_and_scope(self):
        p=fixture();data=independent(p,11);G=len(data['ns']);cert,*_=dual(data,['0']*(G*(G-1)//2));r=C.verify_price_dual(p,11,cert)
        self.assertFalse(r['uniform_growth_proved']);self.assertFalse(r['actual_signed_drift_lower_bound_proved']);self.assertFalse(r['RH_proved']);self.assertTrue(r['diagonal_dual_fixed_one'])
        class Small(C.Meter):
            def reserve(self,n):
                if n>300000:raise C.ResourceLimit('synthetic nu memory gate')
                self.peak_bytes=max(self.peak_bytes,n)
        cert['nu']=['1'*3000]*len(cert['nu']);real=C._rational
        def monitor(value,name,m):
            if name=='nu':raise AssertionError('nu parsed before memory admission')
            return real(value,name,m)
        with patch.object(C,'_rational',side_effect=monitor):r=C.verify_price_dual(p,11,cert,Small())
        self.assertTrue(r['resource_limit'])

def projected_data(p,u):
    data=independent(p,u);ns=data['ns'];known=[i for i,n in enumerate(ns)if n==1 or prime(n)];composite=[i for i,n in enumerate(ns)if n>1 and not prime(n)];sign=[Q(1 if ns[i]==1 else -1)for i in known]
    def project(A):
        if not ns:return[]
        E=1+len(composite);B=[[Q(0)for _ in range(E)]for _ in range(E)]
        B[0][0]=sum(sign[i]*sign[j]*A[g][h]for i,g in enumerate(known)for j,h in enumerate(known))
        for i,g in enumerate(composite):
            B[0][i+1]=B[i+1][0]=sum(sign[j]*A[h][g]for j,h in enumerate(known))
            for j,h in enumerate(composite):B[i+1][j+1]=A[g][h]
        return B
    projected={key:project(data[key])for key in ['A0','A']};projected['Z']=[project(A)for A in data['Z']];projected['grams']=[project(A)for A in data['grams']]
    rows=[row[i]+sum(abs(x)for j,x in enumerate(row)if j!=i)for i,row in enumerate(projected['A'])];projected['cert']=dict(squarefree_count=len(ns),price=str(sum(rows)),row_prices=list(map(str,rows)));projected['labels']=[]if not ns else ['anchor']+[ns[i]for i in composite];return projected,data

class PrimeAnchorTests(unittest.TestCase):
    def test_prime_anchor_negative_known_block_exact_signs(self):
        p=fixture();p.update(prime_anchor=True,kernel=[dict(divisor=1,weight='1')],coupled_terms=[],gram_weights=['0','0']);data,_=projected_data(p,2)
        self.assertEqual(data['A'],[[Q(-3,2)]]);r=C.verify_certificate(p,2,data['cert']);self.assertEqual(r['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND');self.assertEqual(r['price'],'-3/2');self.assertEqual(r['known_sign_coordinates'],2);self.assertEqual(r['effective_dimension'],1);self.assertTrue(r['prime_signs_anchored']);self.assertFalse(r['unknown_composite_signs_used'])
    def test_prime_anchor_joint_composite_cross_and_all_templates(self):
        p=fixture();p['prime_anchor']=True;data,raw=projected_data(p,19);model=C.build_model(p,19)
        self.assertEqual(C.price_matrix(model),data['A']);self.assertEqual(list(model['effective_labels']),data['labels']);self.assertEqual(C.corrected_matrix(model),raw['A'])
        r=C.verify_certificate(p,19,data['cert']);self.assertEqual(r['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND');self.assertLessEqual(Q(r['price']),Q(raw['cert']['price']))
        E=len(data['A']);cert,base,zs,gs=dual(data,['-2'if (g+h)%2 else '1/2'for g in range(E)for h in range(g+1,E)]);r=C.verify_price_dual(p,19,cert)
        self.assertEqual(r['status'],'VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND');self.assertEqual(Q(r['base_functional']),base);self.assertEqual(list(map(Q,r['coupled_template_functionals'])),zs);self.assertEqual(list(map(Q,r['gram_template_functionals'])),gs)
    def test_anchor_shapes_scope_empty_unit_and_explicit_false(self):
        p=fixture();p['prime_anchor']=True
        for u in [1,2,6]:
            data,_=projected_data(p,u);self.assertEqual(C.verify_certificate(p,u,data['cert'])['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
            E=len(data['A']);cert,*_=dual(data,['0']*(E*(E-1)//2));self.assertEqual(C.verify_price_dual(p,u,cert)['status'],'VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND')
        p['kernel']=[dict(divisor=100,weight='1')];data,_=projected_data(p,1);self.assertEqual(C.verify_certificate(p,1,data['cert'])['effective_dimension'],0)
        p=fixture();old=independent(p,11);p['prime_anchor']=False;self.assertEqual(C.verify_certificate(p,11,old['cert'])['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND');p['prime_anchor']=1;self.assertEqual(C.verify_certificate(p,11,old['cert'])['status'],'INVALID')
    def test_anchor_wrong_uncollapsed_cert_and_dual_rejected(self):
        p=fixture();p['prime_anchor']=True;raw=independent(p,19);self.assertEqual(C.verify_certificate(p,19,raw['cert'])['status'],'INVALID')
        G=len(raw['ns']);cert,*_=dual(raw,['0']*(G*(G-1)//2));self.assertEqual(C.verify_price_dual(p,19,cert)['status'],'INVALID')
        data,_=projected_data(p,19);bad=copy.deepcopy(data['cert']);bad['row_prices'][0]=str(Q(bad['row_prices'][0])+1);bad['price']=str(Q(bad['price'])+1);self.assertEqual(C.verify_certificate(p,19,bad)['status'],'INVALID')
if __name__=='__main__':unittest.main()

class NativeContractionTests(unittest.TestCase):
    def test_native_vs_literal_varied_complete_geometry(self):
        for anchor in (False,True):
            for u in (1,6,19,31):
                p=fixture();p['prime_anchor']=anchor
                p['coupled_terms']+=copy.deepcopy(p['coupled_terms'][:2])
                p['coupled_terms'][-1]['theta']='0'
                model=C.build_model(p,u)
                self.assertEqual(C.corrected_matrix(model),C.literal_corrected_matrix(model))
                G=model['squarefree_count'];E=model['effective_dimension'];nu=tuple(Q(1,3)if i%2 else Q(-2)for i in range(E*(E-1)//2))
                base,zs,grams=C._dual_functionals(model,nu,C.Meter())
                mat=C.literal_corrected_matrix(model);m=C.Meter()
                def functional(entry):
                    value=sum(entry(g,g)for g in range(G))
                    return value+sum(C._lift_dual_weight(model,g,h,nu)*entry(g,h)for g in range(G)for h in range(g+1,G))
                self.assertEqual(base,functional(lambda g,h:C._entry(model,g,h,m,False,False)))
                self.assertEqual(zs,[functional(lambda g,h,k=k:C._zentry(model,k,g,h,m))for k in range(len(p['coupled_terms']))])
                self.assertEqual(grams,[functional(lambda g,h,i=i:model['features'][g][i]*model['features'][h][i])for i in range(p['memory']+1)])
    def test_native_arbitrary_denominator_and_zero_terms(self):
        p=fixture();p['kernel'][0]['weight']='1/100000000000000000003';p['kernel'][1]['weight']='-2/100000000000000000019'
        p['gram_weights']=['0','3/100000000000000000033']
        model=C.build_model(p,19)
        self.assertEqual(C.corrected_matrix(model),C.literal_corrected_matrix(model))
