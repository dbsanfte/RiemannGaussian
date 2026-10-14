"""Exact tiny-model oracle/adversarial tests; no research-chart replay."""
from fractions import Fraction as F
import unittest
import time
import copy
from unittest.mock import patch
import primitive_state_balanced_cone_search as B
import primitive_state_free_cone_search as BASE


def dot(a,b):return sum((x*y for x,y in zip(a,b)),F(0))
def combine(weights,gradients):return [sum((weights[i]*gradients[i][j] for i in range(3)),F(0)) for j in range(len(gradients[0]))]
def model_oracle(r,gradients,alpha):
    """Independent exact seven-face maximizer for three rational gradients."""
    if alpha<=0:raise ValueError('positive alpha')
    pool=[]
    def add(w,face):
        if any(x<0 for x in w) or sum(w)!=1:return
        g=combine(w,gradients);value=dot(w,r)-alpha*dot(g,g)/2
        pool.append((value,face,w,g))
    for i in range(3):
        w=[F(0)]*3;w[i]=F(1);add(w,(i,))
    for i,j in ((0,1),(0,2),(1,2)):
        h=[a-b for a,b in zip(gradients[i],gradients[j])];den=dot(h,h)
        if den:
            t=max(F(0),min(F(1),((r[i]-r[j])/alpha-dot(gradients[j],h))/den))
            w=[F(0)]*3;w[i]=t;w[j]=1-t;add(w,(i,j))
    u=[a-b for a,b in zip(gradients[0],gradients[2])];v=[a-b for a,b in zip(gradients[1],gradients[2])]
    a=dot(u,u);b=dot(u,v);c=dot(v,v);det=a*c-b*b
    if det:
        h0=(r[0]-r[2])/alpha-dot(u,gradients[2]);h1=(r[1]-r[2])/alpha-dot(v,gradients[2])
        s=(c*h0-b*h1)/det;t=(a*h1-b*h0)/det;add([s,t,1-s-t],(0,1,2))
    winner=max(pool,key=lambda x:(x[0],tuple(-i for i in x[1])))
    value,face,w,g=winner;return dict(value=value,face=face,weights=w,direction=[-alpha*q for q in g],pool=pool)

class BalancedConeSoundnessTests(unittest.TestCase):
    def assert_optimal(self,r,g,alpha,out):
        w=out['weights'];d=out['direction'];lines=[r[i]+dot(g[i],d) for i in range(3)];t=max(lines)
        self.assertEqual(sum(w),1);self.assertTrue(all(x>=0 for x in w))
        for i in range(3):
            if w[i]:self.assertEqual(lines[i],t)
        self.assertEqual(t+dot(d,d)/(2*alpha),out['value'])
        self.assertLessEqual(t,max(r)-dot(d,d)/alpha)
    def test_nontrivial_interior_and_strict_duality(self):
        r=[F(6,5),F(11,10),F(1)];g=[[F(1),F(0)],[F(0),F(1)],[F(-1),F(-1)]]
        out=model_oracle(r,g,F(1));self.assertEqual(out['weights'],[F(2,5),F(3,10),F(3,10)])
        self.assertEqual(out['direction'],[F(-1,10),F(0)]);self.assert_optimal(r,g,F(1),out)
    def test_identical_gradients_linear_face_uses_vertex(self):
        r=[F(1),F(3),F(2)];g=[[F(2)]]*3
        out=model_oracle(r,g,F(1));self.assertEqual(out['weights'],[F(0),F(1),F(0)])
        self.assert_optimal(r,g,F(1),out)
    def test_singular_interior_is_covered_by_boundary(self):
        r=[F(1)]*3;g=[[F(2),F(0)],[F(0),F(2)],[F(1),F(1)]]
        out=model_oracle(r,g,F(1));self.assertEqual(out['direction'],[F(-1),F(-1)])
        self.assert_optimal(r,g,F(1),out)
    def test_incompatible_toy_blocks_can_be_stationary_above_zero(self):
        # p0=(z-1)^2/2,p1=(z+1)^2/2,p2=0 at z0=0, b_i=1.
        out=model_oracle([F(1,2),F(1,2),F(0)],[[F(-1)],[F(1)],[F(0)]],F(1))
        self.assertEqual(out['direction'],[F(0)])
        self.assertEqual(out['value'],F(1,2))
    def test_halving_alpha_requires_recomputed_simplex_model(self):
        r=[F(2),F(1),F(0)];g=[[F(1)],[F(-1)],[F(0)]]
        a=model_oracle(r,g,F(1));b=model_oracle(r,g,F(1,2))
        self.assertEqual(a['weights'],[F(3,4),F(1,4),F(0)])
        self.assertEqual(b['weights'],[F(1),F(0),F(0)])
        self.assertEqual(a['direction'],b['direction'])
        self.assertNotEqual([q/2 for q in a['direction']],b['direction'])
    def test_positive_normalizers_preserve_feasible_zero(self):
        floor=F(1,1<<40);initial=[F(0),F(1,1<<80),F(1304)];b=[max(p,floor) for p in initial]
        self.assertTrue(all(q>0 for q in b));self.assertEqual(b[:2],[floor,floor])
        self.assertEqual(max(p/q for p,q in zip([F(0)]*3,b)),0)
        self.assertGreater(max(p/q for p,q in zip([F(0),F(1),F(0)],b)),0)
    def test_warm_increment_must_not_be_rebased_or_requantized(self):
        base=F(1);D=F(1,1<<17);z=F(1,1<<518)
        exact=base+D*z;self.assertEqual(exact.denominator,1<<535)
        self.assertNotEqual(exact,F(1));self.assertNotEqual(exact,z)
    def test_exact_ideal_armijo_at_lipschitz_safe_step(self):
        # p_i=(z-a_i)^2/2, all b=1, so Lmax=1; alpha1 is safe.
        z=F(3);targets=[F(0),F(1),F(2)];r=[(z-a)**2/2 for a in targets];g=[[z-a] for a in targets]
        out=model_oracle(r,g,F(1));d=out['direction'][0];new=max((z+d-a)**2/2 for a in targets)
        self.assertLessEqual(new,max(r)-d*d/8);self.assert_optimal(r,g,F(1),out)
    def test_model_gap_detects_nonoptimal_feasible_weights(self):
        r=[F(6,5),F(11,10),F(1)];g=[[F(1),F(0)],[F(0),F(1)],[F(-1),F(-1)]];alpha=F(1)
        for w in ([F(1),F(0),F(0)],[F(2,5),F(3,10),F(3,10)]):
            bar=combine(w,g);d=[-alpha*v for v in bar];q=[r[i]+dot(g[i],d) for i in range(3)]
            gap=max(q)-dot(w,q)
            primal=max(q)+dot(d,d)/(2*alpha);dual=dot(w,r)-alpha*dot(bar,bar)/2
            self.assertEqual(primal-dual,gap);self.assertGreaterEqual(gap,0)
            self.assertEqual(gap==0,w[0]==F(2,5))
    def test_positive_frozen_envelope_allows_individual_increases(self):
        b=[F(100),F(1),F(1)];a=[F(50),F(4,5),F(7,10)];c=[F(55),F(7,10),F(3,5)]
        self.assertGreater(c[0],a[0]);self.assertLess(max(x/y for x,y in zip(c,b)),max(x/y for x,y in zip(a,b)))
    def test_floor_quantization_keeps_exact_simplex(self):
        unit=1<<240;weights=[F(1,3)]*3
        a=F((weights[0]*unit).numerator//(weights[0]*unit).denominator,unit)
        b=F((weights[1]*unit).numerator//(weights[1]*unit).denominator,unit);out=[a,b,1-a-b]
        self.assertEqual(sum(out),1);self.assertTrue(all(x>=0 for x in out))
        self.assertLess(out[0],weights[0]);self.assertGreater(out[2],weights[2])
        self.assertTrue(all(x.numerator.bit_length()<=241 and x.denominator.bit_length()<=241 for x in out))
    def test_near_singular_is_not_exactly_singular(self):
        eps=F(1,1<<100);u=[F(1),F(0)];v=[F(1),eps]
        det=dot(u,u)*dot(v,v)-dot(u,v)**2
        self.assertEqual(det,eps**2);self.assertGreater(det,0)
        self.assertLess(det,F(1,1<<160))
    def budget(self):return B.EXACT.Budget(time.monotonic()+30,2500000,4000000,20000000,4096)
    def actual_model(self,r,g,alpha):
        c=BASE.context();mp=lambda q:c.mpf(q.numerator)/c.mpf(q.denominator)
        direction,norm,record=B.simplex_model(c,[mp(q) for q in r],[[mp(q) for q in row] for row in g],mp(alpha),self.budget())
        return c,direction,norm,record
    def test_actual_model_interior_quantization_and_gap(self):
        r=[F(6,5),F(11,10),F(1)];g=[[F(1),F(0)],[F(0),F(1)],[F(-1),F(-1)]]
        c,d,n,record=self.actual_model(r,g,F(1));oracle=model_oracle(r,g,F(1));weights=list(map(F,record['lambda_vector']))
        unit=1<<240;expected=[F((2*unit)//5,unit),F((3*unit)//10,unit)];expected.append(1-sum(expected))
        self.assertEqual(weights,expected);self.assertEqual(record['candidates'][record['selected_candidate']]['face'],[0,1,2])
        self.assertTrue(record['model_consistent']);self.assertLessEqual(abs(BASE.record_fraction(record['model_gap'])),BASE.record_fraction(record['model_gap_tolerance']))
        for actual,exact in zip(d,oracle['direction']):self.assertLess(abs(BASE.record_fraction(BASE.mp_record(actual))-exact),F(1,10**60))
    def test_actual_degenerate_identical_and_singular_models(self):
        for r,g in (([F(1),F(3),F(2)],[[F(2)]]*3),([F(1)]*3,[[F(2),F(0)],[F(0),F(2)],[F(1),F(1)]])):
            c,d,n,record=self.actual_model(r,g,F(1));oracle=model_oracle(r,g,F(1))
            self.assertEqual([BASE.record_fraction(BASE.mp_record(x)) for x in d],oracle['direction'])
            self.assertEqual(record['interior']['disposition'],'near_singular_numerical_boundary_only')
    def test_actual_model_halving_and_nonfinite_rejection(self):
        r=[F(2),F(1),F(0)];g=[[F(1)],[F(-1)],[F(0)]]
        a=self.actual_model(r,g,F(1))[3];b=self.actual_model(r,g,F(1,2))[3]
        self.assertNotEqual(a['lambda_vector'],b['lambda_vector']);self.assertEqual(a['direction'],b['direction'])
        c=BASE.context()
        with self.assertRaises(OverflowError):B.simplex_model(c,[c.one,c.inf,c.one],[[c.one]]*3,c.one,self.budget())
        with self.assertRaises(ValueError):B.simplex_model(c,[c.one]*3,[[c.one]]*3,c.zero,self.budget())
        with self.assertRaises(OverflowError):B.simplex_model(c,[c.one]*3,[[c.one]]*3,c.one,B.EXACT.Budget(time.monotonic()+30,1,4000000,20000000,4096))
    def test_actual_near_singular_reports_numerical_skip(self):
        eps=F(1,1<<100);r=[F(1)]*3;g=[[F(1),F(0)],[F(1),eps],[F(0),F(0)]]
        _,_,_,record=self.actual_model(r,g,F(1))
        self.assertEqual(record['interior']['disposition'],'near_singular_numerical_boundary_only')
        self.assertGreater(BASE.record_fraction(record['interior']['determinant']),0)
    def test_actual_block_metrics_separate_normalizers_and_offdiagonal(self):
        c=BASE.context();m=dict(ctx=c,width=3,scalar_indices=[0],gram_pairs=[(0,1)],C_indices=[1],P_indices=[2])
        x=list(map(c.mpf,[-2,-3,-1]));normalizers=[c.mpf(2),c.mpf(9)/2,c.mpf(169)/2]
        penalties,coordinates,details=B.block_metrics(m,x,self.budget(),normalizers,apply_adjoint=False)
        for p,q in zip(penalties,[c.mpf(2),c.mpf(9)/2,c.mpf(169)/2]):self.assertLess(abs(p-q),c.mpf('1e-11'))
        expected=[[-1,0,0],[0,F(-2,3),0],[0,F(-104,169),F(-26,169)]]
        for row,want in zip(coordinates,expected):
            for actual,q in zip(row,want):
                q=F(q);self.assertLess(abs(actual-c.mpf(q.numerator)/q.denominator),c.mpf('1e-12'))
        self.assertEqual(len(details['native_negative_parts']),2)
    def test_actual_normalized_weighted_power_operator(self):
        c=BASE.context();m=dict(ctx=c,width=4,free=[1,3],pivots=[0,2],converted={0:{0:c.one,1:c.mpf(2),4:c.mpf(99)},2:{2:c.one,3:c.mpf(-1),4:c.mpf(-7)}},center_mp=[c.mpf(123),c.mpf(-321)],scale_mp=[c.mpf(1)/8,c.mpf(16)],scalar_indices=[1,3],gram_pairs=[(0,0)],C_indices=[0],P_indices=[2])
        actual=B.weighted_power_operator(m,list(map(c.mpf,[2,3])),list(map(c.mpf,[2,3,5])),self.budget())
        for a,q in zip(actual,[F(-8777,960),F(2656,5)]):self.assertLess(abs(a-c.mpf(q.numerator)/q.denominator),c.mpf('1e-70'))
    def test_actual_warm_setup_preserves535bit_seed_and_exact_endpoint(self):
        c=BASE.context();D=F(1,1<<17);z=F(1,1<<518);free=1+D*z
        warm=dict(complete=True,final_free_vector=[str(free)],final_projected_vector=[str(free)])
        records=[dict(index=0,free_index=0,norm=str(F(1<<34)),exponent=17,scale=str(D))]
        norms=dict(complete=True,status='scaled',normalized_basis_hash='chart',seed_endpoint_hash='base',scaling=B.J.SCALING,records=records,records_hash=B.digest(records))
        prior=dict(complete=True,status='proposed',normalized_basis_hash='chart',seed_endpoint_hash='base',norm_records_hash=norms['records_hash'],final_z_mp=[BASE.mp_record(c.power(2,-518))],final_free_vector=[str(free)])
        m=dict(ctx=c,width=1,free=[0],pivots=[],normalized={},converted={},resident_cells=1,normalized_basis_hash='chart',base_endpoint_hash='base',seed_endpoint_hash='base',warm_endpoint_hash=B.digest(warm),initial=[F(1)],warm_projected=[free],retained=[0],shape=[0,0],offset=0,specs={},n_variables=1,rows=[],rhs=[])
        receipt=B.warm_setup(m,norms,prior,warm,deadline=time.monotonic()+30)
        self.assertEqual(receipt['warm_free_vector'],[str(free)]);self.assertEqual(free.denominator.bit_length(),536)
        _,actual,check=B.calibrate(m,self.budget());self.assertTrue(check['passed'])
        self.assertEqual(actual,[c.one]);self.assertNotEqual(BASE.record_fraction(BASE.mp_record(actual[0])),free)
        proposal=dict(complete=True,status='proposed',base_endpoint_hash='base',warm_endpoint_hash=B.digest(warm),warm_proposal_hash=B.digest(prior),norm_records_hash=norms['records_hash'],final_z_mp=prior['final_z_mp'],final_free_vector=[str(free)])
        with patch.object(B.EXACT,'canonical_lift',side_effect=lambda x,*args:list(x)),patch.object(B.EXACT,'candidate_diagnostics',return_value={}):
            endpoint=B.exact_endpoint(m,proposal,deadline=time.monotonic()+30)
            self.assertEqual(endpoint['final_free_vector'],[str(free)])
            bad=copy.deepcopy(proposal);bad['warm_endpoint_hash']='wrong'
            with self.assertRaises(ValueError):B.exact_endpoint(m,bad,deadline=time.monotonic()+30)
        bad=copy.deepcopy(prior);bad['final_free_vector']=['1']
        with self.assertRaises(ValueError):B.warm_setup(m,norms,bad,warm,deadline=time.monotonic()+30)
    def test_large_step_can_fail_three_trial_claim(self):
        # No guarantee all three predeclared alpha=64,32,16 trials succeed.
        r=[F(1,2)]*3;g=[[F(1)]]*3
        for alpha in (F(64),F(32),F(16)):
            d=model_oracle(r,g,alpha)['direction'][0];new=(1+d)**2/2
            self.assertGreater(new,F(1,2)-d*d/(8*alpha))

if __name__=='__main__':unittest.main()
