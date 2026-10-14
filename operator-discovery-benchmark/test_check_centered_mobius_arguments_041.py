"""Synthetic exact identities, certificate attacks and recurrence recovery."""
import unittest
import time
from fractions import Fraction as F
from copy import deepcopy
import check_centered_mobius_arguments_041 as V
from prime_bank_candidates import Meter

METER=Meter(cap=50000000,seconds=180)
START=time.monotonic()

def program(m=2,lam='1',rho='1',delta='1/4',C='1'):
    return {'id':'synthetic','m':m,'lambda':{'kind':'rational','value':lam},
            'rho':rho,'delta':delta,'C':C}

def check(p=None,**kwargs):
    return V.verify_program(program() if p is None else p,meter=METER,**kwargs)

def sums(H,m,X,lam):
    J=H[X:2*X]
    A=[sum(H[m*n+j] for j in range(m))/m for n in range(X,2*X)]
    I=[a-lam*h for a,h in zip(A,J)]
    E=lambda z:sum(x*x for x in z)/(X*X)
    return E(J),E(A),E(I),sum(h*i for h,i in zip(J,I))/(X*X),sum(h*a for h,a in zip(J,A))/(X*X)

class IndependentArguments(unittest.TestCase):
    def test_haar_identity_and_sharp_variance_for_arbitrary_signed_increments(self):
        for m in range(2,9):
            for X in range(1,8):
                H=[F(0)]
                for n in range(1,2*m*X):H.append(H[-1]+F((n*17)%9-4,4))
                EJ,EA,_,_,_=sums(H,m,X,F(1))
                child=sum(h*h for h in H[m*X:2*m*X])/((m*X)**2)
                variance=sum(sum((H[m*n+j]-sum(H[m*n+k] for k in range(m))/m)**2
                                 for j in range(m)) for n in range(X,2*X))/((m*X)**2)
                self.assertEqual(child,EA/m+variance)
                self.assertLessEqual(variance,F(m*m-1,12*m*X))
                linear=[F(n) for n in range(2*m*X)]
                av=[sum(linear[m*n+j] for j in range(m))/m for n in range(X,2*X)]
                actual=sum(sum((linear[m*n+j]-av[n-X])**2 for j in range(m))
                           for n in range(X,2*X))/((m*X)**2)
                self.assertEqual(actual,F(m*m-1,12*m*X))
                METER.charge(2*m*X+80)

    def test_covariance_expansion_preserves_signed_cross_terms(self):
        H=[F((n*13)%17-8,3) for n in range(100)]
        for lam in (F(-2),F(0),F(1,2),F(3,2)):
            EJ,EA,EI,CJI,CJA=sums(H,3,8,lam)
            for damping in (F(0),F(1,4),F(1)):
                rho=F(1,2);b=3*rho-lam*lam
                direct=2*lam*CJI+(1+damping)*EI-b*EJ
                expanded=(1+damping)*EA-2*damping*lam*CJA+(damping*lam*lam-3*rho)*EJ
                self.assertEqual(direct,expanded)
                if damping==0:self.assertEqual(direct,EA-3*rho*EJ)
                else:self.assertEqual(direct,EA-3*rho*EJ+damping*EI)
                METER.charge(80)

    def test_recurrence_implication_is_exact_with_full_child_variance(self):
        H=[F((n*7)%13-6,5) for n in range(200)]
        m,X,lam,delta,rho=3,12,F(3,2),F(1,4),F(1,2)
        EJ,EA,EI,CJI,_=sums(H,m,X,lam)
        variance=sum(sum((H[m*n+j]-sum(H[m*n+k] for k in range(m))/m)**2
                         for j in range(m)) for n in range(X,2*X))/((m*X)**2)
        child=sum(v*v for v in H[m*X:2*m*X])/((m*X)**2)
        self.assertEqual(child+delta*EI/m-rho*EJ-variance,
                         (2*lam*CJI+(1+delta)*EI-(m*rho-lam*lam)*EJ)/m)
        METER.charge(200)

    def test_global_coefficient_gf_and_valuation_one_crossing(self):
        # Formal rational local parameter, independently enumerate all p^e.
        for p in (2,3,5):
            v=F(2,p+3)
            def b(e):return F(1) if e==0 else (v-1)*v**(e-1)
            def c(e):return b(e)-(p*b(e-1) if e else 0)
            for e in range(7):
                rhs=v*c(e)-(p+1)*(b(0) if e==0 else 0)+p*(b(0) if e==1 else 0)
                self.assertEqual(c(e+1),rhs)
                if e>=2:self.assertEqual(c(e+1),v*c(e))
            self.assertNotEqual(c(2),v*c(1))
            METER.charge(90)

    def test_q_prime_full_prefix_identity_including_fractional_below_unit(self):
        p=3;v=F(2,5)
        def b(n):
            e=0
            while n%p==0:e+=1;n//=p
            arbitrary=F((n*11)%7-3,3)
            return arbitrary*(F(1) if e==0 else (v-1)*v**(e-1))
        def c(n):return b(n)-(p*b(n//p) if n%p==0 else 0)
        P=lambda x:sum(c(n) for n in range(1,int(x)+1))
        O=lambda x:sum(b(n) for n in range(1,int(x)+1) if n%p)
        for numerator in range(1,99):
            x=F(numerator,7)
            self.assertEqual(P(p*x),v*P(x)+O(p*x)-(p+1)*O(x)+p*O(x/p))
            METER.charge(150)

    def test_all_integer_cover_requires_all_seed_chains(self):
        for m in (2,3,5,7):
            for X in range(1,401):
                step=1
                while m*step<=X:step*=m
                seed=X//step
                self.assertTrue(1<=seed<m)
                Y=seed*step;Y2=(seed+1)*step
                self.assertLessEqual(Y,X);self.assertLess(X,Y2);self.assertLessEqual(Y2,2*Y)
                self.assertLessEqual(2*X,2*Y2);self.assertLessEqual(Y2,2*X)
                self.assertLessEqual(F(Y*Y+Y2*Y2,X*X),5)
                METER.charge(12)
        # Bare m-adic windows miss these values; a single seed cannot prove coverage.
        self.assertFalse(any(3**j<=8<2*3**j for j in range(4)))

    def test_summable_boundary_not_log_when_C_zero(self):
        out=check(program(m=5,C='0',rho='1'))
        self.assertEqual(out['conditional_energy_bound']['log_power'],0)
        self.assertEqual(out['conditional_energy_bound']['seed_count'],4)
        self.assertEqual(out['conditional_energy_bound']['cover_factor'],'5')
        self.assertEqual(check(program(C='1'))['conditional_energy_bound']['log_power'],1)
        self.assertEqual(check(program(rho='1/2'))['conditional_energy_bound']['log_power'],0)

    def test_exact_boundary_and_forcing_prices(self):
        out=check(program(m=3))
        self.assertEqual(F(out['paid_boundary']['constant']),F(32,9))
        self.assertEqual(F(out['paid_forcing']['constant']),96)
        self.assertEqual(F(out['conditional_energy_bound']['seed_bound']),128)

    def test_all_proof_flags_and_dependencies_keep_covariance_open(self):
        out=check()
        self.assertTrue(out['verified'])
        for flag in ('covariance_proved','uniform_target_bound_proved','whole_signed_bound_proved','RH_proved'):
            self.assertIs(out[flag],False)
        seen={}
        for node in out['dependency_graph']:
            self.assertTrue(all(x in seen for x in node['depends_on']))
            if node['status']=='PROVED':self.assertTrue(all(seen[x]=='PROVED' for x in node['depends_on']))
            seen[node['id']]=node['status']
        self.assertEqual(seen['signed_covariance'],'OPEN')
        self.assertEqual(seen['uniform_target'],'OPEN')

    def test_unit_retaining_generic_countermodel_rejects_norm_only_rule(self):
        for m in (2,3,7):
            for C in ('0','1','257/2'):
                out=check(program(m=m,C=C,lam='3/2'))
                model=out['proof_attempt']['countermodel'];X=int(model['X']);kap=F(1,3)
                # Analytic sums for H=n-kappa, avoid a large synthetic array.
                s1=F(X*(3*X-1),2);s2=F(14*X**3-9*X**2+X,6)
                EH=(s2-2*kap*s1+X*kap*kap)/(X*X)
                A_offset=F(m-1,2)-kap
                EA=(m*m*s2+2*m*A_offset*s1+X*A_offset*A_offset)/(X*X)
                self.assertGreater(EA-m*EH-F(C)*2*m*16,0)
                self.assertGreater(F(model['strict_defect_lower']),0)
                self.assertFalse(model['actual_source_laws_satisfied'])
                self.assertEqual(model['a1'],'1-kappa')
                METER.charge(160)

    def test_prime_lambda_is_an_all_prime_law_not_float_fit(self):
        p=program(m=3);p['lambda']={'kind':'prime_power','prime':3,'exponent':'-1/3'}
        self.assertTrue(check(p)['verified'])
        for bad in ({'kind':'prime_power','prime':4,'exponent':'-1/3'},
                    {'kind':'prime_power','prime':3,'exponent':'-1/4'},
                    {'kind':'rational','value':0.5}):
            p=program(m=4 if bad.get('prime')==4 else 3);p['lambda']=bad
            with self.assertRaises(ValueError):check(p)

    def test_arbitrary_fractional_source_and_composite_haar(self):
        out=check(program(m=6),r='123/257',q=4,kappa_ceiling='9')
        self.assertEqual(out['source_binding']['theta'],'134/257')
        self.assertFalse(out['arithmetic_innovation']['q_is_prime'])
        self.assertIsNone(out['arithmetic_innovation']['q_prime_formula'])

    def test_forged_ceiling_and_lost_centering_or_unit(self):
        with self.assertRaises(ValueError):check(kappa_ceiling='0')
        valid=check()['source_binding']['coefficient_certificate']
        mutations=[('unit','0'),('coefficient_abs_bound','0'),('RH_proved',True)]
        for key,value in mutations:
            bad=deepcopy(valid);bad[key]=value
            with self.assertRaises(ValueError):check(coefficient_certificate=bad)
        bad=deepcopy(valid);bad['periodic']['conditional_prime_laws']['q_divisibility']='geometric at e>=2'
        with self.assertRaises(ValueError):check(coefficient_certificate=bad)
        bad=deepcopy(valid);bad['normalization']['interpretation']='ordinary mu(theta) converges'
        with self.assertRaises(ValueError):check(coefficient_certificate=bad)

    def test_invalid_program_parameters_and_forged_proof_graph(self):
        for key,value in (('m',True),('m',1),('rho','3/2'),('rho','-1/2'),('delta','-1'),
                          ('C','-1'),('C',1.0),('C','2/2'),('id',False)):
            bad=program();bad[key]=value
            with self.assertRaises(ValueError):check(bad)
        for extra in ('RH_proved','covariance_proved','dependency_graph','observations'):
            bad=program();bad[extra]=True
            with self.assertRaises(ValueError):check(bad)
        for r in ('1/2','0','-1/3','2/6'):
            with self.assertRaises(ValueError):check(r=r)

    def test_canonical_endpoint_alias_and_damping_are_distinct(self):
        a=check(program(delta='0',lam='1/2'))['open_covariance']
        b=check(program(delta='0',lam='3/2'))['open_covariance']
        self.assertEqual(a['expanded'],b['expanded'])
        self.assertTrue(a['endpoint_equivalent'])
        prime=program(delta='0');prime['lambda']={'kind':'prime_power','prime':2,'exponent':'-1/3'}
        self.assertEqual(a['expanded'],check(prime)['open_covariance']['expanded'])
        damped=check(program(delta='1/4'))['open_covariance']
        self.assertFalse(damped['endpoint_equivalent'])
        self.assertNotEqual(a['expanded'],damped['expanded'])

    def test_covering_chain_cost_retains_the_extra_child_step(self):
        for m in (2,3,5,7):
            out=check(program(m=m));B=F(out['paid_increment']['constant'])
            seed=4*B*B*(m-1);F0=2*B*B
            V0=F(out['paid_boundary']['constant'])
            K=F(out['conditional_energy_bound']['constant'])/5
            # lnX/logm >= parent level j; next chain has at most j+1 steps.
            for j in range(20):
                cover_cost=seed+V0*F(m,m-1)+F0*(j+1)
                lower_log=F(j*(m-1),m) # lnX >= j ln m >= j(m-1)/m
                self.assertLessEqual(cover_cost,K*(1+lower_log))
                METER.charge(20)

    def test_actual_meter_only_requires_charge(self):
        self.assertFalse(hasattr(METER,'number'))
        self.assertTrue(check(program(rho='0',C='0'))['verified'])

def tearDownModule():
    print(f'SYNTHETIC_WORK module=test_check_centered_mobius_arguments_041 operations={METER.operations} elapsed_seconds={time.monotonic()-START:.6f}')

if __name__=='__main__':unittest.main(verbosity=2)
