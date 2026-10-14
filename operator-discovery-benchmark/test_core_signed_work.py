"""Independent scalar semantics and proof-scope tests for generated signed work."""
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest
from flint import arb,ctx
import core_signed_work as P
from prime_bank_candidates import Meter as BaseMeter

METERS=[]
class Meter(BaseMeter):
    def __init__(self):super().__init__(10000000,60);METERS.append(self)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_core_signed_work operations='+str(sum(m.operations for m in METERS)))


def synthetic(H):
    f=[arb(0)]+[arb((n*n+3*n)%9-4) for n in range(1,H+1)]
    f[1]=arb(2)  # Exercise the nonzero unit and negative eta=2 first-shell work.
    F=[arb(0)]*(H+1);B=[arb(0)]*(H+1)
    for n in range(1,H+1):F[n]=F[n-1]+f[n];B[n]=B[n-1]+f[n]*arb(n).log()
    return dict(H=H,F=F,log_prefix=B,core=f)


class SignedWorkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.old=ctx.prec;ctx.prec=192
    @classmethod
    def tearDownClass(cls):ctx.prec=cls.old

    def test_prefit_gate_and_zero_forcing_guard(self):
        m=Meter();programs=P.catalogue(m)
        self.assertEqual(len(programs),117)
        witness=json.loads(Path('core-bound-results/pilot-001/pole-feedback-001/pole_witness.json').read_text())
        admitted=0
        for row in programs:
            for rho in P.RHOS:
                for k in P.LOG_POWERS:
                    r=P.admission(row['program'],rho,k,witness)
                    admitted+=r['admitted'];m.charge(200)
                    if r['admitted']:self.assertGreaterEqual(r['implied_filtered_log_degree'],2)
        self.assertEqual(admitted,567)
        p=programs[0]['program']
        self.assertTrue(P.admission(p,'1',1,witness)['admitted'])
        self.assertFalse(P.admission(p,'1',1,witness,constant='0')['admitted'])

    def test_streamed_signed_crosses_match_exact_literal_cells(self):
        m=Meter();s=synthetic(127);scales=[1,2,3,8,32,64];t=P.tables(s,scales,m)
        for sign,theta,eta in [(0,'0','2'),(1,'1/6','-1'),(-1,'1/2','3/2')]:
            p=dict(target_filter=dict(kind='delay',sign=sign,theta=theta),eta=eta,cutoff=1024)
            a=sign*arb(2)**P.real(theta);e=P.real(eta)
            for X in scales:
                out=P.measure(p,X,t,m);E=N=W=arb(0)
                for n in range(X,2*X):
                    G=s['F'][n]-a*s['F'][n//2]
                    # Build g's log prefix literally, rather than applying the delayed-bank formula.
                    BG=sum(((s['core'][k]-(a*s['core'][k//2] if k%2==0 else 0))*arb(k).log() for k in range(1,n+1)),arb(0))
                    ell=arb(0) if n==1 else (-arb(n+1).log()).ei()-(-arb(n).log()).ei()
                    E+=G*G;N+=G*G/(n*(n+1));W+=(1-e)*G*G/(n*(n+1))+e*G*BG*ell
                    m.charge(700+80*n)
                self.assertTrue(out['energy_filtered'].overlaps(E/(X*X)))
                self.assertTrue(out['critical_energy'].overlaps(N))
                self.assertTrue(out['work'].overlaps(W))
                self.assertFalse(out['all_scale_work_bound_proved'])
            if sign==0:self.assertTrue(P.measure(p,1,t,m)['work']<0)
        with self.assertRaises(ValueError):P.tables(s,[65],m)

    def test_prime_local_source_matches_complete_small_convolutions(self):
        m=Meter();source=json.loads(Path('joint-preconditioner-results/pilot-001/selection.json').read_text())['selected']
        H=31;s=P.source(H,source,m)
        mu=[0]+[1]*H
        for n in range(2,H+1):
            factors=[p for p in range(2,n+1) if n%p==0 and all(p%d for d in range(2,p))]
            mu[n]=0 if any(n%(p*p)==0 for p in factors) else (-1)**len(factors)
        ku=[arb(0)]+[1/arb(n).root(3) for n in range(1,H+1)]
        mv=[arb(0)]+[mu[n]*ku[n]**2 for n in range(1,H+1)]
        def conv(a,b):return [arb(0)]+[sum((a[d]*b[n//d] for d in range(1,n+1) if n%d==0),arb(0)) for n in range(1,H+1)]
        expected={'nu0':conv(ku,conv(mu,mu)),'nu1':conv(ku,conv(mu,mv)),'nu2':conv(ku,mv),'mu':list(map(arb,mu))}
        for name in P.MODES:
            for a,b in zip(s['modes'][name],expected[name]):self.assertTrue(a.overlaps(b))
        self.assertTrue(s['core'][1].overlaps(-arb(9)/2-s['R_u']))
        m.charge(100000)

    def test_signed_recurrence_has_exact_constants_and_open_premise(self):
        p=dict(target_filter=dict(kind='delay',sign=0,theta='0'),eta='2',cutoff=1024)
        for rho,k,C,power,K in [('1/2',2,'3',2,'8'),('1',1,'3',2,'5'),('1',4,'0',0,'2')]:
            c=P.recurrence_certificate(p,rho,k,C,'2','7')
            self.assertEqual(c['filtered_log_degree'],power);self.assertEqual(c['work_upper_constant'],K)
            self.assertEqual(Q(c['filtered_energy_constant']),4*max(Q(7),5*Q(K)))
            self.assertFalse(c['uniform_step_proved']);self.assertFalse(c['RH_proved'])
        with self.assertRaises(ValueError):P.recurrence_certificate(p,'1',1,'-1','2','7')
        r=P.recovery_certificate(p)
        self.assertEqual(r['history_mass_upper'],'2/5');self.assertTrue(r['strict_smaller_scale_dependencies'])


if __name__=='__main__':unittest.main()
