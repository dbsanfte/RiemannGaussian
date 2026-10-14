"""Exact source-pole profile and full signed support-reduction checks."""
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest
from flint import arb,ctx
import core_work_pair_reduction as P
from prime_bank_candidates import Meter

TOTAL=0


def tearDownModule():print('SYNTHETIC_WORK module=test_core_work_pair_reduction operations='+str(TOTAL))


class PairReductionTests(unittest.TestCase):
    def test_profile_compiles_actual_full_source_and_all_pairs(self):
        global TOTAL
        m=Meter(2000000,60);s=json.loads(Path('joint-preconditioner-results/pilot-001/selection.json').read_text())
        p=P.source_profile(s['selected'],s['tails'],m);TOTAL+=m.operations
        self.assertEqual(len(p['hadamard_pairs']),16)
        self.assertEqual(p['dominant_square_zeta_order'],4)
        self.assertEqual(p['dominant_absolute_zeta_order'],2)
        dom=next(r for r in p['hadamard_pairs'] if r['left']==r['right']=='B')
        self.assertEqual(dom['regular_linear_term'],[[2,'-4'],[4,'1']])
        self.assertEqual(dom['absolute_convergence_Re_s_greater_than'],'2/3')
        self.assertFalse(p['signed_work_upper_bound_proved'])

    def test_literal_ordered_pairs_and_signed_boundary(self):
        global TOTAL
        ctx.prec=192
        for X in (2,3,4):
            for eta in ('-1','0','1','2'):
                g=[arb(0)]+[arb((3*n+1)%7-3) for n in range(1,4*X)]
                F=[arb(0)]*len(g);B=[arb(0)]*len(g)
                for n in range(1,len(g)):F[n]=F[n-1]+g[n];B[n]=B[n-1]+g[n]*arb(n).log()
                def work(Y):
                    out=arb(0);e=arb(Q(eta).numerator)/Q(eta).denominator
                    for n in range(Y,2*Y):
                        ell=(-arb(n+1).log()).ei()-(-arb(n).log()).ei()
                        out+=(1-e)*F[n]**2/(n*(n+1))+e*F[n]*B[n]*ell
                    return out
                whole=fresh=head=arb(0)
                for h in range(1,4*X):
                    for k in range(1,4*X):
                        term=g[h]*g[k]*(P.pair_kernel(2*X,h,k,eta)-P.pair_kernel(X,h,k,eta)/2)
                        whole+=term
                        if max(h,k)>X:fresh+=term
                        else:head+=term
                        TOTAL+=2000
                a=P.logarithmic_weight(X,1)/2-P.logarithmic_weight(2*X,1)
                e=arb(Q(eta).numerator)/Q(eta).denominator
                self.assertTrue(a>0)
                self.assertTrue(whole.overlaps(work(2*X)-work(X)/2))
                self.assertTrue(head.overlaps(-e*a*F[X]*B[X]))
                self.assertTrue((fresh-e*a*F[X]*B[X]).overlaps(whole))
                for M in range(1,4*X):
                    v=P.critical_weight(2*X,M)-P.critical_weight(X,M)/2
                    self.assertEqual(v==0,M<=X);self.assertGreaterEqual(v,0)
        TOTAL+=100000

    def test_diagonal_guard_does_not_refute_signed_candidate(self):
        p=dict(complete_work_diagonal_log_degree=3)
        for rho,k,needs in [('1/2',2,True),('1/2',3,False),('1',1,True),('1',2,False)]:
            r=dict(program_id=1,rho=rho,log_power=k,constant='1',program=dict(eta='2',cutoff=1024,target_filter=dict(kind='delay',sign=0,theta='0')))
            out=P.reduce_obligation(r,p)
            self.assertEqual(out['separate_diagonal_payment_insufficient'],needs)
            self.assertFalse(out['signed_candidate_disproved'])
            self.assertTrue(out['full_termwise_absolute_proof_ruled_out'])
            if rho=='1/2':
                self.assertFalse(out['reduced_obligation']['boundary_sign_known'])
                self.assertFalse(out['reduced_obligation']['boundary_independently_paid'])


if __name__=='__main__':unittest.main()
