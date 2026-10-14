"""Synthetic rational algebra only; no source or residual norm observations."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest
import floor_residual_prime_work_guard_050 as G

METERS=[]


def meter(**kw):
    m=G.Meter(**kw);METERS.append(m);return m


def toy():return {'Q':[['2','0'],['0','2']], 'B':[['1/2','0'],['0','1/2']], 'rho':'3/4'}


def build(r):return G.build_guard(r,meter())


class WorkGuardTests(unittest.TestCase):
    def test_canonical_gram_and_slack(self):
        r=toy();c=build(r)
        self.assertEqual(c['canonical_observable']['parent_gram'],[['1/2','0'],['0','1/2']])
        self.assertEqual(c['parent_slack'],[['1','0'],['0','1']])
        self.assertTrue(c['contraction_guard_paid'])
        self.assertFalse(c['whole_work_bound_weakens_existing_obligation'])
        self.assertTrue(G.verify_guard(r,c,meter())['verified'])
        r['B'][0][0]='0'
        self.assertEqual(c['request']['B'][0][0],'1/2')

    def test_orthogonal_gauge_alias(self):
        r=toy();c=build(r)
        for B in [[['0','-1/2'],['1/2','0']],[['-1/2','0'],['0','-1/2']]]:
            s=toy();s['B']=B
            d=build(s)
            self.assertEqual(c['canonical_observable'],d['canonical_observable'])
            self.assertTrue(G.verify_guard(s,d,meter())['verified'])

    def test_literal_work_cross_cancellation(self):
        q=[[Q(3),Q(-1)],[Q(-1),Q(2)]]
        y,z=[Q(1),Q(2)],[Q(2),Q(-1)]
        dot=lambda x,y:sum(x[i]*q[i][j]*y[j] for i in range(2) for j in range(2))
        works=[];correlations=[]
        for sign in [1,-1]:
            bz=[sign*x/2 for x in z];xi=[y[i]-bz[i] for i in range(2)]
            corr=2*dot(bz,xi);work=corr+dot(xi,xi)
            self.assertEqual(work,dot(y,y)-dot(bz,bz))
            correlations.append(corr);works.append(work)
        self.assertEqual(works[0],works[1])
        self.assertNotEqual(correlations[0],correlations[1])

    def test_non_diagonal_product_independent_polarization(self):
        r={'Q':[['3','-1'],['-1','2']], 'B':[['1/3','1/5'],['-1/7','1/4']], 'rho':'1'}
        c=build(r)
        self.assertTrue(G.verify_guard(r,c,meter())['verified'])
        gram=[[Q(x) for x in row] for row in r['Q']]
        B=[[Q(x) for x in row] for row in r['B']]
        z=[Q(2),Q(-3)]
        bz=[sum(B[i][j]*z[j] for j in range(2)) for i in range(2)]
        R=[[Q(x) for x in row] for row in c['canonical_observable']['parent_gram']]
        self.assertEqual(sum(z[i]*R[i][j]*z[j] for i in range(2) for j in range(2)),
                         sum(bz[i]*gram[i][j]*bz[j] for i in range(2) for j in range(2)))

    def test_failed_contraction_does_not_weaken_old_obligation(self):
        r=toy();r['B']=[['1','0'],['0','1']]
        c=build(r)
        self.assertFalse(c['contraction_guard_paid'])
        self.assertEqual(c['contraction_status'],'FAILED_ALGEBRA_GUARD')
        self.assertIsNone(c['whole_work_bound_weakens_existing_obligation'])
        self.assertTrue(G.verify_guard(r,c,meter())['verified'])

    def test_singular_and_zero_psd_have_no_target_recovery(self):
        for gram in [[['1','1'],['1','1']],[['0','0'],['0','0']]]:
            r=toy();r['Q']=gram;c=build(r)
            self.assertFalse(c['Q_positive_definite'])
            self.assertFalse(c['target_recovery_proved'])
            self.assertFalse(c['uniform_arithmetic_bound_proved'])
            self.assertTrue(G.verify_guard(r,c,meter())['verified'])

    def test_zero_predictor_endpoint_and_parent_dominance(self):
        r=toy();r['B']=[['0','0'],['0','0']];c=build(r)
        self.assertEqual(c['canonical_observable']['parent_gram'],[['0','0'],['0','0']])
        self.assertTrue(c['work_dominates_existing_increment'])
        # Exact synthetic Loewner comparison of two parent reweightings.
        z=[Q(2),Q(-3)]
        Rsmall=Q(1,2);Rlarge=Q(1)
        self.assertGreaterEqual(-Rsmall*sum(x*x for x in z),-Rlarge*sum(x*x for x in z))

    def test_tamper_weakening_uniformpayment_or_kernel(self):
        r=toy();c=build(r)
        for field,value in [('whole_work_bound_weakens_existing_obligation',True),
                            ('uniform_arithmetic_bound_proved',True),('target_recovery_proved',True)]:
            d=deepcopy(c);d[field]=value
            with self.assertRaises(ValueError):G.verify_guard(r,d,meter())
        d=deepcopy(c);d['canonical_observable']['parent_gram'][0][0]='1'
        with self.assertRaises(ValueError):G.verify_guard(r,d,meter())

    def test_request_types_and_psd_strict(self):
        mutations=[]
        r=toy();r['Q']=[['1','2'],['2','1']];mutations.append(r)
        r=toy();r['Q']=[['2','1'],['0','2']];mutations.append(r)
        r=toy();r['rho']='-1';mutations.append(r)
        r=toy();r['B'][0][0]=False;mutations.append(r)
        r=toy();r['Q'][0][0]='2/1';mutations.append(r)
        r=toy();r['source_paid']=True;mutations.append(r)
        for r in mutations:
            with self.assertRaises(ValueError):build(r)

    def test_resource_work_and_bit_caps(self):
        with self.assertRaises(OverflowError):G.build_guard(toy(),meter(cap=1))
        r=toy();r['B'][0][0]='65536'
        with self.assertRaises(OverflowError):G.build_guard(r,meter(max_bits=16))
        with self.assertRaises(TimeoutError):G.build_guard(toy(),meter(seconds=-1))


if __name__=='__main__':unittest.main()
