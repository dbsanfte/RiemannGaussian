"""Tiny source-free rational proof-schema regressions, no Mobius arrays."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest
import floor_residual_prime_argument_047 as G

METERS=[]


def meter(**kwargs):
    m=G.Meter(**kwargs);METERS.append(m);return m


def toy():
    return {'source_recipe':{'id':'toy-profile','base':{'kind':'drift_mixture',
        'a':'2/5','theta':'2/3','terms':[{'rate':'1/2','weight':'3/2'},
                                      {'rate':'3/2','weight':'-1/2'}]},'auxiliary':None},
        'rounding':deepcopy(G.ROUNDING),'prime':3,'original_forcing_b':'-1',
        'target':{'A':'10','eta':'1/4'},
        'argument':{'state':'prime_split_H_A','gram':[['2','0'],['0','2']],
            'recurrence':{'rho':'1/2','C':'1','forcing':'L_parent^-eta','parities':[0,1]},
            'base':{'minimum':32}}}


def evaluate(r):return G.evaluate_argument(r,meter())


class ArgumentTests(unittest.TestCase):
    def test_full_joint_open_dependencies_and_integer_domain(self):
        r=toy();c=evaluate(r)
        self.assertEqual(c['status'],'OPEN')
        self.assertEqual(c['implication_status'],'PAID_UNIVERSAL_ALGEBRA')
        self.assertEqual(c['induction']['whole_base_interval'],[32,63])
        self.assertEqual({d['id'] for d in c['dependencies']},{'SOURCE_SPLIT','BASE','RECURRENCE'})
        self.assertEqual(c['dependencies'][0]['status'],'PAID_UNIVERSAL_ALGEBRA')
        self.assertTrue(all(d['status']=='OPEN' for d in c['dependencies'][1:]))
        self.assertIn('k>N',c['spatial_tail']['required'])
        self.assertFalse(c['uniform_arithmetic_bound_proved'])
        r['source_recipe']['id']='changed'
        self.assertEqual(c['request']['source_recipe']['id'],'toy-profile')

    def test_completed_square_preserves_signed_cross(self):
        for tau,d,H,A in [('3/2','2',Q(2),Q(-3)),('1/3','-1/2',Q(-1),Q(4))]:
            q=G.completed_square_gram(tau,d,meter());q=[[Q(x) for x in row] for row in q]
            actual=q[0][0]*H*H+2*q[0][1]*H*A+q[1][1]*A*A
            self.assertEqual(actual,(H+A)**2+Q(tau)*(H+(1-Q(d))*A)**2)
            self.assertGreaterEqual(actual,(H+A)**2)
        r=toy();r['argument']['gram']=G.completed_square_gram('3/2','2',meter())
        self.assertEqual(evaluate(r)['status'],'OPEN')

    def test_target_dropped_diagonal_not_a_majorant(self):
        for gram in [[['1','0'],['0','1']],[['1','0'],['0','0']],[['2','1'],['1','0']]]:
            r=toy();r['argument']['gram']=gram
            self.assertEqual(evaluate(r)['status'],'INVALID_ARGUMENT')

    def test_target_collinear_control_identified(self):
        r=toy();r['argument']['gram']=G.completed_square_gram('1','0',meter())
        c=evaluate(r)
        self.assertTrue(c['potential']['target_only_control'])
        self.assertFalse(c['potential']['joint_state_strictly_coercive'])

    def test_exact_parent_level_margin_boundary(self):
        r=toy();r['source_recipe']['base']['theta']='1/3'
        r['target']={'A':'14','eta':'1'}
        r['argument']['recurrence']['C']='5'
        self.assertEqual(evaluate(r)['status'],'OPEN') # 1/2+5/14=6/7
        r['argument']['recurrence']['C']='6'
        self.assertEqual(evaluate(r)['status'],'INVALID_ARGUMENT')

    def test_rational_exponent_and_046_barrier(self):
        r=toy();r['target']['eta']='1/3'
        self.assertEqual(evaluate(r)['status'],'OPEN') # equality is not refuted
        r['target']['eta']='2/3'
        self.assertEqual(evaluate(r)['status'],'REFUTED_ARGUMENT')
        self.assertEqual(evaluate(r)['target_status'],'REFUTED')
        r['target']['eta']='1/4';r['argument']['recurrence']['C']='0'
        self.assertEqual(evaluate(r)['status'],'REFUTED_ARGUMENT')
        self.assertEqual(evaluate(r)['target_status'],'OPEN')
        r['source_recipe']['base']['theta']='1/2'
        self.assertEqual(evaluate(r)['status'],'OPEN')

    def test_both_parities_and_full_base_are_mandatory(self):
        for parities in [[0],[1],[False,1],[1,0]]:
            r=toy();r['argument']['recurrence']['parities']=parities
            self.assertEqual(evaluate(r)['status'],'UNSUPPORTED')
        r=toy();r['argument']['base']['minimum']=33
        self.assertEqual(evaluate(r)['status'],'UNSUPPORTED')
        for n in range(32,80):
            for parity in [0,1]:self.assertEqual((2*n+parity).bit_length(),n.bit_length()+1)

    def test_tamper_cannot_pay_arithmetic_or_drop_target(self):
        r=toy();c=evaluate(r)
        self.assertTrue(G.verify_argument(r,c,meter())['verified'])
        mutations=[]
        d=deepcopy(c);d['dependencies'][2]['status']='PAID';mutations.append(d)
        d=deepcopy(c);d['uniform_arithmetic_bound_proved']=True;mutations.append(d)
        d=deepcopy(c);d['request']['argument']['gram']=[['1','0'],['0','0']];mutations.append(d)
        d=deepcopy(c);d['induction']['whole_base_interval']=[32,32];mutations.append(d)
        for d in mutations:
            with self.assertRaises(ValueError):G.verify_argument(r,d,meter())

    def test_signed_predictor_work_identity(self):
        # A negative covariance cannot be replaced by two independent norms.
        Qm=[[Q(2),Q(-1)],[Q(-1),Q(2)]]
        z=[Q(2),Q(-1)];xi=[Q(-1),Q(1)];B=[[Q(1,2),Q(0)],[Q(0),Q(1,2)]];rho=Q(1,2)
        bz=[sum(B[i][j]*z[j] for j in range(2)) for i in range(2)]
        child=[bz[i]+xi[i] for i in range(2)]
        dot=lambda x,y:sum(x[i]*Qm[i][j]*y[j] for i in range(2) for j in range(2))
        self.assertEqual(dot(child,child)-rho*dot(z,z),dot(bz,bz)-rho*dot(z,z)+2*dot(bz,xi)+dot(xi,xi))
        self.assertLess(dot(bz,xi),0)

    def test_tail_telescoping_and_no_zero_beyond_source(self):
        for K in [1,7,31]:
            partial=sum((Q(1,k*(k+1)) for k in range(K+1,K+30)),Q(0))
            self.assertEqual(partial,Q(1,K+1)-Q(1,K+30))
            self.assertLess(partial,Q(1,K+1))
        # A floor basis remains nonzero at arbitrarily large quotient indices.
        for k in [7,100,1000]:self.assertEqual(Q(k,3)-(k//3),Q(k%3,3))

    def test_source_prime_rounding_and_flags_strict(self):
        mutations=[]
        r=toy();r['prime']=4;mutations.append(r)
        r=toy();r['rounding']['bits_multiplier']=3;mutations.append(r)
        r=toy();r['source_recipe']['auxiliary']={'kind':'made_up'};mutations.append(r)
        r=toy();r['original_forcing_b']='0';mutations.append(r)
        r=toy();r['argument']['empirically_paid']=True;mutations.append(r)
        for r in mutations:self.assertEqual(evaluate(r)['status'],'UNSUPPORTED')

    def test_enumeration_and_work_bit_guards(self):
        out=G.enumerate_potentials(['0','1/2'],['0','-1','2'],meter())
        self.assertEqual(len(out),6)
        self.assertEqual(sum(x['target_only_control'] for x in out),4)
        with self.assertRaises(OverflowError):G.evaluate_argument(toy(),meter(cap=1))
        r=toy();r['target']['eta']='1/100000'
        with self.assertRaises(OverflowError):G.evaluate_argument(r,meter())


if __name__=='__main__':unittest.main()
