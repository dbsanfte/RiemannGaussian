"""Synthetic all-cutoff identities and rational proof-certificate regression."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest
import sys

import sympy as S
import global_multiplier_proto_039 as P

METERS=[]


def meter(cap=10_000_000):
    m=P.A.Meter(cap=cap,seconds=60);METERS.append(m);return m


def source(shift=0):
    return dict(lattice=257,channels=[dict(atoms=[dict(kind='mu',shift=shift)],weight=['-2','1/3'])])


class Prototype(unittest.TestCase):
    def test_floor_operator_composition_all_endpoints(self):
        m=meter();a=[[1,'1'],[2,'-1/2'],[2,'1/4']];b=[[1,'-1'],[3,'2']]
        product=P.compose_floor_stencils(a,b,m)
        for N in range(33):
            values=lambda x:Q((x+1)**2-3*x) if x>=1 else Q(0)
            left=sum((Q(c)*Q(v)*values((N//d)//e) for d,c in a for e,v in b),Q(0))
            right=sum((Q(c)*values(N//d) for d,c in product),Q(0));m.charge(40)
            self.assertEqual(left,right)

    def test_complete_source_template_and_tail_scope(self):
        m=meter();s=source(1);cert=P.A.generate(s,m)
        template=P.multiply_complete_relation(s,cert,0,[[1,'1'],[3,'-2']],m)
        self.assertTrue(template['complete_tail_retained']);self.assertFalse(template['uniform_bound_proved'])
        self.assertEqual(template['lhs'][0]['kernel']['factors'][0]['exponent'],'-1/257')
        split=P.complete_split(template,7,m)
        self.assertEqual(split['tail_cost_status'],'OPEN');self.assertTrue(split['unit_retained'])
        bad=deepcopy(template);bad['lhs'][0]['inner_domain']='1<=k<=7'
        with self.assertRaises(ValueError):P.complete_split(bad,7,m)

    def test_finite_inverse_fresh_prime_gate(self):
        m=meter();kernel=dict(op='dirichlet_convolution',factors=[dict(op='power',exponent='0'),dict(op='power',exponent='-2/3')])
        gate=P.finite_inverse_gate(kernel,[[1,'1'],[2,'-2'],[3,'7']],m)
        self.assertEqual(gate['status'],'rejected');self.assertEqual(gate['support_max'],3)
        self.assertEqual(len(gate['residual_prime_polynomial']),2)
        self.assertIn('moving support',gate['scope'])
        self.assertIn('unit',P.finite_inverse_gate(kernel,[[1,'2']],m)['reason'])
        self.assertEqual(P.finite_inverse_gate(dict(op='dirichlet_convolution',factors=[]),[[1,'1']],m)['status'],'delta_kernel')
        self.assertFalse(P.finite_inverse_gate(dict(op='dirichlet_convolution',factors=[]),[[1,'1'],[2,'3']],m)['exact_inverse'])

    def test_exact_PSD_multiplier_synthesis_and_replay(self):
        # x+y=z implies x²<=2y²+2z². No chosen Y or PSD Gram is given.
        m=meter();cert=P.quotient_psd([['-1','0','0'],['0','2','0'],['0','0','2']],[['1','1','-1']],m)
        self.assertEqual(cert['status'],'exact_PSD_modulo_relations')
        self.assertTrue(P.verify_quotient(cert,m));self.assertFalse(cert['uniform_bound_proved'])
        q=S.Matrix(cert['form']);p=S.Matrix(cert['PSD']);L=S.Matrix(cert['relations']);Y=S.Matrix(cert['multipliers'])
        self.assertEqual(q,p+L.T*Y+Y.T*L)
        bad=deepcopy(cert);bad['multipliers'][0][0]='0'
        with self.assertRaises(ValueError):P.verify_quotient(bad,m)
        bad=deepcopy(cert);bad['principal_minors'][0]['value']='-1'
        with self.assertRaises(ValueError):P.verify_quotient(bad,m)

    def test_unpaid_tail_and_free_trajectory_failure_not_source_refutation(self):
        m=meter();known=dict(name='known_rhs',paid=True,form=[['0','0','0'],['0','0','0'],['0','0','1']])
        tail=dict(name='complete_tail',paid=False,form=[['0','0','0'],['0','1','0'],['0','0','0']])
        result=P.search_forcing(['1','0','0'],[['1','1','-1']],[known,tail],grid=('0','1','2'),meter=m)
        self.assertEqual(result['status'],'OPEN_forcing');self.assertEqual(result['unpaid'],['complete_tail'])
        failed=P.search_forcing(['1','0','0'],[['1','1','-1']],[known],grid=('0','1','2','3'),meter=m)
        self.assertEqual(failed['status'],'no_certificate_in_grid');self.assertFalse(failed['actual_source_refuted'])
        with self.assertRaises(ValueError):P.quotient_psd([['1','1'],['0','1']],[],m)

    def test_actual_inverse_calibration_harmonic_dual_search(self):
        m=meter();s=source();cert=P.A.generate(s,m)
        result=P.harmonic_dual_search(s,cert,0,meter=m)
        self.assertEqual(result['status'],'proved');self.assertEqual(result['best']['uniform_constant'],'2')
        self.assertFalse(result['critical_prefix_recovery'])
        self.assertEqual(result['weight'],['-2','1/3'])
        # Universal floor approximation behind each candidate, no source samples.
        for row in result['candidates']:
            offset=Q(row['offset']);bound=Q(row['fractional_error'])
            for x in (Q(1),Q(5,3),Q(27,4),Q(100)):
                m.charge();self.assertLessEqual(abs(x.numerator//x.denominator-x-offset),bound)
        changed=source(1);changed_cert=P.A.generate(changed,m)
        self.assertEqual(P.harmonic_dual_search(changed,changed_cert,0,meter=m)['status'],'provider_not_applicable')


if __name__=='__main__':
    started=time.monotonic()
    suite=unittest.TestSuite(Prototype(name) for name in sys.argv[1:]) if sys.argv[1:] else unittest.defaultTestLoader.loadTestsFromTestCase(Prototype)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    work=sum(m.operations for m in METERS);code=0 if result.wasSuccessful() else 1
    path=Path(__file__).with_name('global_multiplier_proto_039_development.json')
    receipt=json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1',invocations=[])
    receipt['invocations'].append(dict(returncode=code,operations=work,tests=result.testsRun,
        failures=len(result.failures),errors=len(result.errors),elapsed_seconds=time.monotonic()-started,
        exposure='synthetic floor functions/rational matrices/source AST only; no arithmetic source values or archive'))
    receipt['cumulative_operations']=sum(v['operations'] for v in receipt['invocations'])
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print('SYNTHETIC_WORK module=global_multiplier_proto_039_test operations='+str(work))
    raise SystemExit(code)
