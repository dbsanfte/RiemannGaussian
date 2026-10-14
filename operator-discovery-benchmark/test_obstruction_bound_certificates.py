"""Exact synthetic certificate/argument checks, with no numerical scorer."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest

import obstruction_bound_certificates as C

METERS = []


class Meter:
    def __init__(self, cap=1000000): self.operations = 0; self.cap = cap; METERS.append(self)
    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('exact work charge')
        if n > self.cap - self.operations: raise OverflowError('synthetic work cap')
        self.operations += n


def tearDownModule():
    print('SYNTHETIC_WORK module=test_obstruction_bound_certificates operations=' +
          str(sum(m.operations for m in METERS)))


def value(form, assignments, meter):
    total = Q(0)
    for a, b, coefficient in form['terms']:
        meter.charge(3); total += Q(coefficient) * assignments[a] * assignments[b]
    return total


def graph():
    return dict(schema=C.GRAPH_SCHEMA, scope=C.scope('actual_mu_candidate10'),
                premises=[], nodes=[], reviewed_rules=[], equivalences=[], goals=[])


def premise(g, name, statement, kind='uniform_bound', status='open'):
    g['premises'].append(dict(id=name, kind=kind, statement=statement, status=status,
                             provenance='synthetic imported statement; not an independently verified theorem', scope=dict(g['scope'])))


def node(g, name, rule='obligation', deps=None, cert=None, status='open', kind='uniform_bound', statement=None):
    g['nodes'].append(dict(id=name, kind=kind, statement=statement or ('synthetic claim ' + name), status=status,
                          rule=rule, dependencies=[] if deps is None else list(deps), certificate=cert, scope=dict(g['scope'])))


def reviewed(g, name, deps, conclusion):
    g['reviewed_rules'].append(dict(id=name, premises=list(deps), conclusion=conclusion,
                                  provenance='synthetic reviewed implication; its premises remain required', scope=dict(g['scope'])))


def equivalence(g, name, a, b):
    g['equivalences'].append(dict(id=name, left=a, right=b,
                                 provenance='explicit synthetic review of two-way O(1) padding constants, not finite data', scope=dict(g['scope'])))


def recurrence_graph(meter, status='open'):
    g = graph(); cert = C.recurrence_certificate('1/2', '2', 1, '3', step_id='step', base_id='base', meter=meter)
    premise(g, 'step', cert['premises']['step'])
    premise(g, 'base', cert['premises']['base'], kind='base_bound', status='proven')
    node(g, 'goal', 'dyadic_recurrence', ['step', 'base'], cert, status=status)
    g['goals'] = ['goal']; return g


class CertificateTests(unittest.TestCase):
    def test_canonical_sparse_forms_and_monomial_convention(self):
        m = Meter()
        f = C.quadratic_form([['U', 'D', '1/2'], ['D', 'U', '3/2'], ['U', 'U', 2], ['U', 'U', -2]], m)
        self.assertEqual(f, {'terms': [['D', 'U', '2']]})
        self.assertTrue(C.verify_quadratic_form(f, m))
        self.assertEqual(value(f, {'U': Q(3), 'D': Q(4)}, m), 24)
        self.assertEqual(C.quadratic_form([['R', 'R', '0']], m), {'terms': []})
        for bad in ({'terms': [['U', 'D', '2']]}, {'terms': [['D', 'U', '2/1']]}, {'terms': [['D', 'U', '0']]}, {'terms': None}):
            with self.assertRaises(ValueError): C.verify_quadratic_form(bad, m)
        for coefficient in (0.5, True):
            with self.assertRaises(ValueError): C.quadratic_form([['U', 'D', coefficient]], m)

    def test_young_exact_gap_psd_and_tampering(self):
        m = Meter(); cert = C.young_certificate('1/3', meter=m)
        self.assertEqual(cert['gap'], {'terms': [['D', 'D', '3'], ['D', 'U', '-2'], ['U', 'U', '1/3']]})
        result = C.verify_certificate(cert, m)
        self.assertTrue(result['verified_algebra']); self.assertTrue(result['conditional'])
        self.assertFalse(result['uniform_bound_discharged'])
        for U, D in ((0, 0), (3, 1), (2, -4), (-1, 5)):
            self.assertGreaterEqual(value(cert['gap'], {'U': Q(U), 'D': Q(D)}, m), 0)
        bad = deepcopy(cert); bad['psd']['matrix'][0][1] = '0'
        with self.assertRaises(ValueError): C.verify_certificate(bad, m)
        bad = deepcopy(cert); bad['upper']['terms'].pop()
        with self.assertRaises(ValueError): C.verify_certificate(bad, m)
        for eta in ('0', '-1'):
            with self.assertRaises(ValueError): C.young_certificate(eta, meter=m)

    def test_transport_keeps_both_defect_squares_and_signed_crosses(self):
        m = Meter(); cert = C.transport_certificate('1', '-1/2', meter=m)
        self.assertEqual(cert['parent_coefficient'], '5/16')
        self.assertEqual(cert['correction'], {'terms': [['D0', 'D0', '1/4'], ['D0', 'R', '1/2'],
                                                      ['D1', 'D1', '1/4'], ['D1', 'R', '-1/4']]})
        self.assertTrue(C.verify_certificate(cert, m)['verified_algebra'])
        assignments = {'R': Q(3), 'D0': Q(-4), 'D1': Q(2)}
        m.charge(10); expected = ((assignments['R'] + assignments['D0']) ** 2
                                 + (-assignments['R'] / 2 + assignments['D1']) ** 2) / 4
        self.assertEqual(value(cert['child'], assignments, m), expected)
        bad = deepcopy(cert); bad['correction']['terms'] = [t for t in bad['correction']['terms'] if t[:2] != ['D1', 'R']]
        with self.assertRaises(ValueError): C.verify_certificate(bad, m)
        zero = C.transport_certificate(0, 0, meter=m)
        self.assertEqual(len(zero['correction']['terms']), 2)
        self.assertTrue(C.verify_certificate(zero, m)['verified_algebra'])

    def test_conditional_recurrence_bounded_log_and_complete_base(self):
        m = Meter()
        for rho, constant, base, bound in (('1/2', '2', '7', '7'), ('1/2', '2', '1', '4'), ('0', '2', '0', '2'), ('1', '0', '3', '3')):
            cert = C.recurrence_certificate(rho, constant, 1, base, meter=m)
            self.assertEqual(cert['classification'], 'bounded'); self.assertEqual(cert['uniform_bound'], bound)
            self.assertTrue(C.verify_certificate(cert, m)['verified_algebra'])
            f = Q(base)
            for _ in range(5):
                self.assertLessEqual(f, Q(bound)); m.charge(2); f = Q(rho) * f + Q(constant)
        log = C.recurrence_certificate(1, 2, 1, 3, meter=m)
        self.assertEqual(log['classification'], 'logarithmic'); self.assertIsNone(log['uniform_bound'])
        self.assertIn('k>=0', log['iterated_bound'])
        self.assertFalse(log['premise_proved']); self.assertFalse(log['RH_proved'])
        bad = deepcopy(log); bad['premise_proved'] = True
        with self.assertRaises(ValueError): C.verify_certificate(bad, m)
        for rho, constant, base in ((-1, 1, 1), ('3/2', 1, 1), (1, -1, 1), (1, 1, -1)):
            with self.assertRaises(ValueError): C.recurrence_certificate(rho, constant, 1, base, meter=m)

    def test_open_recurrence_premise_is_exposed_not_discharged(self):
        m = Meter(); g = recurrence_graph(m)
        result = C.verify_graph(g, m)
        self.assertEqual(result['verified_algebra_nodes'], ['goal'])
        self.assertEqual(result['goals'][0]['undischarged_leaf_classes'], ['step'])
        self.assertEqual(result['goals'][0]['proof_rank'], 1)
        self.assertFalse(result['goals'][0]['relatively_closed'])
        self.assertEqual(result['trusted_inputs'][0]['type'], 'external_reviewed_assumption')
        self.assertFalse(result['discharged_uniform_bound']); self.assertFalse(result['RH_proved'])

    def test_finite_or_open_evidence_cannot_close_a_uniform_goal(self):
        m = Meter(); g = recurrence_graph(m, status='proven')
        with self.assertRaisesRegex(ValueError, 'open or finite'): C.verify_graph(g, m)
        g['premises'][0].update(status='finite_evidence', kind='finite_evidence')
        with self.assertRaisesRegex(ValueError, 'open or finite'): C.verify_graph(g, m)
        g = graph(); node(g, 'sample', rule='finite_observation', status='finite_evidence', kind='finite_evidence')
        node(g, 'goal', rule='reviewed_implication', deps=['sample'], cert={'review_id': 'fit'}, status='proven')
        reviewed(g, 'fit', ['sample'], 'goal'); g['goals'] = ['goal']
        with self.assertRaisesRegex(ValueError, 'open or finite'): C.verify_graph(g, m)

    def test_external_closure_stays_relative_and_registry_is_not_a_theorem(self):
        m = Meter(); g = recurrence_graph(m, status='proven'); g['premises'][0]['status'] = 'proven'
        result = C.verify_graph(g, m)
        self.assertTrue(result['goals'][0]['relatively_closed'])
        self.assertEqual(result['undischarged_leaves'], [])
        self.assertEqual(len(result['trusted_inputs']), 2)
        self.assertFalse(result['goals'][0]['independently_discharged_uniform_bound'])
        self.assertFalse(result['RH_proved'])
        g = graph(); cert = C.young_certificate(1, meter=m)
        node(g, 'fake_bound', 'young_split', cert=cert, status='proven', kind='uniform_bound')
        with self.assertRaisesRegex(ValueError, 'not a uniform bound'): C.verify_graph(g, m)

    def test_equivalent_restatement_preserves_unresolved_proof_rank(self):
        m = Meter(); g = graph(); node(g, 'R')
        node(g, 'new_R', 'equivalent_restatement', ['R'], {'review_id': 'padding'})
        equivalence(g, 'padding', 'R', 'new_R'); g['goals'] = ['R', 'new_R']
        result = C.verify_graph(g, m)
        self.assertEqual([r['proof_rank'] for r in result['goals']], [1, 1])
        self.assertEqual(result['goals'][0]['equivalence_class'], result['goals'][1]['equivalence_class'])
        self.assertEqual(result['known_change_of_representation'], ['new_R'])
        self.assertFalse(result['discharged_uniform_bound'])
        g['nodes'][1]['status'] = 'proven'
        with self.assertRaisesRegex(ValueError, 'open or finite'): C.verify_graph(g, m)
        g['nodes'][1]['status'] = 'open'; g['equivalences'] = []
        with self.assertRaises(ValueError): C.verify_graph(g, m)

    def test_explicit_cycles_and_cycles_through_reviewed_equivalences(self):
        m = Meter(); g = graph()
        node(g, 'A', 'reviewed_implication', ['B'], {'review_id': 'rA'})
        node(g, 'B', 'reviewed_implication', ['A'], {'review_id': 'rB'})
        reviewed(g, 'rA', ['B'], 'A'); reviewed(g, 'rB', ['A'], 'B')
        with self.assertRaisesRegex(ValueError, 'cycle'): C.verify_graph(g, m)
        g = graph()
        node(g, 'A', 'reviewed_implication', ['B'], {'review_id': 'rA'})
        node(g, 'B', 'reviewed_implication', ['C'], {'review_id': 'rB'}); node(g, 'C')
        reviewed(g, 'rA', ['B'], 'A'); reviewed(g, 'rB', ['C'], 'B'); equivalence(g, 'eq', 'A', 'C')
        with self.assertRaisesRegex(ValueError, 'cycle'): C.verify_graph(g, m)
        g = graph(); node(g, 'A', 'reviewed_implication', ['B'], {'review_id': 'rA'}); node(g, 'B')
        reviewed(g, 'rA', ['B'], 'A'); equivalence(g, 'eq', 'A', 'B')
        with self.assertRaisesRegex(ValueError, 'circular'): C.verify_graph(g, m)

    def test_unknown_rules_source_full_domain_and_missing_base_rejected(self):
        m = Meter(); g = graph(); node(g, 'goal', rule='numerical_cancellation')
        with self.assertRaisesRegex(ValueError, 'unverified rule'): C.verify_graph(g, m)
        g = recurrence_graph(m); g['premises'][0]['scope']['source'] = 'coherent_one_control'
        with self.assertRaisesRegex(ValueError, 'same source'): C.verify_graph(g, m)
        g = recurrence_graph(m); g['scope']['domain'] = 'finite tested X=32,64'
        with self.assertRaises(ValueError): C.verify_graph(g, m)
        g = recurrence_graph(m); g['nodes'][0]['dependencies'] = ['step']
        with self.assertRaisesRegex(ValueError, 'including base'): C.verify_graph(g, m)
        g = recurrence_graph(m); cert = C.recurrence_certificate('1/2', 2, 2, 3, meter=m)
        g['nodes'][0]['certificate'] = cert
        with self.assertRaisesRegex(ValueError, 'domain/base'): C.verify_graph(g, m)

    def test_meter_is_shared_and_certificate_flags_cannot_be_promoted(self):
        m = Meter(); cert = C.transport_certificate('1/2', '1/2', meter=m); first = m.operations
        C.verify_certificate(cert, m); self.assertGreater(m.operations, first)
        cert['RH_proved'] = True
        with self.assertRaises(ValueError): C.verify_certificate(cert, m)
        limited = Meter(1)
        with self.assertRaises(OverflowError): C.young_certificate('1/2', meter=limited)
        self.assertEqual(limited.operations, 1)


if __name__ == '__main__': unittest.main()
