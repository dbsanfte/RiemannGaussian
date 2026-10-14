"""Tiny synthetic workflow checks; no study source, scale or response access."""
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from potential_candidate_language import Meter
import permuted_arithmetic_circuits as P
import check_permuted_arithmetic_circuits as C
import permuted_circuit_discovery as D
import run_permuted_circuit_discovery as R

METERS = []


def meter(cap=1000000, **kwargs):
    result = Meter(cap, **kwargs); METERS.append(result); return result


def tearDownModule():
    total = sum(m.operations for m in METERS)
    print('SYNTHETIC_WORK module=test_permuted_circuit_discovery operations=' + str(total))


def fixtures():
    m = meter()
    programs = [{'stages': []}, {'stages': [
        {'op': 'permute', 'map': {'kind': 'xor', 'mask': 'all'}, 'inverse': False},
        {'op': 'shear', 'coefficient': '-1/2', 'phase': ['constant', 1], 'direction': 'even_from_odd'},
        {'op': 'convolve', 'alpha': '1/6', 'prime_phase': ['constant', -1]}]}]
    catalog = [dict(id=i, evaluation_id=i, family='baseline' if i == 0 else D.FAMILIES[0],
                    program=p, certificate=P.certificate(p, m), complexity=len(D.canonical(p))) for i, p in enumerate(programs)]
    cases = []
    for H, scales in ((7, [2, 4]), (31, [8, 16])):
        for s in D.SOURCES:
            for i in range(2):
                E = 8 if i == 0 else {'mu': 2, 'one': 4, 'partial_prime_13': 8}[s]
                cases.append(dict(id=i, source=s, horizon=H, scales=scales, status='available', initial_cost='1',
                                  cases=[dict(X=X, energy=str(E), absolute_energy='8') for X in scales]))
    return catalog, cases


class WorkflowTests(unittest.TestCase):
    def test_catalogue_full_payload_reconstruction_and_aliases(self):
        produced = D.generate_catalog(meter(), P)
        checked = D.generate_catalog(meter(), C)
        self.assertEqual(produced, checked)
        self.assertEqual(len(produced), 49)
        self.assertEqual([sum(r['family'] == f for r in produced) for f in D.FAMILIES], [12] * 4)
        self.assertEqual(produced[27]['evaluation_id'], 0)
        self.assertTrue(produced[27]['normalization']['rewrites'])
        for r in produced:
            self.assertLessEqual(sum(s['op'] == 'convolve' for s in r['raw_program']['stages']), 2)
            self.assertLessEqual(sum(s['op'] == 'permute' for s in r['raw_program']['stages']), 2)
            self.assertLessEqual(sum(s['op'] == 'shear' for s in r['raw_program']['stages']), 1)
        self.assertEqual(produced[37]['calibration'], 'generic_smoothness_not_prime_information')

    def test_one_authentic_tiny_case_per_family_and_baseline(self):
        catalog = D.generate_catalog(meter(), P)
        # Synthetic all-one input at the complete tiny horizon31. Full head is
        # still1..31; no altered production diagnostic definition.
        values = [0] + [1] * 31
        for i in (0, 1, 13, 25, 37):
            record = catalog[i]
            a = D.evaluate_case(record, 'one', 31, [4, 8, 16], meter(), P, values)
            b = D.evaluate_case(record, 'one', 31, [4, 8, 16], meter(), C, values)
            self.assertEqual(a, b); self.assertEqual(a['status'], 'available')
            for c in a['cases']:
                self.assertLessEqual(Q(c['energy']), Q(c['absolute_energy']))

    def test_mu_only_training_fit_exact_kappa_and_squared_cost(self):
        catalog, cases = fixtures()
        a = D.analyze_discovery(catalog, cases, meter(), [2, 4], [8, 16])
        b = R.independent_analysis(catalog, cases, meter(), [2, 4], [8, 16])
        self.assertEqual(a, b)
        self.assertEqual(a[1]['constants'], {str(q): '1' for q in D.LEVELS})
        self.assertEqual(a[1]['specificity'], '1/2')
        self.assertEqual(a[1]['raw_ratio'], '1/4')
        self.assertEqual(a[1]['conditional_cost'], str(9 * 4 * 13**2 * 49))
        controls_changed = deepcopy(cases)
        for r in controls_changed:
            if r['horizon'] == 7 and r['source'] != 'mu':
                for c in r['cases']: c.update(energy='1000', absolute_energy='1000')
        self.assertEqual(D.analyze_discovery(catalog, controls_changed, meter(), [2, 4], [8, 16])[1]['constants'], a[1]['constants'])

    def test_zero_denominators_inactive_and_invalid_envelope(self):
        self.assertEqual(D._ratio('0', '0', meter(), True), dict(status='defined', value='1', inactive=True))
        self.assertEqual(D._ratio('0', '0', meter())['status'], 'undefined')
        with self.assertRaises(ValueError): D._ratio('1', '0', meter(), True)
        catalog, cases = fixtures()
        for r in cases:
            if r['id'] == 1 and r['source'] == 'one' and r['horizon'] == 31:
                for c in r['cases']: c['energy'] = '0'
        a = D.analyze_discovery(catalog, cases, meter(), [2, 4], [8, 16])
        self.assertEqual(a, R.independent_analysis(catalog, cases, meter(), [2, 4], [8, 16]))
        self.assertEqual(a[1]['status'], 'ineligible')
        self.assertEqual(a[1]['reason'], 'undefined_matched_validation_diagnostic')
        self.assertEqual(a[1]['diagnostics'][0]['specificity']['status'], 'undefined')
        for r in cases:
            if r['id'] == 1 and r['source'] == 'one' and r['horizon'] == 31:
                for c in r['cases']: c.update(energy='1', absolute_energy='0')
        for analysis in (D.analyze_discovery, R.independent_analysis):
            with self.assertRaises(ValueError): analysis(catalog, cases, meter(), [2, 4], [8, 16])

    def test_missing_scales_head_and_baseline_alias_screen(self):
        catalog, cases = fixtures()
        incomplete = deepcopy(cases); incomplete[-1].update(status='missing', reason='synthetic interruption', cases=[])
        a = D.analyze_discovery(catalog, incomplete, meter(), [2, 4], [8, 16])
        self.assertEqual(a, R.independent_analysis(catalog, incomplete, meter(), [2, 4], [8, 16]))
        self.assertEqual(a[1]['status'], 'ineligible')
        catalog.append(dict(catalog[0], id=2, family=D.FAMILIES[2]))
        a = D.analyze_discovery(catalog, cases, meter(), [2, 4], [8, 16])
        self.assertEqual(a[2]['reason'], 'baseline_alias')
        self.assertEqual(a, R.independent_analysis(catalog, cases, meter(), [2, 4], [8, 16]))
        malformed = deepcopy(cases); malformed[-1]['cases'].pop()
        for analysis in (D.analyze_discovery, R.independent_analysis):
            with self.assertRaises(ValueError): analysis(catalog, malformed, meter(), [2, 4], [8, 16])
        malformed = deepcopy(cases); malformed[-1]['initial_cost'] = '2'
        for analysis in (D.analyze_discovery, R.independent_analysis):
            with self.assertRaises(ValueError): analysis(catalog, malformed, meter(), [2, 4], [8, 16])

    def test_pareto_failure_priority_and_unique_family_leads(self):
        def row(i, f, eid, failures, raw, specific, cost):
            return dict(id=i, family=D.FAMILIES[f], evaluation_id=eid, status='eligible', gate_failures=failures,
                        raw_ratio=str(raw), specificity=str(specific), conditional_cost=str(cost), complexity=1)
        rows = [row(1, 0, 1, 1, 1, 1, 1), row(2, 0, 2, 0, 10, 10, 10), row(3, 0, 3, 0, 2, 2, 2),
                row(4, 1, 3, 0, 1, 1, 1), row(5, 1, 5, 0, 2, 2, 2), row(6, 2, 3, 0, 1, 1, 1),
                row(7, 3, 7, 0, 3, 1, 4), row(8, 3, 8, 0, 1, 3, 2)]
        selected = D.select_leads(rows, meter())
        self.assertEqual(selected, R.independent_selection(rows, meter()))
        self.assertEqual(selected['selected_ids'], [0, 3, 5, 7])
        self.assertEqual(selected['missing_families'], [D.FAMILIES[2]])
        self.assertEqual(next(r for r in selected['ranking'] if r['id'] == 2)['pareto_layer'], 1)
        self.assertEqual(next(r for r in selected['ranking'] if r['id'] == 7)['pareto_layer'], 0)

    def test_exact_ceil_roots_and_finite_gates(self):
        m = meter()
        for X, q, expected in ((1, 2, 1), (16, 2, 4), (17, 2, 5), (63, 6, 2)):
            self.assertEqual(D.ceil_root(X, q, m), expected)
        fitted = {str(q): '1' for q in D.LEVELS}
        result = D.scores([dict(X=4, energy='2'), dict(X=5, energy='3')], fitted, m)
        self.assertTrue(result[0]['passed']); self.assertTrue(result[0]['dyadic'])
        self.assertFalse(result[-1]['passed']); self.assertFalse(result[-1]['dyadic'])

    def test_bounded_failure_preserves_no_fabricated_moments(self):
        record = dict(evaluation_id=0, program={'stages': []})
        result = D.evaluate_case(record, 'one', 31, [16], meter(1), P, [0] + [1] * 31)
        self.assertEqual(result['status'], 'missing'); self.assertEqual(result['cases'], [])
        self.assertNotIn('initial_cost', result)

    def test_receipt_schemas_and_frozen_suite_cumulative_charge(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            records = [dict(operations=7, runs=[dict(operations=3, returncode=1), dict(operations=4, returncode=0)]),
                       dict(cumulative_operations=11, invocations=[dict(operations=11, returncode=0)]),
                       dict(operations=13, runs=[dict(operations=13, returncode=0)])]
            for name, data in zip(R.DEVELOPMENT, records): R.write(root / name, data)
            with patch.object(R, 'ROOT', root):
                self.assertEqual(len(R.development_receipts()), 3)
                stdout = '\n'.join('SYNTHETIC_WORK module=' + name + ' operations=5' for name in R.TESTS)
                receipt = R.synthetic_receipt(stdout)
                self.assertEqual(receipt['total'], R.ROOT_RESERVE + 31 + 15)
                with self.assertRaises(ValueError): R.synthetic_receipt(stdout + '\n' + stdout.splitlines()[0])
                records[0]['operations'] = 4
                (root / R.DEVELOPMENT[0]).write_text(D.canonical(records[0]))
                with self.assertRaises(ValueError): R.development_receipts()

    def test_append_only_markers_and_resident_cap(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'started.json'
            R.write(path, {'once': True})
            with self.assertRaises(FileExistsError): R.write(path, {'twice': True})
            checkpoint = Path(directory) / 'completed.jsonl'
            R.append_checkpoint(checkpoint, {'id': 1}); R.append_checkpoint(checkpoint, {'id': 2})
            self.assertEqual(len(checkpoint.read_text().splitlines()), 2)
        m = R.ResidentMeter(10, max_cells=1000001); METERS.append(m)
        m.live(1)
        with self.assertRaises(OverflowError): m.live(2)
        self.assertEqual(m.peak_live_cells, 1000002)
        self.assertFalse(any(D.obligation(dict(id=1, program={'stages': []}, certificate={})) [k] for k in D.FLAGS))


if __name__ == '__main__': unittest.main()
