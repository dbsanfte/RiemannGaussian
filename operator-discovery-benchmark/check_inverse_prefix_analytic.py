"""Independent post-queue symbolic admission checker; no producer imports.

Finite fits are checked against an error-polynomial induction certificate.
Admission never proves an actual signed Lyapunov innovation inequality.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

FEATURES = ('one', 'k', 'r', 'r_is_one', 'same', 'left', 'right',
            'previous', 'previous_left', 'k_same', 'r_same')


def _rational(value):
    if isinstance(value, (float, bool)) or not isinstance(value, (str, int, Fraction)):
        raise ValueError('exact rational strings or integers required')
    return Fraction(value)


def _positive_integer(value):
    if type(value) is not int or value < 1:
        raise ValueError('positive integer required')
    return value


def _key(value):
    if not isinstance(value, str) or str(int(value)) != value or int(value) < 1:
        raise ValueError('canonical positive integer string key required')
    return int(value)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


def recurrence_certificate(model):
    """Check inferred coefficients, then prove their unrestricted continuation.

    Feature functions are independent symbolic atoms except k_same=k*same
    and r_same=r*same; this is a sufficient symbolic admission criterion.
    Duplicate terms are combined before comparison, including exact zeros.
    """
    checks = {}
    reason = None
    try:
        coefficients = {name: Fraction(0) for name in FEATURES}
        relation = model['selected_recurrence']
        for term in relation['terms']:
            if not isinstance(term, list) or len(term) != 2 or term[0] not in FEATURES:
                raise ValueError('invalid recurrence term')
            coefficients[term[0]] += _rational(term[1])
        expected = {name: Fraction(0) for name in FEATURES}
        expected.update(same=Fraction(1), left=Fraction(-1), r_is_one=Fraction(1))
        checks['symbolic_recurrence_same_minus_left_plus_r_is_one'] = coefficients == expected
        checks['unit_seed'] = (type(model['initial_arity']) is int and
                               model['initial_arity'] == 1 and
                               [_rational(x) for x in model['initial_weights']] == [Fraction(1)])
        vectors = {_key(k): [_rational(x) for x in v]
                   for k, v in model['learned_vectors'].items()}
        table = {_key(k): [_rational(x) for x in v]
                 for k, v in model['coefficient_table'].items()}
        checks['nonempty_matching_observed_arities'] = bool(table) and set(table) == set(vectors)
        checks['full_vectors_have_2k_plus_2_entries'] = all(len(v) == 2*k+2 for k,v in vectors.items())
        checks['all_wrong_and_constant_columns_zero'] = all(all(x == 0 for x in v[k:]) for k,v in vectors.items())
        checks['coefficient_table_is_first_k_entries'] = all(len(v) == k and vectors.get(k, [])[:k] == v for k,v in table.items())
        checks['observed_seed_one'] = table.get(1) == [Fraction(1)]
        # Derive the continuation independently from the admitted symbolic rule.
        # Comparing all supplied rows also checks gaps between observed arities.
        row = [Fraction(1)]
        agrees = True
        for k in range(1, max(table, default=1)+1):
            if k in table and table[k] != row:
                agrees = False
            row = [(row[r-1] if r <= k else 0)
                   - (row[r-2] if 2 <= r <= k+1 else 0)
                   + (1 if r == 1 else 0) for r in range(1,k+2)]
        checks['every_observed_row_agrees_with_recurrence'] = agrees
    except (ValueError, TypeError, KeyError, ZeroDivisionError, AttributeError) as exc:
        reason = str(exc)
        checks['well_formed_exact_model'] = False
    admitted = reason is None and bool(checks) and all(checks.values())
    return {
        'kind': 'inverse_prefix_error_polynomial_certificate',
        'admitted': admitted, 'checks': checks, 'rejection_reason': reason,
        'global_reconstruction_proved': admitted,
        'premises': ['h(1)=1', 'a*h=delta', 'integer k>=1', 'integer u>=0',
                     'integer x>=1', 'x<(u+1)^k'],
        'coefficient_polynomial': 'P_1(t)=t; P_(k+1)(t)=(1-t)P_k(t)+t; P_k(t)=1-(1-t)^k',
        'error_identity': 'a-sum_(r=1)^k c_(k,r) a_u^{*r}*h^{*(r-1)} = a*(delta-a_u*h)^{*k}',
        'support_argument': 'delta-a_u*h=(a-a_u)*h is supported on indices >=u+1; its kth convolution vanishes at every n<(u+1)^k; multiplication by a preserves this support',
        'prefix_conclusion': 'sum_(n<=x)a(n)=sum_(r=1)^k c_(k,r) sum_(n<=x)(a_u^{*r}*h^{*(r-1)})(n)',
        'all_integer_arities': True, 'semantic_arity_cap': False,
        'actual_signed_upper_bound_proved': False,
        'finite_tests_are_global_signed_proof': False,
    }


def potential_certificate(program):
    """Prove nonnegativity only; global innovation remains an explicit premise."""
    checks = {}
    reason = None
    try:
        terms = program['terms']
        if not isinstance(terms, list):
            raise ValueError('terms must be a list')
        weights_ok = features_ok = True
        for term in terms:
            weights_ok &= _rational(term['weight']) >= 0
            feature = term['feature']
            k = _positive_integer(feature['arity'])
            slot = _positive_integer(feature['slot'])
            features_ok &= slot <= k and _rational(feature['normalizing_power']) >= 0
        constants = program['fitted_constants']
        if not isinstance(constants, dict) or not constants:
            raise ValueError('nonempty per-level constants required')
        for q, value in constants.items():
            _key(q)
            if _rational(value) <= 0:
                raise ValueError('per-level fitted constant must be positive')
        checks.update(nonnegative_exact_weights=bool(weights_ok),
                      valid_arity_slot_and_nonnegative_rational_power=bool(features_ok),
                      positive_scale_independent_per_level_constants=True)
    except (ValueError, TypeError, KeyError, ZeroDivisionError, AttributeError) as exc:
        reason = str(exc)
        checks['well_formed_exact_program'] = False
    admitted = reason is None and bool(checks) and all(checks.values())
    return {
        'kind': 'nonnegative_inverse_prefix_potential_certificate',
        'admitted': admitted, 'checks': checks, 'rejection_reason': reason,
        'global_potential_nonnegativity_proved': admitted,
        'potential_semantics': 'V(X)=sum lambda_i B_(arity_i,slot_i)(X)/ceil(X^p_i); B is the exact reconstructed-component square energy on [X,2X)',
        'ceiling_semantics': 'full rational power ceiling, positive integer denominator; no separately rounded factor substitution',
        'conditional_cofinal_RH_if_innovation_inequality': admitted,
        'missing_premise': 'exists q0, every integer q>=q0, some finite C_q independent of X, every dyadic X>=1: E(2X)+V(2X)<=E(X)+V(X)+C_q ceil(X^(1/q))',
        'initialization': 'E(1)=1; finite exact V(1) is charged',
        'exact_telescope': 'E(2^J)+V(2^J)<=1+V(1)+C_q sum_(j=0)^(J-1) ceil(2^(j/q))',
        'geometric_bound': 'sum_(j<J)ceil(2^(j/q))<=2(2^(J/q)-1)/(2^(1/q)-1)',
        'proof_reference': 'candidate-review-results/sol-6.1-proof-routes-001/route-05.txt: sections 1-4',
        'unobserved_level_constants_known': False,
        'all_scale_actual_premise_proved': False,
        'global_signed_upper_bound_proved': False, 'RH_proved': False,
        'semantic_arity_cap': False,
    }


RECONSTRUCTION_FIELDS = frozenset(('admitted', 'global_reconstruction_proved',
    'all_integer_arities', 'semantic_arity_cap', 'actual_signed_upper_bound_proved'))
POTENTIAL_FIELDS = frozenset(('admitted', 'global_potential_nonnegativity_proved',
    'conditional_cofinal_RH_if_innovation_inequality', 'all_scale_actual_premise_proved',
    'global_signed_upper_bound_proved', 'RH_proved', 'semantic_arity_cap'))


def actual_component_envelope_certificate(program):
    """Elementary tuple-count envelope, separate from the innovation claim."""
    native = potential_certificate(program)
    subpower = native['admitted'] and all(
        _rational(term['weight']) == 0 or
        _rational(term['feature']['normalizing_power']) >= 3
        for term in program.get('terms', []))
    return {
        'premises': ['h(n)=1 at every positive integer', 'a(n)=mu(n)',
                     '|mu(n)|<=1', 'a_u is the exact cutoff truncation of a'],
        'component': 'F_r(n)=sum_(m<=n)(a_u^{*r}*h^{*(r-1)})(m)',
        'coefficient_bound': '|(a_u^{*r}*h^{*(r-1)})(m)|<=d_(2r-1)(m)',
        'tuple_count_proof': 'For m>=1, ordered positive integer m-tuples of product <=n have count T_m(n)<=n(1+log n)^(m-1). Base T_1(n)=floor(n)<=n; induction sums T_(m-1)(n/d) over 1<=d<=n and uses sum_(d<=n)1/d<=1+log n.',
        'prefix_envelope': '|F_r(n)|<=n(1+log n)^(2r-2)',
        'square_block_envelope': 'sum_(n=X)^(2X-1) F_r(n)^2 <=4X^3(1+log(2X))^(4r-4)',
        'normalized_feature_envelope': 'B_(k,r)(X)/ceil(X^p)<=4X^(3-p)(1+log(2X))^(4r-4)',
        'globally_subpower_potential_if_all_active_powers_at_least_three': subpower,
        'meaning_of_subpower': 'For every eta>0, some finite K_eta independent of X bounds V(X)<=K_eta X^eta on every dyadic X>=1.',
        'actual_mertens_energy_bound_proved': False,
        'actual_innovation_bound_proved': False,
    }


def _exact_projected_match(backend, native, fields):
    return (isinstance(backend, dict) and set(backend) == fields and
            all(type(backend[key]) is bool for key in fields) and
            backend == {key: native[key] for key in fields})


def verify_run(run_dir):
    """Compare a fixed narrow backend contract against independent proofs.

    Successful verification is immutable. Every declared code/proof input
    must match protocol, frozen source and workspace bytes; checker is included.
    """
    run_dir = Path(run_dir)
    destination = run_dir/'analytical_verification.json'
    if destination.exists():
        raise FileExistsError('refusing to overwrite existing analytical verification')
    names = ('protocol.json', 'proof_queue.json', 'analytical_review.json')
    raw = {name: (run_dir/name).read_bytes() for name in names}
    data = {name: json.loads(value) for name,value in raw.items()}
    queue = data['proof_queue.json']; backend = data['analytical_review.json']
    native_reconstruction = recurrence_certificate(queue['reconstruction_inference'])
    checks = {
        'queue_protocol_hash_matches': queue.get('protocol_sha256') == digest(data['protocol.json']),
        'backend_top_level_no_RH_or_actual_signed_overclaim': (backend.get('RH_proved') is False and
            backend.get('actual_full_signed_innovation_bound_proved') is False and
            all(backend.get(key, False) is False for key in (
                'actual_all_scale_signed_bound_proved', 'global_actual_signed_innovation_bound_proved',
                'global_signed_upper_bound_proved', 'actual_signed_upper_bound_proved'))),
        'backend_finite_fits_scope_explicit': backend.get('numerical_fits_do_not_establish_all_scale_estimates') is True,
        'source_queue_hash_matches': backend.get('source_queue_sha256') == hashlib.sha256(raw['proof_queue.json']).hexdigest(),
        'protocol_hash_matches': backend.get('protocol_sha256') == digest(data['protocol.json']),
        'reconstruction_certificate_matches': _exact_projected_match(
            backend.get('reconstruction_certificate'), native_reconstruction, RECONSTRUCTION_FIELDS),
    }
    root = Path(__file__).resolve().parent
    frozen = run_dir/'frozen_source'
    expected_names = {'inverse_prefix_grammar.py', 'inverse_prefix_search.py',
        'inverse_prefix_analytic.py', 'inverse_prefix_report.py', 'inverse_prefix_proof.txt',
        'check_inverse_prefix_math.py', 'check_inverse_prefix_search.py',
        'check_inverse_prefix_analytic.py', 'test_inverse_prefix_contracts.py', 'plot_inverse_prefix.py'}
    declared = data['protocol.json'].get('code_sha256', {})
    code_hashes = {}
    code_matches = isinstance(declared, dict) and set(declared) == expected_names
    for name in sorted(expected_names):
        file, live = frozen/name, root/name
        frozen_hash = hashlib.sha256(file.read_bytes()).hexdigest() if file.is_file() else None
        live_hash = hashlib.sha256(live.read_bytes()).hexdigest() if live.is_file() else None
        protocol_hash = declared.get(name) if isinstance(declared, dict) else None
        code_hashes[name] = {'frozen_sha256': frozen_hash, 'live_sha256': live_hash,
                             'protocol_sha256': protocol_hash}
        code_matches &= frozen_hash is not None and frozen_hash == live_hash == protocol_hash
    checks['all_frozen_code_matches_workspace'] = bool(code_matches)
    rows = queue['potential_queue']; attempts = backend['potential_attempts']
    ids = [row['program_id'] for row in rows]
    attempt_ids = [row['program_id'] for row in attempts]
    checks['unique_complete_potential_ids'] = (len(ids)==len(set(ids)) and len(attempt_ids)==len(set(attempt_ids)) and set(ids)==set(attempt_ids))
    by_id = {row['program_id']: row for row in attempts}
    comparisons = []
    for row in rows:
        program = row['exact_program']; pid = row['program_id']
        actual = potential_certificate(program)
        attempt = by_id.get(pid, {})
        good = (set(attempt) == {'program_id', 'exact_program_sha256', 'certificate'} and
                attempt.get('exact_program_sha256') == digest(program) and
                _exact_projected_match(attempt.get('certificate'), actual, POTENTIAL_FIELDS))
        comparisons.append({'program_id': pid, 'exact_program_sha256': digest(program),
                            'certificate_matches': good, 'native_certificate': actual,
                            'actual_component_envelope': actual_component_envelope_certificate(program)})
    checks['all_potential_certificates_match'] = all(row['certificate_matches'] for row in comparisons)
    if not all(checks.values()):
        raise ValueError('analytical backend certificate disagreement: '+json.dumps(checks,sort_keys=True))
    result = {'schema': 1, 'independent_checker': Path(__file__).name,
              'input_sha256': {name: hashlib.sha256(value).hexdigest() for name,value in raw.items()},
              'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'frozen_code_hashes': code_hashes,
              'checks': checks, 'potential_comparisons': comparisons,
              'native_reconstruction_certificate': native_reconstruction,
              'backend_certificates_independently_agree': True, 'all_passed': True,
              'mathematical_audit_imports_production_code': False,
              'actual_all_scale_signed_bound_proved': False, 'RH_proved': False}
    # Exclusive creation also protects against a concurrent successful writer.
    with destination.open('x') as stream:
        stream.write(json.dumps(result,indent=2)+'\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', required=True)
    args = parser.parse_args()
    result = verify_run(args.run_dir)
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
