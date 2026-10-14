#!/usr/bin/env python3
"""Post-freeze formal error-polynomial and potential admission backend."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import comb
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parent


def read(p):
    return json.loads(Path(p).read_text())


def digest(v):
    return hashlib.sha256(json.dumps(v, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def reconstruction(model):
    # Numerical discovery supplies the recurrence. The AFTER-freeze proof
    # method admits error polynomials multiplied by (1-z) and checks the
    # observed rows by an independent binomial expansion.
    expected = {'r_is_one': Q(1), 'same': Q(1), 'left': Q(-1)}
    terms = {}
    try:
        for name, c in model['selected_recurrence']['terms']:
            terms[name] = terms.get(name, Q(0)) + Q(c)
        terms = {k: v for k, v in terms.items() if v}
        admitted = model['initial_arity'] == 1 and list(map(Q, model['initial_weights'])) == [Q(1)] and terms == expected
        for k, row in model['coefficient_table'].items():
            j = int(k)
            correct = [Q((-1) ** (r - 1) * comb(j, r)) for r in range(1, j + 1)]
            vector = list(map(Q, model['learned_vectors'][k]))
            admitted = admitted and list(map(Q, row)) == correct and vector == correct + [Q(0)] * (j + 2)
        admitted = admitted and bool(model['coefficient_table']) and model['coefficient_table'].get('1') == ['1']
    except (KeyError, TypeError, ValueError):
        admitted = False
    return {'admitted': bool(admitted), 'global_reconstruction_proved': bool(admitted),
        'all_integer_arities': True, 'semantic_arity_cap': False,
        'actual_signed_upper_bound_proved': False}


def potential(program):
    try:
        admitted = bool(program['fitted_constants'])
        for term in program['terms']:
            f = term['feature']; k, r = f['arity'], f['slot']
            admitted = admitted and type(k) is int and k >= 1 and type(r) is int and 1 <= r <= k
            admitted = admitted and Q(f['normalizing_power']) >= 0 and Q(term['weight']) >= 0
        for q, c in program['fitted_constants'].items():
            admitted = admitted and str(int(q)) == q and int(q) > 0 and Q(c) > 0
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        admitted = False
    return {'admitted': bool(admitted), 'global_potential_nonnegativity_proved': bool(admitted),
        'conditional_cofinal_RH_if_innovation_inequality': bool(admitted),
        'all_scale_actual_premise_proved': False, 'global_signed_upper_bound_proved': False,
        'RH_proved': False, 'semantic_arity_cap': False}


def review(d):
    d = Path(d).resolve(); spec, queue = read(d / 'protocol.json'), read(d / 'proof_queue.json')
    path = d / 'analytical_review.json'
    if path.exists():
        raise FileExistsError('Keep the completed analytical attempt immutable')
    result = {'protocol_sha256': digest(spec),
        'source_queue_sha256': hashlib.sha256((d / 'proof_queue.json').read_bytes()).hexdigest(),
        'reconstruction_certificate': reconstruction(queue['reconstruction_inference']),
        'potential_attempts': [{'program_id': row['program_id'], 'exact_program_sha256': digest(row['exact_program']),
            'certificate': potential(row['exact_program'])} for row in queue['potential_queue']],
        'actual_full_signed_innovation_bound_proved': False,
        'numerical_fits_do_not_establish_all_scale_estimates': True, 'RH_proved': False}
    path.write_text(json.dumps(result, indent=2) + '\n')
    subprocess.run([sys.executable, str(BASE / 'check_inverse_prefix_analytic.py'), '--run-dir', str(d)], cwd=BASE, check=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--run-dir', required=True, type=Path)
    review(p.parse_args().run_dir)
