#!/usr/bin/env python3
"""Frozen actual-arithmetic search with conditional pole-multiplicity admission."""
import argparse
import builtins
from fractions import Fraction as F
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import fixed_pole_filter_search as search
from detector_workflow_guard import require_verified_runtime

BASE = Path(__file__).resolve().parent
CODE = ['run_fixed_pole_filter.py', 'test_run_fixed_pole_filter.py',
        'fixed_pole_filter_search.py', 'test_fixed_pole_filter_search.py',
        'fixed_pole_filter_checks.py', 'test_fixed_pole_filter_checks.py',
        'check_fixed_pole_filter_run.py', 'test_check_fixed_pole_filter_run.py',
        'arithmetic_filter_pole_budget.py', 'arithmetic_filter_pole_budget_proof.txt',
        'test_arithmetic_filter_pole_budget.py', 'detector_safe_evaluation.py',
        'inverse_prefix_grammar.py', 'detector_workflow_guard.py',
        'prime_power_pairing.py', 'prime_power_pairing_proof.txt',
        'test_prime_power_pairing.py']
OUTPUTS = ['candidate_batch.json', 'validation.json', 'proof_queue.json']
INPUTS = ['training.json', 'validation_data.json']
CLAIM = ('For the exact actual target and fixed filter specified by the program, '
         'there exists an integer q0>=1 such that for every integer q>=q0 there '
         'exists finite Kq>=0 independent of X such that for every dyadic integer '
         'X>=1, sum_(n=X)^(2X-1)|G(n)|^2 <= Kq X^2 ceil(X^(1/q)). '
         'Here a=mu^{*r}*lambda^{*l}, A(x)=sum_(n<=x)a(n), and '
         'G(x)=sum_j w_j A(floor(x/d_j)); all coefficients, terms and boundaries '
         'are retained. Stored direct and innovation constants are finite fits, '
         'not assertions of the unknown existential constants.')


def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(value): return search.digest(value)


def write(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def target_key(candidate):
    t = candidate['program']['target']
    return t['r'], t['l']


def maximum_constant(candidate, mode):
    return max([F(x) for x in candidate['program']['constants'][mode].values()
                if x is not None] or [F(0)])


def rank(candidate, score, baseline=None):
    constants = candidate['program']['constants']
    missing = sum(s['missing_cases'] for s in score['modes'].values())
    missing += sum(x is None for row in constants.values() for x in row.values())
    failures = sum(s['finite_failures'] for s in score['modes'].values())
    direct, innovation = [maximum_constant(candidate, m) for m in ('direct', 'innovation')]
    if baseline is not None:
        direct /= max(F(1), maximum_constant(baseline, 'direct'))
        innovation /= max(F(1), maximum_constant(baseline, 'innovation'))
    terms = candidate['program']['filter']
    return (missing, failures, direct, innovation,
            sum(abs(F(t['weight'])) for t in terms if t['divisor'] != 1),
            len(terms), candidate['program_id'])


def select(factory, results):
    candidates = factory['candidates']
    scores = {r['program_id']: r['score'] for r in results}
    baselines = {target_key(c): c for c in candidates if len(c['program']['filter']) == 1}
    queue, decisions = {}, []
    groups = [('target', t) for t in search.TARGETS]
    groups += [('c_baseline', None), ('composition_square', None), ('inferred', None)]
    for group, target in groups:
        if group == 'target':
            eligible = [c for c in candidates if c['program']['target'] == target]
        elif group == 'c_baseline':
            eligible = [baselines[(1, 1)]]
        else:
            eligible = [c for c in candidates if any(o['kind'] == group for o in c['origins'])]
        def order(c):
            baseline = baselines[target_key(c)] if group in ('composition_square', 'inferred') else None
            return rank(c, scores[c['program_id']], baseline)
        chosen = min(eligible, key=order) if eligible else None
        label = {'kind': group, 'target': target}
        decisions.append(dict(group=label, eligible_ids=sorted(c['program_id'] for c in eligible),
                              selected_id=None if chosen is None else chosen['program_id'],
                              rank=None if chosen is None else [str(x) if isinstance(x, F) else x for x in order(chosen)]))
        if chosen is None:
            continue
        pid = chosen['program_id']
        if pid not in queue:
            queue[pid] = dict(program_id=pid, exact_program=chosen['program'],
                             exact_program_sha256=digest(chosen['program']),
                             global_claim=CLAIM, precise_claim_sha256=digest(CLAIM),
                             conditional_admission=chosen['admission'], selection_origins=[],
                             validation_score=scores[pid], global_bound_proved=False)
        queue[pid]['selection_origins'].append(label)
    return sorted(queue.values(), key=lambda c: c['program_id']), decisions


def specification():
    import numpy
    prior = 'convolution-control-results/pilot-001/verification.json'
    gate = 'convolution-control-results/pole-budget-001/verification.json'
    return dict(schema=1, version='fixed-pole-filter-v1',
                code_sha256={name: sha(BASE / name) for name in CODE},
                dictionary=search.DICTIONARY, dictionary_sha256=search.DICTIONARY_SHA256,
                training_scales=[2**j for j in range(14)],
                validation_scales=[12288, 16384, 24576], levels=[2, 3, 6, 12],
                final_levels=[3, 12, 17, 29], global_claim=CLAIM,
                budgets=dict(work=1000000000, max_n=1048575, bit=1000000),
                final_generation=dict(fixed=[32768, 65536], odd_min=40001, odd_count=5000,
                                      formula='40001+2*(int(seal_sha256[:16],16)%5000)'),
                selection=dict(groups='one per target plus c baseline, best composition and best inferred',
                               rank=['missing', 'validation_failures_both_modes', 'max_direct_training_constant',
                                     'max_innovation_training_constant', 'nonleading_l1', 'support', 'program_id'],
                               cross_target_normalization='constants divided by max(1, own-target baseline constant)'),
                runtime=dict(python=sys.version, numpy=numpy.__version__),
                provenance=dict(prior_verifications={prior: sha(BASE / prior), gate: sha(BASE / gate)},
                                actual_source='complete prime sieve and generic full Dirichlet convolution',
                                coefficient_history_overlap=True, unseen_prime_holdout=False,
                                guided_design='target arities, divisor grid, exact least squares and composition rules supplied before scoring',
                                actual_all_scale_signed_bound_proved=False))


def dataset(spec, scales):
    b = spec['budgets']
    return dict(protocol_sha256=digest(spec), data=search.build_dataset(
        scales, work_budget=b['work'], max_n=b['max_n']))


def worker(directory):
    require_verified_runtime()
    d = Path(directory).resolve()
    if any((d / name).exists() for name in OUTPUTS + ['seal.json', 'verification.json', 'failure.json']):
        raise FileExistsError('worker requires unused output directory')
    spec = read(d / 'protocol.json')
    for name, expected in spec['code_sha256'].items():
        if sha(BASE / name) != expected:
            raise ValueError('worker differs from frozen source: ' + name)
    allowed = {d / name for name in ['protocol.json'] + INPUTS + OUTPUTS}
    old, oldio, oldpath = builtins.open, io.open, Path.open
    def check(path):
        if isinstance(path, (str, bytes, os.PathLike)) and Path(path).resolve() not in allowed:
            raise PermissionError('outside frozen discovery dataflow')
    def guarded(path, *a, **kw): check(path); return old(path, *a, **kw)
    def guarded_io(path, *a, **kw): check(path); return oldio(path, *a, **kw)
    def guarded_path(path, *a, **kw): check(path); return oldpath(path, *a, **kw)
    builtins.open, io.open, Path.open = guarded, guarded_io, guarded_path
    try:
        denied = {}
        for label, path in [('proof', BASE / 'arithmetic_filter_pole_budget_proof.txt'),
                            ('final', d / 'final_evaluation.json'), ('cases', d / 'final_cases.json'),
                            ('prior_results', BASE / 'convolution-control-results/pilot-001/report.json')]:
            try:
                read(path); denied[label] = False
            except PermissionError:
                denied[label] = True
        training, validation_data = [read(d / name) for name in INPUTS]
        if any(x['protocol_sha256'] != digest(spec) for x in (training, validation_data)):
            raise ValueError('dataset binding mismatch')
        factory = search.candidate_factory(training['data'], spec['training_scales'], spec['levels'], bit_budget=spec['budgets']['bit'])
        write(d / OUTPUTS[0], dict(protocol_sha256=digest(spec), training_sha256=sha(d / INPUTS[0]), access_denials=denied, factory=factory))
        results = [dict(program_id=c['program_id'], score=search.score(c['program'], validation_data['data'],
                   spec['validation_scales'], spec['levels'], bit_budget=spec['budgets']['bit'])) for c in factory['candidates']]
        write(d / OUTPUTS[1], dict(protocol_sha256=digest(spec), validation_sha256=sha(d / INPUTS[1]), results=results))
        queue, decisions = select(factory, results)
        write(d / OUTPUTS[2], dict(protocol_sha256=digest(spec), queue=queue, selection_decisions=decisions,
                                  final_used_for_selection=False, candidate_ids_frozen_before_final=True))
    finally:
        builtins.open, io.open, Path.open = old, oldio, oldpath


def replay(directory):
    with tempfile.TemporaryDirectory(prefix='fixed-pole-replay-') as tmp:
        d = Path(tmp)
        for name in ['protocol.json'] + INPUTS:
            shutil.copyfile(directory / name, d / name)
        subprocess.run([sys.executable, '-B', str(BASE / 'run_fixed_pole_filter.py'), 'worker', str(d)], check=True, cwd=BASE)
        matches = {name: sha(directory / name) == sha(d / name) for name in OUTPUTS}
        if not all(matches.values()):
            raise ValueError('worker byte replay mismatch')
        return dict(files_match=matches, independent_implementation=False, python_guard_is_OS_sandbox=False)


def final_cases(spec, seal_hash):
    return dict(protocol_sha256=digest(spec), seal_sha256=seal_hash,
                base_scales=sorted([32768, 65536, 40001 + 2 * (int(seal_hash[:16], 16) % 5000)]),
                levels=spec['final_levels'], generated_after_seal=True)


def run(directory):
    require_verified_runtime()
    d = Path(directory).resolve()
    d.mkdir(parents=True, exist_ok=False)
    spec = specification()
    (d / 'frozen_source').mkdir()
    for name in CODE:
        shutil.copyfile(BASE / name, d / 'frozen_source' / name)
    write(d / 'protocol.json', spec)
    tests = [Path(name).stem for name in CODE if name.startswith('test_')]
    result = subprocess.run([sys.executable, '-B', '-m', 'unittest', *tests], cwd=BASE, capture_output=True, text=True)
    (d / 'contract_tests.txt').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError('contract failure retained')
    write(d / 'source_seal.json', dict(protocol_sha256=digest(spec), code_sha256=spec['code_sha256'],
          tests=tests, tests_passed=True, contract_tests_sha256=sha(d / 'contract_tests.txt'), source_frozen_before_data=True))
    for name, scales in [(INPUTS[0], spec['training_scales']), (INPUTS[1], spec['validation_scales'])]:
        if any(sha(BASE / name) != h for name, h in spec['code_sha256'].items()):
            raise ValueError('source changed before data')
        write(d / name, dataset(spec, scales))
    subprocess.run([sys.executable, '-B', str(BASE / 'run_fixed_pole_filter.py'), 'worker', str(d)], check=True, cwd=BASE)
    write(d / 'worker_replay.json', replay(d))
    sealed = ['protocol.json', 'contract_tests.txt', 'source_seal.json', 'worker_replay.json'] + INPUTS + OUTPUTS
    write(d / 'seal.json', dict(protocol_sha256=digest(spec), files={name: sha(d / name) for name in sealed}, selection_closed=True))
    if any(sha(BASE / name) != h for name, h in spec['code_sha256'].items()):
        raise ValueError('source changed before final evaluation')
    cases = final_cases(spec, sha(d / 'seal.json'))
    write(d / 'final_cases.json', cases)
    data = dataset(spec, cases['base_scales'])
    results = [dict(program_id=c['program_id'], score=search.score(c['exact_program'], data['data'], cases['base_scales'], cases['levels'],
               bit_budget=spec['budgets']['bit'])) for c in read(d / OUTPUTS[2])['queue']]
    write(d / 'final_evaluation.json', dict(protocol_sha256=digest(spec), cases_sha256=sha(d / 'final_cases.json'),
                                          data=data, results=results, global_bound_proved=False))
    subprocess.run([sys.executable, '-B', str(BASE / 'check_fixed_pole_filter_run.py'), str(d)], check=True, cwd=BASE)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=['run', 'worker'])
    parser.add_argument('directory')
    args = parser.parse_args()
    (run if args.command == 'run' else worker)(args.directory)
