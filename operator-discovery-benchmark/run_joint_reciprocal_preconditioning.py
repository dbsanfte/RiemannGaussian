"""Frozen algebraic preconditioner search and complete-source numerical audit."""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction as Q
import gzip
import json
import multiprocessing as mp
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

from flint import arb, ctx
import prime_bank_candidates as S
import centered_product_fibers as SERIAL
import joint_reciprocal_correlation as J
import joint_preconditioner_discovery as G
import joint_preconditioned_source as P
import check_joint_reciprocal_correlation as C
import check_joint_preconditioner as A

ROOT = Path(__file__).resolve().parent
PARENT = ROOT / 'centered-product-results/pilot-002'
INPUT = 'candidate10_centered_reciprocal_obligation.json'
TESTS = ['test_joint_reciprocal_correlation', 'test_joint_preconditioner_discovery',
         'test_joint_preconditioned_source', 'test_check_joint_reciprocal_correlation',
         'test_check_joint_preconditioner']
RECEIPTS = ['joint_reciprocal_producer_development.json', 'joint_preconditioner_development.json',
            'joint_preconditioned_source_development.json', 'joint_reciprocal_checker_development.json',
            'joint_preconditioner_checker_development.json']
REVIEWS = ['JOINT_CORRELATION_PAIRING_REVIEW_004.txt', 'JOINT_CORRELATION_GRAMMAR_REVIEW_004.txt',
           'CENTERED_BAND_FORCING_REVIEW_003.txt', 'CENTERED_BAND_PREDICTION_REVIEW_003.txt']
SOURCES = ['run_joint_reciprocal_preconditioning.py', 'joint_reciprocal_preconditioning_protocol.txt',
           'joint_reciprocal_correlation.py', 'joint_preconditioner_discovery.py',
           'joint_preconditioned_source.py', 'check_joint_reciprocal_correlation.py',
           'check_joint_preconditioner.py', 'prime_bank_candidates.py', 'centered_product_fibers.py',
           INPUT] + REVIEWS + [name + '.py' for name in TESTS] + RECEIPTS
CALIBRATION = [1, 16, 64, 1024]
FRESH = [2048, 4096, 8192, 16384, 32768, 65536]
SCALES = CALIBRATION + FRESH
H = 2 * max(SCALES) - 1
CAPS = {'producer': 450000000, 'checker': 650000000}
MAIN_CAP = 150000000
TOTAL = 1300000000
SECONDS = 3600
METADATA_RESERVE = 2000000
NAMES = ('B', 'U', 'V', 'power')
VECTOR_NAMES = ['a', 'a_u', 'a_v', 'p', 'd', 'R', 'pure', 'tilde_b', 'tilde_R',
                'kernel', 'inverse', 'w', 'prefix', 'core', 'core_prefix', 'correction', 'correction_prefix']
VECTOR_NAMES += ['mode:' + name for name in NAMES] + ['mode_prefix:' + name for name in NAMES]


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def development():
    rows = {name: read(ROOT / name) for name in RECEIPTS}
    for row in rows.values():
        if (not row['runs'] or row['runs'][-1]['returncode'] or
                row['operations'] != sum(run['operations'] for run in row['runs'])):
            raise ValueError('complete cumulative passed development receipts')
    return rows


def parent_input():
    parent = read(ROOT / INPUT)
    if (parent['schema'] != 'centered-reciprocal-correlation-obligation-v1' or
            parent['whole_signed_bound_proved'] or parent['RH_proved']):
        raise ValueError('open joined signed obligation')
    published = PARENT / 'analytical_followup_001/next_search_input.json'
    if (ROOT / INPUT).read_bytes() != published.read_bytes():
        raise ValueError('unchanged published obstruction')
    for name in read(PARENT / 'source_files.json'):
        if (ROOT / name).read_bytes() != (PARENT / 'source_snapshot' / name).read_bytes():
            raise ValueError('changed immutable parent source ' + name)
    return parent


def specification():
    return dict(schema='joint-reciprocal-preconditioning-v1', parent=parent_input(),
        horizon=H, calibration_scales=CALIBRATION, fresh_scales=FRESH,
        shifts=list(G.SHIFTS), powers=list(G.POWERS), grammar_size=37,
        selection='exact source-factor cancellation and paid recovery, before any fresh source evaluation',
        priority=['positive_factor_order', 'max_positive_factors_in_one_term',
                  'prefer_integral_local_rational_functions', 'numerator_factor_order', 'abs(power)', 'id'],
        selection_uses_numerical_responses=False,
        tail_search='exact rational Euler numerator, simple-pole recurrence and geometric tail factorization',
        whole_target='one-sided joined high-product off-diagonal O_X, equivalent up to the paid remainder',
        all_units_valuations_and_crosses=True, all_vectors=VECTOR_NAMES,
        source_precision_bits=160, independent_precision_bits=192,
        independent_methods='direct Mobius convolutions, reciprocal interval identity, independent binomial kernels and inverse reconstruction',
        no_global_estimate_from_finite_values=True,
        worker_caps=CAPS, main_cap=MAIN_CAP, total_work_limit=TOTAL,
        worker_seconds=SECONDS, main_seconds=2*SECONDS, workers=2,
        memory_bytes_per_process=4*1024**3, aggregate_memory_limit=16*1024**3,
        storage='gzip JSON lines, one complete vector per line; direct code byte snapshots',
        metadata_reserve=METADATA_RESERVE, development=development(), hashes=False,
        whole_signed_bound_proved=False, RH_proved=False)


def freeze(directory):
    directory = Path(directory).resolve()
    protocol = specification()
    raw = {name: (ROOT / name).read_bytes() for name in SOURCES}
    if directory.exists():
        raise FileExistsError('new immutable experiment directory required')
    directory.mkdir(parents=True)
    (directory / 'source_snapshot').mkdir()
    for name, value in raw.items():
        (directory / 'source_snapshot' / name).write_bytes(value)
    write(directory / 'source_files.json', SOURCES)
    write(directory / 'protocol.json', protocol)


def verify_sources(directory):
    if read(directory / 'source_files.json') != SOURCES:
        raise ValueError('complete frozen source manifest')
    for name in SOURCES:
        if (ROOT / name).read_bytes() != (directory / 'source_snapshot' / name).read_bytes():
            raise ValueError('changed frozen source ' + name)
    if read(directory / 'protocol.json') != specification():
        raise ValueError('changed target or protocol')


def limit():
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))


def compare(left, right, meter):
    a, b = arb(left), arb(right)
    meter.charge(16)
    if not SERIAL.tight(a) or not SERIAL.tight(b) or not a.overlaps(b):
        raise ArithmeticError('independent tight enclosure disagreement')


def export_vectors(path, vectors, meter):
    if list(vectors) != VECTOR_NAMES:
        raise ValueError('complete ordered source/transformation vector archive')
    with gzip.open(path, 'xt', compresslevel=1) as stream:
        for name, values in vectors.items():
            if len(values) != H + 1:
                raise ValueError('complete vector horizon')
            meter.charge(10 * len(values))
            json.dump(dict(name=name, values=[SERIAL.encode(v) for v in values]), stream)
            stream.write('\n')


def checker_transform_query(X, state, transformed, meter):
    N = 2*X-1
    W, F, E = transformed['prefix'], transformed['core_prefix'], transformed['correction_prefix']
    prefixes = [transformed['mode_prefixes'][name] for name in ('nu0', 'nu1', 'mu', 'nu2')]
    def block(left, right):
        total = arb(0)
        for n in range(X, N+1):
            total += left[n] * right[n]
            meter.charge(3)
        return total / (X*X)
    gram = [[block(left, right) for right in prefixes] for left in prefixes]
    energy_w, energy_f, energy_e = block(W, W), block(F, F), block(E, E)
    cross = 2*block(F, E)
    beta = arb(9)/2
    scalars = [beta, -beta, -beta, -state['R_u']]
    recovered = sum((scalars[i]*scalars[j]*gram[i][j] for i in range(4) for j in range(4)), arb(0))
    if not (recovered-energy_f).contains(0) or not (energy_w-energy_f-energy_e-cross).contains(0):
        raise ArithmeticError('independent complete source-mode/correction Gram identity')
    norm_t = norm_w = forward = backward = arb(0)
    for n in range(1, N+1):
        norm_t += state['tilde_R'][n]**2 / (n*(n+1))
        norm_w += W[n]**2 / (n*(n+1))
        root = arb(n).sqrt()
        forward += abs(transformed['kernel'][n])/root
        backward += abs(transformed['inverse'][n])/root
        meter.charge(60)
    meter.charge(200)
    return dict(X=X, energy_w=energy_w, energy_core=energy_f, energy_correction=energy_e,
                core_correction_cross=cross, mode_names=list(NAMES), mode_gram=gram,
                critical_norm_tilde=norm_t, critical_norm_w=norm_w,
                forward_mass=forward, inverse_mass=backward,
                whole_signed_bound_proved=False, RH_proved=False)


def worker(role, directory, program):
    directory = Path(directory)
    ctx.prec = 160 if role == 'producer' else 192
    meter = S.Meter(CAPS[role], SECONDS)
    start = time.monotonic()
    status = 'FAILED'
    try:
        state = J.source(H, meter) if role == 'producer' else C.source(H, meter)
        print(json.dumps(dict(stage=role+'_source_complete', H=H, operations=meter.operations)), flush=True)
        if role == 'producer':
            tables = J.prepare(state, max(SCALES), meter)
            transformed = P.prepare(state, program, meter)
            # Peak includes the simultaneously resident source, tables and transformed arrays.
            meter.live(tables['_resident_cells'] + 30*(H+1) + 4096)
            cases = {str(X): dict(original=J.query(X, tables, meter),
                                 transformed=P.query(X, state, transformed, tables, program, meter),
                                 remainder=J.analytic_remainder(X, state, meter)) for X in SCALES}
            vectors = {name: state[name] for name in VECTOR_NAMES[:8]}
            vectors['tilde_R'] = tables['tilde_R']
            for name in VECTOR_NAMES[9:17]:
                vectors[name] = transformed[name]
            for name in NAMES:
                vectors['mode:'+name] = transformed['modes'][name]
            for name in NAMES:
                vectors['mode_prefix:'+name] = transformed['mode_prefixes'][name]
        else:
            transformed = A.precondition(state, program['shift'], program['power'], meter)
            if (program['shift'], program['power']) != ('2/3', '1'):
                raise ValueError('independent complete four-mode reduction requires its declared algebraic selection')
            for value in transformed['reconstruction_residual']:
                meter.charge(3)
                if not SERIAL.tight(value) or not value.contains(0):
                    raise ArithmeticError('full finite inverse recovery')
            cases = {str(X): dict(original=C.query(X, state, meter),
                                 transformed=checker_transform_query(X, state, transformed, meter)) for X in SCALES}
            meter.live(56*(H+1)+4096)
            aliases = {'a_u':'au', 'a_v':'av', 'pure':'power_center'}
            vectors = {name: state[aliases.get(name, name)] for name in VECTOR_NAMES[:9]}
            for name in VECTOR_NAMES[9:17]:
                vectors[name] = transformed[name]
            for name, independent in zip(NAMES, ('nu0', 'nu1', 'mu', 'nu2')):
                vectors['mode:'+name] = transformed[independent]
            for name, independent in zip(NAMES, ('nu0', 'nu1', 'mu', 'nu2')):
                vectors['mode_prefix:'+name] = transformed['mode_prefixes'][independent]
        meter.charge(100000)
        write(directory / (role+'_cases.json'), SERIAL.serialize(dict(cases=cases,
            constants={key: state[key] for key in ('m_u', 'R_u', 'E0')},
            H=H, precision=ctx.prec, whole_signed_bound_proved=False, RH_proved=False)))
        print(json.dumps(dict(stage=role+'_complete_cases', operations=meter.operations)), flush=True)
        export_vectors(directory / (role+'_vectors.jsonl.gz'), vectors, meter)
        status = 'COMPLETE'
    finally:
        record = dict(status=status, operations=meter.operations, peak_cells=meter.peak_cells,
                      elapsed_seconds=time.monotonic()-start,
                      peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        write(directory / (role+'_resources.json'), record)
    return record


def audit_tensor(tails, sectors, meter):
    terms = {row['name']: row for row in tails['terms']}
    if len(sectors) != 16 or {(r['left'], r['right']) for r in sectors} != {(a,b) for a in NAMES for b in NAMES}:
        raise ValueError('complete sixteen ordered tensor sectors')
    for row in sectors:
        left, right = terms[row['left']], terms[row['right']]
        meter.charge(100)
        if left['zero_above_first_valuation'] or right['zero_above_first_valuation']:
            if row != dict(left=left['name'], right=right['name'], status='ZERO_ON_SHARED_SQUARE'):
                raise ValueError('exact shared-square zero sector')
        else:
            weight = Q(left['valuation_mass_power']) + Q(right['valuation_mass_power'])
            const = Q(left['valuation_mass_constant'])*Q(right['valuation_mass_constant'])*(1+1/(3+weight))
            if (row['status'] != 'UNIFORM_ABSOLUTE_SECTOR_ENVELOPE' or
                    Q(row['prime_weight']) != weight or Q(row['cofinal_rho_threshold']) != 1/(3+weight) or
                    Q(row['constant']) != const or not row['union_subtracted_once'] or
                    row['full_target_recovered'] or row['whole_signed_bound_proved'] or
                    'abs(c_left*c_right)' not in row['coefficient_scope']):
                raise ValueError('paid sector exponent, constant and scope')


def audit_vectors(directory, meter):
    checked = 0
    with gzip.open(directory/'producer_vectors.jsonl.gz', 'rt') as left, gzip.open(directory/'checker_vectors.jsonl.gz', 'rt') as right:
        for name in VECTOR_NAMES:
            a, b = json.loads(next(left)), json.loads(next(right))
            if a['name'] != name or b['name'] != name or len(a['values']) != H+1 or len(b['values']) != H+1:
                raise ValueError('complete independently aligned coefficient vectors')
            for n, (old, new) in enumerate(zip(a['values'], b['values'])):
                try:
                    compare(old, new, meter)
                except ArithmeticError as error:
                    raise ArithmeticError(name+'['+str(n)+']') from error
                checked += 1
            print(json.dumps(dict(stage='independent_vector_verified', vector=name, entries=H+1)), flush=True)
        if left.read() or right.read():
            raise ValueError('unexpected unverified vector data')
    return checked


def audit_cases(producer, checker, meter):
    if set(producer['cases']) != set(map(str, SCALES)) or set(checker['cases']) != set(map(str, SCALES)):
        raise ValueError('all declared complete scales')
    for key in ('m_u', 'R_u', 'E0'):
        compare(producer['constants'][key], checker['constants'][key], meter)
    core_keys = ('energy_w', 'energy_core', 'energy_correction', 'core_correction_cross',
                 'critical_norm_tilde', 'critical_norm_w', 'forward_mass', 'inverse_mass')
    numeric = []
    for X in SCALES:
        p, c = producer['cases'][str(X)], checker['cases'][str(X)]
        a, b = p['original'], c['original']
        for key in ('O', 'low_head', 'high_diagonal', 'energy_R', 'energy_tilde', 'center_correction'):
            compare(a[key], b[key], meter)
        for sector in ('aa', 'cross', 'mm'):
            compare(a['sectors'][sector]['O'], b['O_'+sector], meter)
        for key in ('low_head', 'high_diagonal', 'center_correction'):
            if arb(a[key]).abs_lower() > arb(p['remainder'][key]).upper():
                raise ArithmeticError('finite inconsistency with reviewed uniform paid complement')
        for key in core_keys:
            compare(p['transformed'][key], c['transformed'][key], meter)
        for i in range(4):
            for j in range(4):
                compare(p['transformed']['mode_gram'][i][j], c['transformed']['mode_gram'][i][j], meter)
        numeric.append(dict(X=X, **{key:a[key] for key in ('O','energy_R','energy_tilde')},
                            **{key:p['transformed'][key] for key in core_keys},
                            O_sectors={key:a['sectors'][key]['O'] for key in ('aa','cross','mm')}))
    return numeric


def next_input(selection, report):
    return dict(schema='joint-preconditioned-correlation-obligation-v1', status='open',
        source='actual_mu_candidate10', prior_input=INPUT,
        equivalence_class='candidate10_complete_prime_bank_covariance',
        original_target='E_R(X)=X^-2 sum_(X<=n<2X) R(n)^2 <= C_epsilon X^epsilon for every epsilon>0 uniformly over dyadic X',
        joined_target='O_X <= C_epsilon X^epsilon; all bands joined, one-sided, complete pure center',
        paid_original_remainder='|E_R-O_X| <= 3(beta+m)^2(1+log(2X-1))^3 + 4E0(beta+m)(1+log(2X)) + E0^2/X',
        selected_operator=selection['selected'], exact_tails=selection['tails'], paid_tensor_sectors=selection['tensor_sectors'],
        full_reduction=dict(w='tilde_b*mu_(2/3)=f+eta',
            core='f=beta*nu0-beta*nu1-beta*mu-R_u*nu2',
            nu0='k_(1/3)*(mu*mu)', nu1='k_(1/3)*(mu*mu_(2/3))', nu2='k_(1/3)*mu_(2/3)',
            eta='beta*mu_(2/3)-d*mu_(2/3), including unit and all prime powers',
            forward_and_inverse_critical_norm_cost='zeta(7/6)<=7',
            complete_d_prefix_critical_norm_bound='C_D=20*beta/sqrt(log4)',
            eta_prefix_critical_norm_bound='beta*sqrt27+7*C_D',
            recovery='||T||_sigma <= zeta(2/3+sigma)*(||F||_sigma+||prefix eta||_sigma), sigma>1/2',
            unit='f(1)=-beta-R_u; eta(1)=beta; w(1)=-R_u',
            finite_crosses_retained=True, sharp_cut_eta_drop_permitted=False),
        missing_bound=dict(expression='F(x)=sum_(n<=x) f(n), complete signed four-mode core',
            equivalent_goal='||F||_sigma<infinity for every sigma>1/2, or its cofinal dyadic moment',
            uniformity='all dyadic scales; constants may depend on epsilon/sigma, not on X or omitted primes',
            open_sectors=['unsuppressed nu0 tensor nu0 below rho=1/3',
                          'all first valuations and remaining common-prime interactions',
                          'joint signed cross terms after any paid union decomposition'],
            separately_bounding_modes_required=False, whole_signed_bound_proved=False),
        next_constructions=[
            dict(kind='valuation pairing with exact cofactor defect',
                 example='nu1(q^e H)+q^(-1/3)nu0(q^e H)=q^(-1/3)l0(e)*(nu0(H)-nu1(H)), q does not divide H, e>=2',
                 open='prove the joint smaller-cofactor defect; inverse prime weights must be charged'),
            dict(kind='all-prime logarithmic recurrence',
                 reference=REVIEWS[0]+' section7',
                 paid='Volterra memory on x>=64 is absorbable; complete finite head explicit',
                 open='joint prime-power source bank; pole-compensated pieces cannot be paid separately'),
            dict(kind='mixed log-divisor kernel commutator', reference=REVIEWS[1]+' section6',
                 gain='d^(-1/3)-d^(-2/3) on the symmetric transported kernel',
                 open='unattenuated max/prefix boundary commutator and recovery of the symmetric target mode'),
            dict(kind='fixed-prime insertion and actual-prime divided differences', reference=REVIEWS[1]+' sections2-3',
                 open='q-free current-scale forcing, insertion complements and prime-gap inverse costs')],
        dependency_guards=['recoverable rewrites are one target class, not independent exponent gains',
                           'a bound for an RH-equivalent companion is a new obligation, not a paid lemma',
                           'signed common core and all domain/center/diagonal complements survive projection',
                           'finite coefficients and energies do not provide uniform scale induction'],
        reviewed_inputs=REVIEWS, finite_report=report, whole_signed_bound_proved=False, RH_proved=False)


def run(directory):
    directory = Path(directory).resolve()
    verify_sources(directory)
    limit()
    start = time.monotonic()
    write(directory/'started.json', dict(attempt=1, monotonic=start))
    test = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT,
                          capture_output=True, text=True, timeout=60)
    counts = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$', test.stdout, re.M)
    frozen_work = sum(int(n) for _, n in counts)
    write(directory/'frozen_tests.json', dict(returncode=test.returncode, stdout=test.stdout,
          stderr=test.stderr, operations=frozen_work))
    if test.returncode or sorted(name for name, _ in counts) != sorted(TESTS):
        raise RuntimeError('one complete passed frozen suite required')
    preparation = METADATA_RESERVE + frozen_work + sum(row['operations'] for row in development().values())
    if preparation + MAIN_CAP + sum(CAPS.values()) > TOTAL:
        raise ValueError('complete work reserve exceeds declared cap')
    main = S.Meter(MAIN_CAP, 2*SECONDS)
    ctx.prec = 192
    rows = G.generate(main)
    selected = G.choose(rows)
    tails = G.compile_tails(selected, main)
    sectors = G.tensor_sectors(tails, main)
    A.verify_selection(rows, selected['id'], main)
    A.verify_tails(selected, tails, main)
    audit_tensor(tails, sectors, main)
    selection = dict(grammar=rows, selected=selected, tails=tails, tensor_sectors=sectors,
                     selection_uses_numerical_responses=False, selected_before_source_generation=True,
                     whole_signed_bound_proved=False, RH_proved=False)
    write(directory/'selection.json', selection)
    print(json.dumps(dict(stage='algebraic_selection_frozen', selected_id=selected['id'],
                         shift=selected['shift'], power=selected['power'], grammar_size=len(rows))), flush=True)
    resources = {}
    with ProcessPoolExecutor(max_workers=2, mp_context=mp.get_context('spawn'), initializer=limit) as pool:
        futures = {pool.submit(worker, role, str(directory), selected): role for role in CAPS}
        for future in as_completed(futures):
            role = futures[future]
            resources[role] = future.result()
            print(json.dumps(dict(stage=role+'_archived', **resources[role])), flush=True)
    checked = audit_vectors(directory, main)
    producer, checker = read(directory/'producer_cases.json'), read(directory/'checker_cases.json')
    numeric = audit_cases(producer, checker, main)
    total = preparation + main.operations + sum(row['operations'] for row in resources.values())
    if total > TOTAL:
        raise OverflowError('complete cumulative work cap')
    report = dict(status='EXACT_PRECONDITIONER_AND_COMPLETE_JOINT_SOURCE_FINITELY_VERIFIED',
        grammar_size=len(rows), cofinal_recoverable_programs=sum(row['recovery']['cofinal'] for row in rows),
        selected=selected, calibration_scales=CALIBRATION, fresh_scales=FRESH,
        checked_source_horizon=H, independent_source_precision_bits=192,
        complete_vector_count=len(VECTOR_NAMES), independently_compared_scalar_entries=checked,
        exact_repeated_valuation_tails_verified=True, ordered_shared_square_sectors=len(sectors),
        source_mode_coefficients_retained=True, finite_values=numeric,
        proof_status='bounded recovery and specified shared-square envelopes proved analytically; complete signed core bound OPEN',
        no_independent_exponent_gain_from_rewriting=True,
        preparation_operations=preparation, main_operations=main.operations, worker_resources=resources,
        total_operations=total, elapsed_seconds=time.monotonic()-start,
        main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        whole_signed_bound_proved=False, RH_proved=False)
    verify_sources(directory)
    write(directory/'report.json', report)
    write(directory/'next_search_input.json', next_input(selection, report))
    print(json.dumps(dict(stage='complete', total_operations=total, seconds=report['elapsed_seconds'],
                         scalar_checks=checked, whole_signed_bound_proved=False)), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['freeze', 'run'])
    parser.add_argument('directory')
    args = parser.parse_args()
    globals()[args.action](args.directory)
