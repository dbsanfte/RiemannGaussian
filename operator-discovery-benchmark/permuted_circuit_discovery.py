"""Source-free catalogue and finite discovery rules for permuted circuits.

Finite fits and cancellation diagnostics never discharge the cofinal moment
obligation. Arithmetic providers are explicit so the audit uses its own source,
map, kernel and complete-moment implementation.
"""
from copy import deepcopy
from fractions import Fraction as Q
import json

TRAIN = [32, 64, 128, 256]
VALIDATION = [384, 512, 768, 1024]
LEVELS = [2, 3, 6, 12]
SOURCES = ['mu', 'one', 'partial_prime_13']
FAMILIES = ['permutation_input', 'permutation_interleaving',
            'conjugated_convolution', 'shear_interleaving']
FINAL_SCALES = {'mu': [20480, 32768], 'one': [8192, 16384],
                'partial_prime_13': [8192, 16384]}
FINAL_HORIZONS = {'mu': 65535, 'one': 32767, 'partial_prime_13': 32767}
FLAGS = dict(moment_estimate_proved=False, global_bound_proved=False, RH_proved=False)
ALPHAS = ['-1', '-1/2', '-1/3', '-1/6', '1/6', '1/3', '1/2', '1']
PHASES = [['constant', 1], ['constant', -1],
          ['parity', ['root', 1, 2]], ['parity', ['root', 1, 3]],
          ['residue_sign', ['n'], 3, [1]],
          ['residue_sign', ['n'], 5, [1, 4]],
          ['source_sign', ['subtract_root', 1, 2]],
          ['source_sign', ['root', 1, 3]]]
MAPS = [
    {'kind': 'polynomial', 'coefficients': [1, 1]},
    {'kind': 'polynomial', 'coefficients': [0, 3, 2]},
    {'kind': 'polynomial', 'coefficients': [0, 1, 0]},
    {'kind': 'xor', 'mask': 'all'}, {'kind': 'xor', 'mask': 'top'},
    {'kind': 'xor', 'mask': 'alternating'}, {'kind': 'reverse_bits'},
    {'kind': 'rotate_bits', 'shift': 1}, {'kind': 'rotate_bits', 'shift': -2},
    {'kind': 'compose', 'maps': [
        {'kind': 'polynomial', 'coefficients': [1, 3, 2]},
        {'kind': 'xor', 'mask': 'alternating'}]},
    {'kind': 'choose', 'phase': ['source_sign', ['subtract_root', 1, 2]],
     'positive': {'kind': 'reverse_bits'}, 'negative': {'kind': 'xor', 'mask': 'all'}},
    {'kind': 'choose', 'phase': ['source_sign', ['root', 1, 3]],
     'positive': {'kind': 'rotate_bits', 'shift': 1},
     'negative': {'kind': 'polynomial', 'coefficients': [1, -1, 2]}}]


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def _certificate(program, meter):
    """Schema reconstruction when the independent provider exposes verify only."""
    order = sum((abs(Q(s['alpha'])) for s in program['stages'] if s['op'] == 'convolve'), Q(0))
    shear = Q(1)
    for stage in program['stages']:
        meter.charge()
        if stage['op'] == 'shear':
            shear = meter.number(shear * (1 + 2 * abs(Q(stage['coefficient']))))
    return dict(schema='permuted-arithmetic-circuit-v1', program=deepcopy(program),
                fractional_order=str(order), recovery_power=(order.numerator + order.denominator - 1) // order.denominator,
                permutation_count=sum(s['op'] == 'permute' for s in program['stages']),
                shear_count=sum(s['op'] == 'shear' for s in program['stages']), shear_factor=str(shear),
                domain='closed_dyadic_horizon_weighted_l2_half_lt_sigma_le_one',
                bound='3^permutation_count*shear_factor*(1+1/epsilon)^recovery_power',
                coefficient_binding='same_fixed_source_and_block_branches_in_inverse')


def _inverse(program, meter):
    stages = []
    for original in reversed(program['stages']):
        meter.charge()
        s = deepcopy(original)
        if s['op'] == 'convolve': s['alpha'] = str(-Q(s['alpha']))
        elif s['op'] == 'shear': s['coefficient'] = str(-Q(s['coefficient']))
        elif s['op'] == 'permute': s['inverse'] = not s['inverse']
        stages.append(s)
    return {'stages': stages}


def generate_catalog(meter, arithmetic=None):
    if arithmetic is None:
        import permuted_arithmetic_circuits as arithmetic
    words = [('baseline', {'stages': []})]
    for family in FAMILIES:
        for j, descriptor in enumerate(MAPS):
            p = dict(op='permute', map=deepcopy(descriptor), inverse=False)
            pi = dict(op='permute', map=deepcopy(descriptor), inverse=True)
            t = dict(op='convolve', alpha=ALPHAS[j % 8], prime_phase=deepcopy(PHASES[j % 8]))
            u = dict(op='convolve', alpha=ALPHAS[(j + 3) % 8], prime_phase=deepcopy(PHASES[(j + 2) % 8]))
            if family == 'permutation_input':
                stages = [p, t]
            elif family == 'permutation_interleaving':
                if j % 3 == 0:
                    u['prime_phase'] = ['multiply', ['constant', -1], deepcopy(t['prime_phase'])]
                stages = [t, p, u]
            elif family == 'conjugated_convolution':
                if j % 2 == 0:
                    u = deepcopy(t); u['alpha'] = str(-Q(t['alpha']))
                if j % 3 == 1:
                    p, pi = pi, p
                stages = [p, t, pi, u]
            else:
                # First c=-1, phi=+1 is a generic adjacent-difference calibration.
                c = ['-1', '1', '-1/2', '1/2', '-1/3', '1/3'][j % 6]
                h = dict(op='shear', coefficient=c, phase=deepcopy(PHASES[j % 8]),
                         direction='even_from_odd' if j % 2 == 0 else 'odd_from_even')
                if j == 0:
                    p['map'] = pi['map'] = {'kind': 'polynomial', 'coefficients': [0, 1]}
                stages = [p, h, pi, u] if j % 2 == 0 else [t, p, h, pi, u]
            words.append((family, {'stages': stages}))
    records = []
    for family, raw in words:
        meter.charge(len(canonical(raw)))
        norm = arithmetic.normalize(raw, meter)
        program = norm['program']
        alias = next((r['evaluation_id'] for r in records if r['program'] == program), len(records))
        cert = (arithmetic.certificate(program, meter) if hasattr(arithmetic, 'certificate')
                else _certificate(program, meter))
        if hasattr(arithmetic, 'verify'):
            arithmetic.verify(cert, meter)
        records.append(dict(id=len(records), family=family, raw_program=raw,
                            normalization=norm, program=program, evaluation_id=alias,
                            certificate=cert, inverse=_inverse(program, meter),
                            complexity=len(canonical(program)),
                            alias_domain='dyadic_moments; all diagnostics use normalized word',
                            calibration='generic_smoothness_not_prime_information' if family == 'shear_interleaving' and len(records) == 37 else None))
    meter.live(100000)
    return records


def evaluate_case(record, source, horizon, scales, meter, arithmetic, values=None):
    row = dict(id=record['evaluation_id'], source=source, horizon=horizon,
               scales=list(scales), status='available', cases=[])
    try:
        if values is None:
            values = arithmetic.source(source, horizon, meter)
        state = arithmetic.evaluate(record['program'], values, meter)
        row.update(cases=arithmetic.moments(state, scales, meter),
                   initial_cost=arithmetic.initial_cost(state, meter))
    except (OverflowError, TimeoutError, MemoryError) as error:
        row.update(status='missing', reason=str(error) or type(error).__name__, cases=[])
    except (ValueError, TypeError, KeyError, ZeroDivisionError) as error:
        row.update(status='invalid', reason=str(error) or type(error).__name__, cases=[])
    return row


def ceil_root(X, q, meter):
    # Bounded binary integer search; no numerical backend or floated root.
    lo, hi = 0, X
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        meter.charge(q); power = meter.number(mid ** q)
        if power < X: lo = mid
        else: hi = mid
    return hi


def constants(cases, meter):
    return {str(q): str(max((meter.number(Q(c['energy']) / ceil_root(c['X'], q, meter))
                            for c in cases), default=Q(0))) for q in LEVELS}


def scores(cases, fitted, meter):
    result = []
    for c in cases:
        for q in LEVELS:
            bound = meter.number(Q(fitted[str(q)]) * ceil_root(c['X'], q, meter))
            result.append(dict(X=c['X'], q=q, bound=str(bound),
                               passed=Q(c['energy']) <= bound,
                               dyadic=c['X'] & (c['X'] - 1) == 0))
    return result


def _ratio(numerator, denominator, meter, inactive=False):
    a, b = Q(numerator), Q(denominator)
    if a < 0 or b < 0: raise ValueError('nonnegative complete energy')
    if b == 0:
        if inactive and a == 0: return {'status': 'defined', 'value': '1', 'inactive': True}
        if inactive: raise ValueError('positive signed energy with zero absolute path envelope')
        return {'status': 'undefined', 'reason': 'zero_denominator'}
    return {'status': 'defined', 'value': str(meter.number(a / b)), 'inactive': False}


def analyze_discovery(catalog, cases, meter, train=TRAIN, validation=VALIDATION):
    rows = {(r['id'], r['source'], r['horizon']): r for r in cases}
    if len(rows) != len(cases): raise ValueError('duplicate evaluation key')
    Ht, Hv = 2 * max(train) - 1, 2 * max(validation) - 1
    result = []
    for record in catalog:
        meter.charge()
        eid = record['evaluation_id']
        fitted = rows.get((eid, 'mu', Ht))
        row = dict(id=record['id'], evaluation_id=eid, family=record['family'],
                   status='ineligible', reason='missing_complete_discovery', constants=None,
                   scores=[], diagnostics=[], gate_failures=None, raw_ratio=None,
                   specificity=None, conditional_cost=None, complexity=record['complexity'])
        if record['id'] != 0 and eid == 0:
            row['reason'] = 'baseline_alias'; result.append(row); continue
        training = [rows.get((eid, s, Ht)) for s in SOURCES]
        val = [rows.get((eid, s, Hv)) for s in SOURCES]
        base = rows.get((0, 'mu', Hv))
        required = training + val + [base]
        if any(r is None or r['status'] != 'available' for r in required):
            result.append(row); continue
        if any([c['X'] for c in r['cases']] != list(train) for r in training) or any(
                [c['X'] for c in r['cases']] != list(validation) for r in val + [base]):
            raise ValueError('complete fixed partitions required')
        if any(rows[(eid, s, Ht)]['initial_cost'] != rows[(eid, s, Hv)]['initial_cost'] for s in SOURCES):
            raise ValueError('fixed source head changed with closed horizon')
        row['constants'] = constants(fitted['cases'], meter)
        row['scores'] = scores(val[0]['cases'], row['constants'], meter)
        for i, c in enumerate(val[0]['cases']):
            kappas = {s: _ratio(val[j]['cases'][i]['energy'], val[j]['cases'][i]['absolute_energy'], meter, True)
                      for j, s in enumerate(SOURCES)}
            if any(k['status'] == 'defined' and Q(k['value']) > 1 for k in kappas.values()):
                raise ValueError('signed energy exceeds absolute path envelope')
            raw = _ratio(c['energy'], base['cases'][i]['energy'], meter)
            if all(k['status'] == 'defined' for k in kappas.values()):
                specificity = _ratio(kappas['mu']['value'], min(Q(kappas[s]['value']) for s in SOURCES[1:]), meter)
            else:
                specificity = {'status': 'undefined', 'reason': 'undefined_kappa'}
            row['diagnostics'].append(dict(X=c['X'], kappas=kappas, raw_ratio=raw, specificity=specificity))
        if any(d[k]['status'] != 'defined' for d in row['diagnostics'] for k in ('raw_ratio', 'specificity')):
            row['reason'] = 'undefined_matched_validation_diagnostic'; result.append(row); continue
        cert = record['certificate']; q = 12
        cost = meter.number(9 ** cert['permutation_count'] * Q(cert['shear_factor']) ** 2
                            * (1 + q) ** (2 * cert['recovery_power'])
                            * (Q(fitted['initial_cost']) + 4 * q * Q(row['constants'][str(q)])))
        row.update(status='eligible', reason=None, gate_failures=sum(not s['passed'] for s in row['scores']),
                   raw_ratio=str(max(Q(d['raw_ratio']['value']) for d in row['diagnostics'])),
                   specificity=str(max(Q(d['specificity']['value']) for d in row['diagnostics'])),
                   conditional_cost=str(cost))
        result.append(row)
    return result


def select_leads(analysis, meter):
    """Within each family/failure stratum, nondominated layers then exact ties."""
    selected = [0]; ranking = []; seen = {0}; missing = []
    for family in FAMILIES:
        eligible = [deepcopy(r) for r in analysis if r['family'] == family and r['status'] == 'eligible']
        for failures in sorted(set(r['gate_failures'] for r in eligible)):
            remaining = [r for r in eligible if r['gate_failures'] == failures]
            layer = 0
            while remaining:
                front = []
                for row in remaining:
                    coordinates = tuple(Q(row[k]) for k in ('raw_ratio', 'specificity', 'conditional_cost'))
                    dominated = False
                    for other in remaining:
                        meter.charge(3)
                        oc = tuple(Q(other[k]) for k in ('raw_ratio', 'specificity', 'conditional_cost'))
                        if all(a <= b for a, b in zip(oc, coordinates)) and any(a < b for a, b in zip(oc, coordinates)):
                            dominated = True; break
                    if not dominated: front.append(row)
                for row in front:
                    row['pareto_layer'] = layer; ranking.append(row)
                front_ids = {r['id'] for r in front}
                remaining = [r for r in remaining if r['id'] not in front_ids]; layer += 1
        candidates = [r for r in ranking if r['family'] == family]
        candidates.sort(key=lambda r: (r['gate_failures'], r['pareto_layer'], Q(r['specificity']),
                                       Q(r['raw_ratio']), Q(r['conditional_cost']), r['complexity'], r['id']))
        unique = [r for r in candidates if r['evaluation_id'] not in seen]
        if unique:
            selected.append(unique[0]['id']); seen.add(unique[0]['evaluation_id'])
        else: missing.append(family)
    return dict(selected_ids=selected, ranking=sorted(ranking, key=lambda r: r['id']),
                missing_families=missing)


def obligation(record):
    return dict(id=record['id'], program=record['program'], certificate=record['certificate'],
                target='complete actual Mobius prefix after one fixed normalized circuit',
                required='For cofinally many integer q>=2, finite C_q independent of every dyadic X>=32: E(X)<=C_q*ceil(X^(1/q))',
                recovery='uniform inverse critical weighted L2 with permutation/shear costs and complete finite head1..31',
                same_fixed_source_in_inverse=True, all_mixed_terms_retained=True, **FLAGS)
