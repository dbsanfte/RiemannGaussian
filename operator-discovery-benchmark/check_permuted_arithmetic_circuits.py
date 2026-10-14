"""Independent exact closed-horizon permutation/shear circuit checker.

Only frozen independent divisor arithmetic is reused. Recovery certificates
prove the stated operator grammar, never a source-specific moment estimate.
"""
from copy import deepcopy
from fractions import Fraction as Q

import check_reversible_divisor_circuits as OLD


SCHEMA = 'permuted-arithmetic-circuit-v1'
DOMAIN = 'closed_dyadic_horizon_weighted_l2_half_lt_sigma_le_one'
BOUND = '3^permutation_count*shear_factor*(1+1/epsilon)^recovery_power'
BINDING = 'same_fixed_source_and_block_branches_in_inverse'
MAX_HORIZON = OLD.MAX_HORIZON
RULES = ('identity_permutation', 'inverse_permutations', 'inverse_signs',
         'merge_convolutions', 'merge_shears', 'terminal_sign',
         'terminal_dyadic_permutation')


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _cells(value, meter):
    """Charge each bounded, already validated payload before retaining copies."""
    meter.charge()
    if type(value) is dict:
        return 1 + sum(_cells(key, meter) + _cells(item, meter)
                       for key, item in value.items())
    if type(value) is list:
        return 1 + sum(_cells(item, meter) for item in value)
    if type(value) is str:
        meter.charge(len(value) // 32)
        return 1 + len(value) // 32
    if type(value) is int:
        meter.number(value)
    return 1


def _copy(value, meter):
    meter.charge(_cells(value, meter))
    return deepcopy(value)


def _same(left, right, meter):
    meter.charge()
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(_same(left[k], right[k], meter) for k in left)
    if type(left) is list:
        return len(left) == len(right) and all(_same(a, b, meter) for a, b in zip(left, right))
    return left == right


def _map_syntax(descriptor, meter):
    count = 0

    def visit(node, depth):
        nonlocal count
        meter.charge()
        count += 1
        _require(count <= 15 and depth <= 3, 'bounded map nodes/depth')
        _require(type(node) is dict and type(node.get('kind')) is str,
                 'explicit map descriptor')
        kind = node['kind']
        if kind == 'polynomial':
            _require(set(node) == {'kind', 'coefficients'}
                     and type(node['coefficients']) is list
                     and 2 <= len(node['coefficients']) <= 5,
                     'polynomial exact keys and degree')
            coefficients = node['coefficients']
            for value in coefficients:
                meter.charge()
                _require(type(value) is int and -8 <= value <= 8,
                         'strict bounded polynomial coefficient')
                meter.number(value)
            _require(coefficients[1] % 2 == 1
                     and all(value % 2 == 0 for value in coefficients[2:]),
                     'odd linear/even higher polynomial coefficients')
        elif kind == 'xor':
            _require(set(node) == {'kind', 'mask'} and type(node['mask']) is str
                     and node['mask'] in ('all', 'top', 'alternating'), 'xor mask descriptor')
        elif kind == 'reverse_bits':
            _require(set(node) == {'kind'}, 'bit reversal exact keys')
        elif kind == 'rotate_bits':
            _require(set(node) == {'kind', 'shift'} and type(node['shift']) is int
                     and -4 <= node['shift'] <= 4 and node['shift'] != 0,
                     'nonzero strict bounded bit rotation')
            meter.number(node['shift'])
        elif kind == 'compose':
            _require(set(node) == {'kind', 'maps'} and type(node['maps']) is list
                     and 2 <= len(node['maps']) <= 3, 'bounded index-map composition')
            for child in node['maps']:
                visit(child, depth + 1)
        elif kind == 'choose':
            _require(set(node) == {'kind', 'phase', 'positive', 'negative'},
                     'block-base choice exact keys')
            OLD._phase_syntax(node['phase'], meter)
            visit(node['positive'], depth + 1)
            visit(node['negative'], depth + 1)
        else:
            raise ValueError('supported dyadic map descriptor')

    visit(descriptor, 0)
    return count


def _program(program, meter):
    meter.charge()
    _require(type(program) is dict and set(program) == {'stages'}
             and type(program['stages']) is list and len(program['stages']) <= 7,
             'exact bounded permuted circuit')
    parsed = []
    counts = dict(convolve=0, sign=0, permute=0, shear=0)
    for stage in program['stages']:
        meter.charge()
        _require(type(stage) is dict and type(stage.get('op')) is str, 'explicit stage object')
        op = stage['op']
        if op == 'convolve':
            _require(set(stage) == {'op', 'alpha', 'prime_phase'}, 'convolution exact keys')
            parameter = OLD._alpha(stage['alpha'], meter)
            OLD._phase_syntax(stage['prime_phase'], meter)
        elif op == 'sign':
            _require(set(stage) == {'op', 'phase'}, 'sign exact keys')
            OLD._phase_syntax(stage['phase'], meter)
            parameter = None
        elif op == 'permute':
            _require(set(stage) == {'op', 'map', 'inverse'}
                     and type(stage['inverse']) is bool, 'permutation exact keys/direction')
            _map_syntax(stage['map'], meter)
            parameter = stage['inverse']
        elif op == 'shear':
            _require(set(stage) == {'op', 'coefficient', 'phase', 'direction'}
                     and type(stage['direction']) is str
                     and stage['direction'] in ('even_from_odd', 'odd_from_even'),
                     'same-block shear exact keys/direction')
            parameter = OLD._alpha(stage['coefficient'], meter)
            OLD._phase_syntax(stage['phase'], meter)
        else:
            raise ValueError('supported reversible stage')
        counts[op] += 1
        parsed.append((op, parameter, stage))
    _require(counts['convolve'] <= 3 and counts['sign'] <= 3
             and counts['permute'] <= 3 and counts['shear'] <= 2,
             'bounded stage-type counts')
    meter.live(16384 + 8 * _cells(program, meter))
    return parsed


def validate(program, meter):
    _program(program, meter)
    return True


def _metadata(parsed, meter):
    order = Q(0)
    shear_factor = Q(1)
    permutations = shears = 0
    for op, parameter, _ in parsed:
        meter.charge(2)
        if op == 'convolve':
            order = meter.number(order + abs(parameter))
        elif op == 'permute':
            permutations += 1
        elif op == 'shear':
            shears += 1
            shear_factor = meter.number(shear_factor * meter.number(1 + 2 * abs(parameter)))
    power = meter.number((order.numerator + order.denominator - 1) // order.denominator)
    return dict(fractional_order=str(order), recovery_power=power,
                permutation_count=permutations, shear_count=shears,
                shear_factor=str(shear_factor))


def verify(certificate, meter=None):
    meter = OLD.Meter(2000000) if meter is None else meter
    meter.charge()
    _require(type(certificate) is dict and set(certificate) == {
        'schema', 'program', 'fractional_order', 'recovery_power', 'permutation_count',
        'shear_count', 'shear_factor', 'domain', 'bound', 'coefficient_binding'},
        'recovery certificate exact keys')
    parsed = _program(certificate['program'], meter)
    expected = _metadata(parsed, meter)
    for key, value in expected.items():
        meter.charge()
        _require(type(certificate[key]) is type(value) and certificate[key] == value,
                 'exact complete recovery metadata: ' + key)
    for key, value in (('schema', SCHEMA), ('domain', DOMAIN),
                       ('bound', BOUND), ('coefficient_binding', BINDING)):
        _require(type(certificate[key]) is str and certificate[key] == value,
                 'fixed recovery theorem scope: ' + key)
    return True


def inverse(program, meter):
    parsed = _program(program, meter)
    stages = []
    for op, parameter, stage in reversed(parsed):
        meter.charge()
        result = _copy(stage, meter)
        if op == 'convolve':
            result['alpha'] = str(meter.number(-parameter))
        elif op == 'permute':
            result['inverse'] = not parameter
        elif op == 'shear':
            result['coefficient'] = str(meter.number(-parameter))
        stages.append(result)
    return dict(stages=stages)


def _identity(stage, meter):
    meter.charge()
    if stage['op'] != 'permute' or stage['map']['kind'] != 'polynomial':
        return False
    coefficients = stage['map']['coefficients']
    meter.charge(len(coefficients))
    return coefficients[:2] == [0, 1] and all(value == 0 for value in coefficients[2:])


def normalize(program, meter):
    _program(program, meter)
    stages = _copy(program['stages'], meter)
    rewrites = []
    retained = _cells(program, meter) + _cells(stages, meter)
    while True:
        found = None
        for position, stage in enumerate(stages):
            meter.charge()
            if _identity(stage, meter):
                found = ('identity_permutation', position, 1, [])
                break
            if position + 1 >= len(stages):
                continue
            other = stages[position + 1]
            op = stage['op']
            if op != other['op']:
                continue
            if (op == 'permute' and stage['inverse'] != other['inverse']
                    and _same(stage['map'], other['map'], meter)):
                found = ('inverse_permutations', position, 2, [])
            elif op == 'sign' and _same(stage['phase'], other['phase'], meter):
                found = ('inverse_signs', position, 2, [])
            elif op in ('convolve', 'shear'):
                field = 'prime_phase' if op == 'convolve' else 'phase'
                parameter = 'alpha' if op == 'convolve' else 'coefficient'
                compatible = (op != 'shear' or stage['direction'] == other['direction'])
                if compatible and _same(stage[field], other[field], meter):
                    total = meter.number(OLD._alpha(stage[parameter], meter)
                                         + OLD._alpha(other[parameter], meter))
                    if abs(total) <= 2 and total.denominator <= 6:
                        after = []
                        if total:
                            merged = _copy(stage, meter)
                            merged[parameter] = str(total)
                            after = [merged]
                        rule = 'merge_convolutions' if op == 'convolve' else 'merge_shears'
                        found = (rule, position, 2, after)
            if found is not None:
                break
        if found is None and stages:
            meter.charge()
            if stages[-1]['op'] == 'sign':
                found = ('terminal_sign', len(stages) - 1, 1, [])
            elif stages[-1]['op'] == 'permute':
                found = ('terminal_dyadic_permutation', len(stages) - 1, 1, [])
        if found is None:
            break
        rule, position, length, after = found
        before = _copy(stages[position:position + length], meter)
        saved_after = _copy(after, meter)
        meter.charge(len(stages) + 8)
        record = dict(rule=rule, position=meter.number(position), before=before, after=saved_after)
        retained += _cells(record, meter)
        meter.live(16384 + 4 * retained)
        rewrites.append(record)
        stages[position:position + length] = after
    return dict(program=dict(stages=stages), rewrites=rewrites, equivalence='dyadic_moments')


def _horizon(horizon, meter):
    OLD._horizon(horizon, meter)
    _require(horizon & (horizon + 1) == 0, 'closed dyadic horizon2^K-1')


def source(name, horizon, meter):
    _horizon(horizon, meter)
    return OLD.source(name, horizon, meter)


def _values(values, meter):
    horizon = OLD._values(values, meter)
    _horizon(horizon, meter)
    return horizon


def _exact_vector(vector, horizon, meter):
    _require(type(vector) is list and len(vector) == horizon + 1,
             'complete exact closed-horizon vector')
    meter.charge(len(vector))
    for value in vector:
        _require(type(value) in (int, Q), 'strict exact signed/envelope scalar')
        meter.number(value)
    _require(vector[0] == 0, 'zero vector index')


def _residue_map(descriptor, base, values, meter, roots):
    bits = base.bit_length() - 1
    roots.live(16 * base + 1024)
    meter.charge(base)
    kind = descriptor['kind']
    if kind == 'choose':
        sign = OLD._phase(descriptor['phase'], base, values, meter, roots)
        branch = descriptor['positive'] if sign == 1 else descriptor['negative']
        return _residue_map(branch, base, values, meter, roots)
    if kind == 'compose':
        current = list(range(base))
        for component in descriptor['maps']:
            following = _residue_map(component, base, values, meter, roots)
            meter.charge(base)
            current = [following[r] for r in current]
        return current
    answer = []
    if kind == 'xor':
        mask_type = descriptor['mask']
        if mask_type == 'all':
            mask = base - 1
        elif mask_type == 'top':
            mask = base // 2
        else:
            mask = 0
            for bit in range(0, bits, 2):
                meter.charge(2)
                mask += 1 << bit
    for residue in range(base):
        meter.charge(2)
        if kind == 'polynomial':
            result = 0
            for coefficient in reversed(descriptor['coefficients']):
                meter.charge(3)
                product = meter.number(result * residue)
                result = meter.number(meter.number(product + coefficient) % base)
        elif kind == 'xor':
            result = residue ^ mask
        elif kind == 'reverse_bits':
            result = 0
            value = residue
            for _ in range(bits):
                meter.charge(3)
                result = (result << 1) | (value & 1)
                value >>= 1
        else:
            shift = descriptor['shift'] % bits if bits else 0
            meter.charge(4)
            result = (((residue << shift) & (base - 1))
                      | (residue >> (bits - shift))) if shift else residue
        answer.append(meter.number(result))
    return answer


def _permutation(descriptor, horizon, values, meter, roots):
    meter.charge(2 * (horizon + 1))
    roots.live(2 * (horizon + 1) + 1024)
    forward = [0] * (horizon + 1)
    backward = [0] * (horizon + 1)
    base = 1
    while base <= horizon:
        roots.live(2 * (horizon + 1) + 16 * base + 1024)
        residues = _residue_map(descriptor, base, values, meter, roots)
        _require(len(residues) == base, 'complete residue permutation')
        for residue, mapped in enumerate(residues):
            meter.charge(4)
            _require(type(mapped) is int and 0 <= mapped < base,
                     'map stays within original dyadic block')
            origin = base + residue
            target = base + mapped
            _require(backward[target] == 0, 'bijective exact block map')
            forward[origin] = target
            backward[target] = origin
        base *= 2
    meter.charge(horizon)
    _require(all(value != 0 for value in backward[1:]), 'no missing inverse residues')
    return forward, backward


def _apply(program, values, initial, meter):
    horizon = _values(values, meter)
    parsed = _program(program, meter)
    _exact_vector(initial, horizon, meter)
    meter.charge(2 * (horizon + 1))
    signed = list(initial)
    absolute = [meter.number(abs(value)) for value in initial]
    resident = 13 * (horizon + 1) + 16384
    meter.live(resident)
    roots = OLD._RootMaps(horizon, meter, resident)
    table = (OLD._spf(horizon, meter, resident)
             if any(op == 'convolve' for op, _, _ in parsed) else None)
    for op, parameter, stage in parsed:
        meter.charge()
        if op == 'sign':
            for n in range(1, horizon + 1):
                meter.charge()
                signed[n] = meter.number(signed[n] * OLD._phase(
                    stage['phase'], n, values, meter, roots))
        elif op == 'permute':
            forward, backward = _permutation(stage['map'], horizon, values, meter, roots)
            mapping = backward if parameter else forward
            meter.charge(2 * (horizon + 1))
            signed = [signed[index] for index in mapping]
            absolute = [absolute[index] for index in mapping]
            del forward, backward, mapping
        elif op == 'shear':
            for n in range(2, horizon, 2):
                meter.charge(5)
                sign = OLD._phase(stage['phase'], n, values, meter, roots)
                target, origin = ((n, n + 1) if stage['direction'] == 'even_from_odd'
                                  else (n + 1, n))
                signed[target] = meter.number(signed[target] + meter.number(
                    parameter * sign * signed[origin]))
                absolute[target] = meter.number(absolute[target] + meter.number(
                    abs(parameter) * absolute[origin]))
        else:
            kernel = OLD._kernel(parameter, stage['prime_phase'], horizon, values,
                                 table, meter, resident, roots)
            meter.charge(2 * (horizon + 1))
            new_signed = [Q(0)] * (horizon + 1)
            new_absolute = [Q(0)] * (horizon + 1)
            for n in range(1, horizon + 1):
                divisors = OLD._divisors(n, table, meter)
                roots.live(4 * len(divisors) + 256)
                signed_total = absolute_total = Q(0)
                for divisor in divisors:
                    meter.charge(4)
                    argument = n // divisor
                    signed_total = meter.number(signed_total + meter.number(
                        kernel[divisor] * signed[argument]))
                    absolute_total = meter.number(absolute_total + meter.number(
                        abs(kernel[divisor]) * absolute[argument]))
                new_signed[n] = signed_total
                new_absolute[n] = absolute_total
            signed, absolute = new_signed, new_absolute
            del kernel
    return dict(signed=signed, absolute=absolute)


def apply_to_state(program, values, state, meter):
    return _apply(program, values, state, meter)['signed']


def evaluate(program, values, meter):
    horizon = _values(values, meter)
    _program(program, meter)
    meter.charge(horizon + 1)
    meter.live(3 * (horizon + 1) + 16384)
    initial = [Q(0)]
    for value in values[1:]:
        initial.append(meter.number(initial[-1] + value))
    return _apply(program, values, initial, meter)


def _state(state, meter):
    _require(type(state) is dict and set(state) == {'signed', 'absolute'},
             'exact signed/path-envelope state')
    signed, absolute = state['signed'], state['absolute']
    _require(type(signed) is list and 2 <= len(signed) <= MAX_HORIZON + 1,
             'complete signed state vector')
    horizon = len(signed) - 1
    _horizon(horizon, meter)
    _exact_vector(signed, horizon, meter)
    _exact_vector(absolute, horizon, meter)
    meter.charge(horizon + 1)
    _require(all(envelope >= abs(value) for value, envelope in zip(signed, absolute)),
             'pointwise full absolute path envelope')
    meter.live(4 * (horizon + 1) + 16384)
    return horizon


def moments(state, scales, meter):
    horizon = _state(state, meter)
    _require(type(scales) is list and len(scales) <= horizon, 'bounded moment scale list')
    meter.charge(len(scales))
    seen = set()
    for scale in scales:
        meter.charge(2)
        _require(type(scale) is int and scale >= 1 and scale not in seen
                 and 2 * scale - 1 <= horizon, 'distinct complete strict moment blocks')
        meter.number(scale)
        seen.add(scale)
    meter.live(4 * (horizon + 1) + 16 * len(scales) + 16384)
    records = []
    for scale in scales:
        signed_total = absolute_total = Q(0)
        for n in range(scale, 2 * scale):
            meter.charge(4)
            signed_total = meter.number(signed_total + meter.number(state['signed'][n] ** 2))
            absolute_total = meter.number(absolute_total + meter.number(state['absolute'][n] ** 2))
        denominator = meter.number(scale * scale)
        records.append(dict(X=scale, energy=str(meter.number(signed_total / denominator)),
                            absolute_energy=str(meter.number(absolute_total / denominator))))
    return records


def initial_cost(state, meter):
    horizon = _state(state, meter)
    _require(horizon >= 31, 'complete initial head1..31')
    total = Q(0)
    for n in range(1, 32):
        meter.charge(3)
        term = meter.number(meter.number(state['signed'][n] ** 2) / meter.number(n * n))
        total = meter.number(total + term)
    return str(total)


def decomposition(program, values, state, scales, meter):
    """Split an already evaluated full output into same/lower-block paths.

    The caller binds state to program by execution/audit. This helper validates
    its exact payload and checks the algebraic split without repeating that
    full evaluation. The remaining raw word is intentionally not normalized.
    """
    _program(program, meter)
    horizon = _values(values, meter)
    _require(_state(state, meter) == horizon, 'same source/output closed horizon')
    _require(type(scales) is list and len(scales) <= horizon, 'bounded split scales')
    seen = set()
    for scale in scales:
        meter.charge(3)
        _require(type(scale) is int and scale >= 1 and scale & (scale - 1) == 0
                 and scale not in seen and 2 * scale - 1 <= horizon,
                 'distinct complete dyadic split blocks')
        meter.number(scale)
        seen.add(scale)
    meter.charge(len(program['stages']))
    residual_word = dict(stages=[stage for stage in program['stages']
                                 if stage['op'] != 'convolve'])
    diagonal = evaluate(residual_word, values, meter)['signed']
    meter.charge(horizon + 1)
    meter.live(12 * (horizon + 1) + 16 * len(scales) + 16384)
    lower = [meter.number(value - head) for value, head in zip(state['signed'], diagonal)]
    records = []
    for scale in scales:
        first = second = mixed = total = Q(0)
        for n in range(scale, 2 * scale):
            meter.charge(8)
            first = meter.number(first + meter.number(diagonal[n] ** 2))
            second = meter.number(second + meter.number(lower[n] ** 2))
            mixed = meter.number(mixed + meter.number(2 * meter.number(diagonal[n] * lower[n])))
            total = meter.number(total + meter.number(state['signed'][n] ** 2))
        denominator = meter.number(scale * scale)
        first, second, mixed, total = [meter.number(value / denominator)
                                       for value in (first, second, mixed, total)]
        _require(meter.number(meter.number(first + second) + mixed) == total,
                 'complete exact diagonal/lower/mixed identity')
        records.append(dict(X=scale, diagonal_energy=str(first), lower_energy=str(second),
                            mixed_energy=str(mixed), total_energy=str(total)))
    return records
