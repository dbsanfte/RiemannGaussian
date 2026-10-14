"""Unfrozen reproducible exploration of the supplied exact signed AST grammar.

Sampling is independent of response values. Net signed mass is exploratory
finite evidence, not the full Mertens defect or a theorem score.
"""

from fractions import Fraction
import hashlib
import json

from detector_safe_evaluation import EvaluationResult, Status
from signed_arithmetic_language import expr, evaluate, WorkBudget


VERSION = 'seeded-signed-arithmetic-ast-exploration-v1-unfrozen'
ATOMS = ('one', 'unit', 'mu', 'liouville')
OPERATIONS = ('scale', 'add', 'convolution', 'product', 'prefix', 'shift',
              'dilate', 'floor_index', 'root_index', 'truncate',
              'coprime_mask', 'residue_mask', 'normalize')
WEIGHTS = ('-2', '-1', '-1/2', '-1/4', '0', '1/4', '1/2', '1', '2')
POWERS = ('0', '1/2', '1', '3/2', '2', '5/2', '1000001')


class _Random:
    def __init__(self, seed):
        self.state = seed & 0xffffffff

    def choice(self, values):
        self.state = (1664525 * self.state + 1013904223) & 0xffffffff
        # Use upper bits rather than alternating low LCG bits.
        return values[(self.state >> 9) % len(values)]


class _ConstructionLimit(Exception):
    pass


def program_digest(expression):
    return hashlib.sha256(json.dumps(expression, sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


def sample_programs(seed, count, max_depth, *, max_attempts=None, max_nodes_per_program=128):
    """Return a typed report of unique generated ASTs and all sampled attempts.

    max_depth is an upper bound, not an exact depth. Every positive-depth node
    chooses a leaf with probability 1/5; otherwise it chooses uniformly from
    OPERATIONS. Atoms and each recorded literal grid are uniform under this
    deterministic generator. A construction budget failure is recorded, never
    replaced by an unreported truncation of the sampled expression.
    """
    if (type(seed) is not int or type(count) is not int or count < 0
            or type(max_depth) is not int or max_depth < 0
            or type(max_nodes_per_program) is not int or max_nodes_per_program < 1):
        return EvaluationResult(Status.INVALID, reason='invalid_sampler_design')
    if max_attempts is None:
        max_attempts = max(1, count * 16)
    if type(max_attempts) is not int or max_attempts < 1:
        return EvaluationResult(Status.INVALID, reason='positive_attempt_budget_required')
    random = _Random(seed)
    programs, attempts, seen = [], [], set()

    def construct(depth, counter):
        counter[0] += 1
        if counter[0] > max_nodes_per_program:
            raise _ConstructionLimit()
        if depth == 0 or random.choice((0, 1, 2, 3, 4)) == 0:
            return expr(random.choice(ATOMS))
        op = random.choice(OPERATIONS)
        children = [construct(depth - 1, counter)]
        if op in ('add', 'convolution', 'product'):
            children.append(construct(depth - 1, counter))
        params = {}
        if op == 'scale':
            params['weight'] = random.choice(WEIGHTS)
        elif op == 'shift':
            params['offset'] = random.choice((-5, -2, -1, 0, 1, 2, 5))
        elif op == 'dilate':
            params['factor'] = random.choice((1, 2, 3, 4))
        elif op == 'floor_index':
            params['divisor'] = random.choice((1, 2, 3, 4, 5))
        elif op == 'root_index':
            params['order'] = random.choice((1, 2, 3, 4, 7, 10 ** 100))
        elif op == 'truncate':
            params['cutoff'] = random.choice((0, 1, 2, 3, 7, 16, 31))
        elif op in ('coprime_mask', 'residue_mask'):
            params['modulus'] = random.choice((2, 3, 4, 5, 6, 7))
            if op == 'residue_mask':
                params['residue'] = random.choice(tuple(range(params['modulus'])))
        elif op == 'normalize':
            params['power'] = random.choice(POWERS)
        return expr(op, *children, **params)

    for attempt in range(max_attempts):
        if len(programs) == count:
            break
        nodes = [0]
        try:
            expression = construct(max_depth, nodes).to_dict()
            identifier = program_digest(expression)
        except (RecursionError, _ConstructionLimit):
            attempts.append({'attempt': attempt, 'status': 'missing',
                             'reason': 'construction_resource_limit', 'nodes': nodes[0]})
            continue
        if identifier in seen:
            attempts.append({'attempt': attempt, 'status': 'duplicate',
                             'program_id': identifier, 'nodes': nodes[0]})
            continue
        seen.add(identifier)
        record = {'program_id': identifier, 'expression': expression,
                  'top_operation': expression['op'], 'construction_nodes': nodes[0],
                  'exploratory_not_full_RH_target': True}
        programs.append(record)
        attempts.append({'attempt': attempt, 'status': 'generated',
                         'program_id': identifier, 'nodes': nodes[0]})
    report = {'sampler_version': VERSION, 'seed': seed, 'requested_count': count,
              'max_depth': max_depth, 'max_attempts': max_attempts,
              'max_nodes_per_program': max_nodes_per_program,
              'atoms': list(ATOMS), 'operations': list(OPERATIONS),
              'weight_grid': list(WEIGHTS), 'normalizing_power_grid': list(POWERS),
              'programs': programs, 'attempts': attempts,
              'generated_count': len(programs),
              'duplicate_attempts': sum(a['status'] == 'duplicate' for a in attempts),
              'missing_attempts': sum(a['status'] == 'missing' for a in attempts),
              'invalid_attempts': 0, 'requested_count_completed': len(programs) == count,
              'response_values_used_for_generation': False,
              'global_actual_signed_bound_proved': False}
    # The report is available even if its requested unique-program count was
    # unattainable within the construction budget; that is explicit above.
    return EvaluationResult(Status.AVAILABLE, report)


def evaluate_programs(programs, N, *, budget=None):
    """Evaluate every sampled program independently, archiving every outcome."""
    records = []
    for program in programs:
        expression = program['expression']
        identifier = program_digest(expression)
        if identifier != program['program_id']:
            outcome = EvaluationResult(Status.INVALID, reason='program_digest_mismatch')
        else:
            outcome = evaluate(expression, N, budget=budget)
        record = {'program_id': program['program_id'], 'expression': expression,
                  'top_operation': expression['op'], 'N': N,
                  'status': outcome.status.value, 'reason': outcome.reason,
                  'details': outcome.details, 'metrics': None, 'arithmetic': None,
                  'exploratory_not_full_RH_target': True,
                  'global_actual_signed_bound_proved': False}
        if outcome.available:
            limits = budget or WorkBudget()
            coefficients = outcome.value['coefficients']
            operations = outcome.value['cost']['operations']
            signed, unsigned, square = Fraction(0), Fraction(0), Fraction(0)
            metric_missing = None
            for n in range(1, len(coefficients)):
                operations += 5  # add; absolute/add; multiply/add
                if operations > limits.max_operations:
                    metric_missing = 'metric_operation_budget_exhausted'
                    break
                value = Fraction(coefficients[n])
                signed += value
                unsigned += abs(value)
                square += value * value
                if any(abs(v.numerator).bit_length() + v.denominator.bit_length()
                       > limits.max_bits for v in (signed, unsigned, square)):
                    metric_missing = 'metric_bit_budget_exhausted'
                    break
            operations += 3  # absolute/subtract/divide for the gain ratio
            if operations > limits.max_operations:
                metric_missing = 'metric_operation_budget_exhausted'
            if metric_missing:
                record.update({'status': 'missing', 'reason': metric_missing,
                               'details': {'charged_operations': operations}})
            else:
                gain = unsigned - abs(signed)
                ratio = gain / unsigned if unsigned else Fraction(0)
                record['metrics'] = {'signed_mass': str(signed), 'unsigned_mass': str(unsigned),
                                     'square_mass': str(square), 'cancellation_gain': str(gain),
                                     'cancellation_gain_ratio': str(ratio),
                                     'nontrivial_unsigned_mass': unsigned > 0}
                record['arithmetic'] = outcome.value
                record['metric_operations'] = 5 * N + 3
                record['total_charged_operations'] = operations
        records.append(record)
    return {'N': N, 'observations': records,
            'available_cases': sum(r['status'] == 'available' for r in records),
            'missing_cases': sum(r['status'] == 'missing' for r in records),
            'invalid_cases': sum(r['status'] == 'invalid' for r in records),
            'global_actual_signed_bound_proved': False}


def select_diverse(observations, per_top_operation=1):
    """Finite exploratory ranking; one structural quota per top operation."""
    if type(per_top_operation) is not int or per_top_operation < 1:
        raise ValueError('positive structural quota required')
    groups = {}
    for record in observations:
        if record['status'] == 'available':
            groups.setdefault(record['top_operation'], []).append(record)
    def rank(record):
        metrics = record['metrics']
        return (-int(metrics['nontrivial_unsigned_mass']),
                -Fraction(metrics['cancellation_gain_ratio']),
                record['total_charged_operations'],
                len(json.dumps(record['expression'], sort_keys=True)), record['program_id'])
    return [record for op in sorted(groups)
            for record in sorted(groups[op], key=rank)[:per_top_operation]]
