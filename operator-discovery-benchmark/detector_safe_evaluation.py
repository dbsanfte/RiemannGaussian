"""Unfrozen safety boundary for exact detector evaluation.

This wrapper preserves the native full rational-power ceiling API but turns
unavailable arithmetic into explicit outcomes. It does not alter any frozen
detector or claim a global bound. A completed score report may contain missing
observations; its own available status means the report was produced.
"""

from dataclasses import dataclass, field
from enum import Enum
from fractions import Fraction
from copy import deepcopy
from typing import Any

import inverse_prefix_grammar as grammar


class Status(str, Enum):
    AVAILABLE = 'available'
    MISSING = 'missing'
    INVALID = 'invalid'


@dataclass(frozen=True)
class EvaluationResult:
    status: Status
    value: Any = None
    reason: str | None = None
    details: dict = field(default_factory=dict)

    @property
    def available(self):
        return self.status is Status.AVAILABLE


def _available(value):
    return EvaluationResult(Status.AVAILABLE, value)


def _missing(reason, **details):
    return EvaluationResult(Status.MISSING, reason=reason, details=details)


def _invalid(reason, **details):
    return EvaluationResult(Status.INVALID, reason=reason, details=details)


def _rational(value):
    if isinstance(value, (float, bool)):
        raise TypeError('exact rational values must not be floats or booleans')
    return Fraction(value)


def _positive_integer(value):
    return type(value) is int and value >= 1


def rational_ceiling(n, exponent, *, bit_budget=1000000):
    """Available exact integer, explicit missing arithmetic, or invalid input."""
    if not _positive_integer(n) or not _positive_integer(bit_budget):
        return _invalid('positive_integer_base_and_budget_required')
    try:
        power = _rational(exponent)
    except (ValueError, TypeError, ZeroDivisionError) as exc:
        return _invalid('invalid_rational_exponent', error=str(exc))
    if power < 0:
        return _invalid('negative_exponent')
    try:
        value = grammar.ceiling(n, power, bit_budget=bit_budget)
    except (MemoryError, OverflowError, ImportError) as exc:
        return _missing('ceiling_resource_or_evaluator_unavailable', error=str(exc))
    except (ValueError, TypeError, ZeroDivisionError) as exc:
        return _invalid('ceiling_evaluation_rejected_input', error=str(exc))
    if value is None:
        return _missing('ceiling_native_resource_limit', base=n, exponent=str(power))
    if type(value) is not int or value < 1:
        return _invalid('ceiling_returned_nonpositive_or_noninteger')
    return _available(value)


def _feature(feature):
    if not isinstance(feature, dict):
        return _invalid('feature_must_be_a_dictionary')
    if not _positive_integer(feature.get('arity')) or not _positive_integer(feature.get('slot')):
        return _invalid('positive_integer_arity_and_slot_required')
    if feature['slot'] > feature['arity']:
        return _invalid('component_slot_exceeds_arity')
    try:
        power = _rational(feature['normalizing_power'])
    except (KeyError, ValueError, TypeError, ZeroDivisionError) as exc:
        return _invalid('invalid_feature_power', error=str(exc))
    if power < 0:
        return _invalid('negative_feature_power')
    return _available(power)


def safe_potential(program, rows, X, *, bit_budget=1000000):
    """Evaluate all retained signed component-square terms, without omissions.

    A structurally valid zero-weight term is exactly zero and needs no row or
    ceiling arithmetic. Negative weights and malformed zero-weight features
    are invalid. No missing nonzero term is dropped.
    """
    if not _positive_integer(X):
        return _invalid('positive_integer_scale_required')
    if not isinstance(program, dict) or not isinstance(program.get('terms'), list):
        return _invalid('program_terms_list_required')
    total = Fraction(0)
    for index, term in enumerate(program['terms']):
        if not isinstance(term, dict) or 'weight' not in term:
            return _invalid('malformed_potential_term', term=index)
        valid = _feature(term.get('feature'))
        if not valid.available:
            return valid
        try:
            weight = _rational(term['weight'])
        except (ValueError, TypeError, ZeroDivisionError) as exc:
            return _invalid('invalid_term_weight', term=index, error=str(exc))
        if weight < 0:
            return _invalid('negative_potential_weight', term=index)
        if weight == 0:
            continue
        feature = term['feature']
        matching = [row for row in rows if row.get('X') == X
                    and row.get('arity') == feature['arity']]
        if len(matching) > 1:
            return _invalid('duplicate_component_profile', X=X, term=index)
        if not matching or matching[0].get('missing'):
            return _missing('component_profile_unavailable', X=X, term=index)
        try:
            moments = matching[0]['component_moments']
            energy = _rational(moments[feature['slot'] - 1]['energy'])
        except (KeyError, IndexError, TypeError, ValueError, ZeroDivisionError) as exc:
            return _invalid('malformed_component_energy', term=index, error=str(exc))
        if energy < 0:
            return _invalid('negative_square_energy', term=index)
        normalizer = rational_ceiling(X, valid.value, bit_budget=bit_budget)
        if not normalizer.available:
            return normalizer
        # The denominator is guaranteed to be an available positive integer.
        total += weight * energy / normalizer.value
    return _available(total)


def safe_innovation(program, rows, X, *, bit_budget=1000000):
    if not _positive_integer(X):
        return _invalid('positive_integer_scale_required')
    matching = [row for row in rows if row.get('X') == X]
    available_rows = [row for row in matching if not row.get('missing')]
    if not available_rows:
        return _missing('actual_block_profile_unavailable', X=X)
    try:
        pairs = {(_rational(row['energy']), _rational(row['child_energy']))
                 for row in available_rows}
    except (KeyError, ValueError, TypeError, ZeroDivisionError) as exc:
        return _invalid('malformed_actual_block_energy', X=X, error=str(exc))
    if len(pairs) != 1:
        return _invalid('conflicting_actual_block_energies', X=X)
    parent, child = next(iter(pairs))
    if parent < 0 or child < 0:
        return _invalid('negative_actual_square_energy', X=X)
    left = safe_potential(program, rows, X, bit_budget=bit_budget)
    if not left.available:
        return left
    right = safe_potential(program, rows, 2 * X, bit_budget=bit_budget)
    if not right.available:
        return right
    return _available(child / (4 * X * X) - parent / (X * X)
                      + right.value - left.value)


def _design(scales, levels):
    if not scales or not levels or any(not _positive_integer(X) for X in scales) or any(
            not _positive_integer(q) for q in levels):
        return _invalid('nonempty_positive_integer_scales_and_levels_required')
    if len(set(scales)) != len(scales) or len(set(levels)) != len(levels):
        return _invalid('duplicate_scales_or_levels')
    return _available(True)


def safe_fit_potential(program, rows, scales, levels, *, bit_budget=1000000):
    """Preserve the native fit; never fit a constant from a partial scale set."""
    valid = _design(scales, levels)
    if not valid.available:
        return valid
    innovations = []
    for X in scales:
        value = safe_innovation(program, rows, X, bit_budget=bit_budget)
        if not value.available:
            return value
        innovations.append((X, value.value))
    constants = {}
    for q in levels:
        ratios = [Fraction(0)]
        for X, value in innovations:
            normalizer = rational_ceiling(X, Fraction(1, q), bit_budget=bit_budget)
            if not normalizer.available:
                return normalizer
            ratios.append(value / normalizer.value)
        constants[str(q)] = str(Fraction(5, 4) * max(ratios) + Fraction(1, 2 ** 64))
    result = deepcopy(program)
    result['fitted_constants'] = constants
    return _available(result)


def safe_score_potential(program, rows, scales, levels, *, bit_budget=1000000):
    """Produce a report with explicit per-observation available/missing status.

    An unknown q constant is missing even if its signed innovation is known.
    Resource failures set the unavailable signed innovation/bound/margin to
    None and finite_pass to None. Missing and invalid cases never pass.
    """
    valid = _design(scales, levels)
    if not valid.available:
        return valid
    if not isinstance(program, dict) or not isinstance(program.get('fitted_constants', {}), dict):
        return _invalid('fitted_constants_dictionary_required')
    constants = program.get('fitted_constants', {})
    observations = []
    for X in scales:
        innovation = safe_innovation(program, rows, X, bit_budget=bit_budget)
        for q in levels:
            entry = {'X': X, 'level': q,
                     'signed_innovation': str(innovation.value) if innovation.available else None,
                     'bound': None, 'margin': None, 'finite_pass': None,
                     'global_signed_upper_bound_proved': False}
            if not innovation.available:
                outcome = innovation
            elif str(q) not in constants:
                outcome = _missing('unknown_level_constant', q=q)
            else:
                try:
                    constant = _rational(constants[str(q)])
                    if constant < 0:
                        raise ValueError('negative bound constant')
                except (ValueError, TypeError, ZeroDivisionError) as exc:
                    outcome = _invalid('invalid_level_constant', q=q, error=str(exc))
                else:
                    normalizer = rational_ceiling(X, Fraction(1, q), bit_budget=bit_budget)
                    outcome = normalizer
                    if normalizer.status is Status.MISSING:
                        # Keep resource-limited observations wholly unavailable;
                        # this differs from an explicitly unknown level constant.
                        entry['signed_innovation'] = None
                    if normalizer.available:
                        bound = constant * normalizer.value
                        entry.update({'bound': str(bound),
                                      'margin': str(bound - innovation.value),
                                      'finite_pass': innovation.value <= bound})
            entry.update({'status': outcome.status.value,
                          'missing': outcome.status is Status.MISSING,
                          'invalid': outcome.status is Status.INVALID,
                          'reason': outcome.reason})
            observations.append(entry)
    report = {'observations': observations,
              'finite_cases': sum(row['status'] == 'available' for row in observations),
              'finite_passes': sum(row['finite_pass'] is True for row in observations),
              'missing_cases': sum(row['missing'] for row in observations),
              'invalid_cases': sum(row['invalid'] for row in observations),
              'global_signed_upper_bound_proved': False}
    return _available(report)
