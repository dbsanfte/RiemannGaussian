"""Unfrozen finite-fit wrapper preserving the entire response dictionary.

Native sparse candidates are archived unchanged. Only complete, core-column
fits are eligible for separate inverse-polynomial admission. Eligibility is
not admission, an identifiability theorem, or a global reconstruction proof.
"""

from copy import deepcopy
from fractions import Fraction

import inverse_prefix_grammar as grammar
from detector_safe_evaluation import EvaluationResult, Status


def _invalid(reason, **details):
    return EvaluationResult(Status.INVALID, reason=reason, details=details)


def _exact(value):
    if isinstance(value, (float, bool)):
        raise TypeError('finite response arithmetic must be exact rational')
    return Fraction(value)


def predict_full(native_model, row):
    """Validate a finite response using every learned column, never projection."""
    try:
        arity = row['arity']
        if type(arity) is not int or arity < 1:
            return _invalid('positive_integer_prediction_arity_required')
        weights = native_model['learned_vectors'].get(str(arity))
        if weights is None:
            return EvaluationResult(Status.MISSING, reason='arity_has_no_fitted_vector')
        columns = row['columns']
        if len(weights) != len(columns):
            return _invalid('response_width_differs_from_fitted_vector')
        value = sum((_exact(w) * _exact(x) for w, x in zip(weights, columns)), Fraction(0))
        target = _exact(row['anonymous_target'])
    except (KeyError, TypeError, ValueError, ZeroDivisionError) as exc:
        return _invalid('malformed_prediction_input', error=str(exc))
    return EvaluationResult(Status.AVAILABLE, {
        'predicted': str(value), 'observed_target': str(target),
        'finite_pass': value == target, 'full_column_vector_used': True,
        'global_reconstruction_proved': False,
    })


def safe_infer(rows, arities, support_budget=3):
    """Run the native learner only on present arities and expose missingness.

    No selected native weights are overwritten. The result is a completed
    finite-fit report even when some requested arities are missing or rejected.
    """
    if (not isinstance(arities, (list, tuple)) or not arities
            or any(type(k) is not int or k < 1 for k in arities)
            or len(set(arities)) != len(arities)):
        return _invalid('distinct_positive_integer_arities_required')
    if type(support_budget) is not int or support_budget < 1:
        return _invalid('positive_integer_recurrence_support_budget_required')
    if not isinstance(rows, (list, tuple)):
        return _invalid('response_rows_list_required')
    requested = list(arities)
    samples = []
    for index, row in enumerate(rows):
        try:
            if not isinstance(row, dict) or type(row['arity']) is not int or row['arity'] < 1:
                raise ValueError('positive integer row arity required')
            columns = row['columns']
            if not isinstance(columns, (list, tuple)) or len(columns) != 2 * row['arity'] + 2:
                raise ValueError('native dictionary requires 2*arity+2 columns')
            [_exact(value) for value in columns]
            _exact(row['anonymous_target'])
        except (KeyError, TypeError, ValueError, ZeroDivisionError) as exc:
            return _invalid('malformed_response_row', row=index, error=str(exc))
        if row['arity'] in requested:
            samples.append(deepcopy(row))
    present = [k for k in requested if any(row['arity'] == k for row in samples)]
    # Empty native input would index data[0]. Do not invoke that unsupported
    # branch. The missing report retains all requested arities explicitly.
    native = grammar.infer(samples, present, support_budget) if present else None
    outcomes, reasons = [], []
    if sorted(requested) != list(range(1, len(requested) + 1)):
        reasons.append({'reason': 'incomplete_core_arity_chain',
                        'declared_arities': sorted(requested),
                        'expected_chain_length': max(requested)})
    for k in requested:
        if k not in present:
            outcomes.append({'arity': k, 'status': 'missing',
                             'reason': 'no_response_rows', 'full_weights': None})
            reasons.append({'arity': k, 'reason': 'no_response_rows'})
            continue
        weights = native['learned_vectors'].get(str(k))
        if weights is None:
            outcomes.append({'arity': k, 'status': 'missing',
                             'reason': 'no_exact_fit', 'full_weights': None})
            reasons.append({'arity': k, 'reason': 'no_exact_fit'})
            continue
        noncore = [j for j, weight in enumerate(weights) if j >= k and _exact(weight) != 0]
        outcomes.append({'arity': k, 'status': 'available', 'reason': None,
                         'full_weights': list(weights), 'noncore_nonzero_columns': noncore,
                         'inverse_polynomial_core_eligible': not noncore})
        if noncore:
            reasons.append({'arity': k, 'reason': 'noncore_coefficients_present',
                            'columns': noncore})
    predictions = []
    if native is not None:
        for index, row in enumerate(samples):
            prediction = predict_full(native, row)
            predictions.append({'row_index': index, 'arity': row['arity'],
                                'status': prediction.status.value,
                                'reason': prediction.reason,
                                'observation': prediction.value})
            if prediction.available and not prediction.value['finite_pass']:
                reasons.append({'arity': row['arity'], 'reason': 'full_fit_response_failure'})
    report = {'requested_arities': requested, 'present_arities': present,
              'native_inference_archive': deepcopy(native),
              'arity_outcomes': outcomes, 'full_weight_predictions': predictions,
              'macro_eligible': not reasons,
              'macro_candidate': deepcopy(native) if not reasons else None,
              'macro_ineligibility_reasons': reasons,
              'analytical_admission_still_required': True,
              'global_reconstruction_proved': False,
              'original_native_candidates_changed': False}
    return EvaluationResult(Status.AVAILABLE, report)
