"""Expose weak experimental evidence without discarding unsupported leads."""
from fractions import Fraction as Q
from detector_safe_evaluation import safe_innovation


def training_diagnostics(program, rows, training_scales, boundary_scales=(1, 2, 4, 8)):
    observed, unavailable = [], []
    for X in training_scales:
        value = safe_innovation(program, rows, X)
        if value.available:
            observed.append({'X': X, 'innovation': str(value.value)})
        else:
            unavailable.append({'X': X, 'status': value.status.value, 'reason': value.reason})
    signs = {'positive': 0, 'zero': 0, 'negative': 0}
    for row in observed:
        v = Q(row['innovation'])
        signs['positive' if v > 0 else 'negative' if v < 0 else 'zero'] += 1
    boundary = []
    for X in boundary_scales:
        result = safe_innovation(program, rows, X)
        boundary.append({'X': X, 'included_in_fit': X in training_scales,
                         'status': result.status.value,
                         'innovation': str(result.value) if result.available else None})
    flags = []
    if observed and signs['positive'] == 0:
        flags.append('No positive training innovation: tiny fitted constants do not measure positive forcing.')
    if any(not row['included_in_fit'] for row in boundary):
        flags.append('Small dyadic boundaries omitted from fitting an every-dyadic-scale claim.')
    if unavailable:
        flags.append('Unavailable training responses cannot support a complete constant fit.')
    return {'training_sign_counts': signs, 'unavailable_training_cases': unavailable,
            'boundary_observations': boundary, 'evidence_warnings': flags,
            'candidate_discarded': False, 'unknown_global_claim_disproved': False,
            'global_signed_bound_proved': False}
