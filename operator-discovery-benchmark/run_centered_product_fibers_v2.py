"""Startup-only repair: canonical JSON cap keys, preserving the frozen v1."""
import argparse
from pathlib import Path
import run_centered_product_fibers as experiment

_original_specification = experiment.specification
experiment.SOURCES = experiment.SOURCES + [
    'run_centered_product_fibers_v2.py',
    'centered_product_protocol_revision_002.txt',
]


def specification():
    protocol = _original_specification()
    protocol['producer_caps'] = {str(X): cap for X, cap in experiment.CAPS.items()}
    protocol['startup_revision'] = dict(
        prior_attempt='centered-product-results/pilot-001',
        reason='JSON object keys are strings; compare the declared scale-cap mapping in canonical form',
        prior_arithmetic_operations=0, prior_test_operations=0,
        prior_administrative_work='included in the existing one-million metadata reserve',
        numerical_implementation_changed=False,
    )
    return protocol


experiment.specification = specification


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['freeze', 'run'])
    parser.add_argument('directory')
    args = parser.parse_args()
    getattr(experiment, args.action)(Path(args.directory))
