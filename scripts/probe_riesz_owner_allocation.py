#!/usr/bin/env python3
"""Optional floating-point diagnostic for the global owner allocation estimate.

This is not a certificate. The binomial probe uses the literal unpaidOrders.
--literal also enumerates small finite signed prime populations using the
existing radial probe, with the exact moving length, allocation and phase.
Those populations have extra physical restrictions and are not the full carrier.
"""
import argparse
import json
import math

import numpy as np
from scipy.stats import binom
from probe_riesz_fixed_count_period import unpaid_orders
from probe_riesz_global_curvature import literal_row


def allocation_rows():
    rows = []
    shares = np.linspace(.001, .999, 1997)
    for n in (32, 64, 128, 256, 640, 1536, 4096, 8192):
        orders = unpaid_orders(n)
        # Tail sums by CDF avoid constructing a large order-by-share array.
        lo, hi = int(orders[0]), int(orders[-1])
        assert np.array_equal(orders, np.arange(lo, hi+1))
        pmf_low = binom.pmf(lo-1, n, shares)
        pmf_high = binom.pmf(hi, n, shares)
        # T*d/dT F(b/T), using the exact endpoint derivative of the binomial CDF.
        derivative = -(n+1)*shares*(pmf_low-pmf_high)
        at_max = int(np.argmax(abs(derivative)))
        balanced = float(binom.cdf(hi, n+1, .5)-binom.cdf(lo-1, n+1, .5))
        rows.append({
            'N': n, 'unpaid_first': lo, 'unpaid_last': hi,
            'balanced_allocation_at_half': balanced,
            'proved_balanced_envelope_float': math.exp(-n/64),
            'max_abs_T_derivative_over_sqrt_order': float(abs(derivative[at_max])/math.sqrt(n+1)),
            'maximizing_share_in_grid': float(shares[at_max]),
            'proved_uniform_derivative_constant': 6,
            'all_count_window_prefactor_times_nonowner_rate':
                (4*(n+1)/3)*(.503*(2048/1023)*math.exp(-1/64))**n,
        })
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--literal', action='store_true')
    args = parser.parse_args()
    result = {'scope': __doc__, 'allocation': allocation_rows()}
    if args.literal:
        result['literal'] = [literal_row(n) for n in (6, 8, 10)]
    print(json.dumps(result, indent=2))
