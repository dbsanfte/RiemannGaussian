#!/usr/bin/env python3
"""Optional stress test of the proposed passage from complete to masked phases.

These are explicit analytic modes, NOT actual zeta zeros or prime data.
Both complete legs decay geometrically at the requested radius. Their
correlated total-order integral over the literal largest-share interval
has a resonant endpoint and eventually grows. Thus one-leg moment limits
alone do not justify this mask transfer. Extra literal arithmetic
cancellation could still eliminate the mode; this test does not refute
the FullParityPacket conjecture.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    radius = 10001/20000
    axis = 20001/40000
    low, high = 43/80, 9/16
    left = axis+0.1j
    right = axis-(43/370)*1j
    slope = left-right
    pole = lambda share: share*left+(1-share)*right

    def band(order, a, b):
        # Exact antiderivative of (radius/pole(share))^(order+2).
        return radius/(slope*(order+1))*((radius/pole(a))**(order+1)
                                          -(radius/pole(b))**(order+1))

    rows = []
    for n in (256,640,1536,4096,16384,65536,131072,262144,1048576):
        # Log form retains the decay when a float would underflow to zero.
        k = math.ceil(n/200)
        log_leg_error = k*math.log(max(radius/abs(left),radius/abs(right)))
        unmasked = band(n,0,1)
        masked = band(n,low,high)
        rows.append({'N':n,'smallest_good_order':k,
                     'log_uniform_complete_leg_error_bound':log_leg_error,
                     'unmasked_integral_norm':abs(unmasked),
                     'masked_integral_norm':abs(masked),
                     'masked_integral_norm_times_1e_minus_14':1e-14*abs(masked),
                     'masked_integral_real':masked.real,
                     'masked_integral_imag':masked.imag})
    report = {'status':'Analytic-mode stress test, not literal primes or a packet no-go theorem.',
              'input_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'parameters':{'radius':'10001/20000','axis':'20001/40000',
                            'low':'43/80','high':'9/16',
                            'left_im':'1/10','right_im':'-43/370'},
              'complete_leg_distances':[abs(left),abs(right)],
              'masked_endpoint_distances':[abs(pole(low)),abs(pole(high))],
              'formula':'integral_a^b (u / (q*z_left+(1-q)*z_right))^(N+2) dq',
              'rows':rows,
              'interpretation':'All one-leg good-order errors tend to zero, but the share mask has an endpoint at a<u. Its contribution is (u/a)^(N+1)/(N+1) times a nonzero constant. The 1e-14 multiplier is illustrative, not an estimate for any actual packet residual. Original Riesz/all-count identities are not imposed by this model.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
