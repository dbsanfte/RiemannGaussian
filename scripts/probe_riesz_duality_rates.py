#!/usr/bin/env python3
"""Optional source-scale rate audit, not a prime-sum estimate or certificate.

Uses the two explicit envelopes audited in ZetaRieszDualityRateAudit.
The least-prime rate is an optimistic lower bound for a published *upper
allowance*, not a lower bound for an arithmetic error. The hybrid diagnostic
holds its example height fixed. Never run this exploration in ordinary CI.
"""
import argparse
from decimal import Decimal, localcontext
import hashlib
import json
from pathlib import Path


def run(precision):
    with localcontext() as ctx:
        ctx.prec = precision
        D = Decimal
        growth = (D(10001)/10000).ln()
        c = D(100)/203*D(2).ln()
        log10 = D(10).ln()
        rows = []
        for n in (256, 640, 1536, 4096, 8192, 16384, 65536, 262144, 1048576):
            t = D(n)/100
            ratio_log = t-(55*t).ln()
            rows.append(dict(
                N=n,
                duality_scaled_allowance_lower_log10=str(
                    (n*growth+c.ln()-D(n+1).ln())/log10),
                hybrid_prime_cutoff_log=str(t),
                hybrid_fixed_center_norm=55,
                hybrid_cutoff_over_height_logcutoff_log10=str(ratio_log/log10),
                hybrid_envelope_log10={str(k): str(((k+2)*t-k*(55*t).ln())/log10)
                                      for k in (1, 4, 16)},
                hybrid_all_orders_lower_log10=str(2*t/log10) if ratio_log >= 0 else None,
            ))
        return dict(source_log_growth=str(growth), rows=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    low, high = run(50), run(90)
    discrepancy = max(abs(Decimal(a['duality_scaled_allowance_lower_log10'])-
                          Decimal(b['duality_scaled_allowance_lower_log10']))
                      for a, b in zip(low['rows'], high['rows']))
    report = dict(
        scope='Rate/hypothesis audit only; no estimate of the retained signed carrier',
        source_radius='10001/20000',
        duality_core_ceiling='203*N/100',
        duality_allowance_lower='(100*log(2)/203)*(10001/10000)^N/(N+1)',
        duality_relaxation='Only log(y)>=log(2) is used. Other literature hypotheses restrict the choices further.',
        hybrid_scope='Displayed sharp-cutoff envelope, not actual error; its implicit constants need not be uniform in K.',
        precisions=[50, 90],
        precision_change_log10=str(discrepancy),
        interval_certificate=False,
        lean_audit='RiemannGaussian/ZetaRieszDualityRateAudit.lean',
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        **high,
    )
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
