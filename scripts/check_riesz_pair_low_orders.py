#!/usr/bin/env python3
"""Independent high-precision replay; imports no numerical producer module."""
import argparse
import hashlib
import json
from pathlib import Path
import mpmath as mp


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input',type=Path,default=Path('.lake/riesz-pair-low-orders/probe.json'))
    ap.add_argument('--output',type=Path,default=Path('.lake/riesz-pair-low-orders/validation.json'))
    args=ap.parse_args()
    data=json.loads(args.input.read_text())
    for pin in data['sources']:
        assert hashlib.sha256(Path(pin['path']).read_bytes()).hexdigest()==pin['sha256'],pin['path']
    mp.mp.dps=90
    results=[]
    for row in data['rows']:
        N=row['N']
        M,H=N+1,17*N//64+1
        assert row['loggedCutoff']==H and H<=row['originalLoggedCutoff']==13*N//32
        p,q=map(int,row['representative']['primes'])
        x,z=mp.log(p),mp.log(q)
        T=x+z
        D=20000**N//((N+1)*10001**N)
        L=mp.log((D+2)**2)
        def factorial_prefix(share):
            return sum(mp.binomial(M,k)*share**k*(1-share)**(M-k) for k in range(H))
        direct=-T/L*(x*factorial_prefix(x/T)+z*factorial_prefix(z/T))
        def logged_convolution(share):
            # An independently evaluated sum at total factorial order N+2.
            return sum(k*mp.binomial(N+2,k)*share**k*(1-share)**(N+2-k)
                       for k in range(1,H+1))
        convolution=-T*T/((N+2)*L)*(logged_convolution(x/T)+logged_convolution(z/T))
        exact_error=abs(convolution-direct)
        assert exact_error<mp.mpf('1e-70')*max(1,abs(direct))
        float_error=abs(mp.mpf(row['representative']['coefficient'])-direct)
        assert float_error<mp.mpf('1e-9')*max(1,abs(direct))
        physical=max(x,z)<=L
        assert physical==row['representative']['physical']
        if physical:
            assert min(x,z)/T>=mp.mpf(7)/24
            assert T/L<=2
            assert abs(direct)<=2*T*mp.exp(-mp.mpf(N)/1000)
        original=row['originalPrefix']; remaining=row['remainingPrefix']; removed=row['removedLowLogged']
        signed_error=abs(complex(original['re']-remaining['re']-removed['re'],
            original['im']-remaining['im']-removed['im']))
        assert signed_error<1e-7*max(1,abs(complex(original['re'],original['im'])))
        results.append(dict(box=row['box'],weightedFactorialIdentityError=float(exact_error),
            floatCoefficientError=float(float_error),phaseReplayError=signed_error,
            physicalIncidence=physical))
    assert not data['floor'] and not data['fullSignedMainBoundProved']
    output=dict(input=str(args.input),inputSha256=hashlib.sha256(args.input.read_bytes()).hexdigest(),
        checkerSha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        checks=results,everySourcePinMatched=True,originalPhasesAndMasksRetained=True,
        belowFormalThresholdRegressionOnly=True,passed=True,floor=False)
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(dict(independentRows=len(results),
        maxWeightedIdentityError=max(r['weightedFactorialIdentityError'] for r in results),
        passed=True,floor=False)))


if __name__=='__main__':
    main()
