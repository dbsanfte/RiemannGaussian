#!/usr/bin/env python3
"""Diagnostic of exact common-prefix versus divisor-crossing contributions.

Original finite-universe masks and weights; all counts and periods joined.
This is NOT a native-population, interval or source-budget certificate.
No component price is substituted for the joined signed price.
"""
import argparse
from collections import defaultdict
import json
import math
from pathlib import Path
import time

import mpmath as mp
import numpy as np

from probe_riesz_joined_count_correlation import population
from probe_riesz_complex_null_profiles import optimize, period_edge
from probe_riesz_complex_projection import least_positive_cost


def experiment(order, seed, heights):
    start = time.monotonic()
    ceiling = {256:8, 640:16, 1536:32}[order]
    pars, rows, excluded = population(order, ceiling, seed)
    physical = pars['physical']
    endpoint = max(r['label'] for r in rows)
    logscale = max(r['log_amplitude'] for r in rows)
    weights = -np.exp([r['log_amplitude']-logscale for r in rows])[None,:]*np.exp(
        -1j*np.array(heights)[:,None]*np.array([r['total'] for r in rows])[None,:])
    minima = [min(r['factors']) for r in rows]
    late_starts = [r['label']//p for r,p in zip(rows,minima)]
    mu = np.array([r['mu'] for r in rows])
    events = defaultdict(list)
    for i,row in enumerate(rows):
        for d,sign in row['divisors']:
            if d < endpoint:
                events[d].append((i,sign))
    points = sorted({1,physical,endpoint,*events})
    prefix = np.zeros(len(rows), dtype=np.int32)
    grouped = [defaultdict(lambda:np.zeros((3,3),dtype=complex)) for _ in heights]
    channels = np.zeros((len(heights),3,3),dtype=complex)
    energy = np.zeros((len(heights),3,3),dtype=complex)
    max_error = 0.
    for left,right in zip(points,points[1:]):
        for i,sign in events[left]:
            prefix[i] += sign
        early = np.array([left < p for p in minima],dtype=np.int32)
        late = -mu*np.array([a <= left < r['label'] for a,r in zip(late_starts,rows)],dtype=np.int32)
        # The two common values are exact on ACTUAL integers.
        assert np.all(prefix[early != 0] == 1)
        assert np.all(prefix[late != 0] == late[late != 0])
        detail = prefix-early-late
        phi = weights @ np.stack([early,late,detail],axis=1)
        max_error = max(max_error,float(np.max(np.abs(phi.sum(axis=1)-weights@prefix))))
        lo,hi = math.log(left),math.log(right)
        base = left >= physical
        widths = np.array([-(hi-lo) if base else 0.,-(hi-lo),-(hi*hi-lo*lo)/(order+1)])
        channels += phi[:,:,None]*widths[None,None,:]
        if base:
            energy += (hi-lo)*phi[:,:,None]*np.conj(phi[:,None,:])
        for ih,height in enumerate(heights):
            unit = 2*math.pi/height
            cursor,period = lo,math.floor(lo/unit)
            while cursor < hi:
                edge = min(hi,period_edge(period,unit))
                if edge <= cursor:
                    period += 1
                    continue
                dv = np.array([-(edge-cursor) if base else 0.,-(edge-cursor),
                              -(edge*edge-cursor*cursor)/(order+1)])
                grouped[ih][period] += phi[ih,:,None]*dv[None,:]
                cursor,period = edge,period+1
    cases=[]
    for ih,height in enumerate(heights):
        columns=np.array(list(grouped[ih].values()))
        joined_columns=columns.sum(axis=1)
        design=np.column_stack((-joined_columns[:,0].real,joined_columns[:,0].imag,
                                -joined_columns[:,1].real,joined_columns[:,1].imag,
                                -joined_columns[:,2].real,joined_columns[:,2].imag))
        tilt,old_cost=least_positive_cost(design[:,0],-design[:,1],4.)
        fit=optimize(design,[1,2,3,4,5],4.,[tilt,0.,0.,0.,0.])
        p=np.array(fit['parameters'])
        values = columns[:,:,0].real-p[0]*columns[:,:,0].imag
        values += p[1]*columns[:,:,1].real-p[2]*columns[:,:,1].imag
        values += p[3]*columns[:,:,2].real-p[4]*columns[:,:,2].imag
        cost=float(np.maximum(-values.sum(axis=1),0).sum())
        assert abs(cost-fit['rescaledCost']) < 1e-6
        assert cost <= old_cost+1e-6
        null_error=float(np.max(np.abs(channels[ih].sum(axis=0)[1:])))
        assert null_error < 1e-6
        costs=np.maximum(-values,0).sum(axis=0)
        e=energy[ih].real
        total_energy=float(e.sum())
        component_energy=float(np.trace(e))
        positive_adverse_overlap=float(costs.sum()-cost)
        assert positive_adverse_overlap > -1e-7
        cases.append(dict(height=height,periods=len(columns),
            rescaledJoinedCost=cost,
            rescaledOldTiltCost=old_cost,
            globalParameters=p.tolist(),
            diagnosticSeparateChannelCosts=dict(zip(['early','late','crossing'],costs.tolist())),
            cancellationBeforeClipping=positive_adverse_overlap,
            diagnosticChannelSignedTotals=dict(zip(['early','late','crossing'],values.sum(axis=0).tolist())),
            postHingeDiagnosticComplexEnergy=total_energy,
            postHingeDiagnosticChannelDiagonalEnergy=component_energy,
            postHingeDiagnosticCrossChannelEnergy=total_energy-component_energy,
            postHingeDiagnosticEnergyMatrix=e.tolist(),
            channelsFirstThenClipped=False,
            earlyChannelActiveBaseContributionZero=bool(abs(channels[ih,0,0])<1e-8),
            maximumNullSumError=null_error))
    return dict(N=order,seed=seed,selectedLabels=len(rows),counts=sorted({r['count'] for r in rows}),
                sourceAmplitudeLogScale=logscale,excluded=excluded,
                maximumDecompositionError=max_error,seconds=time.monotonic()-start,cases=cases)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',nargs='+',type=int,default=[256])
    parser.add_argument('--seeds',nargs='+',type=int,default=[317])
    parser.add_argument('--heights',nargs='+',type=float,default=[54.,65.,100.])
    parser.add_argument('--output',type=Path,default=Path('.lake/riesz-crossing-coherence/report.json'))
    args=parser.parse_args()
    if any(order not in (256,640,1536) for order in args.orders):
        parser.error('supported native exploratory orders are 256, 640, 1536')
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error('heights must be finite and at least 54')
    mp.mp.dps=100
    report=dict(scope='all subsets of constructed prime universes, not full native core',
                originalMasksAndAllocationRetained=True,allCountsAndPeriodsJoined=True,
                commonAmplitudeRescaling=True,largeCutoffsLogInterpolated=True,
                energyIsLogInterpolatedDiagnostic=True,
                complexNullFitRecomputedGlobally=True,
                intervalArithmetic=False,primeCertificates=False,
                floorCertified=False,cofinalRateCertified=False,cases=[])
    for order in args.orders:
        for seed in args.seeds:
            batch=experiment(order,seed,args.heights)
            report['cases'].append(batch)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps(report,indent=2)+'\n')
            print(json.dumps(batch),flush=True)


if __name__ == '__main__':
    main()
