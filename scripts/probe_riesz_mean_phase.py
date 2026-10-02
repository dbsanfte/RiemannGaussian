#!/usr/bin/env python3
"""Causal phase scan at fixed cofactor-cluster variance.

Original owner/allocation/physical model weights are retained at every shift;
no per-shift amplitude rescaling. This is not prime-density transport or a
native floor certificate. It tests which geometric information fixes signs.
"""

import argparse
from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp

from probe_riesz_crossing_moments import probe, self_test


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--counts',nargs='+',type=int,default=[20,40,55,56,63])
    ap.add_argument('--geometries',nargs='+',default=['owner_rectangle','two_clusters'])
    ap.add_argument('--height',type=float,default=65.)
    ap.add_argument('--output',type=Path,default=Path('.lake/riesz-crossing-moment/mean-phase.json'))
    args=ap.parse_args();mp.mp.dps=100
    rows=[]
    for count in args.counts:
        for geometry in args.geometries:
            # The exact model retains cofactor exp(-A) and eligibility at every
            # shift. A half phase cycle is about 0.07 in total cofactor log.
            for step in range(9):
                shift=(step-4)*math.pi/(4*args.height*.7)
                r=probe(3584,.50005,count,geometry,args.height,317,32,shift)
                r['phaseStep']=step-4
                rows.append(r)
    groups=defaultdict(list)
    for r in rows:groups[(r['geometry'],r['count'])].append(r)
    findings=[]
    for (geometry,count),values in groups.items():
        findings.append(dict(geometry=geometry,count=count,
            positiveShifts=sum(r['modelRealBounds'][0]>0 for r in values),
            negativeShifts=sum(r['modelRealBounds'][1]<0 for r in values),
            minimumSignedOverAbsolute=min(r['modelJoinedReal']/r['centralModelAbsoluteIntegral'] for r in values),
            maximumSignedOverAbsolute=max(r['modelJoinedReal']/r['centralModelAbsoluteIntegral'] for r in values),
            maximumCrossingRemainderRelativeToAbsolute=max(r['remainderRelativeToAbsolute'] for r in values)))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    report=dict(schemaVersion=1,kind='fixed-variance-cofactor-mean-phase-model',
        sourceSha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        helperSha256=hashlib.sha256(Path('scripts/probe_riesz_crossing_moments.py').read_bytes()).hexdigest(),
        selfTest=self_test(),rows=rows,findings=findings,
        internalClusterVarianceHeldFixed=True,originalMovingAllocationAndDensityFactorRetained=True,
        countClassDensityAndPrimeTransportProved=False,nativeFloorCredit=False,
        scope='Fixed-cofactor continuous owner models; not actual prime population estimates.')
    args.output.write_text(json.dumps(report,indent=2))
    print(json.dumps(dict(cases=len(rows),signChanges=sum(r['positiveShifts']>0 and r['negativeShifts']>0 for r in findings),
                         configurations=len(findings),output=str(args.output),nativeFloorCredit=False),indent=2))


if __name__=='__main__':main()
