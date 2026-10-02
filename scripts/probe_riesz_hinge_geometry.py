#!/usr/bin/env python3
"""Unpaid-only high-dimensional signed crossing geometry detector.

Accepts arbitrary native log-model records and discovers signed incidence
correlations, exact local gradients and unsigned hinge walls. The input
has no named cancellation-family labels. Structured active-hinge probes
are additional stress tests, not the discovery rule. All unresolved work
remains null and unranked. No native prime inventory/floor is certified.
"""

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
import mpmath as mp

from probe_riesz_generic_patterns import (
    active_hinge_records, allocation_enclosure, finite_number,
    generic_unpaid_record, record_context,
)
from probe_riesz_clipped_insertions import inner_model, scope_context, text_number
from riesz_subset_moments import binary_fraction
from riesz_hinge_geometry import HingeGeometry, self_test


def scan(pars, owner, logs, ident, state_budget, moment_budget, kind):
    total, context = scope_context(pars,owner,logs)
    result = dict(id=ident, modelConstruction=kind, nativeIndex=pars['j'],
                  original=context, primePopulation=False, nativeFloorCredit=False)
    if not context['unpaidScope']['eligible']:
        result['status'] = 'skipped_paid_before_geometry_work'
        return result
    result['original']['subsetCalculationPerformed'] = True
    owner_exact, length = map(binary_fraction,(owner,pars['length']))
    xs = list(map(binary_fraction,logs))
    T = owner_exact+sum(xs)
    left,right = length-owner_exact,length
    detector = HingeGeometry(xs,state_budget,moment_budget)
    geometry = detector.two_hinge(left,right)
    result.update(status='complete_geometry' if geometry['complete'] else 'unresolved_unranked',
                  geometry=geometry, inputLogs=[str(x) for x in xs],
                  ownerLog=str(owner_exact), literalLengthLower=str(length),
                  lengthRoundingErrorLog=text_number(pars['lengthErrorLog']),
                  fullPhase=[dict(height=y, real=text_number(mp.cos(y*finite_number(T))),
                                  imaginary=text_number(-mp.sin(y*finite_number(T)))) for y in (54,65,100)],
                  allocation=allocation_enclosure(pars,[owner,*logs],total),
                  factorialAndPhaseNotReplacedByDensity=True,
                  geometryIncludesAllocationDerivatives=False)
    if not geometry['complete']:
        return result
    result['coefficientOverTotalLog'] = text_number(Fraction(geometry['coefficient'])/T)
    gap = geometry.get('exactUnsignedTwoHingeGap')
    directions = []
    if gap is not None and Fraction(gap)>0:
        for group in geometry['fixedTotalGradientGroups']:
            if len(group['legs']) < 2:
                continue
            i,j = group['legs'][:2]
            step = min(Fraction(gap)/8,xs[i]/16,xs[j]/16)
            changed = xs[:];changed[i]+=step;changed[j]-=step
            assert sum(changed) == sum(xs) and 2*step < Fraction(gap)
            _, context2 = scope_context(pars,owner,list(map(finite_number,changed)))
            row = dict(legs=[i,j], exactLogShift=str(step), gradient=str(group['gradient']),
                       originalPhaseAndRadialKernelHeldExactlyFixed=True,
                       partnerContext=context2, nativePrimesNotConstructed=True)
            if not context2['unpaidScope']['eligible']:
                row['status']='skipped_partner_before_geometry_work'
            else:
                paired = HingeGeometry(changed,state_budget,moment_budget).two_hinge(left,right)
                row['status']='verified_finite_input_flat_direction' if paired['complete'] else 'unresolved_partner'
                if paired['complete']:
                    assert paired['coefficient'] == geometry['coefficient']
                    row.update(exactCoefficientUnchanged=True,
                               allocation=allocation_enclosure(pars,[owner,*map(finite_number,changed)],finite_number(T)),
                               allocatedAtomInvariant=False, globalTransportCapacityCertified=False)
            directions.append(row)
            if len(directions)>=3:
                break
    result['independentFixedTotalDirectionTests']=directions
    result['geometryOnlyNoNativeBudgetCredit']=True
    return result


def discover(rows):
    complete=[r for r in rows if r['status']=='complete_geometry']
    # Rank/gradient motifs use no model-construction or prior family name.
    signatures=Counter((r['geometry']['interactionRank'],
                        len(r['geometry']['fixedTotalGradientGroups']),
                        sum(any(Fraction(x) for x in wall['first'])
                            for wall in r['geometry']['hingeWall'])) for r in complete)
    return dict(
        exactCorrelationMotifs=[dict(interactionRank=rank,gradientGroups=groups,
                                    activeSignedHingeWalls=walls,profiles=n)
                               for (rank,groups,walls),n in sorted(signatures.items())],
        incompleteProfilesExcluded=True,
        rankIsSignedIncidenceNotCurvature=True,
        noInferenceOfPrimeDensityOrPopulationCancellation=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inputs-json',type=Path,
                   help='arbitrary records with id,j,cofactorUnits[,radius,seed,ownerShare]')
    p.add_argument('--native-j',type=int,default=1024)
    p.add_argument('--counts',type=int,nargs='+',default=[20,55,64,96,300,4000])
    p.add_argument('--seeds',type=int,nargs='+',default=[317,919])
    p.add_argument('--state-budget',type=int,default=8192)
    p.add_argument('--moment-budget',type=int,default=300000)
    p.add_argument('--active-hinges',action='store_true')
    p.add_argument('--inner-regressions',action='store_true')
    p.add_argument('--self-test',action='store_true')
    p.add_argument('--output',type=Path,default=Path('.lake/riesz-hinge-geometry/scan.json'))
    args=p.parse_args()
    if args.native_j<0 or args.state_budget<0 or args.moment_budget<0 or any(c<2 for c in args.counts):
        p.error('nonnegative native index/budgets and cofactor counts>=2 required')
    records=json.loads(args.inputs_json.read_text()) if args.inputs_json else [
        generic_unpaid_record(count,seed,args.native_j) for count in args.counts for seed in args.seeds]
    if args.active_hinges:
        records += [child for record in records[:] for child in active_hinge_records(record)]
    args.output.parent.mkdir(parents=True,exist_ok=True)
    report=dict(schemaVersion=1,head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
                scope=dict(optionalOutsideBuildsCI=True,unpaidScopeCheckedBeforeGeometry=True,
                           fullSignedMomentsAndAllUnsignedKnotsRetained=True,
                           finiteInputTensorExactNotRealLogIntervalCertified=True,
                           nativePopulationCover=False, nativeFloorCredit=False),
                selfTest=self_test() if args.self_test else None,rows=[],scanComplete=False)
    started=time.monotonic()
    for record in records:
        pars,_,logs,owner,*_=record_context(record)
        row=scan(pars,owner,logs,record['id'],args.state_budget,args.moment_budget,
                 record.get('intervention','unlabelled input'))
        report['rows'].append(row)
        args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
        print(json.dumps(dict(id=row['id'],status=row['status'],
                              rank=row.get('geometry',{}).get('interactionRank'))),flush=True)
    if args.inner_regressions:
        for count in args.counts:
            for tau in (Fraction(1,4),Fraction(3,4),Fraction(99,100)):
                pars,owner,q,base=inner_model(count,317,args.native_j,tau)
                row=scan(pars,owner,[q,*base],f'active-{count}-{tau}',
                         args.state_budget,args.moment_budget,'active crossing stress test')
                report['rows'].append(row)
                args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
                print(json.dumps(dict(id=row['id'],status=row['status'],
                                      rank=row.get('geometry',{}).get('interactionRank'))),flush=True)
    sources={}
    for file in (Path(__file__),Path('scripts/riesz_hinge_geometry.py'),
                 Path('scripts/probe_riesz_generic_patterns.py'),Path('scripts/probe_riesz_clipped_insertions.py'),
                 Path('scripts/riesz_subset_moments.py')):
        data=file.read_bytes();sha=hashlib.sha256(data).hexdigest()
        snapshot=args.output.parent/f'source-{sha}{file.suffix}';snapshot.write_bytes(data)
        sources[str(file)]=dict(sha256=sha,snapshot=str(snapshot))
    report.update(sources=sources,scanComplete=True,seconds=time.monotonic()-started,
                  discovery=discover(report['rows']))
    counts=Counter(r['status'] for r in report['rows'])
    report['summary']=dict(statusCounts=dict(counts),
                           verifiedFiniteInputDirections=sum(
                               x['status']=='verified_finite_input_flat_direction'
                               for r in report['rows'] for x in r.get('independentFixedTotalDirectionTests',[])),
                           nativeFloorCredit=False)
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    print(json.dumps(report['summary'],indent=2),flush=True)


if __name__=='__main__':
    main()
