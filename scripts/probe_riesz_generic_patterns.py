#!/usr/bin/env python3
"""Unlabelled signed Riesz profiles and controlled structure interventions.

Optional research, never a build/CI task. Arbitrary positive log vectors
are accepted. The generic exact-moment backend covers every subset, keeps
both parities, and encloses ambiguous crossings. Discovery is based on
response shape and input features, not on old theorem-family names. Paid
count, few-bin and owner regions are rejected BEFORE subset calculation.
The explicit --include-paid-diagnostics flag includes them for regression
only; paid diagnostics never enter discovery.

Generated inputs are continuous-log MODELS, not a prime population. Exact
rational subset enclosures concern the finite supplied numbers. Logarithms,
allocation CDFs and phases are not interval-certified. No floor credit,
native prime matching, density, or cofinal estimate is claimed.
"""

import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import random
import subprocess
import time

import mpmath as mp
import numpy as np
from scipy.cluster.hierarchy import fcluster,linkage
from scipy.stats import binom,spearmanr

from riesz_subset_moments import SubsetMoments,binary_fraction,self_test


def finite_number(x):
    return mp.mpf(x.numerator)/x.denominator if isinstance(x,Fraction) else mp.mpf(x)


def export_bound(bound,scale=1):
    a,b = bound['lower']*scale,bound['upper']*scale
    sign = 1 if a > 0 else -1 if b < 0 else 0 if a == b == 0 else None
    return dict(lower=str(a),upper=str(b),exact=a == b,sign=sign,
                midpoint=float(finite_number((a+b)/2)),
                width=float(finite_number(b-a)),
                representedSubsets=str(bound['representedSubsets']),
                crossingStates=bound['crossingStates'],
                crossingSubsets=str(bound['crossingSubsets']),
                signedRecurrenceAudit=bound['signedRecurrenceAudit'],
                exactFiniteInputEnclosure=True)


def native_parameters(j,radius):
    if j < 0:
        raise ValueError('native index must be nonnegative')
    N = 8*(j+4)*2**(j+3)
    mp.mp.dps = max(110,len(str(N))+60)
    u = mp.mpf(str(radius))
    if radius == .50005:
        u = mp.mpf(10001)/20000
    elif radius == .500025:
        u = mp.mpf(20001)/40000
    elif radius == .5:
        u = mp.mpf(1)/2
    else:
        raise ValueError('retain one of the three original rational radii')
    # L_actual=L_lower+eta with 0<eta<=4(N+1)u^N. This separate
    # error is kept even when adding eta would round back to L_lower.
    length = -2*N*mp.log(u)-2*mp.log(N+1)
    error_log = mp.log(4*(N+1))+N*mp.log(u)
    tilt = 1/(-2*mp.log(u))
    rate = (2-2*tilt)*mp.log(u)-mp.log(tilt)
    log_trial = min(-N*rate/(2*(tilt+mp.mpf('2.5'))),-N*mp.log(u)-mp.log(N+1))
    # Never materialise the enormous moving order range. Its two exact
    # endpoints alone suffice for the same literal contiguous CDF sum.
    # Literal unpaid_orders inequalities, solved with INTEGER arithmetic.
    lo = max((N+1)//8+1,N//5+2)
    hi = min((7*(N+1)+7)//8-1,(15*N+64)//32,13*N//32)
    return dict(j=j,N=N,u=u,length=length,lengthErrorLog=error_log,
                originalCountCeiling=2**(j+3),currentCountCeiling=2**(j+3)//864+1,
                orderLower=lo,orderUpper=hi,logTrial=log_trial)


def actual_bins(logs,N):
    head = max(mp.mpf(5000),32*mp.log(N+1))
    answer = set()
    for x in logs:
        if x <= head:
            continue
        i = int(mp.ceil(mp.log(x/head,2)))-1
        assert head*2**i < x <= head*2**(i+1)
        answer.add(i)
    return sorted(answer),int(mp.floor(mp.log(N+1)/16))


def allocation_enclosure(pars,logs,total):
    """Keep the old allocation; use a Chernoff bound at huge orders.

    In the selected unallocated owner range all cofactor shares exceed
    13/32. This exact MODEL condition is checked, not silently assumed.
    At manageable orders the original binomial CDF is also evaluated.
    """
    N,L = pars['N'],pars['length']
    q0 = mp.mpf(13)/32
    eligible = [x for x in logs if 2*mp.log(N) < x < L]
    qs = [1-x/total for x in eligible]
    if any(q <= q0 for q in qs):
        return dict(lower=0.,upper=1.,boundLog10='0',method='unresolved retained allocation')
    def entropy(q):
        return q0*mp.log(q0/q)+(1-q0)*mp.log((1-q0)/(1-q))
    terms = [-(N+1)*entropy(q) for q in qs]
    upper_log = mp.log(len(terms))+max(terms) if terms else mp.ninf
    result = dict(lower=0.,upper=0. if upper_log < -750 else float(mp.exp(upper_log)),
                  boundLog10=mp.nstr(upper_log/mp.log(10),24),
                  method='all original eligible incidences; binomial lower-tail bound')
    if N <= 100000:
        values = [float(binom.cdf(pars['orderUpper'],N+1,float(q))-
                        binom.cdf(pars['orderLower']-1,N+1,float(q))) for q in qs]
        result['evaluatedOriginalAllocation'] = math.fsum(values)
    return result


def input_features(xs):
    shares = np.asarray([float(x/mp.fsum(xs)) for x in xs])
    small = np.sort(shares)
    pair_sums = np.sort([a+b for i,a in enumerate(shares) for b in shares[i+1:]])
    return dict(cofactorCount=len(xs),entropy=float(-np.sum(shares*np.log(shares))),
                shareSquareMass=float(np.dot(shares,shares)),
                largestCofactorRelativeShare=float(max(shares)),
                leastCofactorRelativeShare=float(min(shares)),
                logShareSpread=float(np.log2(max(shares)/min(shares))),
                twoSmallestShare=float(sum(small[:2])),
                smallestPairSumGap=float(np.min(np.diff(pair_sums))) if len(pair_sums)>1 else 0.)


def unpaid_scope(pars,logs,owner,total,bins,cap,mask):
    """Cheap support gate, not a new theorem or a complete floor cover.

    Count means WHOLE label count, including the owner. Few-bin membership
    uses the literal bin head/half-open bins, not a rounded spread proxy.
    The effective eventual-count regime is kept separate from the geometry.
    """
    count = len(logs)+1
    conditions = dict(fixedCountUnpaid=count >= 56,
                      denseCountUnpaid=count < 5*mp.log(pars['N']+1)+2,
                      fewBinUnpaid=len(bins)>cap,
                      sharpOwnerUnpaid=owner < mp.mpf(60069)/100000*total)
    reasons = [key for key,passes in conditions.items() if not passes]
    reasons += ['support:'+key for key,passes in mask.items() if not passes]
    return dict(conditions={key:bool(value) for key,value in conditions.items()},
                eligible=not reasons,skipReasons=reasons,
                completeNativeComplementCover=False)


def record_context(record):
    """All support tests precede the factorially large subset calculation."""
    pars = native_parameters(int(record['j']),float(record.get('radius',.50005)))
    N,L = pars['N'],pars['length']
    total = mp.mpf(str(record.get('totalLogOverN',2)))*N
    xs = [mp.mpf(x) for x in record['cofactorUnits']]
    if not xs or any(not mp.isfinite(x) or x<=0 for x in xs):
        raise ValueError('cofactorUnits must be finite and strictly positive')
    # Fixed binary owner/cofactor shares retain the SAME total logarithm
    # and therefore the SAME radial kernel and complex phase in every
    # intervention. No arithmetic prime existence is inferred.
    owner_share = mp.mpf(str(record['ownerShare'])) if 'ownerShare' in record else mp.mpf(143)/256
    if not mp.isfinite(total) or total<=0 or not 0<owner_share<1:
        raise ValueError('positive finite total logarithm and owner share in (0,1) required')
    A = (1-owner_share)*total
    unit = A/mp.fsum(xs)
    logs = [unit*x for x in xs]
    owner = owner_share*total
    bins,cap = actual_bins(logs,N)
    rough = [x for x in [owner,*logs] if 2*mp.log(N) < x]
    mask = dict(coreWindow=mp.mpf('1.95')*N < total <= mp.mpf('2.03')*N,
                squarefreeDistinctLogModel=len(set(xs)) == len(xs),
                canonicalLargestOwner=owner > max(logs),
                nonDominant=owner < mp.mpf('0.65')*total,
                allPhysicalUpper=max([owner,*logs]) < L,
                allPhysicalRough=min([owner,*logs]) > 2*mp.log(N),
                roughCountAtLeastTwo=len(rough) >= 2,
                smoothMassBelowLength=mp.fsum(x for x in [owner,*logs] if x not in rough) < L,
                narrowWindow=L < total < 2*L,
                cofactorAboveTrial=min(total-x for x in [owner,*logs]) > pars['logTrial'],
                originalCount=3 <= len(xs)+1 < pars['originalCountCeiling'],
                reducedNativeCount=3 <= len(xs)+1 < pars['currentCountCeiling'])
    scope = unpaid_scope(pars,logs,owner,total,bins,cap,mask)
    return pars,xs,logs,owner,total,unit,bins,cap,mask,scope


def scan_record(record,grid,profile_ratios,heights,include_paid_diagnostics=False,recursion_budget=32768):
    pars,xs,logs,owner,total,unit,bins,cap,mask,scope = record_context(record)
    N,L = pars['N'],pars['length']
    owner_share = owner/total
    result = dict(id=record['id'],parent=record.get('parent'),
                  intervention=record.get('intervention','anchor'),
                  seed=record.get('seed'),j=pars['j'],N=str(N),radius=float(pars['u']),
                  totalLogOverN=float(total/N),ownerShare=float(owner_share),
                  cofactorUnits=[str(x) for x in xs],
                  literalCofactorBins=bins,literalFewBinCeiling=cap,
                  survivingManyBinModel=len(bins)>cap,
                  eventualCountPaymentRegime=pars['j'] >= 1024,
                  masks={k:bool(v) for k,v in mask.items()},
                  modelCoreAdmissible=all(mask.values()),
                  unpaidScope=scope,unpaidProbeEligible=scope['eligible'],
                  paidDiagnostic=not scope['eligible'] and include_paid_diagnostics,
                  splitFraction=record.get('splitFraction'),
                  splitSelection=record.get('selectionReason'),
                  primePopulation=False,nativeFloorCredit=False)
    if not scope['eligible'] and not include_paid_diagnostics:
        result['probeStatus'] = 'skipped_before_subset_calculation'
        result['subsetCalculationPerformed'] = False
        return result
    result['probeStatus'] = 'probed'
    result['subsetCalculationPerformed'] = True
    profile = SubsetMoments(xs,grid,recursion_budget)
    left,right = (L-owner)/unit,L/unit
    target = profile.two_hinge(left,right)
    coefficient = export_bound(target,binary_fraction(unit/total))
    allocation = allocation_enclosure(pars,[owner,*logs],total)
    parity = profile.parity_features()
    sensitivity = profile.coordinate_sensitivity(left,right)
    samples = []
    shape = []
    for ratio in profile_ratios:
        D = mp.fsum(xs)*mp.mpf(str(ratio))
        bound = export_bound(profile.response(D),Fraction(1)/binary_fraction(mp.fsum(xs)))
        samples.append(dict(cofactorCutoffRatio=ratio,**bound))
        shape.append(bound['midpoint'])
    # Actual L rounding is separately enclosed by the elementary hinge
    # Lipschitz bound, not confused with the DP's finite-input enclosure.
    rounding_log10 = (pars['lengthErrorLog']+(len(xs)+1)*mp.log(2)-mp.log(total))/mp.log(10)
    result.update(inputFeatures=input_features(xs),allocation=allocation,
                  targetTwoHingeOverTotalLog=coefficient,
                  lengthRoundingResponseBoundLog10=mp.nstr(rounding_log10,24),
                  subsetFeatures={k:str(v) if isinstance(v,Fraction) else
                                    str(v) if k=='representedSubsets' else v for k,v in parity.items()},
                  profile=samples,shape=shape+[coefficient['midpoint']],
                  responseShapeIncludesLiteralTwoHingeTarget=True,
                  localSensitivity=sensitivity,
                  fullPhase={str(y):dict(real=mp.nstr(mp.cos(mp.mpf(str(y))*total),24),
                                          imaginary=mp.nstr(-mp.sin(mp.mpf(str(y))*total),24)) for y in heights},
                  densityModelRadialLogKernelOverN=mp.nstr(-mp.mpf('0.5')*total/N+1+mp.log(total/(2*N)),24),
                  literalAtomSourceLogAmplitude=mp.nstr((N+1)*mp.log(pars['u'])+
                      N*mp.log(total)-mp.loggamma(N+1)-mp.mpf('1.5')*total+mp.log(total/L),24))
    return result


def random_vector(count,seed):
    """No named geometry class is supplied to the discovery stage."""
    rng = random.Random(seed)
    logs = [max(1,int(round(2**rng.uniform(0,7)))) for _ in range(count)]
    # Integer knots permit an exact arbitrary-profile regression. Avoid
    # repeated prime logs; distinct continuous logs model distinct primes.
    seen = set()
    for i,x in enumerate(logs):
        while x in seen:
            x += 1
        logs[i] = x; seen.add(x)
    return logs


def generic_unpaid_record(count,seed,j):
    """Seeded share vectors with sufficient possible literal bin coverage.

    At eventual native orders the old seven-octave sampler always lands
    in the PAID few-bin population. Seed one leg per separated log scale,
    then randomize within/between scales. This is a support sampler, not
    a named response/cancellation family and not a prime construction.
    """
    pars = native_parameters(j,.50005)
    required = int(mp.floor(mp.log(pars['N']+1)/16))+1
    if required <= 5 or count < required:
        xs = random_vector(count,seed)
    else:
        rng = random.Random(seed)
        scales = [mp.mpf(3)*i/2+mp.mpf(str(rng.uniform(-.1,.1)))
                  for i in range(required)]
        scales += [mp.mpf(str(rng.uniform(0,float(scales[-1]))))
                   for _ in range(count-required)]
        xs = [mp.power(2,x) for x in scales]
        rng.shuffle(xs)
    return dict(id=f'input-{count}-{seed}',j=j,seed=seed,
                cofactorUnits=[mp.nstr(x,mp.mp.dps) for x in xs],radius=.50005,
                generation='seeded support coverage; no response labels')


def active_hinge_records(record):
    """Stress the actual surviving hinge, rather than scan known zero gaps.

    Solve for one cofactor log so that a singleton divisor lies just
    BELOW/ABOVE L-log(owner), with the same total logarithm and owner.
    The displacement is half the smallest other log. These are continuous
    boundary models; no literal prime partner or density is asserted.
    """
    pars,xs,_,owner,total,_,_,_,_,_ = record_context(record)
    cofactor = total-owner
    d = (pars['length']-owner)/cofactor
    if not 0<d<1:
        return
    i = xs.index(max(xs))
    others = xs[:i]+xs[i+1:]
    eps = min(others)/2
    for side in (-1,1):
        replacement = (d*mp.fsum(others)-side*eps)/(1-d)
        if replacement<=0:
            continue
        changed = xs[:]; changed[i] = replacement
        yield dict(record,id=record['id']+f'-hinge-{side:+d}',parent=record['id'],
            intervention='singleton divisor crosses actual inner hinge',
            cofactorUnits=[mp.nstr(x,mp.mp.dps) for x in changed],
            hingeDisplacementSign=side,primePartnersNotAsserted=True)


def interventions(record):
    xs = list(map(mp.mpf,record['cofactorUnits']))
    seed = record.get('seed')
    if seed is None:
        seed = int(hashlib.sha256(record['id'].encode()).hexdigest()[:16],16)
    rng = random.Random(seed+781)
    i,j = rng.sample(range(len(xs)),2)
    # Exact fixed-sum dither; this may resolve or expose an uncertain
    # profile. It is not rounded back to the anchor's integer lattice.
    amount = min(xs[i],xs[j])/64
    changed = xs[:]; changed[i] += amount; changed[j] -= amount
    yield dict(record,id=record['id']+'-dither',parent=record['id'],
               intervention='fixed-total redistribution',cofactorUnits=list(map(str,changed)))
    # Count-changing intervention tests cross-count structure while
    # keeping owner, total log, phase and full radial kernel fixed.
    i = max(range(len(xs)),key=xs.__getitem__)
    untouched = set(xs[:i]+xs[i+1:])
    fractions = [mp.mpf(7)/16,mp.mpf(13)/32,mp.mpf(15)/32,mp.mpf(11)/32]
    fraction = next((v for v in fractions if xs[i]*v not in untouched
                     and xs[i]*(1-v) not in untouched and v != mp.mpf('0.5')),
                    mp.mpf(7)/16+mp.mpf(1)/1024)
    split = xs[:i]+[xs[i]*fraction,xs[i]*(1-fraction)]+xs[i+1:]
    yield dict(record,id=record['id']+'-split',parent=record['id'],
               intervention='one share split into two',splitFraction=mp.nstr(fraction,24),
               splitChosenForDistinctnessOnly=True,cofactorUnits=list(map(str,split)))


def discover(rows):
    """Data-driven response motifs with explicit uncertainty gates.

    Correlations propose hypotheses; they do not prove one. Response
    clusters use no generator labels, counts or input-family names.
    An interval that crosses zero cannot become a sign observation.
    """
    selected = [r for r in rows if r['unpaidProbeEligible']]
    ready = [r for r in selected if all(p['exact'] for p in r['profile'])]
    cluster_records = []
    if len(ready) >= 3:
        vectors = np.asarray([r['shape'] for r in ready])
        scales = np.max(np.abs(vectors),axis=1)
        vectors = vectors/np.maximum(scales[:,None],1e-300)
        groups = fcluster(linkage(vectors,method='average',metric='euclidean'),.25,criterion='distance')
        for g in sorted(set(groups)):
            members = [r['id'] for r,k in zip(ready,groups) if k==g]
            cluster_records.append(dict(responseMotif=int(g),members=members,
                                         inputFamilyLabelsUsed=False))
    anchors = {r['id']:r for r in selected if r['parent'] is None}
    contrasts = []
    for r in selected:
        if r['parent'] not in anchors:
            continue
        a = anchors[r['parent']]
        x,y = a['targetTwoHingeOverTotalLog'],r['targetTwoHingeOverTotalLog']
        rigorous_signs = x['sign'] is not None and y['sign'] is not None
        contrasts.append(dict(anchor=a['id'],child=r['id'],intervention=r['intervention'],
            totalLogOwnerAndPhaseHeldFixed=True,
            bothOriginalModelMasksPass=a['modelCoreAdmissible'] and r['modelCoreAdmissible'],
            exactFiniteInputSignsAvailable=rigorous_signs,
            signChanged=bool(x['sign']*y['sign']<0) if rigorous_signs else None,
            signedSumBounds=[str(Fraction(x['lower'])+Fraction(y['lower'])),
                             str(Fraction(x['upper'])+Fraction(y['upper']))],
            nativeDistinctPrimeMatchingProved=False))
    correlations = []
    targets = [r for r in selected if r['targetTwoHingeOverTotalLog']['exact']]
    if len(targets) >= 6:
        y = np.asarray([r['targetTwoHingeOverTotalLog']['midpoint'] for r in targets])
        for key in targets[0]['inputFeatures']:
            x = np.asarray([r['inputFeatures'][key] for r in targets],dtype=float)
            if len(set(x)) < 3 or len(set(y)) < 3:
                continue
            rho = float(spearmanr(x,y).statistic)
            correlations.append(dict(feature=key,signedResponseRankCorrelation=rho,
                testedFiniteProfiles=len(targets),candidateOnly=True,
                causalOrCofinalProof=False))
        correlations.sort(key=lambda z:abs(z['signedResponseRankCorrelation']),reverse=True)
    return dict(responseMotifs=cluster_records,controlledContrasts=contrasts,
                candidateFeatureRelationships=correlations,
                ambiguousProfilesNotRanked=sum(not all(p['exact'] for p in r['profile']) for r in selected),
                diagnosticModelsExcludedFromDiscovery=len(rows)-len(selected),
                noStatisticalOrNativeCertificate=True)


def scope_self_test():
    """Reject paid examples BEFORE any call to the subset backend."""
    anchor = dict(id='scope-anchor',j=64,seed=317,
                  cofactorUnits=random_vector(55,317),radius=.50005)
    assert record_context(anchor)[-1]['eligible']
    examples = [dict(anchor,id='paid-count',cofactorUnits=random_vector(20,317)),
                dict(anchor,id='paid-few-bin',cofactorUnits=list(range(55,110))),
                dict(anchor,id='paid-owner',ownerShare='0.61'),
                dict(anchor,id='paid-dense',cofactorUnits=random_vector(300,317))]
    expected = ['fixedCountUnpaid','fewBinUnpaid','sharpOwnerUnpaid','denseCountUnpaid']
    for record,reason in zip(examples,expected):
        row = scan_record(record,1,[],[])
        assert row['probeStatus'] == 'skipped_before_subset_calculation'
        assert not row['subsetCalculationPerformed']
        assert reason in row['unpaidScope']['skipReasons']
        assert 'subsetFeatures' not in row and 'targetTwoHingeOverTotalLog' not in row
    return dict(passed=True,paidScopeRejectionsBeforeSubsetCalculation=len(examples),
                literalBinHeadAndWholeCountUsed=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs-json',type=Path,help='arbitrary records with id,j,cofactorUnits[,radius,seed]')
    parser.add_argument('--counts',type=int,nargs='+',default=[55,56,63,96],help='COFACTOR counts; whole count adds one owner')
    parser.add_argument('--seeds',type=int,nargs='+',default=[317,919])
    parser.add_argument('--native-j',type=int,default=1024,
                        help='default is the proved eventual native count-payment regime')
    parser.add_argument('--grid',type=int,default=16384)
    parser.add_argument('--recursion-budget',type=int,default=32768,
                        help='exact signed finite-difference states per ambiguous hinge; exhaustion stays unresolved')
    parser.add_argument('--heights',type=float,nargs='+',default=[54,65,100])
    parser.add_argument('--interventions',action='store_true')
    parser.add_argument('--active-hinges',action='store_true',
                        help='stress both sides of the actual inner hinge in surviving model geometries')
    parser.add_argument('--include-paid-diagnostics',action='store_true',
                        help='explicitly probe paid/out-of-support models, excluded from discovery')
    parser.add_argument('--self-test',action='store_true')
    parser.add_argument('--output',type=Path,default=Path('.lake/riesz-generic-pattern/scan.json'))
    args = parser.parse_args()
    if args.native_j < 0 or args.grid < 1 or args.recursion_budget < 0 or any(c<2 for c in args.counts):
        parser.error('nonnegative native j, positive grid and cofactor counts>=2 required')
    if any(not math.isfinite(y) or y<54 for y in args.heights):
        parser.error('fixed finite heights>=54 required')
    mp.mp.dps = 110
    validation = dict(subsets=self_test(),unpaidScope=scope_self_test())
    if args.self_test:
        print(json.dumps(validation)); return
    if args.inputs_json:
        records = json.loads(args.inputs_json.read_text())
        if not isinstance(records,list):
            parser.error('inputs-json must contain a list')
    else:
        records = [generic_unpaid_record(c,seed,args.native_j)
                   for c in args.counts for seed in args.seeds]
    if len({r['id'] for r in records}) != len(records):
        parser.error('input identifiers must be unique')
    if args.interventions:
        records += [z for r in records[:] for z in interventions(r)]
    if args.active_hinges:
        records += [z for r in records[:] if not r.get('parent') for z in active_hinge_records(r)]
    started = time.monotonic()
    report = dict(schemaVersion=1,head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        scope=dict(optionalOutsideBuildsCI=True,unlabelledGenericInputs=True,
                   unpaidOnlyDefault=True,paidDiagnosticsRequested=args.include_paid_diagnostics,
                   defaultWholeCountMinimum=56,defaultNativeIndex=1024,
                   defaultOwnerShareUpper='60069/100000',
                   defaultFewBinMaskUsesLiteralDefinition=True,
                   exactFiniteInputSubsetEnclosures=True,realLogsIntervalCertified=False,
                   actualPrimePopulation=False,allMasksRetainedAsExplicitTests=True,
                   nativeFloorBudget=False,cofinalEstimate=False),
        sources={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                 [Path(__file__),Path(__file__).with_name('riesz_subset_moments.py')]},
        validation=validation,scanComplete=False,rows=[],skipped=[])
    args.output.parent.mkdir(parents=True,exist_ok=True)
    for i,record in enumerate(records):
        row = scan_record(record,args.grid,[.05,.15,.25,.35,.45,.5,.55,.65,.75,.85,.95],args.heights,
                          args.include_paid_diagnostics,args.recursion_budget)
        if not row['subsetCalculationPerformed']:
            report['skipped'].append(row)
            args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
            print(json.dumps(dict(done=i+1,total=len(records),id=row['id'],
                skippedBeforeSubsetCalculation=True,reasons=row['unpaidScope']['skipReasons'])),flush=True)
            continue
        report['rows'].append(row)
        args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
        print(json.dumps(dict(done=i+1,total=len(records),id=row['id'],
            subsets=row['subsetFeatures']['representedSubsets'],states=row['subsetFeatures']['stateCount'],
            exactTarget=row['targetTwoHingeOverTotalLog']['exact'],
            manyBinModel=row['survivingManyBinModel'],
            allModelMasks=row['modelCoreAdmissible'])),flush=True)
    report['discovery'] = discover(report['rows'])
    report['skipReasonCounts'] = dict(sorted((key,sum(key in r['unpaidScope']['skipReasons']
                                                    for r in report['skipped']))
        for key in {s for r in report['skipped'] for s in r['unpaidScope']['skipReasons']}))
    report['seconds'] = time.monotonic()-started
    report['scanComplete'] = True
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    print(json.dumps(dict(output=str(args.output),seconds=report['seconds'],
        responseMotifs=len(report['discovery']['responseMotifs']),
        skippedBeforeSubsetCalculation=len(report['skipped']),
        signChangingContrasts=sum(x['signChanged'] is True and x['bothOriginalModelMasksPass']
                                 for x in report['discovery']['controlledContrasts']),
        unrankedAmbiguousProfiles=report['discovery']['ambiguousProfilesNotRanked'])),flush=True)


if __name__ == '__main__':
    main()
