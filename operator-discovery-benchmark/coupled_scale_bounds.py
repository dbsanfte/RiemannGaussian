"""Discover sparse compensated-energy recurrences, retaining signed crosses.

Proposal scores use complete block Grams. Candidate programs and constants
are fixed using training blocks before the other partitions are evaluated.
Every recurrence is an OPEN arithmetic lemma until separately proved.
"""
from fractions import Fraction as Q
import math
import time

import numpy as np

import adaptive_rational_exponents as A

SCALES = tuple(2**k for k in range(18))
PARTITIONS = dict(head=list(range(5)), train=list(range(5, 11)),
                  validation=list(range(11, 15)), final=list(range(15, 17)))
COEFFICIENTS = ('-2', '-1', '-1/2', '1/2', '1', '2')
RECURRENCE_CONSTANTS = ('0', '1/4096', '1/1024', '1/256', '1/64',
                        '1/16', '1/4', '1', '4')
DIVISORS = (1, 2, 3)


def rational(text):
    if type(text) is not str:
        raise ValueError('canonical exact rational text')
    q = Q(text)
    if str(q) != text:
        raise ValueError('canonical exact rational text')
    return q


def exponent_plan():
    # A fresh offset stream is a new construction, not a rerun of036 twists.
    # Only a finite search budget, not a semantic denominator restriction.
    return A.next_batch(lower='0', upper='1', max_candidates=16,
                        work_budget=100000, requested=('1/257',))


def helper_primitives(basecert):
    result = []
    for frontier in basecert['frontier_bounds']:
        r = None if frontier['r'] is None else rational(frontier['r'])
        J = rational(frontier['unit_ceiling'])
        D = rational(frontier['coefficient_ceiling'])
        if r is None:
            a, K = Q(0), J
        elif 0 <= r < 1:
            a, K = 1-r, J+D/(1-r)
        elif r > 1:
            a, K = Q(0), J+D*(1+1/(r-1))
        else:
            raise ValueError('logarithmic helper requires its own paid rule')
        ceiling = -(-a.numerator//a.denominator)
        result.append(dict(state=frontier['state'], minimum_gamma=str(max(Q(0), a-Q(1,2))),
                           prefix_constant=str(K), prefix_power=str(a),
                           energy_constant=str(K*K*2**(2*ceiling))))
    return result


def dictionary(basecert, features, offsets):
    primitives = helper_primitives(basecert)
    bounds = {p['state']: p for p in primitives}
    if len(offsets) != len(set(offsets)):
        raise ValueError('distinct exponent offsets')
    result = []
    for feature_index, feature in enumerate(features, 1):
        p = bounds[feature['state']]
        for offset in offsets:
            offset = rational(offset)
            if offset < 0:
                raise ValueError('nonnegative paid-helper exponent offset')
            gamma = Q(p['minimum_gamma']) + offset
            for coefficient in COEFFICIENTS:
                c = Q(coefficient)
                term = dict(state=feature['state'], divisor=feature['divisor'],
                            exponent=str(gamma), coefficient=coefficient)
                result.append(dict(term=term, feature=feature_index,
                    cost=float(c*c*Q(p['energy_constant'])),
                    cost_exact=str(c*c*Q(p['energy_constant'])),
                    key=(feature['state'],feature['divisor'],str(gamma)),
                    extended_fractional=gamma.denominator not in (1,2,3,6)))
    return primitives, result


def _metrics(EG, EH, target, D, partitions=PARTITIONS):
    """Finite proposal diagnostics; no clipping of signed recurrence defects."""
    EG, EH = np.atleast_2d(EG), np.atleast_2d(EH)
    if (not np.isfinite(EG).all() or not np.isfinite(EH).all()
            or not np.isfinite(D).all() or np.any(D <= 0)):
        raise ValueError('finite energies and positive independently paid forcing')
    ratios = np.diff(EG,axis=1)/D
    train = partitions['train']
    required = np.maximum(0, np.max(ratios[:, train], axis=1))
    constants = np.array([float(Q(c)) for c in RECURRENCE_CONSTANTS])
    C_index = np.searchsorted(constants, required, side='left')
    # A larger helper can make finite increments look good just by decaying.
    # Keep such proposals as negative controls, not primary discoveries.
    padding = np.max(EH[:, train]/np.maximum(target[train],1e-300),axis=1)
    return dict(ratios=ratios,required=required,C_index=C_index,padding=padding)


def _rank(C_index, terms, cost, required):
    # Uniform growth class (C=0 vs positive), then simplicity/recovery cost,
    # then the finer finite constant. Nothing in this tuple proves a bound.
    return (int(C_index)>0, int(C_index)>=len(RECURRENCE_CONSTANTS),
            len(terms), float(cost), int(C_index), float(required), tuple(terms))


def search(basecert, evidence, plan=None, *, operation_cap=900_000_000,
           seconds=900):
    started = time.monotonic()
    if plan is None:
        plan = exponent_plan()
    blocks = evidence['blocks']
    if [b['X'] for b in blocks] != list(SCALES):
        raise ValueError('frozen complete block grid')
    features = evidence['features']
    expected = [dict(state=i,divisor=d) for i in range(len(basecert['states'])) for d in DIVISORS]
    if features != expected:
        raise ValueError('full declared prime-profile/dilation basis')
    primitives, terms = dictionary(basecert,features,plan['candidates'])
    gram = np.asarray([b['gram'] for b in blocks], dtype=float)
    dimension = 1+len(features)
    if (gram.shape != (len(SCALES),dimension,dimension)
            or not np.isfinite(gram).all() or not np.allclose(gram,gram.transpose(0,2,1),rtol=1e-13,atol=1e-13)):
        raise ValueError('finite complete symmetric Gram matrices')
    target = gram[:,0,0]
    D = np.array([b['D'] for b in blocks[:-1]],dtype=float)
    if np.any(target <= 0):
        raise ValueError('positive full-source energies for padding comparison')
    scales = np.asarray(SCALES,dtype=float)
    indices = np.array([t['feature'] for t in terms],dtype=int)
    factors = np.array([float(Q(t['term']['coefficient']))*scales**(-float(Q(t['term']['exponent'])))
                        for t in terms])
    helper = np.array([f*f*gram[:,j,j] for f,j in zip(factors,indices)])
    linear = np.array([2*f*gram[:,0,j] for f,j in zip(factors,indices)])
    baseline_metrics = _metrics(target,np.zeros_like(target),target,D)
    baseline_index = int(baseline_metrics['C_index'][0])
    baseC = RECURRENCE_CONSTANTS[min(baseline_index,len(RECURRENCE_CONSTANTS)-1)]
    baseline = dict(id='priced_baseline',program=[],recurrence_C=baseC)
    queues = {key: [] for key in ('overall','mixed_divisor','mixed_state','fractional','padding_control')}
    count = 0; pair_count = 0; operations = 0
    counts = dict(training_fits=0,zero_forcing_training_fits=0,nonpadding=0,
                  padded_training_fits=0,smaller_training_C_than_baseline=0)
    seen_eligible = {key:0 for key in queues}
    seen_best_constants = {key:None for key in queues}

    def consider(program_indices, H, G):
        nonlocal count, operations
        m = _metrics(G,H,target,D)
        batch = len(program_indices)
        count += batch;operations += batch*len(SCALES)*55
        if operations > operation_cap or time.monotonic()-started > seconds:
            raise RuntimeError('coupled candidate resource budget')
        ci, padding = m['C_index'], m['padding']
        fits = ci < len(RECURRENCE_CONSTANTS)
        counts['training_fits'] += int(np.sum(fits))
        counts['zero_forcing_training_fits'] += int(np.sum(ci==0))
        counts['nonpadding'] += int(np.sum(padding<=1))
        counts['padded_training_fits'] += int(np.sum(fits & (padding>1)))
        counts['smaller_training_C_than_baseline'] += int(np.sum(fits & (padding<=1) & (ci<baseline_index)))
        # Python work is only for the few rank minima in each batch/stratum.
        costs = np.array([len(ids)*sum(terms[j]['cost'] for j in ids) for ids in program_indices])
        masks = dict(overall=padding<=1, padding_control=padding>1,
            mixed_divisor=np.array([len({terms[j]['term']['divisor'] for j in ids})>1 for ids in program_indices]) & (padding<=1),
            mixed_state=np.array([len({terms[j]['term']['state'] for j in ids})>1 for ids in program_indices]) & (padding<=1),
            fractional=np.array([any(terms[j]['extended_fractional'] for j in ids) for ids in program_indices]) & (padding<=1))
        for name,mask in masks.items():
            available = np.flatnonzero(mask & fits)
            seen_eligible[name] += len(available)
            if not len(available):
                continue
            bestC = int(np.min(ci[available]))
            oldC = seen_best_constants[name]
            seen_best_constants[name] = bestC if oldC is None else min(oldC,bestC)
            # Equivalent to _rank up to the final stable program tie break.
            order = np.lexsort((available,m['required'][available],ci[available],costs[available],
                                np.array([len(program_indices[i]) for i in available]),ci[available]>0))[:8]
            for index in available[order]:
                ids = program_indices[index]
                rank = _rank(ci[index],ids,costs[index],m['required'][index])
                queues[name].append((rank,ids))
            queues[name] = sorted(set(queues[name]))[:8]

    consider([(i,) for i in range(len(terms))],helper,target+linear+helper)
    for i in range(len(terms)-1):
        js = np.array([j for j in range(i+1,len(terms)) if terms[i]['key']!=terms[j]['key']],dtype=int)
        if not len(js):
            continue
        H = helper[i]+helper[js]+2*factors[i]*factors[js]*gram[:,indices[i],indices[js]].T
        G = target+linear[i]+linear[js]+H
        ids = [(i,int(j)) for j in js]
        pair_count += len(ids)
        consider(ids,H,G)

    chosen=[];programs=set()
    for name in queues:
        for rank,ids in queues[name]:
            if ids not in programs:
                chosen.append((name,ids));programs.add(ids);break
    # At most five nonempty constructions plus the priced baseline.
    candidates = [baseline]
    selected=[]
    for number,(stratum,ids) in enumerate(chosen,1):
        H = sum((helper[i] for i in ids),np.zeros(len(SCALES)))
        if len(ids)==2:
            i,j=ids
            H += 2*factors[i]*factors[j]*gram[:,indices[i],indices[j]]
        G = target+sum((linear[i] for i in ids),np.zeros(len(SCALES)))+H
        m = _metrics(G,H,target,D)
        ci = int(m['C_index'][0]);C = RECURRENCE_CONSTANTS[ci]
        candidate = dict(id='compensator_%02d'%number,
            program=[terms[i]['term'] for i in ids],recurrence_C=C)
        candidates.append(candidate)
        diagnostics = {}
        for partition,ks in PARTITIONS.items():
            defects = np.diff(G)[ks]-float(Q(C))*D[ks]
            diagnostics[partition] = dict(parent_scales=[SCALES[k] for k in ks],
                violations=int(np.sum(defects>0)),max_defect=float(np.max(defects)),
                required_C=float(max(0,np.max(m['ratios'][0,ks]))))
        selected.append(dict(candidate_id=candidate['id'],stratum=stratum,
            term_indices=list(ids),paid_helper_constant=str(len(ids)*sum((Q(terms[i]['cost_exact']) for i in ids),Q(0))),
            training_helper_to_target_ratio=float(m['padding'][0]),
            padding_dominated=bool(m['padding'][0]>1),
            smaller_training_C_than_baseline=ci<baseline_index,
            same_uniform_growth_class_as_baseline=(ci>0)==(baseline_index>0),
            diagnostics=diagnostics,energies=[dict(X=X,EG=float(g),EH=float(h),EF=float(f),cross_twice=float(g-h-f))
                                           for X,g,h,f in zip(SCALES,G,H,target)]))
    return dict(schema='coupled-scale-bound-proposals-v1',
        source_binding=basecert['source'],state_programs=basecert['states'],
        definition='G_X(n)=F(n)+sum c*X^(-gamma)*A_state(floor(n/divisor);ceil(sqrt(2X)))',
        helper_definition='A_i(t;y)=0 if t<1, otherwise h_i(1)+sum_(y<p<=t,p prime)h_i(p)',
        target_is_complete_source=True,prime_profile_is_not_rough_prefix_outside_its_domain=True,
        recurrence='EG(2X)<=EG(X)+C*D(X), every dyadic X>=1',
        forcing='D(X)=X^-1*sum_(1<=n<=4X-1)f(n)^2',
        partitions=PARTITIONS,scale_grid=list(SCALES),exponent_plan=plan,
        coefficients=list(COEFFICIENTS),recurrence_constants=list(RECURRENCE_CONSTANTS),
        helper_primitives=primitives,term_dictionary=terms,candidates=candidates,
        selection=selected,baseline_training_C_index=baseline_index,
        baseline_training_required_C=float(baseline_metrics['required'][0]),
        rank_order='zero forcing first, then term count, paid recovery cost, finite C grid, numeric C, stable program order',
        negative_control='helper energy larger than target on any training block',
        ranking_uses_validation_or_final=False,data_reused_not_novel_holdout=True,
        coverage=dict(single_programs=len(terms),pair_programs=pair_count,total_nonempty=count,
                      pair_same_state_divisor_exponent_excluded=True,all_other_dictionary_pairs_covered=True,
                      eligible_by_stratum=seen_eligible,best_training_C_indices=seen_best_constants,
                      **counts),
        resource=dict(operations=operations,operation_cap=operation_cap,elapsed_seconds=time.monotonic()-started),
        recurrence_proved=False,whole_signed_bound_proved=False,RH_proved=False)
