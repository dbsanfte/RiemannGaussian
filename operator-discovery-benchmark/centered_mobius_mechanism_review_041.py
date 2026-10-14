"""Review saved finite evidence for dependence on a signed cross term.

This performs exact rational interval arithmetic on saved dyadic endpoints.
It neither generates source coefficients nor selects or repairs candidates.
"""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path


ROOT=Path(__file__).resolve().parent
RUN=ROOT/'centered-mobius-bound-results/recovery-001'


def endpoints(enclosure):
    result=[]
    for key in ('lower_dyadic','upper_dyadic'):
        mantissa,exponent=enclosure[key]
        if type(mantissa) is not str or type(exponent) is not int:
            raise ValueError('saved exact dyadic endpoint')
        result.append(Q(int(mantissa))*Q(2)**exponent)
    if result[0]>result[1]:raise ValueError('ordered interval')
    return tuple(result)


def add(a,b):return a[0]+b[0],a[1]+b[1]


def mul(a,b):
    values=[x*y for x in a for y in b]
    return min(values),max(values)


def scale(c,a):return mul((Q(c),Q(c)),a)


def absolute(a):
    return (Q(0) if a[0]<=0<=a[1] else min(abs(a[0]),abs(a[1])),max(abs(a[0]),abs(a[1])))


def sign(a):return 'pass' if a[1]<=0 else 'fail' if a[0]>0 else 'unresolved'


def serialized(a):return dict(lower=str(a[0]),upper=str(a[1]))


def review_row(program,row):
    if (row['id'],row['m'])!=(program['id'],program['m']):raise ValueError('program binding')
    M={key:endpoints(value) for key,value in row['moments'].items()}
    delta=Q(program['delta']);rho=Q(program['rho']);C=Q(program['C']);m=program['m']
    lam2=mul(M['lambda'],M['lambda'])
    parent_coefficient=add(scale(delta,lam2),(-m*rho,-m*rho))
    diagonal=add(add(scale(1+delta,M['E_A']),mul(parent_coefficient,M['E_J'])),scale(-C,M['D']))
    cross=scale(-2*delta,mul(M['lambda'],M['C_JA']))
    expanded=add(diagonal,cross)
    if max(expanded[0],M['Q'][0])>min(expanded[1],M['Q'][1]):
        raise ValueError('saved signed defect inconsistent with independent expansion')
    magnitude=add(diagonal,absolute(cross))
    # Young: 2|lambda*C_JA| <= E_A+lambda^2*E_J.
    # This further comparison uses the two diagonal energies only.
    young=add(add(scale(1+2*delta,M['E_A']),
                  mul(add(scale(2*delta,lam2),(-m*rho,-m*rho)),M['E_J'])),scale(-C,M['D']))
    return dict(id=row['id'],X=row['X'],original_status=row['status'],
        deleted_cross=dict(status=sign(diagonal),defect=serialized(diagonal),
                           scope='algebraic diagnostic only; deletion is not generally an upper bound'),
        absolute_cross=dict(status=sign(magnitude),defect=serialized(magnitude),
                            scope='conservative finite upper bound on the actual signed defect'),
        young_diagonal_bound=dict(status=sign(young),defect=serialized(young)),
        favorable_signed_cross=cross[1]<0,
        signed_cross_required_for_this_finite_pass=(row['status']=='pass' and magnitude[0]>0),
        no_all_scale_inference=True)


def main():
    read=lambda name:json.loads((RUN/name).read_text())
    audit=read('interval_audit.json');report=read('report.json')
    if not audit['complete_coverage_verified'] or report['uniform_covariance_bounds_proved']!=0:
        raise ValueError('completed finite-only input required')
    programs={p['id']:p for p in audit['programs']}
    rows=[review_row(programs[row['id']],row) for row in audit['rows']]
    candidates=[]
    for assessment in report['assessments']:
        selected=[r for r in rows if r['id']==assessment['program']['id']]
        candidates.append(dict(id=assessment['program']['id'],status=assessment['status'],
            samples=len(selected),
            absolute_cross_passes=sum(r['absolute_cross']['status']=='pass' for r in selected),
            young_diagonal_passes=sum(r['young_diagonal_bound']['status']=='pass' for r in selected),
            signed_cross_required_scales=[r['X'] for r in selected if r['signed_cross_required_for_this_finite_pass']],
            mechanism_status=('NO_OBSERVED_NEED_FOR_SIGNED_CROSS' if all(r['absolute_cross']['status']=='pass' for r in selected)
                              else 'SIGNED_STRUCTURE_REVIEW_REQUIRED'),
            uniform_covariance_proved=False))
    result=dict(schema='centered-mobius-mechanism-diagnostic-v1',
        source_run=str(RUN.relative_to(ROOT)),candidates=candidates,rows=rows,
        exact_saved_dyadic_arithmetic=True,new_source_observations=0,
        frozen_selection_changed=False,uniform_covariance_bounds_proved=0,RH_proved=False,
        interpretation='Finite survival does not yet identify arithmetic cancellation or supply a uniform bound.')
    with (RUN/'mechanism_diagnostic.json').open('x') as stream:
        json.dump(result,stream,indent=2,sort_keys=True);stream.write('\n')
    continuation=deepcopy(read('next_search_input.json'))
    continuation['mechanism_review']=dict(path=str((RUN/'mechanism_diagnostic.json').relative_to(ROOT)),
        candidates=candidates,source_observations_added=0,
        stronger_finite_margin_is_not_a_proof_mechanism=True)
    continuation['next_construction']['additional_requirements']=[
        'construct a source-sensitive auxiliary and an argument, not only another bounded energy ansatz',
        'record whether absolute replacement of signed cross terms already passes every finite test',
        'require the proof to use the universal source laws or an independently certified global identity',
        'reject finite-prime-only relaxations as sufficient proof scopes when they admit the042 adversarial model',
        'retain every original source and analytic-normalization assumption when judging countermodel scope']
    with (RUN/'proof_search_input.json').open('x') as stream:
        json.dump(continuation,stream,indent=2,sort_keys=True);stream.write('\n')
    with (RUN/'mechanism_review_source.py').open('x') as stream:
        stream.write(Path(__file__).read_text())
    print(json.dumps(dict(candidates=candidates,new_source_observations=0,uniform_bound_proved=False)))


if __name__=='__main__':main()
