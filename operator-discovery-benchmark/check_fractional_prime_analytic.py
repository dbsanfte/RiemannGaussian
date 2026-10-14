#!/usr/bin/env python3
"""Independent derivative-integral, coefficients and exact corridor coverage."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
from itertools import product
import argparse
import hashlib
import json
import time
import flint

BASE=Path(__file__).resolve().parent
DEST=BASE/'fractional-prime-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def square(radius):return flint.acb(flint.arb(0,radius),flint.arb(0,radius))


@lru_cache(maxsize=None)
def log(n):return flint.arb(n).log() if n>1 else flint.arb(0)


def zeta_derivative(s,order=1):
    value=flint.acb_series([s,1],prec=order+1).zeta()[order]
    return value*2 if order==2 else value


def euler_bound(x,order):
    # For order one/two, monotonicity of (log t)^order*t^-x on
    # t>=2 is assured by x>=3. First term plus its integral bounds
    # the complete differentiated Euler series.
    assert x>=3
    a=x-1;l=log(2)
    if order==1:factor=l+2*l/a+2/a**2
    else:factor=l*l+2*l*l/a+4*l/a**2+4/a**3
    return flint.arb(2)**(-x)*factor


def native_numerator(s,sigma):
    # Independent integration-by-parts formula: no subtraction quotient,
    # Taylor splice, or production integral is imported.
    U=Q(9);edges=(Q(0),Q(1,12),Q(1,3),Q(3,2),Q(7,2),Q(6),U)
    def integrand(u,analytic):return zeta_derivative(s+u*u)
    integral=flint.acb(0)
    for a,b in zip(edges,edges[1:]):
        integral+=flint.acb.integral(integrand,real(a),real(b),
                                    abs_tol=flint.arb('1e-28'),rel_tol=flint.arb('1e-28'),
                                    eval_limit=40000,depth_limit=35)
    x=real(sigma+U*U);tail=euler_bound(x,1)/(flint.arb.pi().sqrt()*log(2)*real(U))
    value=-2*integral/flint.arb.pi().sqrt()+square(tail)
    assert value.is_finite()
    return value,{'formula':'-2/sqrt(pi)*integral_0^infinity zeta_prime(s+u^2)du',
                  'U':str(U),'edges':list(map(str,edges)),
                  'differentiated_Euler_tail_upper_ball':tail.str(28),'all_passed':True}


@lru_cache(maxsize=None)
def factors(n):
    result={}
    for p,e in flint.fmpz(n).factor():result[int(p)]=result.get(int(p),0)+int(e)
    value=1
    for p,e in result.items():value*=p**e
    assert value==n
    return result


def coefficients(N):
    values=[flint.arb(0)]*(N+1)
    for n in range(2,N+1):
        ps=list(factors(n));total=flint.arb(0)
        for bits in product((0,1),repeat=len(ps)):
            d=1
            for p,b in zip(ps,bits):
                if b:d*=p
            if n//d>1:total+=(-1)**sum(bits)*log(n//d).sqrt()
        values[n]=total
        assert total.abs_upper()<=log(n).sqrt() or total.overlaps(log(n).sqrt())
    return values


def native_groups(source):
    cutoff=6144;values=coefficients(cutoff);records=[]
    for row in source['actual_zeta_ball_checks']:
        sigma=Q(row['s'][0]);s=flint.acb(real(sigma),row['s'][1])
        N,certificate=native_numerator(s,sigma);whole=N/s.zeta()
        recorded=flint.acb(flint.arb(row['native_value_real_ball']),flint.arb(row['native_value_imag_ball']))
        assert whole.overlaps(recorded)
        partial=sum((values[n]*(-s*log(n)).exp() for n in range(2,cutoff+1)),flint.acb(0))
        a=real(sigma-1);tail=real(cutoff)**(-a)*(log(cutoff)/a+1/a**2)
        difference=(partial-whole).abs_upper();assert difference<tail
        wrong=(partial+real(Q(1,13))*(-s*log(17)).exp()-whole).abs_lower();assert wrong>tail
        records.append({'s':row['s'],'coefficient_cutoff':cutoff,
                        'coefficient_origin':'independent complete factor/subset differences',
                        'independent_native_formula':certificate,'source_native_value_overlap':True,
                        'difference_upper_ball':difference.str(28),'tail_upper_ball':tail.str(28),
                        'wrong_prime_index':17,'wrong_difference_lower_ball':wrong.str(28),'all_passed':True})
        print('Independent fractional-log group',row['s'],True,flush=True)
    return {'records':records,'all_passed':True}


def numerator_derivative_bound(c,r):
    # Different formula and mesh from the producer: -2 int zeta''.
    region=c+square(real(r));U=Q(9);delta=Q(1,40)
    first=region+flint.acb(flint.arb(real(delta*delta/2),real(delta*delta/2)))
    total=real(delta)*zeta_derivative(first,2).abs_upper();todo=[];a=delta
    while a<U:
        b=min(U,a*Q(7,6));todo.append((a,b));a=b
    accepted=0;refined=0
    while todo:
        a,b=todo.pop();x=Q(1,2)-r+a*a
        if x>=3:bound=euler_bound(real(x),2)
        else:
            shifted=region+flint.acb(flint.arb(real((a*a+b*b)/2),real((b*b-a*a)/2)))
            bound=zeta_derivative(shifted,2).abs_upper()
        if not bound.is_finite():
            assert b-a>Q(1,2**30)
            m=(a+b)/2;todo.extend(((a,m),(m,b)));refined+=1;continue
        total+=real(b-a)*bound;accepted+=1
    x=real(Q(1,2)-r+U*U)
    tail=euler_bound(x,2)/(flint.arb.pi().sqrt()*log(2)*real(U))
    result=2*total/flint.arb.pi().sqrt()+tail
    assert result.is_finite()
    return result,{'formula':'2/sqrt(pi)*integral |zeta_second_derivative(s+u^2)|du',
                   'U':str(U),'delta':str(delta),'geometric_cell_ratio':'7/6',
                   'finite_derivative_cells':accepted,'adaptive_refinements':refined,
                   'infinite_derivative_tail_upper_ball':tail.str(28),'all_passed':True}


def count_one_disk(c,r):
    region=c+square(real(r));derivative=zeta_derivative(c)
    remainder=c.zeta().abs_upper()+real(r*r/2)*zeta_derivative(region,2).abs_upper()
    margin=real(r)*derivative.abs_lower()-remainder
    assert margin>0 and zeta_derivative(region).abs_lower()>0
    return {'radius':str(r),'Rouche_margin_lower_ball':margin.str(28),
            'one_simple_ordinary_zeta_zero_certified':True,'all_passed':True}


def coverage_and_native_boxes(path,c,r):
    scale=path['scale'];left=Q(path['start_real']);right=Q(path['end_real'])
    bottom,top=-scale*r,scale*r
    assert left==(Q(1,2)+2*r if scale==1 else 1-2*r) and right==3
    assert Q(path['imag_radius'])==scale*r
    events={};rectangles={};minimum=None;todo=[];refinements=0
    for row in path['boxes']:
        a,b=Q(row['left']),Q(row['right']);y,z=Q(row['imag_offset_lower']),Q(row['imag_offset_upper'])
        assert left<=a<b<=right and bottom<=y<z<=top
        todo.append((a,b,y,z))
    # Increasing precision can switch Arb's zeta algorithm and widen a
    # rectangular enclosure. A zero lower bound is inconclusive; refine
    # this checker's rectangles instead of trusting the producer's bounds.
    while todo:
        a,b,y,z=todo.pop()
        box=flint.acb(flint.arb(real((a+b)/2),real((b-a)/2)),
                       c.imag*scale+flint.arb(real((y+z)/2),real((z-y)/2)))
        lower=box.zeta().abs_lower()
        if not lower>0:
            assert max(b-a,z-y)>Q(1,2**36),'Zero-free corridor refinement failed'
            # Deliberately change the split point from the producer's halves.
            if b-a>=z-y:
                m=(2*a+b)/3;todo.extend(((a,m,y,z),(m,b,y,z)))
            else:
                m=(2*y+z)/3;todo.extend(((a,b,y,m),(a,b,m,z)))
            refinements+=1;continue
        i=len(rectangles);rectangles[i]=(y,z)
        events.setdefault(a,[]).append((True,i));events.setdefault(b,[]).append((False,i))
        minimum=lower if minimum is None else min(minimum,lower)
    edges=sorted(events);assert edges[0]==left and edges[-1]==right
    active=set();stripes=0
    for index,x in enumerate(edges):
        for addition,i in events[x]:
            if addition:assert i not in active;active.add(i)
            else:assert i in active;active.remove(i)
        if index==len(edges)-1:assert not active;break
        cursor=bottom
        for y,z in sorted(rectangles[i] for i in active):
            assert y==cursor,'Overlapping rectangles or a coverage gap';cursor=z
        assert cursor==top;stripes+=1
    return {'scale':scale,'source_rectangle_count':len(path['boxes']),
            'native_boxes_rechecked':len(rectangles),'independent_ternary_refinements':refinements,
            'exact_vertical_stripes_checked':stripes,
            'minimum_native_zeta_modulus_lower_ball':minimum.str(28),
            'complete_rectangle_coverage_and_no_overlap_proved':True,'all_passed':True}


def zero_controls(source):
    records=[]
    for row in source['fractional_numerator_and_decoder_actual_zero_controls']['records']:
        c=flint.acb(real(Q(1,2)),row['disk_centre'][1]);r=Q(row['radius'])
        assert row['local_connection_disk']['no_uncovered_gap_between_zero_disk_and_corridor']
        N,certificate=native_numerator(c,Q(1,2))
        old=flint.acb(flint.arb(row['native_numerator_real_ball']),flint.arb(row['native_numerator_imag_ball']))
        assert N.overlaps(old)
        M,derivative_certificate=numerator_derivative_bound(c,r)
        lower=N.abs_lower()-real(r)*M;assert lower>0
        d=zeta_derivative(c+square(real(r))).abs_upper()
        branch=flint.arb.pi().sqrt()*lower/d;assert branch>0
        nested=count_one_disk(c,r/2);outer=count_one_disk(c,5*r)
        assert (5*r)**2>5*r*r
        paths=[coverage_and_native_boxes(path,c,r) for path in row['horizontal_zero_free_corridors']]
        records.append({'disk_centre':row['disk_centre'],'radius':str(r),
                        'independent_numerator_real_ball':N.real.str(28),'independent_numerator_imag_ball':N.imag.str(28),
                        'independent_numerator_certificate':certificate,'changed_derivative_certificate':derivative_certificate,
                        'whole_disk_numerator_derivative_upper_ball':M.str(28),
                        'whole_disk_numerator_modulus_lower_ball':lower.str(28),
                        'inverse_sqrt_branch_coefficient_modulus_lower_ball':branch.str(28),
                        'changed_nested_root_disk':nested,'changed_outer_connection_disk':outer,
                        'complete_horizontal_corridors':paths,'new_ordinary_zeta_zero_located':False,'all_passed':True})
        print('Independent whole-zero-disk fractional branch',row['disk_centre'][1],lower.str(20),True,flush=True)
    return {'records':records,'global_nonvanishing_at_every_zeta_zero_proved':False,'all_passed':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-native-groups',action='store_true',
                        help='Reuse this checker\'s passed component with matching source, code and precision')
    args=parser.parse_args()
    start=time.monotonic();flint.ctx.prec=448;flint.ctx.cap=22
    source=json.loads((DEST/'fractional_prime_analytic.json').read_text());assert source['all_passed']
    fingerprint={'source_groups_sha256':hashlib.sha256(json.dumps(source['actual_zeta_ball_checks'],sort_keys=True).encode()).hexdigest(),
                 'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                 'precision':flint.ctx.prec,'series_cap':flint.ctx.cap,'flint_version':flint.__version__}
    checkpoint=DEST/'independent_native_groups_checkpoint.json'
    if args.reuse_native_groups:
        previous=json.loads(checkpoint.read_text());assert previous['fingerprint']==fingerprint
        groups=previous['native_fractional_log_audit'];assert groups['all_passed']
        assert len(groups['records'])==6 and all(r['all_passed'] for r in groups['records'])
    else:
        groups=native_groups(source)
        checkpoint.write_text(json.dumps({'fingerprint':fingerprint,'native_fractional_log_audit':groups,
                                         'component_only_not_complete_analytic_audit':True},indent=2)+'\n')
    zeros=zero_controls(source)
    assert not source['full_normalized_B_decoder_native_value_compared']
    assert not source['new_uniform_prime_distribution_estimate_proved'] and not source['new_RH_estimate_proved']
    assert not source['historical_novelty_established']
    checks={'independent_complete_fractional_log_and_native_derivative_integral':groups['all_passed'],
            'changed_coefficient_cutoff_Euler_tail_and_wrong_prime_controls':groups['all_passed'],
            'independent_actual_zero_numerator_and_whole_disk_nonvanishing':zeros['all_passed'],
            'exact_corridor_coverage_and_native_zero_free_boxes':zeros['all_passed'],
            'changed_nested_Rouche_disks_and_outer_connector_no_gap':zeros['all_passed'],
            'full_decoder_global_zero_prime_information_and_novelty_scope_honest':True}
    out={'checks':checks,'native_fractional_log_audit':groups,'actual_zero_and_corridor_audit':zeros,
         'source_artifact_sha256':hashlib.sha256((DEST/'fractional_prime_analytic.json').read_bytes()).hexdigest(),
         'reused_matching_independent_native_groups':args.reuse_native_groups,'fingerprint':fingerprint,
         'production_imports':False,'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'fractional_prime_analytic_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent fractional analytic audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
