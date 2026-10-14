"""Independent effective all-scale rank-one obstruction for dense SDD PRICE.
No actual mu signs, source sieve, producer, LP or asymptotic prime theorem.
Reuses independent082 program parser and frozen073 exact rational/root helpers.
"""
from fractions import Fraction as Q
import check_mobius_dense_completion_082 as D
from check_mobius_prime_storage_073 import (AdmissionError,ResourceLimit,_rational,_add,_mul,_divide,_int_mul,_power_target,_power_compare)
MAX_INTERVALS=256
class Meter(D.Meter):pass

def _ceil(q):return -(-q.numerator//q.denominator)
def _threshold_power(threshold,scale,left,eta,m):
    t=_divide(_mul(Q(2),scale,m),left,m);b=eta.denominator
    num=_power_target(t.numerator,b,1,0,m);den=_power_target(t.denominator,b,1,0,m)
    target=(num+den-1)//den
    if _power_compare(threshold,b-eta.numerator,target,m)<0:raise AdmissionError('sublinear eventual zero threshold insufficient')
def _finish(out,m,error=None):
    if error is not None:out.update(status='INVALID',reason=str(error),resource_limit=isinstance(error,ResourceLimit))
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_original_source_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,actual_arithmetic_drift_refuted=False,source_kernel_binding_still_required=True)
    return out

def verify_obstruction(program,certificate,meter=None):
    """Verify explicit rational interval/null witness; obstruction is PRICE-only."""
    m=meter or Meter();out={}
    try:
        p=D.parse_program(program,m);dim=p['memory']+1;numprofiles=len(p['profiles']);kernel=p['kernel'];maximum=Q(1,kernel[0][0]);T=D.drift_matrix(p,m);H00=T[0][0]
        keys={'schema','intervals','tau','threshold','H00','lower_coefficient'}
        if type(certificate)is not dict or set(certificate)!=keys or certificate['schema']!='dense-rank-interval-v1':raise AdmissionError('exact rank interval certificate schema')
        intervals=certificate['intervals']
        if type(intervals)is not list or not 1<=len(intervals)<=MAX_INTERVALS:raise AdmissionError('bounded nonempty intervals')
        threshold=certificate['threshold']
        if type(threshold)is not int or threshold<1:raise AdmissionError('positive integer threshold')
        if threshold.bit_length()>100000:raise ResourceLimit('threshold integer bit gate')
        tau=_rational(certificate['tau'],'tau',m);saved_H=_rational(certificate['H00'],'H00',m);saved_lower=_rational(certificate['lower_coefficient'],'lower_coefficient',m)
        if tau<=0 or saved_H!=H00:raise AdmissionError('positive tau and exact H00 required')
        # Prospective input/parsed witness space scales with actual rational text.
        cost=16384+threshold.bit_length()
        for row in intervals:
            if type(row)is not dict or set(row)!={'left','right','profiles','source','t'}:raise AdmissionError('interval exact schema')
            if type(row['profiles'])is not list or len(row['profiles'])!=numprofiles or type(row['source'])is not list or len(row['source'])!=dim:raise AdmissionError('interval complete feature vector shape')
            for v in [row['left'],row['right'],row['t'],*row['source']]:
                if type(v)is not str:raise AdmissionError('canonical interval rational required')
                cost+=512+8*len(v)
            cost+=1024*len(row['profiles'])
        m.reserve(cost*4);tot_source=[Q(0)]*dim;tot_profiles=[Q(0)]*numprofiles;previous=Q(0);stability=[]
        for row in intervals:
            left=_rational(row['left'],'left',m);right=_rational(row['right'],'right',m);t=_rational(row['t'],'t',m);source=tuple(_rational(v,'source',m)for v in row['source'])
            if not 0<left<right<=maximum or left<previous or not t:raise AdmissionError('sorted disjoint positive intervals and nonzero t required')
            previous=right;width=_add(right,-left,m)
            if tau>_divide(width,_mul(Q(4),abs(t),m),m):raise AdmissionError('tau exceeds squarefree population margin')
            required=_ceil(_divide(Q(24),width,m));required=_int_mul(required,required,m)
            if threshold<required:raise AdmissionError('squarefree population threshold insufficient')
            if threshold<_ceil(_divide(Q(2),left,m)):raise AdmissionError('unit exclusion threshold insufficient')
            expected=[]
            for i in range(dim):
                value=Q(0)
                for d,w in kernel:
                    breakpoint=Q(1,(1<<i)*d)
                    if left<breakpoint<right:raise AdmissionError('source breakpoint inside interval')
                    if right<=breakpoint:value=_add(value,w,m)
                expected.append(value)
            if tuple(expected)!=source:raise AdmissionError('independent source interval values mismatch')
            values=[];local_stability=[]
            for j,(scale,eta)in enumerate(p['profiles']):
                v=row['profiles'][j]
                if type(v)is not int or v<0:raise AdmissionError('nonnegative integer profile values')
                if v.bit_length()>4096:raise ResourceLimit('profile value bit gate')
                if eta<1:
                    if v!=0:raise AdmissionError('sublinear interval profile must vanish')
                    _threshold_power(threshold,scale,left,eta,m);local_stability.append('sublinear_zero')
                else:
                    kappa=min(scale,maximum)
                    if left<=_divide(kappa,Q(v+1),m) or (v and right>=_divide(kappa,Q(v),m)):raise AdmissionError('strict linear profile cell margins required')
                    margin=_add(_divide(kappa,right,m),-Q(v),m)
                    needed=_divide(Q(1),_mul(left,margin,m),m)
                    needed=needed.numerator//needed.denominator+1
                    if threshold<needed:raise AdmissionError('linear profile stability threshold insufficient')
                    local_stability.append(needed)
                values.append(Q(v))
            for i,value in enumerate(source):tot_source[i]=_add(tot_source[i],_mul(t,value,m),m)
            for j,value in enumerate(values):tot_profiles[j]=_add(tot_profiles[j],_mul(t,value,m),m)
            stability.append(local_stability)
        if tot_source!=[Q(1)]+[Q(0)]*(dim-1) or any(tot_profiles):raise AdmissionError('exact rank witness null/target constraints fail')
        lower=_mul(H00,_mul(tau,tau,m),m)
        if saved_lower!=lower or lower<=0:raise AdmissionError('exact positive rank-one lower coefficient mismatch')
        out.update(status='VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION',threshold=threshold,lower_coefficient=str(lower),H00=str(H00),tau=str(tau),interval_count=len(intervals),source_moments=[str(v)for v in tot_source],profile_moments=[str(v)for v in tot_profiles],profile_stability=stability,uniform_completion_price_obstruction_proved=True,excluded_price_exponents='every q<2 with fixed finite C',price_lower_bound='B(u)>=lower_coefficient*u^2 for every integer u>=threshold',scope='Formal group-box rank-one covariance; actual mu drift/source bound unrefuted',squarefree_premise='Q(x)=x/zeta(2)+error, |error|<=3sqrt(x), 1/zeta(2)>1/2; elementary square-divisor inversion',linear_floor_note='The conservative margin threshold is verified; integer floor nesting also gives floor(floor(kappa*u)/n)=floor(kappa*u/n).',current_parameter_values_irrelevant=True,profile_roster_must_remain_fixed=True)
    except (ValueError,TypeError,KeyError,OverflowError)as e:return _finish(out,m,e)
    return _finish(out,m)
