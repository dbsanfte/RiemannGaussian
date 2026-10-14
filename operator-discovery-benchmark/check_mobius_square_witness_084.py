"""Exact independent finite fixed-operator square-method lower witnesses."""
from fractions import Fraction as Q
import check_mobius_coupled_remainder_083 as R
from check_mobius_prime_storage_073 import AdmissionError,ResourceLimit,_rational


def quadratic_value(matrix,signs,meter=None):
    m=meter or R.C.Meter();n=len(signs)
    if n>512:raise ResourceLimit('complete Boolean witness cap512')
    if type(signs)is not list or any(type(v)is not int or v not in (-1,1)for v in signs):raise AdmissionError('exact Boolean sign vector')
    if len(matrix)!=n or any(len(row)!=n for row in matrix):raise AdmissionError('complete witness matrix')
    m.reserve(16384+n*n*2048);m.charge(max(1,n*n)*1024)
    if any(matrix[i][j]!=matrix[j][i]for i in range(n)for j in range(i)):raise AdmissionError('symmetric complete witness matrix')
    return sum((signs[i]*signs[j]*matrix[i][j]for i in range(n)for j in range(n)),Q(0))


def verify(program,u,outer_certificate,certificate,meter=None):
    m=meter or R.C.Meter();out={}
    try:
        if type(certificate)is not dict or set(certificate)!={'squarefree_count','signs','lower_bound'}:raise AdmissionError('exact Boolean witness schema')
        signs=certificate['signs']
        if type(signs)is not list or len(signs)>512:raise ResourceLimit('prospective complete Boolean witness cap512')
        if any(type(v)is not int or v not in (-1,1)for v in signs)or signs and signs[0]!=1:raise AdmissionError('exact Boolean witness with anchor1')
        data=R.build_remainder(program,u,outer_certificate,m);model=data['model'];n=model['effective_dimension']
        if n>512:raise ResourceLimit('whole effective witness dimension cap512')
        if len(signs)!=n or type(certificate['squarefree_count'])is not int or certificate['squarefree_count']!=model['squarefree_count']:raise AdmissionError('complete coordinate binding')
        R.C._budget(model,m,extra_bytes=model['squarefree_count']**2*1024+n*n*2048)
        actual=quadratic_value(data['projected_remainder'],signs,m);supplied=_rational(certificate['lower_bound'],'lower bound',m)
        if actual!=supplied:raise AdmissionError('exact complete witness value mismatch')
        out.update(status='VERIFIED_FINITE_FIXED_OPERATOR_SQUARE_LOWER_BOUND',u=u,lower_bound=str(actual),
                   squarefree_count=model['squarefree_count'],effective_dimension=n,all_positive_square_completions_bound=True,
                   fixed_operator_only=True,whole_theta_grammar_bound=False,artificial_signs_not_actual_Mobius=True,
                   actual_signed_drift_lower_bound_proved=False,uniform_obstruction_proved=False,RH_proved=False,
                   proof='For every Q>=0, B(R+Q)>=s^T(R+Q)s>=s^T R s, since every s_i^2=1. The artificial signs need not satisfy divisor identities.')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return R.C._finish(out,m,e)
    return R.C._finish(out,m)
