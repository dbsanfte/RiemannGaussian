#!/usr/bin/env python3
"""Independent factor arithmetic and whole fractional integrals beyond 64 bits."""
from fractions import Fraction as Q
from pathlib import Path
import argparse,flint
from stable_scale_report import BASE,read,sha,digest
from check_mellin_kernels import a,powq,put,tight_overlap
from check_branch_centers import independent_profile,independent_center,scalar_c,cb
from check_divisor_preconditioners import prime_difference,mu

def check(path):
    data=read(path);flint.ctx.prec=1024;counts={};coeffs=0
    assert not data['search_or_selection_changed'] and data['uniform_RH_sufficient_signed_controls_verified']==[] and not data['RH_proved']
    for order,table in data['tables'].items():
        assert Q(order).denominator>2**64 and not table['native_unsigned_denominator_used'] and not table['prime_or_factor_oracle_used']
        for n in range(1,table['cutoff']+1):
            assert table['mu'][n]==mu(n);tight_overlap(table['values'][n],prime_difference(Q(order),n));coeffs+=1
    counts['independent_actual_prime_difference_coefficients_above_64_bit_denominator']=coeffs;profiles={}
    for order,p in data['profiles'].items():
        F=independent_profile(order);tight_overlap(p['value_ball']['real'],F.real);tight_overlap(p['value_ball']['imag'],F.imag);profiles[order]=F
        assert p['whole_continuation_not_prefix_surrogate'] and not p['native_unsigned_denominator_used']
    counts['independent_whole_fractional_zeta_integrals']=len(profiles);p=data['tiny_root_filter'];atoms=[(Q(b),Q(w)) for b,w in p['atoms']];m=data['tiny_root_recovery']['first_nonzero_moment_order'];moment=sum((w*b**m for b,w in atoms),Q(0));assert m==1 and data['tiny_root_recovery']['admitted']
    F=sum((a(w)*profiles[str(b)] for b,w in atoms),flint.acb(0))/a(moment);obs=data['tiny_root_observer'];assert not obs['missing'];tight_overlap(obs['normalized_full_profile_ball']['real'],F.real);tight_overlap(obs['normalized_full_profile_ball']['imag'],F.imag)
    lower=flint.arb(obs['profile_modulus_lower_ball']);assert lower>0 and lower.upper()<abs(cb(obs['normalized_full_profile_ball'])).lower();counts['normalized_tiny_parameter_high_pass_observers']=1
    for order,c in data['centers'].items():
        value=independent_center(order,'32');tight_overlap(c['value_ball'],value);assert flint.arb(c['value_ball']).contains(value)
    counts['complete_tiny_order_centers']=len(data['centers'])
    for row in data['large_constant_contracts']:
        flint.ctx.prec=1024;p=row['program'];q=row['level'];atoms=[(Q(b),Q(w)) for b,w in p['atoms']]
        for m in range(len(atoms)):
            moment=sum((w*b**m for b,w in atoms),Q(0))
            if moment:break
        h=moment/Q(q)**m;C=sum((a(abs(w))*(1+4*a(2).log()*scalar_c(b/q)/a(1-b/q)) for b,w in atoms),flint.arb(0))/a(abs(h));cert=row['certificate']
        assert a(cert['constant'])>C and cert['bound_integer_is_exact_outward_ceiling'] and not cert['decimal_conversion_used_for_integer_guard'] and cert['global_signed_premise_proved'] and not cert['RH_strength']
    counts['exact_outward_integer_guards_beyond_decimal_precision']=len(data['large_constant_contracts'])
    for n,h in data['source_sha256'].items():assert sha(BASE/n)==h
    result={'all_passed':True,'data_sha256':sha(path),'checker_sha256':sha(BASE/'check_rational_fractional_contracts.py'),'counts':counts,'mathematical_audit_imports_production_code':False,'no_search_or_selection_changes':True,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False};destination=path.with_name('rational_fractional_contract_verification.json')
    if destination.exists():raise FileExistsError('Retain completed verification')
    put(destination,result);print('Independent unrestricted-denominator and exact-guard contracts passed',counts,flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--data',type=Path,required=True);check(p.parse_args().data.resolve())
