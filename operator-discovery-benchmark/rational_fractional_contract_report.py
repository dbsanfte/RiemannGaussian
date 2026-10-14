"""Read-only loader for the additional arbitrary-denominator numerical contracts."""
from pathlib import Path
from fractions import Fraction as Q
from stable_scale_report import BASE,read,sha

def load_latest():
    pointer=BASE/'branch-center-results/latest.json'
    if not pointer.exists():return {'status':'not_run'}
    d=Path(read(pointer)['run_directory']);data_path=d/'rational_fractional_contract_data.json';v_path=d/'rational_fractional_contract_verification.json'
    if not v_path.exists():return {'status':'not_run'}
    data=read(data_path);v=read(v_path)
    assert v['all_passed'] and v['data_sha256']==sha(data_path) and v['checker_sha256']==sha(BASE/'check_rational_fractional_contracts.py')
    for n,h in data['source_sha256'].items():assert sha(BASE/n)==h
    assert not v['mathematical_audit_imports_production_code'] and v['no_search_or_selection_changes'] and not data['search_or_selection_changed'] and not data['RH_proved']
    return {'status':'verified_arbitrary_denominator_fractional_evaluation_and_exact_integer_guards','run_directory':str(d),
        'tested_rational_denominators':[str(Q(q).denominator) for q in data['tables']],'all_positive_rational_orders_have_evaluation_semantics':True,
        'native_unsigned_root_denominator_limit_removed':True,'precision_adaptive_serialization':True,'exact_outward_integer_guard_verified':True,
        'normalized_tiny_parameter_high_pass_verified':True,'no_search_or_selection_changes':True,'independent_native_counts':v['counts'],
        'data_sha256':sha(data_path),'verification_sha256':sha(v_path),'producer_sha256':sha(BASE/'rational_fractional_evaluator.py'),'checker_sha256':v['checker_sha256'],
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}
