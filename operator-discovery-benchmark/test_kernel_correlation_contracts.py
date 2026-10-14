"""Public mathematical contracts; separate from autonomous discovery selection."""
from fractions import Fraction as Q
import unittest
import flint
from estimate_grammar import inverse_one_prefix
from mellin_kernel_grammar import canonical,primitive_table,response,real,power
import kernel_correlation_grammar as gram
import kernel_density_bridge as density


def test_singular_metric_preserves_tiny_positive_pivots_and_amplitudes():
    H=gram.metric(Q(1,2**101),0,1);assert H['positive_semidefinite'] and H['rank']==2
    assert Q(H['positive_pivots'][0])==Q(1,2**101)
    K=canonical([[0,0,'1']]);L=canonical([[1,0,'1']]);effective,pivots,vectors=gram.effective_kernels([K,L],H)
    assert effective[0]['terms']==K['terms'] and pivots==H['positive_pivots']
    H=gram.metric(1,Q(1,3),Q(1,9));effective,pivots,vectors=gram.effective_kernels([K,L],H)
    assert H['rank']==1 and effective[0]['terms']==[[0,0,'1'],[1,0,'1/3']]


def test_indefinite_observables_do_not_gain_coercive_recovery():
    K=canonical([[0,0,'1']]);L=canonical([[1,0,'1']]);H=gram.metric(1,2,-1)
    rec=gram.recovery([K,L],H)
    assert not H['positive_semidefinite'] and not rec['all_height_no_common_zero'] and not rec['counterexample_to_signed_bound']


def test_general_rational_rates_retain_pointwise_products():
    flint.ctx.prec=384;K=canonical([[0,0,'1'],[1,1,'-1']]);L=canonical([[2,0,'1'],[0,2,'-1']]);b=Q(5,3)
    rows=gram.kernel_product(K,L,b)
    assert any(Q(r) not in {b**j for j in range(10)} for m,r,c in rows)
    y=real(Q(17,19))
    def at(K):return sum((real(c)*(real(b**j)*y)**m*(-real(b**j)*y).exp() for m,j,c in K['terms']),flint.arb(0))
    product=sum((real(c)*(real(r)*y)**m*(-real(r)*y).exp() for m,r,c in rows),flint.arb(0))
    assert product.overlaps(at(K)*at(L))


def complete_squarefree_tails_and_true_signed_density_remainder(ell):
    mu=inverse_one_prefix(512);k=Q(3,2);ell=Q(ell);b=Q(3,2);points=[Q(1),Q(7,3)]
    K=canonical([[0,0,'1'],[1,1,'-1']]);H=gram.metric(1,0,0);Ks=[K,K]
    table=gram.squarefree_table(mu,k,ell,b,points);rows=gram.diagonal_terms(Ks,H,b);dc=gram.diagonal_certificate(rows,k,ell)
    it=primitive_table(mu,k,ell,b,points);vs=[response(K,it,points)]*2
    obs=gram.observable(Ks,H,vs,table,rows,points);zs=density.value(obs,dc)
    for X,z in zs.items():assert abs(flint.arb(z))<=flint.arb(dc['signed_remainder_constant_ball'])*power(real(X),Q(1,2))
    assert table['all_infinite_squarefree_terms_included'] and not dc['RH_strength_for_full_response']


def test_fractional_approaches_have_no_semantic_denominator_cap():
    f=gram.energy_frontier('1/2','1/17','1/1009','7/101')
    g=density.frontier('1/4','1/19','1/10007','1/101')
    assert f['approach_power']=='1/1009' and g['approach_power']=='1/10007'
    assert not f['constant_growth_in_q_restricted'] and not g['finite_parameter_grid_suffices']


def test_density_certificate_refuses_a_root_inside_the_required_strip():
    k,ell=Q(2),Q(3,2);alpha=(2*k-Q(1,2))/ell
    rec=density.recovery_certificate([[0,'2',str(-alpha-1)],[1,'2','1']],k,ell)
    assert not rec['all_height_recovery'] and not rec['counterexample_to_bound']
    rec=density.recovery_certificate([[4,'7/3','1']],k,ell)
    assert rec['all_height_recovery'] and rec['peeled_nonpositive_roots']==[0,1,2,3]


def test_zero_reflection_halves_heights_with_multiplicity_scope():
    beta,height=Q(3,4),Q(2**24);path=density.reflection_path(beta,height,24)
    for j,row in enumerate(path):
        assert Q(row['height'])==height/2**j
        assert Q(row['distance_from_two_thirds'])==(-Q(1,2))**j*(beta-Q(2,3))


def test_wrong_center_is_globally_false_despite_tiny_finite_perturbation():
    rows=[[0,'2','1']];dc=gram.diagonal_certificate(rows,Q(2),Q(2));p={'diagonal_certificate':dc,'density_recovery':density.recovery_certificate(rows,Q(2),Q(2))}
    f=density.frontier('1/2','1/4','1/6','1/2')
    assert density.transfer(p,f)['uniform_premise_proved']
    assert density.transfer(p,f,1+Q(1,2**100))['status']=='globally_false_uncancelled_density_pole_at_one'


def test_invalid_domains_and_counterfeit_prefix_are_rejected():
    mu=inverse_one_prefix(16)
    with unittest.TestCase().assertRaises(ValueError):gram.squarefree_table(mu,Q(1),Q(1,2),Q(2),[1])
    with unittest.TestCase().assertRaises(ValueError):gram.rate_terms([[Q(1,2),'2','1']])
    with unittest.TestCase().assertRaises(ValueError):gram.rate_terms([[1,'-2','1']])
    with unittest.TestCase().assertRaises(ValueError):gram.metric(0,0,0)
    mu[13]+=1
    with unittest.TestCase().assertRaises(ValueError):gram.squarefree_table(mu,Q(2),Q(1,3),Q(2),[1])


def test_independent_comparator_accepts_raw_energy_control_records():
    from collections import defaultdict
    from check_kernel_correlations import comparison_check
    c={'kind':'energy','rho':'0','frontier':{'limit':'1/2','margin':'1/4','approach_power':'1','log_power':'0'}}
    old={'failures':[],'unresolved':[],'maximum_ratio':0,'finite_points_passed':True,'uniform_signed_premise_proved':False,'point_comparisons':1}
    counts=defaultdict(int)
    comparison_check(c,{'1':{'energy_ball':'1','diagonal_ball':'2'}},{'2':'1'},[2],old,counts)
    assert counts['independent_finite_inequality_comparisons']==1


class Contracts(unittest.TestCase):
    pass


for _name,_fn in list(globals().items()):
    if _name.startswith('test_') and callable(_fn):
        setattr(Contracts,_name,lambda self,fn=_fn:fn())

for _name,_ell in [('square_root','1/2'),('cube_root','1/3'),('sixth_root','1/6'),('unlisted_rational_root','7/101')]:
    setattr(Contracts,'test_complete_density_'+_name,lambda self,ell=_ell:complete_squarefree_tails_and_true_signed_density_remainder(ell))

del _fn,_name,_ell


if __name__=='__main__':unittest.main()
