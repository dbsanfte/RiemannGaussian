"""Proof-scope, exact-position and zero-preservation public contracts."""
from fractions import Fraction as Q
import unittest
import flint
import lattice_synthesis_grammar as g
from lattice_zero_bridge import root_certificate,reflection_path,exceptional_real_parts,complementary_certificate
from mellin_kernel_grammar import real,power


class Contracts(unittest.TestCase):
    def setUp(self):flint.ctx.prec=512

    def test_fractional_positions_have_exact_cutoff_inclusion(self):
        N=256;r=Q(7,2);pairs,mu=g.pair_prefix(N,r)
        self.assertTrue(any(d>1 for j,d,a in pairs))
        for j,d,a in pairs:self.assertLessEqual(j**2*d**7,N**2)
        for d in range(1,len(mu)):
            M=max(j for j,h,a in pairs if h==d)
            self.assertGreater((M+1)**2*d**7,N**2)

    def test_integer_positions_recover_actual_r_free_coefficients(self):
        for r in [2,3,4]:
            pairs,mu=g.pair_prefix(128,Q(r));counts=[0]*129
            for j,d,a in pairs:counts[j*d**r]+=a
            for n in range(1,129):
                allowed=not any(n%(p**r)==0 for p in range(2,n+1))
                self.assertEqual(counts[n],int(allowed))

    def test_complete_inverse_and_unit_channels_remain_distinct(self):
        table=g.complete_table('3','2','7/2','2',[1,Q(7,3)],N=256,maximum_moment=2)
        self.assertTrue(table['all_infinite_arithmetic_positions_included'])
        self.assertTrue(table['fractional_r_positions_are_generalized_signed_measures'])
        self.assertFalse(flint.arb(table['values']['inverse']['0:1']).overlaps(flint.arb(table['values']['unit']['0:1'])))

    def test_known_poles_can_be_cancelled_without_an_RH_claim(self):
        K,ell,r=Q(3),Q(2),Q(3);a=(K-1)/ell;b=(K-1/r)/ell
        c=g.shape([[0,a*b],[1,-1-a-b],[2,1]])
        res=g.residues(c,[K,ell,r]);self.assertTrue(res['both_reference_residues_vanish'])
        cert=g.reference_decay(c,[K,ell,r],Q(1,6))
        self.assertTrue(cert['all_real_scales']);self.assertFalse(cert['RH_consequence']);self.assertFalse(cert['actual_inverse_estimate_proved'])
        g.enforce_certificate_arithmetic(cert,'unit')
        with self.assertRaises(ValueError):g.enforce_certificate_arithmetic(cert,'inverse')

    def test_uniform_reference_bound_survives_fresh_complete_arithmetic(self):
        params=['3','2','3'];K,ell,r=map(Q,params);a=(K-1)/ell;b=(K-1/r)/ell
        c=g.shape([[0,a*b],[1,-1-a-b],[2,1]]);cert=g.reference_decay(c,params,Q(1,3));table=g.complete_table(*params,'2',[1,17,64],maximum_moment=2)
        for X,row in g.responses(c,table,[1,17,64]).items():
            self.assertLessEqual(abs(flint.arb(row['unit_two_residue_residual_ball'])),flint.arb(cert['constant_ball'])*power(real(X),Q(-1,3)))

    def test_sign_loss_barrier_remains_after_both_mass_terms_vanish(self):
        params=['3','2','3'];K,ell,r=map(Q,params);a=(K-1)/ell;b=(K-1/r)/ell;c=g.shape([[0,a*b],[1,-1-a-b],[2,1]])
        barrier=g.sign_loss_barrier(c,params)
        self.assertEqual(barrier['status'],'certified_absolute_rewrite_barrier')
        self.assertEqual(barrier['mode'],'zero_mass_first_nonzero_lattice_coefficient')
        self.assertGreater(flint.arb(barrier['actual_support_lower_constant_ball']),0)
        self.assertTrue(barrier['retaining_actual_squarefree_support_does_not_remove_the_barrier'])
        self.assertFalse(barrier['counterexample_to_actual_bound'])

    def test_real_roots_inside_old_forbidden_halfplane_preserve_nonreal_zeros(self):
        c=g.shape([[0,-10],[1,1]])
        cert=root_certificate(c,['3','3','2'])
        self.assertEqual(cert['kind'],'exact_all_real_polynomial_roots')
        self.assertTrue(cert['all_right_half_ordinary_zeros_preserved'])
        self.assertFalse(cert['kernel_zero_free_halfplane_required'])

    def test_complex_kernel_roots_are_checked_against_actual_zeta(self):
        # v=7/8 +/- i/4 maps to ordinary rho=3/4 -/+ 3i/2.
        c=g.shape([[0,Q(53,64)],[1,Q(-11,4)],[2,1]])
        cert=root_certificate(c,['3','3','2'])
        self.assertEqual(cert['kind'],'certified_finite_operator_root_exclusion')
        self.assertTrue(cert['all_right_half_ordinary_zeros_preserved'])
        self.assertEqual(len(cert['root_disks']),2)
        self.assertTrue(all(not b['outside_ordinary_strip'] for b in cert['root_disks']))
        self.assertTrue(all(flint.arb(b['native_zeta_lower_ball'])>0 for b in cert['root_disks']))
        from collections import defaultdict
        from check_lattice_synthesis import root_check
        root_check({'shape':c,'parameters':['3','3','2'],'zero_bridge':cert},defaultdict(int))

    def test_repeated_real_roots_have_a_semidefinite_certificate(self):
        # (v-1)^2 has one real root with multiplicity two.
        c=g.shape([[0,1],[1,-3],[2,1]]);cert=root_certificate(c,['3','3','2'])
        self.assertTrue(cert['all_right_half_ordinary_zeros_preserved'])
        self.assertTrue(cert['Hermite_factorization']['positive_semidefinite'])
        self.assertEqual(len(cert['Hermite_factorization']['terms']),1)

    def test_independent_root_audit_compares_bound_endpoints_as_inequalities(self):
        # Changing precision improves endpoint bounds without making the
        # endpoints enclosures of one common exact number.
        from collections import defaultdict
        from check_lattice_synthesis import root_check
        c=g.shape([[0,Q(1,3)],[1,-2],[2,Q(1,7)],[3,-1],[4,Q(2,3)]])
        params=['3','1/3','4/3'];cert=root_certificate(c,params)
        self.assertTrue(cert['all_right_half_ordinary_zeros_preserved'])
        self.assertEqual(cert['kind'],'certified_finite_operator_root_exclusion')
        root_check({'shape':c,'parameters':params,'zero_bridge':cert},defaultdict(int))

    def test_safe_operator_can_have_zero_cost_query_without_losing_its_bridge(self):
        c=g.shape([[0,Q(18233,2304)],[1,Q(-67,24)],[2,1]])
        params=['3','3','2'];res=g.residues(c,params)
        p={'shape':c,'parameters':params,'residues':res,'zero_bridge':root_certificate(c,params),'global_constants':g.global_constants(c,params,res)}
        self.assertTrue(p['zero_bridge']['all_right_half_ordinary_zeros_preserved'])
        f=g.frontier('2','1/2','1/16','1','0');cost=g.charge(p,f,{'2':'1'},[2])
        self.assertEqual(cost['status'],'query_kernel_or_numerator_zero_not_excluded')

    def test_larger_r_does_not_improve_normalized_zeta_exponents(self):
        for r in ['2','3','7/2','101/7']:
            weak=g.weak_actual(g.shape([[0,1]]),['3','1/3',r])
            self.assertEqual(Q(r)*Q(weak['growth_exponent']),1)
            self.assertFalse(weak['RH_strength'])
            f=g.frontier(r,'1/2','1/19','1/10007','7/101')
            self.assertEqual(Q(r)*Q(f['limit']),Q(1,2))
            self.assertFalse(f['constant_growth_in_q_restricted'])

    def test_general_reflection_chain_retains_all_height_scope(self):
        for r in [Q(2),Q(3),Q(7,2)]:
            beta,height=Q(3,4),Q(2**25);fixed=r/(r+1);path=reflection_path(beta,height,r,24)
            for j,row in enumerate(path):
                self.assertEqual(Q(row['distance_from_fixed_point']),(-1/r)**j*(beta-fixed))
                self.assertEqual(Q(row['height']),height/r**j)
                self.assertGreater(Q(row['real_part']),Q(1,2))

    def test_fractional_zero_constraints_are_complementary(self):
        self.assertEqual(exceptional_real_parts('3/2')['real_parts'],['3/4'])
        self.assertEqual(exceptional_real_parts('4/3')['real_parts'],['2/3','8/9'])
        self.assertEqual(reflection_path('3/4','17','3/2')[-1]['branch'],'critical_line_mask')
        self.assertEqual(reflection_path('8/9','17','4/3')[-1]['branch'],'critical_line_mask')
        c=g.shape([[0,1]])
        ps=[{'id':str(r),'zero_bridge':root_certificate(c,['3','2',str(r)]),'zero_exceptions':exceptional_real_parts(r)} for r in [Q(3,2),Q(4,3)]]
        self.assertTrue(complementary_certificate(ps)['RH_sufficient_if_every_member_uniform'])
        self.assertFalse(complementary_certificate(ps[:1])['RH_sufficient_if_every_member_uniform'])

    def test_incomplete_exception_sets_do_not_supply_a_bridge(self):
        self.assertFalse(exceptional_real_parts('10001/10000',8)['complete'])

    def test_invalid_domains_are_rejected(self):
        for params in [['1','1','2'],['3','0','2'],['3','1','1']]:
            with self.assertRaises(ValueError):g.parameters(*params)
        with self.assertRaises(ValueError):g.shape([[Q(1,2),1]])
        with self.assertRaises(ValueError):g.shape([[0,0]])
        with self.assertRaises(ValueError):g.reference_decay(g.shape([[0,1]]),['3','1','2'],0)


if __name__=='__main__':unittest.main()
