"""Focused independent arithmetic contracts; run-schema tests follow binding."""
from fractions import Fraction
import unittest
import check_signed_arithmetic_search as c


class IndependentArithmeticContracts(unittest.TestCase):
    def test_factor_prefix_and_actual_positive_boundary(self):
        data=c.factor_prefix(16)
        self.assertEqual(data['mu'][1:9],[1,-1,-1,0,-1,1,-1,0])
        self.assertEqual(data['liouville'][1:9],[1,-1,-1,1,-1,1,-1,-1])
        r=c.block_energy(c.prefix(data['mu']),2)
        self.assertEqual((r['A_X'],r['A_2X'],r['Delta']),(1,10,6))

    def test_liouville_floor_sum_finite_calibration(self):
        values=c.factor_prefix(64)['liouville']
        for N in range(65):
            # Direct square enumeration is independent of root rounding.
            squares=sum(k*k<=N for k in range(1,N+1))
            self.assertEqual(c.liouville_floor_sum(values,N),squares)

    def test_full_rational_ceiling_and_exact_inputs(self):
        self.assertEqual(c.ceil_power(2,'3/2'),3)
        self.assertEqual(c.ceil_power(4,'3/2'),8)
        self.assertEqual(c.ceil_power(2,'1/1000000'),2)
        for bad in (True,0.5):
            with self.assertRaises(ValueError):c.rational(bad)
        with self.assertRaises(ValueError):c.block_energy([0,1],2)

    def test_shared_primitive_projection_complete_at_small_cutoff(self):
        mu=c.factor_prefix(16)['mu']
        rows=c.basis_profile(mu,2,[1,2],B=8)
        for row in rows:
            self.assertEqual(row['A'],row['diagonal']+row['projection'])
        # Direct p0 moment cancels for the critical parent-child stencil.
        kernel=c.kernel_from_terms([[1,-4],[2,1]])
        self.assertEqual(c.integral_moment(kernel),0)
        self.assertEqual(c.integral_moment(c.kernel_from_terms([[1,1]])),Fraction(3,2))

    def test_kernel_bound_accepts_rigorous_enclosure_rejects_undercharge(self):
        kernel=c.kernel_from_terms([[1,-4],[2,1]])
        record={'kernel':kernel,'kernel_sha256':c.digest(kernel),'exact_integral':'0',
            'left_endpoint':'-2','right_endpoint':'0','left_endpoint_zero':False,
            'right_endpoint_zero':True,'left_discrepancy_zero':True,
            'admitted_zero_moment_component':True,'full_signed_bound_proved':False,
            'segments':[
              {'a':'0','b':'1','slope':'0','sqrt_a':['0','0'],'sqrt_b':['1','1'],'weighted_variation_upper':'0'},
              {'a':'1','b':'2','slope':'4','sqrt_a':['1','1'],'sqrt_b':['1','2'],'weighted_variation_upper':'8'},
              {'a':'2','b':'4','slope':'-1','sqrt_a':['1','2'],'sqrt_b':['2','2'],'weighted_variation_upper':'4'}],
            'weighted_sqrt_variation_upper':'12'}
        self.assertTrue(c.verify_kernel_certificate(record,[[1,-4],[2,1]]))
        record['weighted_sqrt_variation_upper']='11'
        self.assertFalse(c.verify_kernel_certificate(record))

    def test_absent_protocol_fails_closed(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):c.audit_run(directory)


    def test_huge_root_plateau_and_ast_semantics(self):
        self.assertEqual(c.floor_root(384,10**100),1)
        node={'op':'prefix','args':[{'op':'mu','args':[],'params':{}}],'params':{}}
        self.assertEqual(c.ast_values(node,8),c.prefix(c.factor_prefix(8)['mu']))

    def test_moving_cutoff_coupled_identity(self):
        for X in (1,2,4,8,16):
            r=c.coupled_numeric(X)
            self.assertTrue(r['all_prefix_coefficients_recovered'])
            self.assertEqual(r['identity_residual'],0)
            self.assertLessEqual(r['negative_low_prefix_credit'],0)

    def test_fresh_cases_unique_and_claim_domain(self):
        cases=c.final_design('0'*64)
        self.assertEqual(len(set(cases['actual_scales'])),6)
        self.assertEqual(len(set(cases['calibration_indices'])),5)
        candidate={'program':{'scales':[1],'weights':['1']},'constants':{'2':'1'}}
        rows=[{'X':3,'shared_primitive_cutoff':1,'basis':[{'energy':1,'diagonal':1,'primitive_projection':0}]}]
        self.assertFalse(c.stencil_score(candidate,rows,[2])['cases'][0]['in_dyadic_claim_domain'])

    def test_ast_coefficients_and_metrics_are_independent(self):
        expression={'op':'mu','args':[],'params':{}}
        identifier=c.digest(expression);values=c.factor_prefix(8)['mu'];s=sum(values);u=sum(map(abs,values));sq=sum(v*v for v in values);g=u-abs(s)
        cost={'operations':1,'allocated_cells':9,'evaluated_nodes':1,'peak_coefficient_bits':2,'limits':{'operations':5000000,'cells':2000000,'bits':1000000,'nodes':1024}}
        record={'program_id':identifier,'expression':expression,'status':'available','global_actual_signed_bound_proved':False,'exploratory_not_full_RH_target':True,
                'arithmetic':{'coefficients':values,'cost':cost},'metric_operations':43,'total_charged_operations':44,
                'metrics':{'signed_mass':str(s),'unsigned_mass':str(u),'square_mass':str(sq),'cancellation_gain':str(g),'cancellation_gain_ratio':str(Fraction(g,u)),'nontrivial_unsigned_mass':True}}
        block={'N':8,'observations':[record],'available_cases':1,'missing_cases':0,'invalid_cases':0,'global_actual_signed_bound_proved':False}
        programs=[{'expression':expression,'program_id':identifier}]
        self.assertEqual(c.audit_ast(block,programs,8)['available'],1)
        record['arithmetic']['coefficients'][7]=1
        with self.assertRaises(ValueError):c.audit_ast(block,programs,8)

    def test_invalid_atom_parameters_rejected(self):
        with self.assertRaises(ValueError):c.ast_values({'op':'mu','args':[],'params':{'unexpected':1}},8)

    def test_positive_transform_recovers_energy_conditionally(self):
        terms=[[1,-4],[2,1],[4,-4],[8,1]]
        record={'terms':[[str(s),str(v)] for s,v in terms],'epsilon':'1/12','signed_inequality_proved':False,'RH_proved':False,
            'status':'available','shift_polynomial_coefficients':['-4','1','-4','1'],'factor_coefficients':['1','0','1'],
            'factor_terms':[[1,'1'],[2,'0'],[4,'1']],'exact_constant_remainder':'0','quadratic_moment':'0','factorization_admitted':True,
            'factor_coefficients_nonnegative_nonzero':True,'conditional_bridge_admitted':True,'unsigned_factor_coefficient_l1':'2',
            'symbolic_cells_charged':7,'symbolic_order':3,'max_order':256,'recovery_index':0,'recovery_scale':1,'recovery_coefficient':'1'}
        self.assertTrue(c.verify_positive_energy_transform(record,terms))
        record['recovery_coefficient']='0'
        self.assertFalse(c.verify_positive_energy_transform(record,terms))

if __name__=='__main__':unittest.main()
