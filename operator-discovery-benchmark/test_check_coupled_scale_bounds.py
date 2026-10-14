"""Exact synthetic programs and mutations; no arithmetic observations."""
import copy
from fractions import Fraction as F
import json
from pathlib import Path
import time
import unittest

import check_coupled_scale_bounds as C
from prime_bank_candidates import Meter


METER = Meter(cap=50000000, seconds=180)
STARTED = time.monotonic()


def term(state=0, divisor=1, exponent='1/6', coefficient='-1'):
    return dict(state=state, divisor=divisor, exponent=exponent, coefficient=coefficient)


def candidate(program=None, constant='0'):
    return dict(id='synthetic_program', program=[] if program is None else program,
                recurrence_C=constant)


class CoupledScaleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # This is the permitted frozen symbolic source-law premise only.
        # No old search, test suite, evidence or coefficient archive is run.
        path=Path(__file__).parent/'prime-cofactor-bound-results/pilot-001/search.json'
        cls.base=json.loads(path.read_text())['certificate']
        cls.context=C.prepare(cls.base,METER)

    def test_paid_boundary_helper_and_unit_cancellation(self):
        result=C.verify_candidate(self.context,candidate([term()]))
        self.assertTrue(result['verified'])
        self.assertEqual(result['paid_helper']['constant'],'15625/4')
        self.assertEqual(result['paid_head']['constant'],'0')
        self.assertEqual(result['paid_head']['affine_value'],['0','0'])
        row=result['paid_helper']['terms'][0]
        self.assertEqual(row['prefix_constant'],'125/4')
        self.assertEqual(row['scaled_energy_power'],'0')
        self.assertEqual(row['required_exponent'],'1/6')
        self.assertEqual(result['conditional_energy_bound']['constant'],'78125/2')
        self.assertEqual(result['conditional_energy_bound']['log_power'],0)
        self.assertEqual(result['conditional_energy_bound']['dyadic_covering_factor'],'5')
        self.assertFalse(result['recurrence_proved'])

    def test_divisor_below_one_retains_original_head(self):
        result=C.verify_candidate(self.context,candidate([term(divisor=2)]))
        self.assertEqual(result['paid_head']['constant'],'361/4')
        self.assertEqual(result['paid_head']['affine_value'],['-9/2','-1'])
        defect=result['open_recurrence']['defect_expansion']
        self.assertEqual(defect['prefix_below_one'],'0')
        self.assertTrue(defect['helper_unit_retained'])

    def test_positive_forcing_conditional_logs_constants_and_original_F_covering(self):
        result=C.verify_candidate(self.context,candidate([],constant='1/4096'))
        Chead=F(361,4)
        expected=2*Chead+F(147852,4096)
        self.assertEqual(F(result['conditional_F_dyadic']['constant']),expected)
        self.assertEqual(F(result['conditional_energy_bound']['constant']),65*expected)
        self.assertEqual(result['conditional_energy_bound']['log_power'],4)
        self.assertEqual(result['conditional_energy_bound']['covering_applies_to'],'complete original F only')
        self.assertTrue(result['conditional_energy_bound']['requires_open_recurrence'])
        self.assertEqual(result['epsilon_conversion']['factor'],'8*(1+24*epsilon^(-4))')

    def test_zero_forcing_is_stronger_but_still_conditional(self):
        result=C.verify_candidate(self.context,candidate())
        self.assertEqual(result['conditional_energy_bound']['constant'],'1805/2')
        self.assertEqual(result['conditional_energy_bound']['log_power'],0)
        self.assertEqual(result['conditional_G_dyadic']['forcing_constant'],'0')
        self.assertEqual(result['epsilon_conversion']['factor'],'1')
        self.assertTrue(result['conditional_energy_bound']['requires_open_recurrence'])
        self.assertFalse(result['whole_signed_bound_proved'])

    def test_coefficient_forcing_polynomial_witnesses_and_integer_divisor_gap(self):
        result=C.verify_candidate(self.context,candidate())
        forcing=result['forcing_provider']
        self.assertEqual(forcing['source_coefficient_constant'],'37/2')
        self.assertEqual(forcing['bound']['constant'],'36963')
        certificates=forcing['polynomial_nonnegative_certificates']
        self.assertEqual(next(v for v in certificates if v['polynomial']=='a-a^2')
                         ['bernstein_coefficients'],['0','1/2','0'])
        for e in range(12):
            METER.charge()
            gap=F((e+1)*(e+2)*(e+3),6)-(e+1)**2
            self.assertEqual(gap,F((e+1)*e*(e-1),6))
            self.assertGreaterEqual(gap,0)

    def test_fractional_257_and_every_other_state_gate(self):
        gamma=F(1,6)+F(1,257)
        program=[term(exponent=str(gamma))]+[term(i,exponent='1/2') for i in (1,2,3)]
        result=C.verify_candidate(self.context,candidate(program))
        self.assertEqual(result['paid_helper']['terms'][0]['exponent'],'263/1542')
        self.assertEqual(result['paid_helper']['terms'][0]['scaled_energy_power'],'-2/257')
        self.assertEqual([row['required_exponent'] for row in result['paid_helper']['terms']],
                         ['1/6','1/2','1/2','1/2'])
        for i,gamma in [(0,'251/1542'),(1,'1/3'),(2,'0'),(3,'1/257')]:
            with self.subTest(i=i),self.assertRaises(ValueError):
                C.verify_candidate(self.context,candidate([term(i,exponent=gamma)]))

    def test_complete_signed_defect_has_both_children_all_crosses_and_scale_powers(self):
        program=[term(exponent='263/1542',coefficient='-1/2'),
                 term(1,divisor=3,exponent='1/2',coefficient='1')]
        result=C.verify_candidate(self.context,candidate(program,constant='1/4'))
        defect=result['open_recurrence']['defect_expansion']
        self.assertEqual(len(defect['quadratic_terms']),18)
        self.assertTrue(defect['odd_child_endpoint_retained'])
        self.assertTrue(defect['variable_values_are_unweighted_prefixes'])
        self.assertEqual(defect['coefficient_square_forcing']['coefficient'],'-1')
        child_cross=next(t for t in defect['quadratic_terms']
            if t['factors']==['child_even:H0','child_even:H1'])
        self.assertEqual(child_cross['coefficient'],'-1')
        self.assertEqual(child_cross['X_power'],'-517/771')
        self.assertEqual(child_cross['scale_power'],'-517/771')
        self.assertEqual(child_cross['scale_base'],2)
        parent_cross=next(t for t in defect['quadratic_terms']
            if t['factors']==['parent:H0','parent:H1'])
        self.assertEqual(parent_cross['coefficient'],'4')
        self.assertEqual(parent_cross['scale_base'],1)
        for v in defect['variables']:
            if v['kind']=='explicit_prime_profile':
                self.assertIn(v['cutoff'],('ceil(sqrt(4*X))','ceil(sqrt(2*X))'))

    def test_complete_defect_symbolic_polynomial_identity_on_free_variables(self):
        # Artificial prefix symbols verify expansion, not source behavior.
        program=[term(exponent='1',coefficient='-1/2'),term(1,exponent='1',coefficient='2')]
        result=C.verify_candidate(self.context,candidate(program,constant='1/4'))
        defect=result['open_recurrence']['defect_expansion']
        X=F(8)
        values={v['id']:F(i+2) for i,v in enumerate(defect['variables'])}
        expanded=F(0)
        for t in defect['quadratic_terms']:
            METER.charge()
            expanded+=F(t['coefficient'])*X**int(F(t['X_power']))*\
                F(t['scale_base'])**int(F(t['scale_power']))*\
                values[t['factors'][0]]*values[t['factors'][1]]
        direct=F(0)
        for branch,scale,weight in [('child_even',2,1),('child_odd',2,1),('parent',1,-4)]:
            G=values[branch+':F']+sum(F(p['coefficient'])*values[branch+':H'+str(j)]/(scale*X)
                                     for j,p in enumerate(program))
            direct+=weight*G*G
        self.assertEqual(expanded,direct)

    def test_generic_norm_rule_countermodel_is_exact_and_scope_limited(self):
        result=C.verify_candidate(self.context,candidate())
        attempt=result['proof_attempt']
        self.assertEqual(attempt['status'],'GENERIC_ENVELOPE_RULE_REJECTED')
        model=attempt['exact_countermodel']
        X=int(model['X'])
        self.assertEqual(X&(X-1),0)
        self.assertEqual(model['source_unit'],'-13/2')
        exact=sum((F(n)-F(15,2))**2 for n in range(X,2*X))/X**2
        METER.charge(X)
        self.assertEqual(exact,F(7,3)*X-24+F(767,12*X))
        self.assertGreater(F(model['positive_margin']),0)
        self.assertFalse(model['all_prime_source_laws_satisfied'])
        self.assertFalse(model['actual_zeta_R_binding_satisfied'])
        self.assertFalse(model['actual_source_recurrence_refuted'])
        self.assertFalse(attempt['broader_arithmetic_proof_grammar_refuted'])

    def test_generic_countermodel_retains_nonzero_units_and_scaled_signed_helpers(self):
        proposal=candidate([term(exponent='1')],constant='2')
        result=C.verify_candidate(self.context,proposal)
        model=result['proof_attempt']['exact_countermodel']
        X=int(model['X']); u=F(model['helper_units'][0])
        self.assertNotEqual(u,0)
        self.assertEqual(u,F(-13,2))
        def energy(scale):
            return sum((F(n)-F(15,2)-u/F(scale))**2
                       for n in range(scale,2*scale))/scale**2
        difference=energy(2*X)-energy(X)
        METER.charge(3*X)
        actual_forcing=2*(4+F(161,4*X))
        self.assertGreater(difference,actual_forcing)
        self.assertGreaterEqual(difference,F(model['recurrence_defect_lower']))

    def test_candidate_canonical_rational_sign_and_schema_guards(self):
        for value in ('-1','0.1','2/12','1e999999999',0.1,True):
            with self.subTest(exponent=value),self.assertRaises(ValueError):
                C.verify_candidate(self.context,candidate([term(exponent=value)]))
        for value in ('-1','1.0',True):
            with self.subTest(C=value),self.assertRaises(ValueError):
                C.verify_candidate(self.context,candidate(constant=value))
        for key,value in [('state',True),('state',4),('divisor',0),('divisor',1.0),
                          ('coefficient','0'),('coefficient','2/2')]:
            p=term();p[key]=value
            with self.subTest(key=key,value=value),self.assertRaises(ValueError):
                C.verify_candidate(self.context,candidate([p]))
        p=candidate();p['recurrence_proved']=True
        with self.assertRaises(ValueError):
            C.verify_candidate(self.context,p)

    def test_context_and_complete_original_source_are_mandatory(self):
        with self.assertRaises(ValueError):
            C.verify_candidate(dict(verified=True),candidate())
        for mutation in ('drop_channel','change_weight','change_shift','drop_unit','truncate_tail'):
            bad=copy.deepcopy(self.base)
            if mutation=='drop_channel': bad['source']['channels'].pop()
            elif mutation=='change_weight': bad['source']['channels'][2]['weight']=['0','1']
            elif mutation=='change_shift': bad['source']['channels'][0]['atoms'][0]['shift']=3
            elif mutation=='drop_unit': bad['unit'].pop()
            else: bad['transfer'][0][0]['denominator']=[[0,0,'1']]
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):
                C.prepare(bad,METER)

    def test_open_premises_never_become_paid_and_cycles_are_rejected(self):
        result=C.verify_candidate(self.context,candidate())
        graph=result['dependency_graph']
        self.assertEqual(next(n for n in graph if n['id']=='full_signed_core')['status'],'OPEN')
        self.assertEqual(next(n for n in graph if n['id']=='conditional_recovery')['status'],'CONDITIONAL')
        self.assertEqual(result['open_recurrence']['status'],'OPEN')
        bad=copy.deepcopy(graph)
        next(n for n in bad if n['id']=='conditional_recovery')['status']='PROVED'
        with self.assertRaises(ValueError): C._verify_dependencies(bad)
        bad=copy.deepcopy(graph);bad[0]['requires']=['full_signed_core']
        with self.assertRaises(ValueError): C._verify_dependencies(bad)

    def test_publication_mutations_cannot_drop_cross_cutoff_or_original_F(self):
        proposal=candidate([term(coefficient='1'),term(1,exponent='1/2')],constant='1')
        result=C.verify_candidate(self.context,proposal)
        for mutation in ('cross','odd','cutoff','forcing','head','recovery','source','helper'):
            bad=copy.deepcopy(result)
            defect=bad['open_recurrence']['defect_expansion']
            if mutation=='cross': defect['quadratic_terms'].pop(1)
            elif mutation=='odd': defect['odd_child_endpoint_retained']=False
            elif mutation=='cutoff': defect['variables'][1]['cutoff']='ceil(sqrt(2*X))'
            elif mutation=='forcing': bad['forcing_provider']['bound']['constant']='1'
            elif mutation=='head': bad['paid_head']['constant']='0'
            elif mutation=='recovery': bad['conditional_energy_bound']['constant']='1'
            elif mutation=='source': bad['source_binding']['channels'].pop()
            else: bad['paid_helper']['constant']='0'
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):
                C.verify_result(self.context,proposal,bad)

    def test_publication_cannot_promote_generic_failure_or_conditional_core_to_proof(self):
        proposal=candidate();result=C.verify_candidate(self.context,proposal)
        for key in ('recurrence_proved','whole_signed_bound_proved','RH_proved',
                    'inherited_source_and_transport_obligations_discharged'):
            bad=copy.deepcopy(result);bad[key]=True
            with self.subTest(key=key),self.assertRaises(ValueError):
                C.verify_result(self.context,proposal,bad)
        bad=copy.deepcopy(result)
        bad['proof_attempt']['exact_countermodel']['actual_source_recurrence_refuted']=True
        with self.assertRaises(ValueError): C.verify_result(self.context,proposal,bad)
        bad=copy.deepcopy(result)
        bad['conditional_energy_bound']['requires_open_recurrence']=False
        with self.assertRaises(ValueError): C.verify_result(self.context,proposal,bad)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_coupled_scale_bounds operations='+str(METER.operations)+
          ' elapsed_seconds='+str(time.monotonic()-STARTED),flush=True)


if __name__=='__main__':
    unittest.main()
