import copy
import unittest
from fractions import Fraction as Q
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

import mobius_count_control_076 as P
import check_mobius_count_control_076 as C


class Integration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=dict(grid=80,theta=['1/2','17/31','7/8'],multipliers=[2,3,6])
        cls.data=P.S.make_data(cls.spec,list(range(65,801)))
        cls.admission=C.F.verify_data(cls.data)

    def test_learned_mixed_power_program_independently_admitted(self):
        self.assertEqual(self.admission['status'],'VERIFIED')
        atoms=P.grammar(self.spec,['1/2','17/31','1'],'joint')
        proposed=P.fit_operator(self.data,atoms,'33/32','1/2',64,P.S.Meter())
        p=P.make_program(self.data,proposed['atoms'],proposed['coefficients'],'33/32','structural_cauchy',64,12)
        result=C.verify_program(p,self.data)
        self.assertEqual(result['status'],'VERIFIED_ON_FINITE_DOMAIN',result)
        self.assertTrue(result['universal_correlation_proved'])
        self.assertTrue(result['conditional_induction_verified'])
        self.assertFalse(result['uniform_source_bound_proved'])
        self.assertEqual([x['lemma'] for x in P.obligations(p,result)],['innovation'])

    def test_repeated_column_arbitrary_power_program(self):
        atoms=[dict(column=0,gamma='1/2'),dict(column=0,gamma='1001/1000'),dict(column=2,gamma='0')]
        p=P.make_program(self.data,atoms,[Q(1,16),Q(-1,32),Q(1,8)],'129/128','structural_cauchy',64,12)
        result=C.verify_program(p,self.data)
        self.assertEqual(result['status'],'VERIFIED_ON_FINITE_DOMAIN',result)
        base=P.make_program(self.data,[],[],'129/128','structural_cauchy',64,12)
        d=P.diagnostics(p,base)
        self.assertTrue(d['repeated_source_columns'])
        self.assertEqual(Q(d['complete_bound_ratio']),Q(p['bound_B'])/Q(base['bound_B']))

    def test_low_gamma_requires_arithmetic_lemma(self):
        atoms=[dict(column=0,gamma='1/3')]
        with self.assertRaises(ValueError):P.make_program(self.data,atoms,[Q(1,8)],'1','structural_cauchy',64)
        p=P.make_program(self.data,atoms,[Q(1,8)],'1','arithmetic_claim',64)
        result=C.verify_program(p,self.data)
        self.assertFalse(result['universal_correlation_proved'])
        self.assertNotEqual(result['status'],'INVALID',result)
        self.assertEqual({x['lemma'] for x in P.obligations(p,result)},{'innovation','correlation'})

    def test_old_failure_cannot_be_overwritten_by_new_finite_pass(self):
        p=P.make_program(self.data,[],[],'1','structural_cauchy',64)
        evaluation=dict(universal_correlation_proved=True,failures=[
            dict(u=70,lemma='innovation',status='UNRESOLVED_ROUNDING'),
            dict(u=71,lemma='innovation',status='REFUTED')])
        leaf=P.obligations(p,evaluation)[0]
        self.assertEqual(leaf['status'],'FINITE_COUNTEREXAMPLE')
        self.assertEqual(leaf['first_witness']['u'],71)

    def test_complete_runner_pipeline_and_final_gate(self):
        import run_mobius_count_control_076 as R
        spec=dict(R.SPEC,source=self.spec,q=['1'],base_u=64,precision=12,
                  certified_gammas=['1/2'],open_gammas=['1/3','1/2'],
                  certified_radii=['1/2'],open_radii=['1/2'],phases=[0,1])
        record=dict(id='test',shape=['1','0','0','0','0'],kind='prime_only',
                    adaptation_correlation=dict(status='REFUTED'))
        feedback=P.F.generate_feedback([record],self.spec,exponents=('1/3','1/2'))
        admission=dict(source_admission=self.admission,source_spec=self.spec,
                       scales=[r['u'] for r in self.data['rows']])
        with tempfile.TemporaryDirectory() as tmp,patch.object(R,'OUT',Path(tmp)),patch.object(R,'SPEC',spec):
            R.write(Path(tmp)/'discovery_data.json',self.data)
            R.write(Path(tmp)/'discovery_source_admission.json',admission)
            R.write(Path(tmp)/'input_feedback075.json',feedback)
            R.initialize_worker()
            summary=R.candidate_task('1')
            before=(Path(tmp)/summary['file']).read_bytes()
            saved=json.loads(before)
            eligible=[p for p in saved['programs'] if p['discovery_eligible']]
            self.assertTrue(eligible)
            R.source_phase('adaptation',R.scales([11,12]))
            evaluation=R.evaluation_task(('adaptation',eligible[0]))
            self.assertNotEqual(evaluation['evaluation']['status'],'INVALID')
            rejected=dict(eligible[0],adaptation_status='REFUTED')
            with self.assertRaises(ValueError):R.evaluation_task(('final',rejected))
            self.assertEqual((Path(tmp)/summary['file']).read_bytes(),before)
            self.assertFalse(evaluation['uniform_source_bound_proved'])


if __name__=='__main__':unittest.main()
