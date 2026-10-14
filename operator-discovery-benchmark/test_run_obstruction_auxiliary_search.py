import unittest
from flint import arb,ctx
import run_obstruction_auxiliary_search as R

METERS=[]


class WorkflowChecks(unittest.TestCase):
    def setUp(self):ctx.prec=128;self.m=R.P.P.Meter();METERS.append(self.m)

    def test_argument_preserves_unknown_drift_and_equivalent_joint_bound(self):
        p=next(p for p in R.P.catalogue() if p.get('channel')=='V' and p.get('exponent')=='1/2')
        result=R.argument(p,'1','10',self.m)
        audit=result['verification']
        self.assertTrue(audit['validated']);self.assertFalse(audit['discharged_uniform_bound'])
        self.assertTrue(any('step' in row['members'] for row in audit['undischarged_leaves']))
        self.assertTrue(any(set(('target','joint','via_drift'))<=set(row['members']) for row in audit['equivalence_classes']))
        self.assertFalse(result['full_uniform_estimate_proved'])

    def test_complete_tight_finite_checks_reject_missing_or_wide_terms(self):
        row={'X':4,'energy':'1','cross':'-2'};actual={'X':4,'energy':arb(1),'cross':arb(-2)}
        R.compare(row,actual)
        with self.assertRaises(ValueError):R.compare(row,{'X':4,'energy':arb(1)})
        actual['cross']=arb('-2 +/- 0.001')
        with self.assertRaises(ArithmeticError):R.compare(row,actual)
        self.m.charge(50)

    def test_proof_reduction_precedes_numerical_constant_in_ranking(self):
        programs=[p for p in R.P.catalogue() if p.get('channel')=='V' and p.get('mode')=='shift']
        good=next(p for p in programs if p['exponent']=='1/2')
        unknown=next(p for p in programs if p['exponent']=='2/3')
        a=dict(program=good,constant='1000000',validation_score={'failed':2})
        b=dict(program=unknown,constant='0',validation_score={'failed':0})
        self.assertLess(R.P.rank(a),R.P.rank(b))
        self.assertFalse(good['uniform_bound_proved'])


def tearDownModule():
    print('SYNTHETIC_WORK module=test_run_obstruction_auxiliary_search operations='+str(sum(m.operations for m in METERS)))


if __name__=='__main__':unittest.main()
