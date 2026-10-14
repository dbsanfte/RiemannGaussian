import copy
from fractions import Fraction as Q
import unittest

import numpy as np

import coupled_scale_bounds as P


def fixture():
    # Synthetic profile; no source values, trained winner, or archive access.
    return dict(states=[{'synthetic':True}],frontier_bounds=[dict(state=0,r='1/3',
        unit_ceiling='2',coefficient_ceiling='1')],source={'synthetic':True})


class CoupledProposals(unittest.TestCase):
    def test_paid_threshold_and_fractional_language(self):
        p=P.helper_primitives(fixture())[0]
        self.assertEqual(p['minimum_gamma'],'1/6')
        self.assertEqual(p['energy_constant'],'49')
        plan=P.exponent_plan()
        self.assertIn('1/257',plan['candidates'])
        self.assertIn('1/7',plan['candidates'])
        _,terms=P.dictionary(fixture(),[{'state':0,'divisor':2}],['1/257'])
        self.assertEqual(terms[0]['term']['exponent'],str(Q(1,6)+Q(1,257)))
        self.assertTrue(terms[0]['extended_fractional'])

    def test_exact_inputs_and_unpriced_log(self):
        for bad in (0.5,True,'2/4'):
            with self.assertRaises(ValueError):P.rational(bad)
        b=fixture();b['frontier_bounds'][0]['r']='1'
        with self.assertRaises(ValueError):P.helper_primitives(b)

    def test_training_does_not_read_final(self):
        target=np.ones(18);D=np.ones(17);H=np.zeros(18)
        EG=np.arange(18,dtype=float)
        m=P._metrics(EG,H,target,D)
        changed=EG.copy();changed[12:]=1e12
        other=P._metrics(changed,H,target,D)
        self.assertEqual(m['C_index'].tolist(),other['C_index'].tolist())
        self.assertEqual(m['required'].tolist(),other['required'].tolist())

    def test_padding_is_not_cancellation(self):
        target=np.ones(18);D=np.ones(17);H=1e4/np.array(P.SCALES)
        m=P._metrics(target+H,H,target,D)
        self.assertEqual(m['required'][0],0)
        self.assertGreater(m['padding'][0],1)

    def test_complete_pair_cross_can_cancel(self):
        # Test the producer's scored/returned programs against direct signed
        # vectors, including a selected two-term program; dropping one cross
        # in either scoring or reconstruction must disagree with this oracle.
        b=fixture();features=[{'state':0,'divisor':d} for d in P.DIVISORS]
        values=np.array([[2.,1.,-1.,.5],[1.,2.,-2.,1.]])
        gram=values.T@values
        evidence=dict(features=features,blocks=[dict(X=X,gram=gram.tolist(),D=1. if k<17 else None)
                                              for k,X in enumerate(P.SCALES)])
        result=P.search(b,evidence,dict(candidates=['0']))
        candidates={c['id']:c for c in result['candidates']}
        self.assertTrue(any(len(c['program'])==2 for c in candidates.values()))
        for selected in result['selection']:
            program=candidates[selected['candidate_id']]['program']
            for row in selected['energies']:
                X=row['X'];auxiliary=np.zeros(2)
                for term in program:
                    auxiliary+=float(Q(term['coefficient']))*X**(-float(Q(term['exponent'])))*values[:,term['divisor']]
                direct=values[:,0]+auxiliary
                self.assertAlmostEqual(row['EG'],float(direct@direct),places=10)
                self.assertAlmostEqual(row['EH'],float(auxiliary@auxiliary),places=10)

    def test_exhaustive_small_search_and_scale_guard(self):
        b=fixture();features=[{'state':0,'divisor':d} for d in P.DIVISORS]
        v=np.array([2.,1.,-.5,.25]);G=np.outer(v,v)
        evidence=dict(features=features,blocks=[dict(X=X,gram=G.tolist(),D=1. if k<17 else None)
                                              for k,X in enumerate(P.SCALES)])
        r=P.search(b,evidence,dict(candidates=['0']))
        #18 terms;15 same-key coefficient pairs per feature excluded.
        self.assertEqual(r['coverage']['pair_programs'],18*17//2-3*15)
        self.assertEqual(len(r['term_dictionary']),18)
        self.assertFalse(r['ranking_uses_validation_or_final'])
        self.assertFalse(r['whole_signed_bound_proved'])
        self.assertLessEqual(len(r['candidates']),6)
        self.assertTrue(all(c['recurrence_C'] in P.RECURRENCE_CONSTANTS for c in r['candidates']))
        bad=copy.deepcopy(evidence);bad['blocks'].pop()
        with self.assertRaises(ValueError):P.search(b,bad,dict(candidates=['0']))


if __name__=='__main__':unittest.main()
