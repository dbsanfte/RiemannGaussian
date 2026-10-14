import copy
import unittest

import check_global_multiplier_bounds as C


class ExactMultiplierReplay(unittest.TestCase):
    def test_singular_psd_and_indefinite_rejection(self):
        self.assertTrue(C.psd([['1','-1'],['-1','1']])['PSD'])
        self.assertTrue(C.psd([['0','0'],['0','1']])['PSD'])
        for m in ([['0','1'],['1','0']],[['1','2'],['2','1']]):
            with self.assertRaises(ValueError):C.psd(m)

    def test_exact_multiplier_bound_and_mutations(self):
        # On x+y=0, y²-x²=0; complete multiplier removes this indefinite form.
        form=[['-1','0'],['0','1']];L=[['1','1']]
        cert=dict(status='exact_PSD_modulo_relations',form=form,relations=L,
            PSD=[['0','0'],['0','0']],multipliers=[['-1/2','1/2']],uniform_bound_proved=False)
        self.assertTrue(C.verify_quadratic(form,L,cert)['verified'])
        for mutation in ('cross','forcing','scope'):
            bad=copy.deepcopy(cert)
            if mutation=='cross':bad['PSD'][0][1]='1'
            elif mutation=='forcing':bad['multipliers'][0][0]='0'
            else:bad['uniform_bound_proved']=True
            with self.assertRaises(ValueError):C.verify_quadratic(form,L,bad)

    def test_negative_witness_is_scoped_to_relaxation(self):
        r=C.verify_formal_witness([['-1','0'],['0','0']],[['1','1']],['1','-1'])
        self.assertEqual(r['value'],'-1')
        self.assertFalse(r['actual_arithmetic_counterexample'])
        with self.assertRaises(ValueError):
            C.verify_formal_witness([['-1','0'],['0','0']],[['1','1']],['1','0'])


if __name__=='__main__':unittest.main()
