import copy
import unittest
import cancellation_divisor_coupling as D
import check_cancellation_divisor_coupling as C

class CouplingTests(unittest.TestCase):
    def test_complete_calibration(self):
        for weights in [['1'],['0'],['-3/2','0','2/3','-1','0','1/7'],['0','1','-2','0']]:
            out=D.build_coupling(len(weights),weights);self.assertTrue(C.check_coupling(len(weights),weights,out)['verified'])
    def test_mutations(self):
        w=['-2','0','1/3','2'];original=D.build_coupling(4,w)
        for kind in ['unit','cross','pair','zero','constant','claim']:
            out=copy.deepcopy(original)
            if kind=='unit':out['normalization_certificate']['relations'][0]['multiplier']=[]
            if kind=='cross':out['square_polynomial'].pop()
            if kind=='pair':out['source']['pairs'].pop()
            if kind=='zero':out['source']['blocks'][1]['divisors']=[]
            if kind=='constant':out['scalar_minus_c_squared']=[]
            if kind=='claim':out['global_bound_proved']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError):C.check_coupling(4,w,out)
    def test_limits(self):
        out=D.build_coupling(1,['1'])
        for args in [dict(horizon=True,weights=['1']),dict(horizon=2,weights=['1']),dict(horizon=1,weights=[True]),dict(horizon=1,weights=['1e999999']),dict(horizon=1,weights=['1'],target='c'),dict(horizon=1,weights=['1'],max_operations=1)]:
            with self.subTest(args=args),self.assertRaises((ValueError,OverflowError)):C.check_coupling(output=out,**args)

if __name__=='__main__':unittest.main()
