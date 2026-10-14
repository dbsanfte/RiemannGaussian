import copy
import unittest
import check_cancellation_cell_gram_program as I
import cancellation_cell_gram_program as B
class Replay(unittest.TestCase):
    def test_full_blocks(self):
        self.assertEqual(I.SPEC,B.SPEC)
        self.assertEqual(I.group_descriptors(),B.group_descriptors())
        for X in [1,2]:
            a=I.build_blocks(X);b=B.build_blocks(X);b.pop('construction_operations')
            self.assertEqual(a,b)
            self.assertEqual(len(a['blocks']),20)
            for name,d in I.group_descriptors().items():
                self.assertEqual(len(a['blocks'][name]),X*(1 if d['region']=='parent' else 2))
                if d['kind']=='divisor_cell':
                    for atoms in a['blocks'][name]:self.assertEqual(I.P.parse(atoms[1],4*X-1)[()],I.F(-1,2))
    def test_full_build_and_binding(self):
        program=dict(target='mu',q=6,C='32',claim='critical')
        for X in (1,2):
            out=B.build(program,X)
            self.assertTrue(I.check_builder(program,X,out)['verified'])
            out['gram_blocks']['cell_000'][0][1]=[]
            with self.assertRaises(ValueError):I.check_builder(program,X,out)
    def test_auxiliary(self):self.assertEqual(I.auxiliary(),B.auxiliary())
    def test_complete_preflight(self):
        with self.assertRaises(OverflowError):I.build_blocks(2,max_horizon=6)
        with self.assertRaises(ValueError):I.build_blocks(True)
if __name__=='__main__':unittest.main()
