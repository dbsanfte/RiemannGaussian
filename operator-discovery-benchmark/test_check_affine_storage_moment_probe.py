import copy
import unittest
import affine_storage_moment_probe as A
import check_affine_storage_moment_probe as C
from test_affine_storage_moment_probe import fixture


class Audit(unittest.TestCase):
    def test_independent_full_matrix_replay(self):
        for first in ['0','1','-1']:
            b,h,d=fixture(first=first);result=A.moments(b,h,d)
            self.assertTrue(C.verify(b,h,d,result)['verified'])

    def test_unknown_and_cancellation_replay(self):
        b,h,d=fixture(child_count=4,parent_count=1)
        d['monomials'].pop(1);d['weights'].pop(1)
        self.assertTrue(C.verify(b,h,d,A.moments(b,h,d))['verified'])

    def test_witness_matrix_direction_and_scope_corruption(self):
        b,h,d=fixture();original=A.moments(b,h,d)
        for field,value in [('matrix',[['0']*15 for _ in range(15)]),('direction',['0']*15),
                            ('missing',[dict(instance=0,m=[1])]),('full_polynomial_dot','0')]:
            bad=copy.deepcopy(original);bad['groups']['storage_K'][field]=value
            with self.assertRaises(ValueError):C.verify(b,h,d,bad)
        bad=copy.deepcopy(original);bad['larger_cone_feasibility_proved']=True
        with self.assertRaises(ValueError):C.verify(b,h,d,bad)


if __name__=='__main__':unittest.main()
