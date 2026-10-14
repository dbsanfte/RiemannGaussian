import copy
from fractions import Fraction as F
import unittest
import affine_storage_moment_probe as A


def fixture(first='1',diagonal='0',child_count=1,parent_count=1):
    atoms=[[dict(m=[1],c='1')]]+[[] for _ in range(13)]
    blocks=[dict(full_child=[copy.deepcopy(atoms) for _ in range(child_count)],
                 full_parent=[copy.deepcopy(atoms) for _ in range(parent_count)])]
    matrices={}
    for name,multiplier in [('full_child',child_count),('full_parent',parent_count),('storage_K',child_count-4*parent_count)]:
        m=[['0']*14 for _ in range(14)];m[0][0]=str(F(diagonal)*multiplier)
        matrices[name]=dict(matrix=m)
    dual=dict(gram_specs=A.B.gram_specs(),gram_block_hashes=list(map(A.I.digest,blocks)),
              gram_duals=matrices,monomials=[dict(instance=0,m=m) for m in [[],[1],[1,1]]],
              weights=['0',first,diagonal])
    return blocks,[1],dual


class AffineProbe(unittest.TestCase):
    def test_zero_mass_nonzero_first_moment_invalidates_witness(self):
        result=A.moments(*fixture())
        self.assertEqual(result['status'],'witness_invalid_for_affine_cone')
        for row in result['groups'].values():
            self.assertEqual(row['quadratic_value'],row['full_polynomial_dot'])
            self.assertLess(F(row['quadratic_value']),0)
            self.assertEqual(len(row['direction']),15)
        self.assertFalse(result['larger_cone_feasibility_proved'])

    def test_zero_first_row_psd_extension(self):
        result=A.moments(*fixture(first='0'))
        self.assertEqual(result['status'],'witness_extends_to_affine_cone')
        self.assertEqual(set(result['groups']),set(A.B.gram_specs()))

    def test_unknown_not_implicit_zero_and_exact_cancellation(self):
        blocks,horizons,dual=fixture(child_count=4,parent_count=1)
        dual['monomials'].pop(1);dual['weights'].pop(1)
        result=A.moments(blocks,horizons,dual)
        self.assertEqual(result['status'],'unknown_missing_coordinates')
        self.assertEqual(result['groups']['full_parent']['status'],'unknown_missing_coordinates')
        self.assertEqual(result['groups']['storage_K']['status'],'PSD_extension')

    def test_source_domain_and_existing_moment_mismatch_rejected(self):
        blocks,horizons,dual=fixture()
        bad=copy.deepcopy(blocks);bad[0]['full_child']=[]
        with self.assertRaises(ValueError):A.moments(bad,horizons,dual)
        bad=copy.deepcopy(dual);bad['monomials'][1]=bad['monomials'][0]
        with self.assertRaises(ValueError):A.moments(blocks,horizons,bad)
        bad=copy.deepcopy(dual);bad['gram_duals']['full_child']['matrix'][0][0]='5'
        with self.assertRaises(ValueError):A.moments(blocks,horizons,bad)


if __name__=='__main__':unittest.main()
