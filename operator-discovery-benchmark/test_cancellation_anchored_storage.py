import copy
import unittest
from fractions import Fraction as F
import cancellation_anchored_storage as A
import cancellation_anchored_storage_synthesis as S
import cancellation_complete_gram_program as B
import check_cancellation_anchored_storage as I


class StorageGrammarTests(unittest.TestCase):
    def test_full_sources_and_auxiliary_unchanged(self):
        program=dict(target='mu',q=6,C='32',claim='critical')
        out=A.build(program,1); old=B.build(program,1)
        self.assertEqual(I.SPEC,A.SPEC)
        self.assertTrue(I.check_builder(program,1,out)['verified'])
        for key in ('instance','dictionary_sha256','square_ids','relation_ids','cell_archive','gram_blocks'):
            self.assertEqual(out[key],old[key])
        self.assertEqual(A.auxiliary(),I.auxiliary())
        aux=A.auxiliary()
        self.assertEqual(aux['storage_blocks']['child'],[])
        self.assertEqual(aux['storage_blocks']['parent'],[])
        self.assertEqual(A.gram_specs(),dict(full_child=14,full_parent=14,storage_K=14))

    def test_complete_cross_constants_and_zero_embedding(self):
        grams={k:[['0']*14 for _ in range(14)] for k in A.gram_specs()}
        K=grams['storage_K']
        for i in (5,6):
            for j in (5,6):K[i][j]='1'
        budget=A.scalar_budget(grams,3)
        self.assertEqual(budget['storage_zKz'],'1')
        self.assertEqual(budget['storage_contribution'],'-6')
        self.assertEqual(budget['total'],I.scalar_budget(grams,3)['total'])
        K[5][6]=K[6][5]='-1'
        self.assertEqual(A.scalar_budget(grams,3)['storage_contribution'],'0')
        regional={k:grams[k] for k in B.gram_specs()}
        embedded=A.embed_base_grams(regional)
        self.assertEqual(embedded['storage_K'],[['0']*14 for _ in range(14)])
        self.assertEqual(A.scalar_budget(embedded,3)['total'],B.scalar_budget(regional,3)['total'])

    def test_sign_orientation_and_complete_domain(self):
        built=A.build(dict(target='mu',q=6,C='32',claim='critical'),1)
        inst,blocks,storage=[built['instance']],[built['gram_blocks']],[built['storage_blocks']]
        cols,lhs,ms,shape,offset,_,specs=S.prepare(inst,blocks,storage)
        independent=I.coefficient_system(inst,blocks,storage,specs)
        flat=lambda p:{(k,)+m:q for (k,m),q in p.items()}
        self.assertEqual(cols,[flat(p) for p in independent['columns']])
        self.assertEqual(lhs,flat(independent['lhs']))
        self.assertEqual(ms,sorted((k,)+m for k,m in independent['domain']))
        for j in range(105):
            expected=dict(cols[offset+j])
            for m,q in cols[offset+105+j].items():expected[m]=expected.get(m,F(0))-4*q
            self.assertEqual(cols[offset+210+j],{m:q for m,q in expected.items() if q})
        wrong=copy.deepcopy(storage);wrong[0]['parent_multiplier']='4'
        with self.assertRaises(ValueError):S.prepare(inst,blocks,wrong)
        wrong=copy.deepcopy(storage);wrong[0]['kind']='nonnegative_SOS'
        with self.assertRaises(ValueError):S.prepare(inst,blocks,wrong)
        wrong=copy.deepcopy(storage);wrong[0]['parent'][0][13]=[]
        with self.assertRaises(ValueError):S.prepare(inst,blocks,wrong)

    def test_nonzero_K_anchor(self):
        K=[['0']*14 for _ in range(14)];K[1][1]='1'
        R=A.anchored_matrix(K)
        self.assertEqual(R,I.anchored_matrix(K))
        self.assertEqual(R[0][0],'1');self.assertEqual(R[1][1],'1')
        K[1][1]='-1'
        with self.assertRaises(ValueError):A.anchored_matrix(K)

if __name__=='__main__':unittest.main()
