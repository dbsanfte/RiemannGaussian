import copy
import unittest
from fractions import Fraction as F
import cancellation_affine_storage as A
import cancellation_affine_storage_synthesis as S
import cancellation_anchored_storage as OLD
import cancellation_complete_gram_program as B
import grouped_arithmetic_language as L


def zero_grams():return {name:[['0']*15 for _ in range(15)] for name in A.gram_specs()}


class AffineGrammarTests(unittest.TestCase):
    def test_original_scalars_and_entire_rows(self):
        program=dict(target='mu',q=6,C='32',claim='critical')
        out=A.build(program,1);base=B.build(program,1)
        for key in ('instance','dictionary_sha256','square_ids','relation_ids','cell_archive'):
            self.assertEqual(out[key],base[key])
        self.assertEqual(len(out['instance']['square_groups']),366)
        self.assertEqual(len(out['instance']['relation_groups']),403)
        for name,rows in out['gram_blocks'].items():
            self.assertTrue(all(len(row)==15 for row in rows))
            self.assertTrue(all(L.load_poly(row[0])=={():F(1)} for row in rows))
            self.assertEqual([row[1:] for row in rows],base['gram_blocks'][name])
        self.assertEqual(A.SPEC['anchor_index'],1)
        self.assertEqual(A.SPEC['atoms'],['unit']+B.SPEC['atoms'])
        self.assertEqual(A.auxiliary()['instance'],B.auxiliary()['instance'])
        self.assertTrue(all(not rows for rows in A.auxiliary()['gram_blocks'].values()))
        self.assertEqual(A.auxiliary()['storage_blocks']['child'],[])

    def test_formal_constants_cross_and_actual_initial_state(self):
        grams=zero_grams()
        for name in grams:
            for i in (0,6):
                for j in (0,6):grams[name][i][j]='1'
        budget=A.scalar_budget(grams,4)
        self.assertEqual(budget['storage_zKz'],'1/4')
        self.assertEqual([r['contribution'] for r in budget['ledger']],['2','1','-2'])
        self.assertEqual(budget['total'],'1')
        K=zero_grams()['storage_K'];K[0][0]='1'
        self.assertEqual(A.initial_cost(K)['anchored_initial_cost'],'2')
        self.assertEqual(A.initial_cost(K)['actual_initial_vector'],['1','1','0','0','1']+['0']*10)
        R=A.anchored_matrix(K)
        self.assertEqual(R[0][0],'1');self.assertEqual(R[1][1],'1')
        K[0][0]='-1'
        with self.assertRaises(ValueError):A.anchored_matrix(K)

    def test_old_to_new_embedding_preserves_scalar_budget_and_initial_cost(self):
        old={name:[['0']*14 for _ in range(14)] for name in OLD.gram_specs()}
        for name in old:old[name][5][5]='2'
        embedded=A.embed_anchored_grams(old)
        self.assertEqual(A.scalar_budget(embedded,7)['total'],OLD.scalar_budget(old,7)['total'])
        self.assertEqual(embedded['storage_K'][6][6],'2')
        self.assertEqual(embedded['storage_K'][0],['0']*15)
        self.assertEqual(A.initial_cost(embedded['storage_K'])['anchored_initial_cost'],'1')
        regional={name:old[name] for name in B.gram_specs()}
        self.assertEqual(A.scalar_budget(A.embed_base_grams(regional),7)['total'],B.scalar_budget(regional,7)['total'])

    def test_all_upper_columns_sign_factor_two_and_auxiliary(self):
        program=dict(target='mu',q=6,C='32',claim='critical')
        out=A.build(program,1);aux=A.auxiliary()
        instances=[out['instance'],aux['instance']]
        blocks=[out['gram_blocks'],aux['gram_blocks']]
        storage=[out['storage_blocks'],aux['storage_blocks']]
        cols,lhs,ms,shape,offset,_,specs=S.prepare(instances,blocks,storage)
        self.assertEqual(len(cols)-offset,360)
        self.assertEqual(shape,(366,403))
        for j in range(120):
            expected=dict(cols[offset+j])
            for m,q in cols[offset+120+j].items():expected[m]=expected.get(m,F(0))-4*q
            self.assertEqual(cols[offset+240+j],{m:q for m,q in expected.items() if q})
            self.assertTrue(all(m[0]==0 for m in cols[offset+j]))
        self.assertEqual(cols[offset][(0,)],2)
        self.assertEqual(cols[offset+120][(0,)],1)
        self.assertEqual(cols[offset+240][(0,)],-2)
        self.assertEqual(cols[offset+1][(0,1)],4)
        wrong=copy.deepcopy(storage);wrong[0]['parent_multiplier']='4'
        with self.assertRaises(ValueError):S.prepare(instances,blocks,wrong)
        wrong=copy.deepcopy(blocks);wrong[0]['full_child'][0]=wrong[0]['full_child'][0][1:]
        with self.assertRaises(ValueError):S.prepare(instances,wrong,storage)


if __name__=='__main__':unittest.main()
