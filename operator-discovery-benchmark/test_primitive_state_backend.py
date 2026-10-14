import copy
import unittest
import cancellation_primitive_state_backend as B
import cancellation_primitive_state_localizers as L
import check_cancellation_primitive_state_localizers as C


def fixture(primal=False):
    unit=[dict(m=[],c='1')];x=[dict(m=[1],c='1')]
    row=[unit,x]+[[] for _ in range(13)]
    blocks=[dict(full_child=[] if primal else [row],full_parent=[row] if primal else [])]
    storage=[L.BASE.storage_transport(blocks[0])]
    inst=dict(target='mu',horizon=1,lhs=[dict(m=[1,1],c='-1')],square_groups=[],relation_groups=[])
    return [inst],blocks,storage


class Backend(unittest.TestCase):
    def test_complete_exact_dual_with_new_grammar_binding(self):
        inputs=fixture();saved=[]
        result=B.propose(*inputs,on_checkpoint=saved.append,time_limit=360)
        self.assertEqual(result['status'],'exact_separator')
        self.assertEqual(result['grammar_hash'],L.digest(L.SPEC))
        self.assertEqual(result['proposal_checkpoint']['grammar_hash'],result['grammar_hash'])
        self.assertTrue(all(c['grammar_hash']==result['grammar_hash'] for c in saved))
        self.assertTrue(C.verify_dual(*inputs,L.gram_specs(),result)['verified'])

    def test_signed_primal_admission_and_checkpoint_binding(self):
        inputs=fixture(True)
        result=B.synthesize(*inputs,row_normalization=True,max_exact_cells=4000000,time_limit=360)
        self.assertEqual(result['status'],'finite_PSD_certificate')
        self.assertTrue(C.verify_primal(*inputs,L.gram_specs(),result)['verified'])
        self.assertNotEqual(result['grams']['storage_K'][1][1],'0')
        bad=copy.deepcopy(result);bad['grammar_hash']=B.S.digest(B.A.SPEC)
        with self.assertRaises(ValueError):C.verify_primal(*inputs,L.gram_specs(),bad)

    def test_bad_grammar_and_verification_cannot_promote(self):
        with self.assertRaises(ValueError):B.translated(dict(grammar_hash='bad'))
        result=B.propose(*fixture(),time_limit=360,verification_callback=lambda *args:dict(verified=False))
        self.assertFalse(result.get('certified'))
        self.assertEqual(result['status'],'uncertified')


if __name__=='__main__':unittest.main()
