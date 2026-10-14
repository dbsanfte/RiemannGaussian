"""Synthetic universal proof producer calibrations; no finite grid proof."""
import copy
import time
import unittest
import parametric_arithmetic_identity as P
import check_parametric_arithmetic_identity as C

CONTEXT={'integer_parameters':[{'name':'X','lower':1}], 'functions':[{'name':'rho','arity':1,'definition_hash':'a'*64}]}

class ProducerTests(unittest.TestCase):
    def verify(self,p,a,b):
        r=p.prove(p.from_tree(a),p.from_tree(b))
        self.assertEqual(r['status'],'proved',r.get('reason'))
        self.assertTrue(C.verify_certificate(r)['verified'])
        return r
    def test_ring_discovered_cancellation(self):
        p=P.Producer(CONTEXT);a=['symbol','rho',['v','X']]
        self.verify(p,['mul',['add',a,['q','2']],['add',a,['q','-2']]],['add',['mul',a,a],['q','-4']])
    def test_rational_constant_normalization(self):
        self.verify(P.Producer(CONTEXT),['q','2'],['add',['q','1/3'],['q','5/3']])
    def test_all_root_partition_parameters(self):
        for theta in ['1/3','1/2','2/3','1/6']:
            for rounding in ['floor','ceiling']:
                p=P.Producer(CONTEXT);cut=['scaled_root',rounding,'3/2',theta,['v','X']]
                body=['mul',['ratio',['int',1],['v','a']],['x',['v','a']]]
                a=['sum','a',['int',1],['v','X'],body]
                b=['add',['sum','a',['int',1],['v','X'],['guard',['le',['v','a'],cut],body]],['sum','a',['int',1],['v','X'],['guard',['lt',cut,['v','a']],body]]]
                self.verify(p,a,b)
    def test_nested_capture_free_alpha(self):
        a=['sum','a',['int',1],['v','X'],['sum','b',['int',1],['v','a'],['mul',['x',['v','a']],['x',['v','b']]]]]
        b=['sum','u',['int',1],['v','X'],['sum','v',['int',1],['v','u'],['mul',['x',['v','v']],['x',['v','u']]]]]
        self.verify(P.Producer(CONTEXT),a,b)
    def test_explicit_partition_and_range(self):
        for range_rule in [False,True]:
            p=P.Producer(CONTEXT);a=p.from_tree(['sum','a',['int',1],['v','X'],['x',['v','a']]])
            cut=p.from_tree(['max',['int',1],['v','X']])
            if range_rule:b,k=p.range_split(a,cut)
            else:b,k=p.partition(a,p.from_tree(['le',['v','a'],['v','X']],('a',)))
            self.assertTrue(C.verify_certificate(p.certificate(a,b,k))['verified'])
    def test_explicit_factor_pull(self):
        p=P.Producer(CONTEXT);factor=p.from_tree(['symbol','rho',['v','X']],('a',));body=p.from_tree(['x',['v','a']],('a',))
        a=p.node('sum',[p.node('int',data={'value':1}),p.from_tree(['v','X']),p.mul(factor,body)],{'binder':'a'})
        b,k=p.pull_factor(a,factor,body);self.assertTrue(C.verify_certificate(p.certificate(a,b,k))['verified'])
    def test_wrong_cut_and_uncertified_identity_unknown(self):
        p=P.Producer(CONTEXT)
        a=p.from_tree(['guard',['le',['int',1],['scaled_root','floor','1','1/3',['v','X']]],['q','1']])
        b=p.from_tree(['guard',['le',['int',1],['scaled_root','ceiling','1','1/3',['v','X']]],['q','1']])
        self.assertEqual(p.prove(a,b)['status'],'unknown')
    def test_bound_slot_cannot_escape(self):
        p=P.Producer(CONTEXT);a=p.from_tree(['x',['v','a']],('a',))
        with self.assertRaises(ValueError):p.prove(a,a)
    def test_declared_integer_symbols_only(self):
        with self.assertRaises(ValueError):P.Producer(CONTEXT).from_tree(['x',['v','missing']])
    def test_resource_limit_no_partial_theorem(self):
        p=P.Producer(CONTEXT);a=p.from_tree(['add',['q','1'],['q','2']]);p.deadline=time.monotonic()-1
        r=p.prove(a,a);self.assertEqual(r['status'],'unknown');self.assertFalse(r['complete']);self.assertIsNone(r['conclusion'])
    def test_context_and_options_closed(self):
        with self.assertRaises(ValueError):P.Producer(CONTEXT,limits=dict(P.LIMITS,max_degree=4))
        with self.assertRaises(ValueError):P.Producer(CONTEXT).node('MU_EQ')
    def test_tree_build_cap_unknown_retained_prefix(self):
        r=P.prove_trees(['sum','a',['int',1],['v','X'],['x',['v','a']]],['q','0'],CONTEXT,limits=dict(P.LIMITS,max_ast_nodes=2))
        self.assertEqual(r['status'],'unknown');self.assertIsNone(r['lhs']);self.assertIsNone(r['conclusion'])
        self.assertEqual(r['counts']['ast_nodes'],len(r['ast']))
        self.assertEqual(r['counts']['receipt_bytes'],len(P.encoded(r)))
    def test_byte_cap_suppresses_dag_without_false_counts(self):
        p=P.Producer(CONTEXT,limits=dict(P.LIMITS,max_receipt_bytes=1100))
        a=p.from_tree(['q','1']);r=p.prove(a,a)
        self.assertLessEqual(len(P.encoded(r)),1100)
        self.assertEqual(r['counts']['ast_nodes'],len(r['ast']))
        self.assertEqual(r['counts']['proof_nodes'],len(r['proof']))
        self.assertEqual(r['counts']['receipt_bytes'],len(P.encoded(r)))
    def test_exact_all_source_recipes(self):
        import primitive_state_parametric_sources as S
        rs=S.recipes()['recipes'];self.assertEqual(len(rs),74)
        for recipe in rs:
            r=S.produce_certificate(recipe)
            result=C.verify_certificate(r,expected_source_bindings=r['source_bindings'],expected_context=S.proof_context(recipe),expected_lhs_tree=S.proof_tree(recipe['lhs']),expected_rhs_tree=S.proof_tree(recipe['rhs']))
            self.assertTrue(result['verified'],recipe['id'])

if __name__=='__main__':unittest.main()
