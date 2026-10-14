import copy
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import check_parametric_arithmetic_identity as C
import parametric_arithmetic_identity as P


CTX=dict(integer_parameters=[dict(name='t',lower=1)],functions=[])


def repair(receipt):
    receipt['counts']['ast_nodes']=len(receipt['ast']);receipt['counts']['proof_nodes']=len(receipt['proof'])
    for _ in range(8):
        size=len(C.encoded(receipt))
        if receipt['counts']['receipt_bytes']==size:break
        receipt['counts']['receipt_bytes']=size
    return receipt


def partition():
    p=P.Producer(CTX,source_bindings={'grammar':'1'*64},recipe_ids=['divisor-cut'])
    lo=p.node('int',data={'value':1});t=p.node('v',data={'name':'t'});d=p.node('bound',data={'index':0})
    cut=p.node('scaled_root',[t],dict(rounding='floor',coefficient='1',power='1/3',negative_extension='zero'))
    body=p.node('x',[d]);total=p.node('sum',[lo,t,body],dict(binder='d'));predicate=p.node('le',[d,cut])
    rhs,conclusion=p.partition(total,predicate)
    return p,p.certificate(total,rhs,conclusion),cut


class IndependentFormalTests(unittest.TestCase):
    def test_universal_complete_partition_and_all_scale_scope(self):
        p,receipt,cut=partition();out=C.verify_certificate(receipt)
        self.assertTrue(out['FORMAL_EQ_verified']);self.assertFalse(out['candidate_admitted']);self.assertFalse(out['global_bound_proved'])
        self.assertFalse(out['numerical_sampling_used']);self.assertFalse(out['formal_degree_or_project_horizon_inferred'])
    def test_independent_named_source_cutoff_binding(self):
        p,receipt,cut=partition();t=['v','t'];d=['v','d'];cutoff=['root',t,1,3]
        lhs=['sum','d',['int',1],t,['x',d]]
        rhs=['add',['sum','d',['int',1],t,['guard',['le',d,cutoff],['x',d]]],['sum','d',['int',1],t,['guard',['not',['le',d,cutoff]],['x',d]]]]
        kw=dict(expected_context=CTX,expected_source_bindings={'grammar':'1'*64},expected_recipe_ids=['divisor-cut'],expected_lhs_tree=lhs,expected_rhs_tree=rhs)
        self.assertTrue(C.verify_certificate(receipt,**kw)['source_semantics_independently_bound'])
        for field,value in [('rounding','ceiling'),('coefficient','2'),('power','1/2')]:
            bad=copy.deepcopy(receipt);bad['ast'][cut]['data'][field]=value;repair(bad)
            self.assertTrue(C.verify_certificate(bad)['FORMAL_EQ_verified'])
            with self.assertRaises(ValueError):C.verify_certificate(bad,**kw)
    def test_wrong_complement_equality_boundary(self):
        p,receipt,cut=partition();inside=p.ast[p.ast[p.ast[receipt['rhs']]['args'][0]]['args'][2]]['args'][0]
        notid=p.ast[p.ast[p.ast[receipt['rhs']]['args'][1]]['args'][2]]['args'][0]
        bad=copy.deepcopy(receipt);bad['ast'][notid]=dict(sort='Bool',op='le',args=bad['ast'][inside]['args'],data={});repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
        # Two strict pieces lose the d=cut case; neither can be silently equated.
        bad=copy.deepcopy(receipt);bad['ast'][inside]['op']='lt'
        d=bad['ast'][inside]['args'][0];bad['ast'][notid]=dict(sort='Bool',op='lt',args=[cut,d],data={});repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
    def test_lost_sum_domain_and_multiplicity(self):
        p,receipt,cut=partition();outside=p.ast[receipt['rhs']]['args'][1]
        bad=copy.deepcopy(receipt);bad['ast'][outside]['args'][1]=p.ast[receipt['lhs']]['args'][0];repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
        bad=copy.deepcopy(receipt);guard=p.ast[outside]['args'][2];bad['ast'][guard]['args'][1]=p.q(2)
        # Append a legal earlier constant before the changed guard instead.
        bad=copy.deepcopy(receipt);bad['ast'][guard]['args'][1]=p.ast[receipt['lhs']]['args'][2];bad['ast'][receipt['rhs']]['op']='mul';repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
    def test_exact_ring_closure_not_mu_relation(self):
        p=P.Producer(CTX);x=p.node('x',[p.node('int',data={'value':1})]);one=p.q(1)
        lhs=p.add(p.mul(x,x),p.q(-1));rhs=p.mul(p.add(x,p.q(-1)),p.add(x,one))
        good=p.prove(lhs,rhs);self.assertTrue(C.verify_certificate(good)['FORMAL_EQ_verified'])
        false=p.prove(p.add(x,p.q(-1)),p.q(0));out=C.verify_certificate(false);self.assertFalse(out['FORMAL_EQ_verified'])
        bad=copy.deepcopy(good);bad['judgment']='MU_EQ';repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
        bad=copy.deepcopy(good);bad['proof'][0]['judgment']='MU_EQ';repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
    def test_no_primitive_vanishing_or_unknown_rule(self):
        p,receipt,cut=partition()
        for rule in ('MU_PRIMITIVE','MU_TO_FORMAL','REINDEX','TRUST_ME'):
            bad=copy.deepcopy(receipt);bad['proof'][0]['rule']=rule;repair(bad)
            with self.assertRaises(ValueError):C.verify_certificate(bad)
        bad=copy.deepcopy(receipt);bad['global_bound_proved']=True;repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
    def test_cycle_forward_and_missing_proof_references(self):
        p,receipt,cut=partition()
        for reference in (0,999,True):
            bad=copy.deepcopy(receipt);bad['proof'][0].update(rule='SYM',premises=[reference]);repair(bad)
            with self.assertRaises(ValueError):C.verify_certificate(bad)
        bad=copy.deepcopy(receipt);bad['ast'][cut]['args']=[cut];repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
    def test_scope_bound_capture_and_free_root(self):
        p,receipt,cut=partition();bound=next(i for i,n in enumerate(p.ast) if n['op']=='bound')
        bad=copy.deepcopy(receipt);bad['ast'][bound]['data']['index']=1;repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
        # Sum bounds are evaluated OUTSIDE their own binder.
        bad=copy.deepcopy(receipt);bad['ast'][receipt['lhs']]['args'][0]=bound;repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
    def test_capture_free_sum_factor_pull_and_alpha(self):
        ctx=dict(integer_parameters=[dict(name='t',lower=1)],functions=[dict(name='w',arity=1,definition_hash='2'*64)])
        p=P.Producer(ctx);lo=p.node('int',data={'value':1});hi=p.node('v',data={'name':'t'});outer=p.node('bound',data={'index':1});inner=p.node('bound',data={'index':0})
        factor=p.node('symbol',[outer],dict(function='w'));body=p.node('x',[inner]);total=p.node('sum',[lo,hi,p.mul(factor,body)],dict(binder='i'))
        pulled,premise=p.pull_factor(total,factor,body,scope=1)
        lhs=p.node('sum',[lo,hi,total],dict(binder='n'));rhs=p.node('sum',[lo,hi,pulled],dict(binder='n'))
        conclusion=p.proof_node('SUM_CONGRUENCE',lhs,rhs,[premise]);receipt=p.certificate(lhs,rhs,conclusion)
        self.assertTrue(C.verify_certificate(receipt)['FORMAL_EQ_verified'])
        bad=copy.deepcopy(receipt);bad['ast'][outer]['data']['index']=0;repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
        renamed,proof=p.alpha(lhs,'fresh');self.assertTrue(C.verify_certificate(p.certificate(lhs,renamed,proof))['FORMAL_EQ_verified'])
    def test_range_split_cut_shift_outside_binder(self):
        p,receipt,cut=partition();rhs,proof=p.range_split(receipt['lhs'],cut)
        good=p.certificate(receipt['lhs'],rhs,proof);self.assertTrue(C.verify_certificate(good)['FORMAL_EQ_verified'])
        bad=copy.deepcopy(good);bad['proof'][proof]['data']['cut']=p.ast[receipt['lhs']]['args'][0];repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
    def test_context_function_source_bindings_not_merely_hashes(self):
        ctx=dict(integer_parameters=[],functions=[dict(name='rho',arity=0,definition_hash='1'*64)])
        p=P.Producer(ctx,source_bindings={'source':'2'*64});rho=p.node('symbol',data=dict(function='rho'));cert=p.certificate(rho,rho,p.refl(rho,0))
        out=C.verify_certificate(cert,expected_source_bindings={'source':'2'*64},expected_roots=dict(lhs=C.AST(cert['ast'],ctx,C.Budget(C.LIMITS,None)).keys[rho],rhs=C.AST(cert['ast'],ctx,C.Budget(C.LIMITS,None)).keys[rho]))
        self.assertFalse(out['source_semantics_independently_bound'])
        bad=copy.deepcopy(cert);bad['context']['functions'][0]['definition_hash']='3'*64;repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad,expected_context=ctx)
    def test_resource_bits_operations_nodes_depth_and_bytes(self):
        p,receipt,cut=partition()
        for kw in ({'max_operations':1},{'max_ast_nodes':1},{'max_depth':1},{'max_receipt_bytes':1}):
            with self.assertRaises(OverflowError):C.verify_certificate(receipt,**kw)
        extra=p.proof_node('SYM',receipt['rhs'],receipt['lhs'],[receipt['conclusion']]); doubled=p.certificate(receipt['rhs'],receipt['lhs'],extra)
        with self.assertRaises(OverflowError):C.verify_certificate(doubled,max_proof_nodes=1)
        bad=copy.deepcopy(receipt);bad['ast'][cut]['data']['coefficient']=str(2**4096);repair(bad)
        with self.assertRaises(OverflowError):C.verify_certificate(bad)
        bad=copy.deepcopy(receipt);bad['ast'][cut]['data']['coefficient']='2/2';repair(bad)
        with self.assertRaises(ValueError):C.verify_certificate(bad)
    def test_ring_factor_blowup_bounded_before_expansion(self):
        p=P.Producer(CTX);x=p.node('x',[p.node('int',data={'value':1})]);value=x
        for _ in range(16):value=p.mul(value,value)
        cert=p.certificate(value,value,p.proof_node('RING',value,value))
        with self.assertRaises(OverflowError):C.verify_certificate(cert,max_ring_cells=200)
    def test_unknown_diagnostic_no_formal_conclusion(self):
        p,receipt,cut=partition();receipt.update(status='unknown',complete=False,lhs=None,rhs=None,conclusion=None,reason='tree cap');repair(receipt)
        out=C.verify_certificate(receipt);self.assertFalse(out['FORMAL_EQ_verified']);self.assertIsNone(out['judgment'])
    def test_named_binders_capture_shadowing_and_negative_extensions(self):
        tree=['sum','n',['int',1],['v','t'],['sum','n',['int',1],['v','n'],['x',['v','n']]]]
        result=C.from_tree(tree,CTX);ast=C.AST(result['ast'],CTX,C.Budget(C.LIMITS,None));self.assertFalse(ast.free[result['root']])
        inner=result['ast'][result['ast'][result['root']]['args'][2]]
        self.assertEqual(result['ast'][inner['args'][1]]['data'],{'index':0})
        self.assertEqual(result['ast'][result['ast'][inner['args'][2]]['args'][0]]['data'],{'index':0})
        with self.assertRaises(ValueError):C.from_tree(['x',['v','undeclared']],CTX)
    def test_all74_source_recipes_independent_tree_binding(self):
        import primitive_state_parametric_sources as S
        records=S.recipes()
        def convert(tree):
            if not isinstance(tree,list):return tree
            if tree and tree[0]=='root':return ['scaled_root','floor','1',str(F(tree[2],tree[3])),convert(tree[1])]
            return [convert(t) for t in tree]
        for recipe in records['recipes']:
            ctx=dict(integer_parameters=[dict(name='X',lower=1)],functions=recipe['functions'])
            p=P.Producer(ctx,source_bindings=records['source_sha256'],recipe_ids=[recipe['id']]);lhs=p.from_tree(convert(recipe['lhs']));rhs=p.from_tree(convert(recipe['rhs']));cert=p.prove(lhs,rhs)
            out=C.verify_certificate(cert,expected_context=ctx,expected_source_bindings=records['source_sha256'],expected_recipe_ids=[recipe['id']],expected_lhs_tree=recipe['lhs'],expected_rhs_tree=recipe['rhs'])
            self.assertTrue(out['FORMAL_EQ_verified']);self.assertTrue(out['source_semantics_independently_bound']);self.assertFalse(out['full_target_proved'])

if __name__=='__main__':unittest.main()
