"""Adversarial local-kernel review; no producer import or finite-grid proof."""
import unittest
import check_parametric_arithmetic_identity as C

class Nodes:
    def __init__(self): self.nodes=[]
    def n(self,sort,op,*args,**data):
        self.nodes.append(dict(sort=sort,op=op,args=list(args),data=data));return len(self.nodes)-1
    def integer(self,k):return self.n('Int','int',value=k)
    def bound(self,k):return self.n('Int','bound',index=k)
    def q(self,k):return self.n('Poly','q',value=str(k))
    def sum(self,lo,hi,body):return self.n('Poly','sum',lo,hi,body,binder='dummy')
    def ast(self):return C.AST(self.nodes,dict(integer_parameters=[],functions=[]),C.Budget(dict(C.LIMITS),None))

def proof(rule,lhs,rhs,scope=0,premises=()):
    return dict(rule=rule,lhs=lhs,rhs=rhs,scope=scope,premises=list(premises),judgment='FORMAL_EQ',data={})

class SoundnessTests(unittest.TestCase):
    def replay(self,n,p):
        ast=n.ast()
        for i in range(len(p)):
            if p[i]['rule']=='SUM_PULL':
                body=n.nodes[n.nodes[p[i]['lhs']]['args'][2]]
                p[i]['data']=dict(factor=body['args'][0],body=body['args'][1])
            C.replay_rule(ast,p,i)
        return ast
    def test_polynomial_atoms_are_not_boolean(self):
        n=Nodes();x=n.n('Poly','x',n.integer(1));xx=n.n('Poly','mul',x,x)
        with self.assertRaises(ValueError):self.replay(n,[proof('GUARD_BOOL',xx,x)])
    def test_opaque_sum_not_evaluated_by_ring(self):
        n=Nodes();one=n.integer(1);two=n.integer(2);s=n.sum(one,two,n.q(1))
        with self.assertRaises(ValueError):self.replay(n,[proof('RING',s,n.q(2))])
    def test_sum_bounds_not_bound_by_own_binder(self):
        n=Nodes();s=n.sum(n.bound(0),n.integer(2),n.q(1))
        with self.assertRaises(ValueError):self.replay(n,[proof('REFL',s,s)])
    def test_factor_dependent_on_summation_variable_rejected(self):
        n=Nodes();lo=n.integer(1);hi=n.integer(2);x=n.n('Poly','x',n.bound(0));one=n.q(1)
        lhs=n.sum(lo,hi,n.n('Poly','mul',x,one));rhs=n.n('Poly','mul',n.n('Poly','x',lo),n.sum(lo,hi,one))
        with self.assertRaises(ValueError):self.replay(n,[proof('SUM_PULL',lhs,rhs)])
    def test_wrong_nested_shift_rejected(self):
        n=Nodes();lo=n.integer(1);hi=n.integer(2);one=n.q(1)
        # Inner factor references outer binder as slot1; external must slot0.
        factor=n.n('Poly','x',n.bound(1));lhs=n.sum(lo,hi,n.n('Poly','mul',factor,one))
        bad=n.n('Poly','mul',factor,n.sum(lo,hi,one))
        with self.assertRaises(ValueError):self.replay(n,[proof('SUM_PULL',lhs,bad,scope=2)])
        good=n.n('Poly','mul',n.n('Poly','x',n.bound(0)),n.sum(lo,hi,one))
        self.replay(n,[proof('SUM_PULL',lhs,good,scope=1)])
    def test_inclusive_cut_overlap_rejected(self):
        n=Nodes();lo=n.integer(1);hi=n.integer(3);i=n.bound(0);cut=n.integer(2);one=n.q(1)
        lhs=n.sum(lo,hi,one)
        a=n.n('Bool','le',i,cut);b=n.n('Bool','le',cut,i)
        rhs=n.n('Poly','add',n.sum(lo,hi,n.n('Poly','guard',a,one)),n.sum(lo,hi,n.n('Poly','guard',b,one)))
        with self.assertRaises(ValueError):self.replay(n,[proof('PARTITION',lhs,rhs)])
    def test_changed_domain_linear_split_rejected(self):
        n=Nodes();lo=n.integer(1);hi=n.integer(3);one=n.q(1);two=n.q(2)
        lhs=n.sum(lo,hi,n.n('Poly','add',one,two))
        rhs=n.n('Poly','add',n.sum(lo,hi,one),n.sum(lo,n.integer(2),two))
        with self.assertRaises(ValueError):self.replay(n,[proof('SUM_LINEAR',lhs,rhs)])
    def test_arithmetic_specialization_not_formal_identity(self):
        n=Nodes();x=n.n('Poly','x',n.integer(1))
        with self.assertRaises(ValueError):self.replay(n,[proof('RING',x,n.q(1))])
    def test_named_shadowing_and_bounds_have_distinct_scopes(self):
        tree=['sum','i',['int',1],['int',3],['sum','i',['v','i'],['int',3],['x',['v','i']]]]
        out=C.from_tree(tree,dict(integer_parameters=[],functions=[]))
        nodes=out['ast'];outer=nodes[out['root']];inner=nodes[outer['args'][2]]
        self.assertEqual(nodes[inner['args'][0]]['data'],{'index':0})
        self.assertEqual(nodes[nodes[inner['args'][2]]['args'][0]]['data'],{'index':0})
        # Bounds slot0 denotes outer i; body slot0 denotes inner i.
    def test_root_rounding_conventions_not_conflated(self):
        n=Nodes();base=n.integer(2)
        floor=n.n('Int','scaled_root',base,rounding='floor',coefficient='1',power='1/2',negative_extension='zero')
        ceil=n.n('Int','scaled_root',base,rounding='ceiling',coefficient='1',power='1/2',negative_extension='zero')
        a=n.n('Poly','embed',floor);b=n.n('Poly','embed',ceil)
        with self.assertRaises(ValueError):self.replay(n,[proof('RING',a,b)])
    def test_same_guard_idempotence_valid(self):
        n=Nodes();p=n.n('Bool','eq',n.integer(1),n.integer(2));one=n.q(1)
        g=n.n('Poly','guard',p,one);gg=n.n('Poly','mul',g,g)
        self.replay(n,[proof('GUARD_BOOL',gg,g)])

if __name__=='__main__':unittest.main()
