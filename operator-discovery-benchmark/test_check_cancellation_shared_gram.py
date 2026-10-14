import copy
import unittest
import check_cancellation_shared_gram as C

def poly(*terms):return [dict(m=list(m),c=str(c)) for m,c in terms]
def fixture():
    one=poly(((),1));x=poly(((1,),1));a=poly(((),1),((1,),1))
    target=C.P.canonical(C.P.multiply(C.P.parse(a,1),C.P.parse(a,1)))
    inst=dict(target='mu',horizon=1,lhs=target,square_groups=[],relation_groups=[])
    specs={'g':2};blocks=[{'g':[[one,x]]}];matrix=[['1','1'],['1','1']]
    gp=dict(polynomial=target,squares=[dict(weight='1',poly=a)],decomposition=dict(matrix=matrix))
    cert=dict(target='mu',horizon=1,lhs=target,squares=gp['squares'],relations=[])
    result=dict(status='finite_PSD_certificate',weights=dict(square_weights=[],relation_weights=[]),grams={'g':matrix},gram_specs=specs,source_hashes=[C.digest(inst)],gram_block_hashes=[C.digest(blocks[0])],constant_slacks=['0'],certificates=[dict(certificate=cert,Gram_proofs={'g':gp})],exact_column_weights=['0','1','1','1'],global_bound_proved=False,RH_proved=False)
    return [inst],blocks,specs,result

class SharedGramCheck(unittest.TestCase):
    def test_constants_and_unit(self):
        args=fixture();self.assertTrue(C.verify_primal(*args)['verified'])
        self.assertEqual(C.gram_polynomial([['1']],[[poly(((),1))]],1),{():C.F(1)})
    def test_dual_constant_domain_and_Gram(self):
        inst=dict(target='mu',horizon=1,lhs=poly(((),-1)),square_groups=[],relation_groups=[])
        blocks=[{'g':[[poly(((),1))]]}];specs={'g':1}
        r=dict(status='exact_separator',certified=True,global_bound_proved=False,RH_proved=False,gram_specs=specs,source_hashes=[C.digest(inst)],gram_block_hashes=[C.digest(blocks[0])],monomials=[dict(instance=0,m=[])],weights=['1'],columns_dot_y=['1'],lhs_dot_y='-1',gram_duals={'g':{'matrix':[['1']]}})
        self.assertTrue(C.verify_dual([inst],blocks,specs,r)['verified'])
        r['gram_duals']['g']['matrix']=[['0']]
        with self.assertRaises(ValueError):C.verify_dual([inst],blocks,specs,r)
        r['monomials']=[];r['weights']=[]
        with self.assertRaises(ValueError):C.verify_dual([inst],blocks,specs,r)
    def test_dual_canceling_aggregated_cross(self):
        inst=dict(target='mu',horizon=2,lhs=poly(((),-1)),square_groups=[],relation_groups=[])
        x=poly(((1,),1));y=poly(((2,),1));minus_y=poly(((2,),-1))
        blocks=[{'g':[[x,y],[x,minus_y]]}];specs={'g':2}
        r=dict(status='exact_separator',certified=True,global_bound_proved=False,RH_proved=False,gram_specs=specs,source_hashes=[C.digest(inst)],gram_block_hashes=[C.digest(blocks[0])],monomials=[dict(instance=0,m=m) for m in [[],[1,1],[2,2]]],weights=['1','1','1'],columns_dot_y=['1'],lhs_dot_y='-1',gram_duals={'g':{'matrix':[['2','0'],['0','2']]}})
        self.assertTrue(C.verify_dual([inst],blocks,specs,r)['verified'])
        r['monomials'].pop();r['weights'].pop()
        with self.assertRaises(ValueError):C.verify_dual([inst],blocks,specs,r)
    def test_scalar_cell_charge(self):
        out=C.scalar_cell_charge({'p':[['0','0'],['0','4']],'c':[['1','0'],['0','2']]},{'p':{'region':'parent'},'c':{'region':'child'}},3)
        self.assertEqual(out['formal_scalar_charge'],'6')
        self.assertEqual(out['linear_coefficient'],'2')
    def test_dropped_cross(self):
        args=fixture();args[3]['certificates'][0]['Gram_proofs']['g']['polynomial']=poly(((),1),((1,1),1))
        with self.assertRaises(ValueError):C.verify_primal(*args)
    def test_zero_diagonal_offdiagonal(self):
        with self.assertRaises(ValueError):C.verify_psd([['0','1'],['1','0']])
    def test_indefinite_positive_diagonal(self):
        with self.assertRaises(ValueError):C.verify_psd([['1','2'],['2','1']])
    def test_source_binding(self):
        for field in ('target','horizon','lhs'):
            args=fixture();args[0][0][field]={'target':'c','horizon':2,'lhs':[]}[field]
            with self.assertRaises(ValueError):C.verify_primal(*args)
    def test_block_binding(self):
        args=fixture();args[1][0]['g']=[]
        with self.assertRaises(ValueError):C.verify_primal(*args)
    def test_aux_empty_legal_and_coverage(self):
        args=fixture();aux=dict(target='mu',horizon=1,lhs=[],square_groups=[],relation_groups=[])
        args[0].append(aux);args[1].append({'g':[]})
        r=args[3];r['source_hashes'].append(C.digest(aux));r['gram_block_hashes'].append(C.digest(args[1][1]));r['constant_slacks'].append('0');r['exact_column_weights'].insert(0,'0')
        r['certificates'].append(dict(certificate=dict(target='mu',horizon=1,lhs=[],squares=[],relations=[]),Gram_proofs={'g':dict(polynomial=[],squares=[],decomposition=dict(matrix=r['grams']['g']))}))
        self.assertTrue(C.verify_primal(*args)['verified'])
        args[1][1]={}
        with self.assertRaises(ValueError):C.verify_primal(*args)
    def test_false_global_claim(self):
        for field in ('global_bound_proved','RH_proved'):
            args=fixture();args[3][field]=True
            with self.assertRaises(ValueError):C.verify_primal(*args)
    def test_scalar_budget_and_slack(self):
        args=fixture();args[0][0]['lhs']=C.P.canonical(C.P.add(C.P.parse(args[0][0]['lhs'],1),{():C.F(-1)}));args[3]['source_hashes']=[C.digest(args[0][0])]
        with self.assertRaises(ValueError):C.verify_primal(*args)
    def test_flattened_cross_and_scale_mutation(self):
        args=fixture();args[3]['certificates'][0]['certificate']['squares']=[]
        with self.assertRaises(ValueError):C.verify_primal(*args)
        args=fixture();args[3]['exact_column_weights'][-2]='0'
        with self.assertRaises(ValueError):C.verify_primal(*args)

if __name__=='__main__':unittest.main()
