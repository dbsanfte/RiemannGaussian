import copy,unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_coupled_square_084 as S
import check_mobius_coupled_completion_083 as C
from test_check_mobius_coupled_remainder_083 import example

def proposal(p,o,u,rank=0):
    d=S.R.build_remainder(p,u,o);E=d['model']['effective_dimension'];nums=[[((i+j)%3)-1 for j in range(rank)]for i in range(E)];r=S.square_price(d['projected_remainder'],nums,8)
    return dict(squarefree_count=d['model']['squarefree_count'],factor_denominator='8',factor_numerators=[[str(x)for x in row]for row in nums],price=str(r['price']),row_prices=list(map(str,r['rows'])))

class Tests(unittest.TestCase):
    def test_zero_factor_recovers_exact_complete_remainder(self):
        for anchor in (False,True):
            p,o=example(True,anchor)
            for u in (1,4,24,53):
                c=proposal(p,o,u);r=S.verify_certificate(p,u,o,c);self.assertEqual(r['status'],'VERIFIED_FINITE_COUPLED_SQUARE_BOUND');self.assertEqual(r['price'],r['old_residual_price']);self.assertEqual(r['factor_trace'],'0');self.assertFalse(r['uniform_remaining_bound_proved']);self.assertFalse(r['uniform_source_bound_proved']);self.assertFalse(r['RH_proved'])
    def test_literal_rational_gram_nonzero_and_all_boolean_bound(self):
        p,o=example(True);u=53;c=proposal(p,o,u,2);out=S.verify_certificate(p,u,o,c);self.assertEqual(out['status'],'VERIFIED_FINITE_COUPLED_SQUARE_BOUND')
        d=S.R.build_remainder(p,u,o);L=[[Q(int(v),8)for v in row]for row in c['factor_numerators']];E=len(L)
        gram=[[sum(L[i][k]*L[j][k]for k in range(2))for j in range(E)]for i in range(E)]
        A=[[d['projected_remainder'][i][j]+gram[i][j]for j in range(E)]for i in range(E)]
        price=sum(A[i][i]for i in range(E))+2*sum(abs(A[i][j])for i in range(E)for j in range(i+1,E));self.assertEqual(Q(out['price']),price)
        self.assertEqual(Q(out['factor_trace']),sum(gram[i][i]for i in range(E)))
    def test_frustrated_triangle_strict_improvement(self):
        # Three mutually negative edges: adding all-ones square cancels each.
        A=[[Q(0)if i==j else Q(-1)for j in range(3)]for i in range(3)]
        old=S.square_price(A,[[],[],[]],1);new=S.square_price(A,[[1],[1],[1]],1)
        self.assertEqual(old['price'],6);self.assertEqual(new['price'],3)
        for bits in range(8):
            x=[1 if bits>>i&1 else -1 for i in range(3)]
            value=sum(x[i]*A[i][j]*x[j]for i in range(3)for j in range(3));self.assertLessEqual(value,new['price'])
    def test_mutations_denominator_rank_integer_and_schema(self):
        p,o=example(True);c=proposal(p,o,24,1)
        for key,value in [('factor_denominator','3'),('factor_denominator',str(1<<49)),('factor_denominator','08'),('price',str(Q(c['price'])+1)),('squarefree_count',True)]:
            bad=copy.deepcopy(c);bad[key]=value;self.assertEqual(S.verify_certificate(p,24,o,bad)['status'],'INVALID')
        for value in ('+1','01','-0',str(1<<129),'1/2'):
            bad=copy.deepcopy(c);bad['factor_numerators'][0][0]=value;self.assertEqual(S.verify_certificate(p,24,o,bad)['status'],'INVALID')
        bad=copy.deepcopy(c);bad['factor_numerators'][0].append('0');self.assertEqual(S.verify_certificate(p,24,o,bad)['status'],'INVALID')
        bad=copy.deepcopy(c);bad['extra']=False;self.assertEqual(S.verify_certificate(p,24,o,bad)['status'],'INVALID')
    def test_outer_source_anchor_and_complete_binding(self):
        p,o=example(True);c=proposal(p,o,53,1)
        bad=copy.deepcopy(p);bad['prime_anchor']=False;self.assertEqual(S.verify_certificate(bad,53,o,c)['status'],'INVALID')
        bad=copy.deepcopy(p);bad['kernel'][0]['weight']='-2';self.assertEqual(S.verify_certificate(bad,53,o,c)['status'],'INVALID')
        bo=copy.deepcopy(o);bo['Astar']='1';self.assertEqual(S.verify_certificate(p,53,bo,c)['status'],'INVALID')
        bad=copy.deepcopy(c);bad['factor_numerators'].pop();self.assertEqual(S.verify_certificate(p,53,o,bad)['status'],'INVALID')
    def test_prospective_horizon_dimension_factor_and_work(self):
        p,o=example();c=proposal(p,o,24)
        with patch.object(C.D,'squarefree_prefix',side_effect=AssertionError('huge gate before sieve')):
            self.assertTrue(S.verify_certificate(p,10**40,o,c)['resource_limit'])
        bad=copy.deepcopy(c);bad['factor_numerators']=[[]]*513;self.assertTrue(S.verify_certificate(p,24,o,bad)['resource_limit'])
        m=C.Meter();m.ops=m.limit;self.assertEqual(S.verify_certificate(p,24,o,c,m)['status'],'INVALID')
        with self.assertRaises(ValueError):S.square_price([[Q(0)]],[['not integer']],1)

class DualTests(unittest.TestCase):
    def setup_case(self):
        p,o=example(True);u=53;d=S.R.build_remainder(p,u,o);d['input_program']=p;E=d['model']['effective_dimension'];nums=[[1 if i%2 else -1]for i in range(E)];system=S.R.O.equality_constraints(p);lam=[Q(1,7),Q(-2,5),Q(3,11)];self.assertEqual(len(lam),len(system['rows']))
        result=S.dual_components(d,nums,2,lam)
        c=dict(squarefree_count=d['model']['squarefree_count'],factor_denominator='2',factor_numerators=[[str(v)for v in row]for row in nums],equality_multipliers=list(map(str,lam)),lower_bound=str(result['lower']))
        return p,o,u,d,nums,lam,result,c
    def test_literal_dual_templates_fixed_gram_outer_equalities(self):
        p,o,u,d,nums,lam,result,c=self.setup_case();model=d['model'];G=model['squarefree_count'];E=model['effective_dimension'];X=[[Q(1)if i==j else Q(nums[i][0]*nums[j][0],4)for j in range(E)]for i in range(E)];m=C.Meter()
        def functional(raw):
            return sum(raw[g][h]*model['projection_signs'][g]*model['projection_signs'][h]*X[model['projection_indices'][g]][model['projection_indices'][h]]for g in range(G)for h in range(G))
        vals=[]
        for k in range(len(p['coupled_terms'])):
            B=[[Q(0)if d['outer_mask'][g]and d['outer_mask'][h]else C._zentry(model,k,g,h,m)for h in range(G)]for g in range(G)]
            vals.append(functional(B))
        self.assertEqual(vals,result['template_functionals'])
        raw0=[[((Q(0)if d['outer_mask'][g]and d['outer_mask'][h]else C._entry(model,g,h,m,False,True))-d['raw_Gram'][g][h])for h in range(G)]for g in range(G)]
        self.assertEqual(functional(raw0),result['base'])
        eq=S.R.O.equality_constraints(p);rows=[[Q(v)for v in row]for row in eq['rows']];t=len(vals);b=[Q(v)-sum(row[t+i]*Q(w)for i,w in enumerate(p['gram_weights']))for row,v in zip(rows,eq['rhs'])]
        expected=result['base']-sum(x*y for x,y in zip(lam,b))-16*sum(abs(v+sum(row[k]*x for row,x in zip(rows,lam)))for k,v in enumerate(vals))
        self.assertEqual(expected,result['lower']);out=S.verify_dual(p,u,o,c);self.assertEqual(out['status'],'VERIFIED_FINITE_COUPLED_SQUARE_GRAMMAR_LOWER_BOUND');self.assertFalse(out['actual_signed_drift_lower_bound_proved']);self.assertFalse(out['uniform_grammar_obstruction_proved'])
        upper=proposal(p,o,u,2);self.assertLessEqual(Q(out['lower_bound']),Q(upper['price']))
    def test_dual_norm_multipliers_binding_and_mutation(self):
        p,o,u,d,nums,lam,result,c=self.setup_case()
        for mutate in ('norm','multiplier','lower','den','shape'):
            bad=copy.deepcopy(c)
            if mutate=='norm':bad['factor_numerators'][0][0]='3'
            elif mutate=='multiplier':bad['equality_multipliers'].pop()
            elif mutate=='lower':bad['lower_bound']=str(Q(bad['lower_bound'])+1)
            elif mutate=='den':bad['factor_denominator']='3'
            else:bad['factor_numerators'][0].append('0')
            self.assertEqual(S.verify_dual(p,u,o,bad)['status'],'INVALID')
        bad=copy.deepcopy(p);bad['gram_weights'][0]='0';self.assertEqual(S.verify_dual(bad,u,o,c)['status'],'INVALID')
        bad=copy.deepcopy(p);bad['kernel'][0]['weight']='-2';self.assertEqual(S.verify_dual(bad,u,o,c)['status'],'INVALID')
    def test_empty_factor_identity_dual_and_resource_scope(self):
        p,o=example();u=24;d=S.R.build_remainder(p,u,o);d['input_program']=p;E=d['model']['effective_dimension'];nums=[[]for _ in range(E)];lam=[Q(0)]*len(S.R.O.equality_constraints(p)['rows']);r=S.dual_components(d,nums,1,lam)
        c=dict(squarefree_count=d['model']['squarefree_count'],factor_denominator='1',factor_numerators=nums,equality_multipliers=list(map(str,lam)),lower_bound=str(r['lower']))
        out=S.verify_dual(p,u,o,c);self.assertEqual(out['status'],'VERIFIED_FINITE_COUPLED_SQUARE_GRAMMAR_LOWER_BOUND');self.assertFalse(out['uniform_source_bound_proved']);self.assertFalse(out['RH_proved'])
        with patch.object(C.D,'squarefree_prefix',side_effect=AssertionError('gate before sieve')):self.assertTrue(S.verify_dual(p,10**40,o,c)['resource_limit'])
