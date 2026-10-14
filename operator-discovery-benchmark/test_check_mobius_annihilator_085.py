import copy,unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_annihilator_085 as A
from test_check_mobius_coupled_remainder_083 import example

def bank():return [dict(scale='1',u_exponent='1',complement=False,unit_balance=False),dict(scale='1/2',u_exponent='1',complement=True,unit_balance=True),dict(scale='3/2',u_exponent='-17/31',complement=False,unit_balance=True)]
def mu(n):
    count=0;d=2;v=n
    while d*d<=v:
        if v%d==0:
            v//=d;count+=1
            if v%d==0:return 0
        d+=1
    if v>1:count+=1
    return(-1)**count

def proposal(p,o,u,b):
    data=A.R.build_remainder(p,u,o);ids=A.build_identities(data['model'],b);E=data['model']['effective_dimension'];m=len(b);S=[[Q(-1)if i==j else Q(2,3)for j in range(m)]for i in range(m)];nums=[[]for _ in range(E)];r=A.annihilator_price(data['projected_remainder'],ids['vectors'],S,nums,1)
    return dict(squarefree_count=data['model']['squarefree_count'],identity_matrix=[[str(v)for v in row]for row in S],factor_denominator='1',factor_numerators=nums,price=str(r['price']),row_prices=list(map(str,r['rows'])))

class Tests(unittest.TestCase):
    def test_negative_zero_square_strict_improvement_and_mixed_cross(self):
        V=[[Q(1)],[Q(1)],[Q(-2)]];R=[[a[0]*b[0]for b in V]for a in V]
        r=A.annihilator_price(R,V,[[Q(-1)]],[[],[],[]],1);self.assertEqual(r['price'],0);self.assertEqual(r['identity_trace'],-6)
        V=[[Q(1),Q(0)],[Q(-1),Q(1)],[Q(0),Q(-1)]];S=[[Q(-1),Q(2,3)],[Q(2,3),Q(-3)]];R=[[Q(0)if i==j else Q((-1)**(i+j),3)for j in range(3)]for i in range(3)];r=A.annihilator_price(R,V,S,[[1],[0],[-1]],2)
        Z=[[sum(V[i][k]*S[k][l]*V[j][l]for k in range(2)for l in range(2))for j in range(3)]for i in range(3)];self.assertEqual(r['identity_correction'],Z)
        for bits in range(8):
            x=[1 if bits>>i&1 else -1 for i in range(3)]
            if all(sum(V[i][k]*x[i]for i in range(3))==0 for k in range(2)):
                self.assertEqual(sum(x[i]*Z[i][j]*x[j]for i in range(3)for j in range(3)),0)
                self.assertLessEqual(sum(x[i]*R[i][j]*x[j]for i in range(3)for j in range(3)),r['price'])
    def test_actual_complete_divisor_identity_unit_and_projection(self):
        p,o=example(True)
        for u in (1,4,24,53):
            data=A.R.build_remainder(p,u,o);model=data['model'];b=bank()+[dict(scale='1/100',u_exponent='-1001/1000',complement=False,unit_balance=False)];ids=A.build_identities(model,b);G=model['squarefree_count'];E=model['effective_dimension'];x=list(map(mu,model['coordinates']));y=[1]+[mu(n)for n in model['effective_labels'][1:]]if E else []
            for j in range(len(b)):
                self.assertEqual(sum(x[g]*ids['raw_vectors'][g][j]for g in range(G)),0)
                self.assertEqual(sum(y[i]*ids['vectors'][i][j]for i in range(E)),0)
                self.assertEqual(ids['vectors'][0][j]if E else 0,sum(model['projection_signs'][g]*ids['raw_vectors'][g][j]for g in range(G)if model['projection_indices'][g]==0))
            c=proposal(p,o,u,b);r=A.verify_certificate(p,u,o,b,c);self.assertEqual(r['status'],'VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND');self.assertTrue(r['zero_identity_rule_verified_for_all_u']);self.assertFalse(r['uniform_remaining_bound_proved']);self.assertFalse(r['uniform_source_bound_proved']);self.assertFalse(r['RH_proved']);self.assertTrue(r['old_outer_block_unchanged'])
    def test_empty_bank_factor_and_literal_full_price(self):
        p,o=example(True);b=[];u=53;c=proposal(p,o,u,b);r=A.verify_certificate(p,u,o,b,c);self.assertEqual(r['status'],'VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND');self.assertEqual(r['identity_trace'],'0')
        d=A.R.build_remainder(p,u,o);old=A.F.square_price(d['projected_remainder'],c['factor_numerators'],1);self.assertEqual(Q(c['price']),old['price'])
        b=bank();c=proposal(p,o,u,b);E=len(c['factor_numerators']);nums=[[(-1)**i]for i in range(E)];ids=A.build_identities(d['model'],b);S=[[Q(v)for v in row]for row in c['identity_matrix']];price=A.annihilator_price(d['projected_remainder'],ids['vectors'],S,nums,4);c.update(factor_denominator='4',factor_numerators=[[str(v)for v in row]for row in nums],price=str(price['price']),row_prices=list(map(str,price['rows'])));self.assertEqual(A.verify_certificate(p,u,o,b,c)['status'],'VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND')
    def test_schema_symmetry_denominator_and_bank_mutations(self):
        p,o=example();b=bank();c=proposal(p,o,53,b)
        for kind in ('asym','signed','size','factor','price','extra'):
            bad=copy.deepcopy(c)
            if kind=='asym':bad['identity_matrix'][0][1]='1/2'
            elif kind=='signed':bad['identity_matrix'][0][0]='-2'
            elif kind=='size':bad['identity_matrix'].pop()
            elif kind=='factor':bad['factor_denominator']='3'
            elif kind=='price':bad['price']=str(Q(bad['price'])+1)
            else:bad['extra']=False
            self.assertEqual(A.verify_certificate(p,53,o,b,bad)['status'],'INVALID')
        for kind in ('scale','exponent','bool','extra'):
            bb=copy.deepcopy(b)
            if kind=='scale':bb[0]['scale']='0'
            elif kind=='exponent':bb[0]['u_exponent']='01'
            elif kind=='bool':bb[0]['complement']=1
            else:bb[0]['extra']=False
            self.assertEqual(A.verify_certificate(p,53,o,bb,c)['status'],'INVALID')
        bb=copy.deepcopy(b);bb[0]['u_exponent']='0';self.assertEqual(A.verify_certificate(p,53,o,bb,c)['status'],'INVALID')
    def test_same_outer_source_and_complete_anchored_binding(self):
        p,o=example();b=bank();c=proposal(p,o,53,b)
        bad=copy.deepcopy(p);bad['prime_anchor']=False;self.assertEqual(A.verify_certificate(bad,53,o,b,c)['status'],'INVALID')
        bad=copy.deepcopy(p);bad['kernel'][0]['weight']='-2';self.assertEqual(A.verify_certificate(bad,53,o,b,c)['status'],'INVALID')
        bo=copy.deepcopy(o);bo['Astar']='2';self.assertEqual(A.verify_certificate(p,53,bo,b,c)['status'],'INVALID')
        bad=copy.deepcopy(c);bad['factor_numerators'].pop();self.assertEqual(A.verify_certificate(p,53,o,b,bad)['status'],'INVALID')
    def test_prospective_resource_power_and_helper_symmetry(self):
        p,o=example();b=bank();c=proposal(p,o,24,b)
        with patch.object(A.C.D,'squarefree_prefix',side_effect=AssertionError('huge gate before sieve')):self.assertTrue(A.verify_certificate(p,10**40,o,b,c)['resource_limit'])
        bb=b*6;self.assertEqual(A.verify_certificate(p,24,o,bb,c)['status'],'INVALID')
        bad=copy.deepcopy(c);bad['factor_numerators']=[[]]*513;self.assertTrue(A.verify_certificate(p,24,o,b,bad)['resource_limit'])
        bb=copy.deepcopy(b);bb[0]['u_exponent']='1000001';out=A.verify_certificate(p,24,o,bb,c);self.assertEqual(out['status'],'INVALID');self.assertTrue(out['resource_limit'])
        m=A.C.Meter();m.ops=m.limit;self.assertEqual(A.verify_certificate(p,24,o,b,c,m)['status'],'INVALID')
        with self.assertRaises(ValueError):A.annihilator_price([[Q(0)]],[[Q(1),Q(1)]],[[Q(0),Q(1)],[Q(0),Q(0)]],[[]],1)
