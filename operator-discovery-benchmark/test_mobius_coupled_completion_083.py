import copy
import unittest
from fractions import Fraction as Q
import mobius_coupled_completion_083 as P
import check_mobius_coupled_completion_083 as C


def program(extended=False):
    kernel=[(4,'-1'),(5,'1'),(8,'1'),(10,'-1')]
    if extended:kernel+= [(12,'-3547/8192'),(15,'3547/8192'),(24,'3547/8192'),(30,'-3547/8192')]
    terms=[]
    for mirror in (False,True):
        terms.append(dict(cut=dict(scale='1',n_exponent='1',u_exponent='0',complement=mirror,unit_balance=True),
                          weight=dict(kind='product',i=0,j=0,arithmetic='all'),theta='0'))
    terms.append(dict(cut=dict(scale='2/3',n_exponent='-2/7',u_exponent='5/11',complement=False,unit_balance=False),
                      weight=dict(kind='source',i=1,arithmetic='prime'),theta='0'))
    return dict(schema='coupled-divisor-completion-v1',kernel=[dict(divisor=d,weight=w)for d,w in sorted(kernel)],
                memory=2,rays=[dict(a=['1','1'],weight='1/4')],drift_multiplier='3/2',
                coupled_terms=terms,gram_weights=['0','0','0'])


def mu(n):
    sign=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;sign=-sign
            if n%p==0:return 0
        p+=1
    return -sign if n>1 else sign


class CoupledTests(unittest.TestCase):
    def test_physical_geometry_independent_and_arithmetic_filters(self):
        p=program(True)
        p['coupled_terms']+=[dict(cut=copy.deepcopy(p['coupled_terms'][0]['cut']),
                               weight=dict(kind='band',left='1/12',right='1/4',arithmetic='composite'),theta='0')]
        for u in (1,7,137,401):
            a=P.build_model(p,u);b=C.build_model(p,u)
            self.assertEqual(list(map(int,a['coordinates'])),list(b['coordinates']))
            self.assertEqual([[Q(int(v),a['denominator'])for v in row]for row in a['features']], [list(r)for r in b['features']])
            self.assertEqual([list(map(int,r))for r in a['cuts']],[list(r)for r in b['cuts']])
            self.assertEqual([[Q(int(v),a['denominator']**2)for v in row]for row in a['weights']],[list(r)for r in b['weights']])
            self.assertEqual(a['prime_count'],b['prime_count'])

    def test_signed_rational_power_cut_root_and_complement(self):
        c=P.parse_program(program())['coupled_terms'][2]['cut']
        for n in (1,2,17,113):
            value=P.cut_value(n,1231,307,c)
            self.assertEqual(value,C.floor_cut(c['scale'],c['n_exponent'],c['u_exponent'],n,1231,307))
            mirror=dict(c,complement=True)
            self.assertEqual(P.cut_value(n,1231,307,mirror)+value,307)
        c=dict(c,n_exponent=Q(1,100001),scale=Q(2))
        with self.assertRaises(P.ResourceLimit):P.cut_value(2,1231,307,c)

    def test_zero_identity_all_unit_and_prime_composite_terms(self):
        p=program(True);p['coupled_terms'][0]['theta']='7/5';p['coupled_terms'][1]['theta']='-2/9'
        p['coupled_terms'][2]['theta']='1/11';p['gram_weights']=['0','1/7','0']
        u=211;model=P.build_model(p,u);coords=list(map(int,model['coordinates']));signs=[mu(n)for n in coords]
        for k in range(len(model['cuts'])):
            Z,den=P.coupled_basis(model,k)
            self.assertEqual(sum(int(Z[i,j])*signs[i]*signs[j]for i in range(len(coords))for j in range(len(coords))),0)
        certificate,diagnostics=P.upper_certificate(model)
        self.assertEqual(C.verify_certificate(p,u,certificate)['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
        source=[sum(Q(int(row[i]),model['denominator'])*sign for row,sign in zip(model['features'],signs))for i in range(3)]
        drift=sum(model['T'][i][j]*source[i]*source[j]for i in range(3)for j in range(3))
        self.assertGreaterEqual(Q(certificate['price']),drift)
        self.assertGreaterEqual(Q(diagnostics['unit_offdiagonal_absolute_price']),0)

    def test_boolean_negative_row_price_is_retained(self):
        p=program();p.update(kernel=[dict(divisor=1,weight='1')],memory=1,rays=[],gram_weights=['0','0'])
        p['coupled_terms']=[]
        certificate,diag=P.upper_certificate(P.build_model(p,2))
        self.assertEqual(certificate['row_prices'],['1/2','2'])
        # A separate exact instance where diagonal is negative and no offdiagonal remains.
        p['kernel']=[dict(divisor=2,weight='1'),dict(divisor=3,weight='-1')]
        certificate,_=P.upper_certificate(P.build_model(p,5))
        self.assertEqual(certificate['row_prices'],['-3/2','1'])
        self.assertEqual(C.verify_certificate(p,5,certificate)['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND')

    def test_balanced_unit_column_zero_with_zero_unit_weight(self):
        p=program();model=P.build_model(p,211)
        for j in (0,1):
            Z,_=P.coupled_basis(model,j)
            self.assertTrue(all(int(v)==0 for v in Z[0,:]))

    def test_exact_dual_and_lp_proposal(self):
        p=program();result=P.optimize(p,131,time_limit=30)
        self.assertEqual(result['status'],'LP_PROPOSAL')
        self.assertEqual(C.verify_certificate(result['program'],131,result['certificate'])['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
        self.assertEqual(C.verify_price_dual(result['program'],131,result['dual'])['status'],'VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND')
        self.assertGreaterEqual(Q(result['exact_gap']),0)
        bad=copy.deepcopy(result['dual']);bad['nu'][0]='3'
        self.assertEqual(C.verify_price_dual(p,131,bad)['status'],'INVALID')

    def test_prospective_full_geometry_and_rational_gates(self):
        with self.assertRaises(P.ResourceLimit):P.build_model(program(),4*(P.MAX_N+1))
        p=program();p['kernel'][0]['weight']=str(Q(-1,2**90+1))
        with self.assertRaises(P.ResourceLimit):P.build_model(p,131)

    def test_exact_affine_outer_program(self):
        import mobius_coupled_outer_control_083 as OUTER
        p=program();system=OUTER.equality_constraints(p)
        self.assertEqual(system['status'],'OUTER_EQUALITY_SYSTEM')
        eq={k:system[k]for k in ('rows','rhs')}
        result=P.optimize(p,131,time_limit=30,equalities=eq)
        self.assertEqual(result['status'],'LP_PROPOSAL')
        proof=OUTER.synthesize(result['program'])
        self.assertEqual(proof['status'],'PROPOSED_UNIFORM_WHOLE_OUTER_CONTROL')
        self.assertTrue(proof['full_remaining_kernel_unpaid'])
        self.assertEqual(C.verify_certificate(result['program'],131,result['certificate'])['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
        self.assertEqual(C.verify_price_dual(result['program'],131,result['dual'])['status'],'VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND')

    def test_persistent_model_memory_accounted_before_basis(self):
        model=P.build_model(program(),91)
        model['resident_bytes']=P.OLD.MAX_BYTES
        with self.assertRaises(P.ResourceLimit):P.coupled_basis(model,0)
        with self.assertRaises(P.ResourceLimit):P.upper_certificate(model)
        n=model['squarefree_count']
        with self.assertRaises(P.ResourceLimit):P.dual_certificate(model,[Q(0)]*(n*(n-1)//2))
        p=program();p['rays']=[dict(a=['1','1'],weight=str(Q(1,2**4080-v)))for v in range(1,35,2)]
        with self.assertRaises(P.ResourceLimit):P.build_model(p,131)

    def test_prime_anchor_preserves_signed_form_and_improves_price(self):
        p=program(True);p['coupled_terms'][0]['theta']='7/5';p['coupled_terms'][1]['theta']='-2/9'
        p['coupled_terms'][2]['theta']='1/11';p['gram_weights'][1]='1/7'
        raw=P.build_model(p,211);A=P.native_matrix(raw)
        old,_=P.upper_certificate(raw);p['prime_anchor']=True;model=P.build_model(p,211)
        B=P.native_matrix(model);certificate,_=P.upper_certificate(model)
        signs=[mu(int(n))for n in model['coordinates']]
        reduced=[1]+[signs[int(i)]for i in model['composite_indices']]
        lhs=sum(A[i,j]*signs[i]*signs[j]for i in range(len(signs))for j in range(len(signs)))
        rhs=sum(B[i,j]*reduced[i]*reduced[j]for i in range(len(reduced))for j in range(len(reduced)))
        self.assertEqual(lhs,rhs)
        self.assertGreaterEqual(Q(certificate['price']),Q(str(rhs)))
        self.assertLessEqual(Q(certificate['price']),Q(old['price']))
        self.assertEqual(C.verify_certificate(p,211,certificate)['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND')

    def test_prime_anchor_with_exact_outer_proof_and_dual(self):
        import mobius_coupled_outer_control_083 as OUTER
        import check_mobius_coupled_outer_control_083 as CHECK_OUTER
        p=program();p['prime_anchor']=True;system=OUTER.equality_constraints(p)
        result=P.optimize(p,131,time_limit=30,equalities={k:system[k]for k in ('rows','rhs')})
        self.assertEqual(result['status'],'LP_PROPOSAL')
        self.assertEqual(C.verify_certificate(result['program'],131,result['certificate'])['status'],'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
        self.assertEqual(C.verify_price_dual(result['program'],131,result['dual'])['status'],'VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND')
        proof=OUTER.synthesize(result['program'])
        self.assertEqual(CHECK_OUTER.verify_certificate(result['program'],proof['certificate'])['status'],'VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL')


if __name__=='__main__':unittest.main()
