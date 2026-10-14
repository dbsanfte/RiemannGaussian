"""Source-free064 reconstruction fixtures via independent threshold jumps."""
import copy
import unittest
from fractions import Fraction as Q
from math import gcd
import check_mobius_quadratic_source_064 as C
from prime_bank_candidates import Meter as PipelineMeter

METERS=[]
def meter():
    m=C.Meter(cap=1_000_000_000);METERS.append(m);return m

def mu_trial(n,m):
    answer=1
    for p in range(2,n+1):
        m.charge(4)
        if any(p%d==0 for d in range(2,p)):continue
        if n%(p*p)==0:return 0
        if n%p==0:answer=-answer
    return answer

def W(N,base,d):return (4*N)//(base*d)-3*((2*N)//(base*d))+2*(N//(base*d))

def fill(row,rule,m):
    H=len(row);result=[];nodes=[d for d in range(1,H+1) if gcd(d,14)==1]+[H+1]
    for d in range(1,H+1):
        if gcd(d,14)==1 or rule=='raw':value=row[d-1]
        elif rule=='zero':value=Q(0)
        elif rule in ('core','core_inverse'):
            core=d
            while core%2==0:core//=2;m.charge(4)
            while core%7==0:core//=7;m.charge(4)
            value=row[core-1]/(d//core if rule=='core_inverse' else 1)
        else:
            a=max(x for x in nodes if x<d);b=min(x for x in nodes if x>d)
            u=row[a-1];v=row[b-1] if b<=H else Q(0)
            if rule=='left':value=u
            elif rule=='right':value=v
            else:
                # Direct interpolation in its coordinate, rather than explicit weights.
                xa,xb,xd=(Q(x) for x in (a,b,d)) if rule=='linear' else (Q(1,x) for x in (a,b,d))
                value=u+(v-u)*(xd-xa)/(xb-xa)
        result.append(value);m.charge(100)
    return result

def inverse(row,m):
    H=len(row);c=[Q(0)]*H
    for d in range(H,0,-1):
        c[d-1]=row[d-1]
        for j in range(d+1,H+1):c[d-1]-=c[j-1]*(j//d);m.charge(100)
    return c

def fixture(m,rule='raw',N=17,y=10,H=3):
    K=y//(H+1);radius=max(H,K);u=[0]+[mu_trial(n,m) for n in range(1,radius+1)]
    raw=[[[0]*K for _ in range(H)] for _ in range(2)]
    # Reconstruct aggregated thresholds through finite source differences.
    # The verifier instead expands each original floor into outer indicators.
    for e,base in enumerate((2,7)):
        for T in range(H+1,y+1):
            jump=W(N,base,T)-(W(N,base,T+1) if T<y else 0)
            for ell in range(1,T//(H+1)+1):
                for d in range(1,H+1):raw[e][d-1][ell-1]+=jump*(T//(ell*d));m.charge(100)
    source=[];pf=[];pg=[];residual=[];filled=[];coeff=[]
    for r in (Q(2,7),Q(1)):
        f=[Q(W(N,2,d))-r*W(N,7,d) if d<=y else Q(0) for d in range(1,H+1)]
        G=[[Q(raw[0][d][ell])-r*raw[1][d][ell] for ell in range(K)] for d in range(H)]
        PG=[[Q(0)]*K for _ in range(H)]
        for ell in range(K):
            column=fill([G[d][ell] for d in range(H)],rule,m)
            for d in range(H):PG[d][ell]=column[d]
        R=[f[d]-sum((G[d][ell]*u[ell+1] for ell in range(K)),Q(0)) for d in range(H)]
        E=fill(R,rule,m);Pf=fill(f,rule,m)
        self_check=[Pf[d]-sum((PG[d][ell]*u[ell+1] for ell in range(K)),Q(0)) for d in range(H)]
        if E!=self_check:raise ArithmeticError('fixture linear fill')
        source.append(f);pf.append(Pf);pg.append(PG);residual.append(R);filled.append(E);coeff.append(inverse(E,m));m.charge(200*H*max(1,K))
    text=lambda rows:[[str(x) for x in row] for row in rows]
    repair={'schema':'mobius-short-repair-v1','primes':[2,7],'H':H,'rule':rule,
        'residuals':text(residual),'filled':text(filled),'coefficients':text(coeff),
        'coefficient_l1':[str(sum(map(abs,row),Q(0))) for row in coeff]}
    lift={'schema':'mobius-factored-quadratic-repair-v1',
        'parameters':{'alpha':'1/2','gamma':'1/3','tau':'1/2','primes':[2,7],'p':2,'q':7},
        'N':N,'y':y,'H':H,'rule':rule,'K':K,'arithmetic_radius':radius,
        'ordinary_mu_through_radius':u[1:],'linear_terms':text(pf),
        'long_kernels_after_fill':[[[str(x) for x in row] for row in matrix] for matrix in pg],
        'expression':C.EXPRESSION,'same_u_sequence_in_both_factors':True,'arithmetic_degree_at_most':2,
        'formal_source_only_factorization_reviewed':True,'producer_exact_replay':True,
        'independent_quadratic_schema_admission':False,'independent_whole_completion_admission_still_required':True,
        'uniform_quadratic_variation_bound_proved':False,'RH_proved':False}
    return lift,repair

class QuadraticSourceTests(unittest.TestCase):
    def test_all_fill_rules_source_entries_and_complete_repair(self):
        m=meter()
        for rule in ('raw','zero','left','right','linear','reciprocal_linear','core','core_inverse'):
            lift,repair=fixture(m,rule);out=C.verify_quadratic(lift,repair,m)
            self.assertTrue(out['quadratic_source_factorization_proved']);self.assertTrue(out['every_Pf_and_PG_entry_verified'])
            self.assertEqual(out['kernel_entries_verified'],12)

    def test_zero_K_and_virtual_boundary_case(self):
        m=meter();lift,repair=fixture(m,'reciprocal_linear',N=5,y=2,H=2)
        self.assertEqual(lift['K'],0);self.assertEqual(lift['long_kernels_after_fill'],[[[],[]],[[],[]]])
        self.assertTrue(C.verify_quadratic(lift,repair,m)['raw_residual_source_binding_proved'])
        bad=copy.deepcopy(lift);bad['linear_terms'][0][1]='0'
        with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)

    def test_independent_mu_includes_registered_primes_and_squares(self):
        m=meter();lift,repair=fixture(m,N=35,y=30,H=2)
        self.assertEqual(lift['ordinary_mu_through_radius'],[1,-1,-1,0,-1,1,-1,0,0,1])
        self.assertTrue(C.verify_quadratic(lift,repair,m)['ordinary_mu_independently_verified'])
        for i,value in ((1,0),(3,1),(6,0),(8,-1)):
            bad=copy.deepcopy(lift);bad['ordinary_mu_through_radius'][i]=value
            with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)

    def test_matrix_entry_sign_endpoint_or_unit_mutation(self):
        m=meter();lift,repair=fixture(m)
        for kind in ('Pf','PG','endpoint','unit'):
            bad=copy.deepcopy(lift)
            if kind=='Pf':bad['linear_terms'][0][2]=str(Q(bad['linear_terms'][0][2])+1)
            elif kind=='PG':bad['long_kernels_after_fill'][1][1][0]=str(Q(bad['long_kernels_after_fill'][1][1][0])+1)
            elif kind=='endpoint':bad['linear_terms'].reverse()
            else:bad['linear_terms'][0][0]='0'
            with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)

    def test_raw_noncoprime_residual_binding_even_when_zero_fill_ignores_it(self):
        m=meter();lift,repair=fixture(m,'zero')
        repair['residuals'][0][1]=str(Q(repair['residuals'][0][1])+1)
        #Generic fill/repair still valid; actual source binding must now reject.
        self.assertTrue(C.REPAIR.verify_repair(repair,m)['verified'])
        with self.assertRaises(ValueError):C.verify_quadratic(lift,repair,m)

    def test_linked_fill_rule_primes_H_and_coefficients(self):
        m=meter();lift,repair=fixture(m,'linear')
        for key,value in (('rule','raw'),('primes',[2,5]),('H',2)):
            bad=copy.deepcopy(repair);bad[key]=value
            with self.assertRaises(ValueError):C.verify_quadratic(lift,bad,m)
        bad=copy.deepcopy(repair);bad['coefficients'][0][0]=str(Q(bad['coefficients'][0][0])+1)
        with self.assertRaises(ValueError):C.verify_quadratic(lift,bad,m)

    def test_missing_column_row_or_linear_term(self):
        m=meter();lift,repair=fixture(m)
        for kind in ('endpoint','row','column','Pf'):
            bad=copy.deepcopy(lift)
            if kind=='endpoint':bad['long_kernels_after_fill'].pop()
            elif kind=='row':bad['long_kernels_after_fill'][0].pop()
            elif kind=='column':bad['long_kernels_after_fill'][0][0].pop()
            else:bad['linear_terms'][0].pop()
            with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)

    def test_K_radius_mu_coverage_and_strict_types(self):
        m=meter();lift,repair=fixture(m)
        for key,value in (('K',1),('K',True),('arithmetic_radius',2),('arithmetic_radius',True),
            ('ordinary_mu_through_radius',[1,-1]),('ordinary_mu_through_radius',[True,-1,-1])):
            bad=copy.deepcopy(lift);bad[key]=value
            with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)

    def test_source_N_y_H_and_parameter_swaps(self):
        m=meter();lift,repair=fixture(m)
        for key,value in (('N',1),('N',65537),('N',True),('y',0),('y',35),('H',0),('H',4097)):
            bad=copy.deepcopy(lift);bad[key]=value
            with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)
        for key,value in (('primes',[2,9]),('p',7),('alpha','1'),('tau','0')):
            bad=copy.deepcopy(lift);bad['parameters'][key]=value
            with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)

    def test_arbitrary_rational_order_and_source_parameters(self):
        m=meter();lift,repair=fixture(m,'core_inverse')
        lift['parameters'].update(alpha='1/257',gamma='257/1026',tau='3/7')
        self.assertTrue(C.verify_quadratic(lift,repair,m)['verified'])

    def test_forged_flags_expression_and_extra_fields(self):
        m=meter();lift,repair=fixture(m)
        for key,value in (('same_u_sequence_in_both_factors',False),('arithmetic_degree_at_most',True),
            ('uniform_quadratic_variation_bound_proved',True),('RH_proved',True),('expression','independent signs')):
            bad=copy.deepcopy(lift);bad[key]=value
            with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)
        bad=copy.deepcopy(lift);bad['source_verified']=True
        with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)

    def test_source_factorization_does_not_prove_uniform_growth(self):
        m=meter();lift,repair=fixture(m);out=C.verify_quadratic(lift,repair,m)
        self.assertTrue(out['source_generic_completion_identity_proved']);self.assertTrue(out['same_u_sequence_in_both_factors_proved'])
        self.assertFalse(out['saved_whole_completion_bytes_verified'])
        for key in ('uniform_quadratic_variation_bound_proved','whole_signed_target_bound_proved','RH_proved','scientific_source_tables_or_LP_evaluated'):
            self.assertIs(out[key],False)

    def test_canonical_fraction_and_resource_guards(self):
        m=meter();lift,repair=fixture(m)
        for value in (True,0.0,'0.0','0/2',str(1<<4097)):
            bad=copy.deepcopy(lift);bad['long_kernels_after_fill'][0][0][0]=value
            with self.assertRaises(ValueError):C.verify_quadratic(bad,repair,m)
        tiny=C.Meter(cap=1);METERS.append(tiny)
        with self.assertRaises(OverflowError):C.verify_quadratic(lift,repair,tiny)

    def test_charge_only_pipeline_meter(self):
        m=PipelineMeter();METERS.append(m);lift,repair=fixture(m)
        self.assertTrue(C.verify_quadratic(lift,repair,m)['verified']);self.assertGreater(m.operations,100)

if __name__=='__main__':
    try:unittest.main()
    finally:print('SYNTHETIC_WORK module=check_mobius_quadratic_source_064 operations='+str(sum(m.operations for m in METERS)))
