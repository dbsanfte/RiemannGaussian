"""Synthetic algebra and tamper checks; no source/norm archive observations."""
import copy
from fractions import Fraction as Q
import unittest
import check_floor_residual_prime_047 as C
import floor_residual_prime_047 as P
from prime_bank_candidates import Meter as ExternalMeter

CHECKER=C.Meter(50000000)
PRODUCER=P.Meter(cap=50000000,seconds=180)


def request(p=2,N=5,zero=False,negative=False):
    U=['1']+[str(Q((-1)**n*(n+2),n+3)) for n in range(2,N+1)]
    V=['1']+[str(Q(n+1,2*n+3)) for n in range(2,p*N+1)]
    V[p-1]='0' if zero else '-3/7' if negative else '3/7'
    return {'prime':p,'parent_support':N,'parent_values':U,'child_values':V}


def build(r):return P.build_prime_construction(r,PRODUCER)
def verify(r,c):return C.verify_prime_construction(r,c,CHECKER)


class PrimeIdentityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.r=request();cls.c=build(cls.r)

    def reject(self,r,c):
        with self.assertRaises((ValueError,OverflowError,ArithmeticError)):
            verify(r,c)

    def test_complete_signed_identity(self):
        result=verify(self.r,self.c)
        self.assertIs(result['verified'],True)
        self.assertFalse(result['global_bound_proved'])
        # Independent numerical rational identity on integer cells, including
        # the region beyond both finite source supports.
        p=self.r['prime'];N=self.r['parent_support']
        U=[Q(0)]+list(map(Q,self.r['parent_values']))
        V=[Q(0)]+list(map(Q,self.r['child_values']))
        def mu(n):
            parity=0;d=2
            while d*d<=n:
                if n%d==0:
                    n//=d;parity+=1
                    if n%d==0:return 0
                d+=1
            return (-1)**(parity+int(n>1))
        for k in range(1,34):
            target=Q(1)+sum(mu(n)*V[n]*Q(k%n,n) for n in range(2,p*N+1))
            if k>=p:
                target+=1+sum(mu(n)*U[n]*Q((k//p)%n,n) for n in range(2,N+1))
            got=C._cell(C._decode(self.c['original_forcing'],CHECKER),k,CHECKER)
            self.assertEqual(got,target)

    def test_prime_square_and_higher_valuation_retained(self):
        verify(self.r,self.c)
        rows=self.c['p_adic_source_coefficients']
        self.assertEqual(Q(rows[3]['value']),-Q(self.r['parent_values'][1]))
        self.assertEqual(rows[3]['child_term'],'0')
        self.assertEqual(rows[7]['valuation'],3)
        self.assertEqual(rows[7]['value'],'0')
        for index in (3,7):
            c=copy.deepcopy(self.c);c['p_adic_source_coefficients'].pop(index)
            self.reject(self.r,c)

    def test_other_prime_and_unit_only_parent(self):
        for r in (request(3,4),request(5,1)):
            self.assertTrue(verify(r,build(r))['verified'])

    def test_negative_normalization_is_exact(self):
        r=request(negative=True);c=build(r)
        self.assertTrue(verify(r,c)['matched_normalization_available'])
        self.assertEqual(c['matched']['normalized_parent_values'][0],'1')
        self.assertFalse(c['matched']['range_or_contraction_proved'])

    def test_zero_normalization_retains_direct_match_and_auxiliary(self):
        r=request(zero=True);c=build(r);out=verify(r,c)
        self.assertFalse(out['matched_normalization_available'])
        self.assertIsNone(c['matched']['parent_program'])
        self.assertIsNone(c['matched']['normalized_parent_values'])
        self.assertTrue(out['division_free_matched_verified'])
        for field in ('direct_parent_program','program','conversion_auxiliary'):
            bad=copy.deepcopy(c);bad['matched'][field]=None;self.reject(r,bad)
        bad=copy.deepcopy(c);bad['matched']['normalized_parent_values']=['1']*r['parent_support'];self.reject(r,bad)

    def test_normalized_profile_provenance_including_zero_mu(self):
        # Profile index4 has mu=0, so a vector-only equality would miss this
        # exact normalized-source swap. The full supplied profile is bound.
        c=copy.deepcopy(self.c);c['matched']['normalized_parent_values'][3]='1'
        self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['source_request']['child_values'][3]='1'
        self.reject(self.r,c)

    def test_omitted_square_normalizer_indicator_and_conversion(self):
        for key,index in (('prime_split',3),('prime_split',4),('prime_split',5),('matched',2),('matched',4)):
            c=copy.deepcopy(self.c);c[key]['blocks'].pop(index);self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['original_forcing']['steps']=[];self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['matched']['conversion_auxiliary']['steps']=[];self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['matched']['conversion_auxiliary']['coefficients']=[];self.reject(self.r,c)

    def test_identity_and_prime_manifest_tampering(self):
        for change in ('identity','factor','valuation','cancelled'):
            c=copy.deepcopy(self.c)
            if change=='identity':c['identities'][-1]['difference']['constant']='1'
            if change=='factor':c['mu_certificate']['rows'][3]['factors'][0]['exponent']=1
            if change=='valuation':c['p_adic_source_coefficients'][3]['valuation']=1
            if change=='cancelled':c['matched']['cancelled_valuation_one'][0]['value']='1'
            self.reject(self.r,c)

    def test_domain_canonical_and_source_unit_guards(self):
        for key,val in (('prime',4),('prime',True),('prime',2.0),('parent_support',True)):
            r=copy.deepcopy(self.r);r[key]=val;self.reject(r,self.c)
        for key,index,val in (('parent_values',0,'0'),('child_values',0,'2'),
                              ('child_values',1,'2/4'),('parent_values',1,0.5)):
            r=copy.deepcopy(self.r);r[key][index]=val;self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['child_values'].pop();self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['extra_bound']=True;self.reject(r,self.c)

    def test_false_global_and_recipe_claims_rejected(self):
        for key,val in (('RH_proved',True),('RH_refuted',True),('identity_only',False),
                        ('global_bound_status','PROVED'),('norm_convergence_status','PROVED'),
                        ('supplied_values_independently_source_verified',True)):
            c=copy.deepcopy(self.c);c[key]=val;self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['matched']['range_or_contraction_proved']=True;self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['uniform_source_bound']=True;self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['RH_proved']=0;self.reject(self.r,c)

    def test_charge_only_meter_and_capacity_guards(self):
        meter=ExternalMeter(cap=1000000,seconds=60)
        self.assertTrue(C.verify_prime_construction(self.r,self.c,meter)['verified'])
        CHECKER.charge(meter.operations)
        with self.assertRaises(OverflowError):C.verify_prime_construction(self.r,self.c,C.Meter(1))
        r=copy.deepcopy(self.r);r['parent_values'][1]=str(2**4097)
        self.reject(r,self.c)
        # Each input denominator is within4096 bits, but their common
        # profile lattice exceeds8192 and must fail before reconstruction.
        r=request(2,2);r['parent_values'][1]='1/'+str(2**4095)
        r['child_values'][1]='1/'+str(3**2580)
        r['child_values'][2]='1/'+str(5**1750)
        self.reject(r,self.c)

    def test_emitted_scalar_text_can_exceed_python_decimal_limit(self):
        value=Q(2**18000+1,3**9000)
        encoded=C._text(value)
        self.assertEqual(C._rational(encoded,CHECKER,32768),value)
        with self.assertRaises(ValueError):C._rational(encoded,CHECKER,4096)


class CellBlockTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.r=request();cls.c=P.cell_energy_certificate(cls.r,8,PRODUCER)

    def reject(self,c):
        with self.assertRaises((ValueError,OverflowError,ArithmeticError)):
            C.verify_cell_energy(self.r,c,CHECKER)

    def test_complete_finite_block_and_direct_signed_squares(self):
        out=C.verify_cell_energy(self.r,self.c,CHECKER)
        self.assertTrue(out['verified']);self.assertFalse(out['whole_norm_proved'])
        vector=C._reconstruct(self.r,CHECKER)['original']
        values=[C._cell(vector,k,CHECKER) for k in range(8,16)]
        self.assertEqual(Q(self.c['energy']),sum(v*v for v in values))
        self.assertEqual(Q(self.c['weighted_norm']),sum(v*v/Q(k*(k+1)) for k,v in zip(range(8,16),values)))
        # k=15 exceedschild10/parent5: full truncated divisor heads remain.
        row=self.c['cells'][-1]
        self.assertNotEqual(row['child_truncated_divisor_sum'],'0')

    def test_cell_tail_divisor_and_unit_tampering(self):
        for field in ('child_truncated_divisor_sum','parent_floor_sum','unit_and_indicator',
                      'parent_harmonic_term','value','weight','weighted_square'):
            c=copy.deepcopy(self.c);c['cells'][-1][field]='0';self.reject(c)
        c=copy.deepcopy(self.c);c['cells'].pop();self.reject(c)
        c=copy.deepcopy(self.c);c['end_exclusive']+=1;self.reject(c)
        c=copy.deepcopy(self.c);c['cells'][0]['parent_cell']+=1;self.reject(c)

    def test_cross_energy_and_whole_norm_claim_tampering(self):
        for field in ('energy','weighted_norm'):
            c=copy.deepcopy(self.c);c[field]='1';self.reject(c)
        for field in ('whole_norm_proved','unobserved_cells_or_tails_inferred','supplied_values_independently_source_verified'):
            c=copy.deepcopy(self.c);c[field]=True;self.reject(c)
        c=copy.deepcopy(self.c);c['K']=True;self.reject(c)
        c=copy.deepcopy(self.c);c['K']=7;self.reject(c)

    def test_signed_rational_profiles_and_small_cells(self):
        for r,K in ((request(negative=True),1),(request(zero=True),4),(request(3,4),2)):
            certificate=P.cell_energy_certificate(r,K,PRODUCER)
            self.assertTrue(C.verify_cell_energy(r,certificate,CHECKER)['verified'])


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_floor_residual_prime_047 operations='+str(CHECKER.operations+PRODUCER.operations))
    print('SYNTHETIC_SPLIT checker='+str(CHECKER.operations)+' fixture='+str(PRODUCER.operations))

if __name__=='__main__':unittest.main()
