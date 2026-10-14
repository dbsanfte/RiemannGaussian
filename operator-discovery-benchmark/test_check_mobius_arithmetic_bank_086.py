import unittest,copy,itertools
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_arithmetic_bank_086 as A
from test_check_mobius_coupled_remainder_083 import example

def prime(n):return n>=2 and all(n%d for d in range(2,n))
def mu(n):
    factors=0
    for p in range(2,n+1):
        if prime(p)and n%p==0:
            if n%(p*p)==0:return 0
            factors+=1
    return(-1)**factors

def pair(u,K,on='prime',weight=None):return dict(kind='prime_pair',cut_on=on,cut=dict(scale=str(Q(K,u)),u_exponent='1',complement=False),weight=weight or dict(kind='one'))
def divisor():return dict(kind='divisor',cut=dict(scale='1/10',u_exponent='1',complement=True,unit_balance=True))
def lower_proposal(p,o,u,b,s):
    data=A.R.build_remainder(p,u,o);model=data['model'];value=A.quadratic_value(data['projected_remainder'],s)
    return dict(squarefree_count=model['squarefree_count'],signs=s,lower_bound=str(value))
def upper_proposal(p,o,u,b):
    data=A.R.build_remainder(p,u,o);model=data['model'];ids=A.build_identities(model,b);E=model['effective_dimension'];W=[[Q((i+j)%3-1,7)for j in range(len(b))]for i in range(E)];L=[[(-1)**i]for i in range(E)];r=A.mixed_price(data['projected_remainder'],ids['vectors'],W,L,4)
    return dict(squarefree_count=model['squarefree_count'],partner_matrix=[[str(v)for v in row]for row in W],factor_denominator='4',factor_numerators=[[str(v)for v in row]for row in L],price=str(r['price']),row_prices=list(map(str,r['rows'])))

class Tests(unittest.TestCase):
    def test_all_directed_prime_pairs_unit_and_multiplicities(self):
        p,o=example();u=53;model=A.C.build_model(p,u);b=[pair(u,13),pair(u,3,'cofactor')];d=A.build_identities(model,b);ns=model['coordinates'];G=len(ns)
        for j,desc in enumerate(b):
            expected=[Q(0)]*G;count=0
            for pp in range(2,model['N']+1):
                if not prime(pp):continue
                for n in ns:
                    if n%pp==0 or pp*n>model['N']:continue
                    if desc['cut_on']=='cofactor'and n>3:continue
                    count+=1;expected[ns.index(n)]+=1;expected[ns.index(pp*n)]+=1
            self.assertEqual(expected,[row[j]for row in d['raw_vectors']]);self.assertEqual(count,d['prime_pair_counts'][j])
            self.assertEqual(sum(mu(n)*v for n,v in zip(ns,expected)),0)
        self.assertGreaterEqual(d['raw_vectors'][ns.index(6)][0],2) #2*3 and3*2 bothretained.
        self.assertEqual(d['raw_vectors'][ns.index(1)][0],sum(prime(n)for n in ns))
    def test_source_weights_fractional_cuts_complement_and_zero(self):
        p,o=example();u=83;model=A.C.build_model(p,u);b=[pair(u,3,'cofactor',dict(kind='source',i=0)),pair(u,2,'prime',dict(kind='source',i=1)),dict(kind='prime_pair',cut_on='prime',cut=dict(scale='1',u_exponent='17/31',complement=True),weight=dict(kind='one')),dict(kind='prime_pair',cut_on='cofactor',cut=dict(scale='1/100',u_exponent='-1001/1000',complement=False),weight=dict(kind='one')),divisor()];d=A.build_identities(model,b);ns=model['coordinates']
        for j in range(len(b)):self.assertEqual(sum(mu(n)*d['raw_vectors'][g][j]for g,n in enumerate(ns)),0)
        self.assertEqual(d['cuts'][3],0);self.assertEqual(d['prime_pair_counts'][3],0);self.assertTrue(all(row[3]==0 for row in d['vectors']))
        for j in (0,1):
            desc=b[j];K=d['cuts'][j];raw=[Q(0)]*len(ns)
            for pp in range(2,model['N']+1):
                if not prime(pp):continue
                for g,n in enumerate(ns):
                    if n%pp or n==1:
                        if pp*n<=model['N']and(desc['cut_on']!='prime'or pp<=K)and(desc['cut_on']!='cofactor'or n<=K):
                            w=model['features'][g][desc['weight']['i']];raw[g]+=w;raw[ns.index(pp*n)]+=w
            self.assertEqual(raw,[row[j]for row in d['raw_vectors']])
    def test_compatible_fake_boolean_lower_and_incompatible_rejection(self):
        p,o=example();u=83;b=[pair(u,2)];model=A.C.build_model(p,u);s=[1]+[1 for _ in model['effective_labels'][1:]];s[model['effective_labels'].index(15)]=-1
        self.assertNotEqual(s,[1]+[mu(n)for n in model['effective_labels'][1:]])
        c=lower_proposal(p,o,u,b,s);r=A.verify_lower(p,u,o,b,c);self.assertEqual(r['status'],'VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND');self.assertTrue(r['unrestricted_signed_and_mixed_zero_plus_PSD_grammars_bound']);self.assertFalse(r['actual_signed_drift_lower_bound_proved']);self.assertFalse(r['uniform_obstruction_proved']);self.assertFalse(r['RH_proved'])
        bad=copy.deepcopy(c);bad['signs'][model['effective_labels'].index(6)]=-1;self.assertEqual(A.verify_lower(p,u,o,b,bad)['status'],'INVALID')
        bad=copy.deepcopy(c);bad['signs'][0]=-1;self.assertEqual(A.verify_lower(p,u,o,b,bad)['status'],'INVALID')
        bad=copy.deepcopy(c);bad['lower_bound']=str(Q(c['lower_bound'])+1);self.assertEqual(A.verify_lower(p,u,o,b,bad)['status'],'INVALID')
    def test_actual_calibration_compatible_divisor_and_prime_bank(self):
        p,o=example(True);u=53;b=[divisor(),pair(u,13),pair(u,3,'cofactor',dict(kind='source',i=0))];model=A.C.build_model(p,u);s=[1]+[mu(n)for n in model['effective_labels'][1:]];c=lower_proposal(p,o,u,b,s);r=A.verify_lower(p,u,o,b,c);self.assertEqual(r['status'],'VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND');self.assertTrue(r['zero_identity_rule_verified_for_all_u'])
    def test_literal_mixed_partner_half_factor_signed_cross_and_bound(self):
        V=[[Q(1)],[Q(-1)]];W=[[Q(-2)],[Q(3)]];R=[[Q(1),Q(-1,3)],[Q(-1,3),Q(-2)]];r=A.mixed_price(R,V,W,[[],[]],1);self.assertEqual(r['mixed_correction'],[[Q(-2),Q(5,2)],[Q(5,2),Q(-3)]])
        for s in ([1,1],[-1,-1]):
            self.assertEqual(A.quadratic_value(r['mixed_correction'],s),0);self.assertLessEqual(A.quadratic_value(R,s),r['price'])
        V=[[Q(1)],[Q(1)],[Q(-2)]];R=[[a[0]*b[0]for b in V]for a in V];r=A.mixed_price(R,V,[[-v for v in row]for row in V],[[],[],[]],1);self.assertEqual(r['price'],0)
    def test_complete_upper_binding_nonzero_factor_and_empty_domains(self):
        p,o=example(True)
        for u,b in [(1,[pair(1,1)]),(4,[]),(53,[divisor(),pair(53,13),pair(53,3,'cofactor')])]:
            c=upper_proposal(p,o,u,b);r=A.verify_upper(p,u,o,b,c);self.assertEqual(r['status'],'VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND');self.assertTrue(r['old_outer_block_unchanged']);self.assertFalse(r['uniform_remaining_bound_proved']);self.assertFalse(r['uniform_source_bound_proved'])
        bad=copy.deepcopy(c);bad['partner_matrix'][0][0]=str(Q(bad['partner_matrix'][0][0])+1);self.assertEqual(A.verify_upper(p,53,o,b,bad)['status'],'INVALID')
        bad=copy.deepcopy(c);bad['factor_denominator']='3';self.assertEqual(A.verify_upper(p,53,o,b,bad)['status'],'INVALID')
        bb=copy.deepcopy(b);bb.pop(1);self.assertEqual(A.verify_upper(p,53,o,bb,c)['status'],'INVALID')
    def test_typed_schema_indices_canonical_and_source_binding(self):
        p,o=example();u=53;b=[pair(u,3)];c=upper_proposal(p,o,u,b)
        for desc in [dict(kind='divisor',cut=dict(scale='1',u_exponent='1',complement=False)),dict(kind='prime_pair',cut_on='other',cut=b[0]['cut'],weight=dict(kind='one')),dict(kind='prime_pair',cut_on='prime',cut=b[0]['cut'],weight=dict(kind='source',i=True)),dict(kind='prime_pair',cut_on='prime',cut=b[0]['cut'],weight=dict(kind='source',i=2))]:self.assertEqual(A.verify_upper(p,u,o,[desc],c)['status'],'INVALID')
        bad=copy.deepcopy(p);bad['prime_anchor']=False;self.assertEqual(A.verify_upper(bad,u,o,b,c)['status'],'INVALID')
        bad=copy.deepcopy(p);bad['kernel'][0]['weight']='-2';self.assertEqual(A.verify_upper(bad,u,o,b,c)['status'],'INVALID')
        bo=copy.deepcopy(o);bo['Astar']='2';self.assertEqual(A.verify_upper(p,u,bo,b,c)['status'],'INVALID')
    def test_resources_preallocation_shapes_power_and_work(self):
        p,o=example();u=24;b=[pair(u,3)];c=upper_proposal(p,o,u,b)
        with patch.object(A.C.D,'squarefree_prefix',side_effect=AssertionError('must reject before sieve')):self.assertTrue(A.verify_upper(p,10**40,o,b,c)['resource_limit'])
        bad=copy.deepcopy(c);bad['factor_numerators']=[[]]*513;self.assertTrue(A.verify_upper(p,u,o,b,bad)['resource_limit'])
        bad=copy.deepcopy(c);bad['factor_numerators'][0][0]='1'*1000
        with patch.object(A.R,'build_remainder',side_effect=AssertionError('reject huge factor before source allocation')):self.assertEqual(A.verify_upper(p,u,o,b,bad)['status'],'INVALID')
        bb=copy.deepcopy(b);bb[0]['cut']['u_exponent']='1000001';self.assertTrue(A.verify_upper(p,u,o,bb,c)['resource_limit'])
        self.assertEqual(A.verify_upper(p,u,o,b*17,c)['status'],'INVALID')
        m=A.C.Meter();m.ops=m.limit;self.assertEqual(A.verify_upper(p,u,o,b,c,m)['status'],'INVALID')
    def test_exact_extension_rank_gain_and_zero_compatible_rejection(self):
        p,o=example(True);u=83;b=[pair(u,2)];model=A.C.build_model(p,u);s=[1]+[mu(n)for n in model['effective_labels'][1:]];s[model['effective_labels'].index(15)]=-1;c=lower_proposal(p,o,u,b,s)
        added=pair(u,3);r=A.verify_extension(p,u,o,b,c,added);self.assertEqual(r['status'],'VERIFIED_FINITE_ARITHMETIC_BANK_INFORMATION_GAIN');self.assertNotEqual(Q(r['new_identity_dot']),0);self.assertFalse(r['uniform_rank_gain_proved'])
        self.assertEqual(A.verify_extension(p,u,o,b,c,b[0])['status'],'INVALID')
        bad=copy.deepcopy(c);bad['lower_bound']=str(Q(c['lower_bound'])+1);self.assertEqual(A.verify_extension(p,u,o,b,bad,added)['status'],'INVALID')
        self.assertEqual(A.verify_extension(p,u,o,b*16,c,added)['status'],'INVALID')
