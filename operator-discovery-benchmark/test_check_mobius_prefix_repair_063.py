"""Synthetic063 full-row floor repairs and rule/source-scope mutations."""
import copy
import unittest
from fractions import Fraction as Q
import check_mobius_prefix_repair_063 as C
from prime_bank_candidates import Meter as PipelineMeter

METERS=[]
def meter():
    m=C.Meter(cap=1_000_000_000);METERS.append(m);return m

FILLS={
    'raw':[Q(i) for i in range(1,11)],
    'zero':list(map(Q,[1,0,3,0,5,0,0,0,9,0])),
    'left':list(map(Q,[1,1,3,3,5,5,5,5,9,9])),
    'right':list(map(Q,[1,3,3,5,5,9,9,9,9,0])),
    'linear':list(map(Q,[1,2,3,4,5,6,7,8,9]))+[Q(9,2)],
    'reciprocal_linear':[Q(1),Q(5,2),Q(3),Q(17,4),Q(5),Q(13,2),Q(53,7),Q(67,8),Q(9),Q(81,20)],
    'core':list(map(Q,[1,1,3,1,5,3,1,1,9,5])),
    'core_inverse':[Q(1),Q(1,2),Q(3),Q(1,4),Q(5),Q(3,2),Q(1,7),Q(1,8),Q(9),Q(5,2)]}

def triangular_inverse(row,m):
    # Direct backwards floor matrix elimination; no Mobius inversion/suffixes.
    H=len(row);coeff=[Q(0)]*H
    for d in range(H,0,-1):
        coeff[d-1]=row[d-1]
        for j in range(d+1,H+1):
            coeff[d-1]-=coeff[j-1]*(j//d);m.charge(100)
    return coeff

def fixture(rule,m):
    residuals=[[Q(i) for i in range(1,11)],[-Q(i,3) for i in range(1,11)]]
    filled=[FILLS[rule],[-x/3 for x in FILLS[rule]]]
    coeffs=[triangular_inverse(row,m) for row in filled]
    return {'schema':'mobius-short-repair-v1','primes':[2,7],'H':10,'rule':rule,
        'residuals':[[str(x) for x in row] for row in residuals],
        'filled':[[str(x) for x in row] for row in filled],
        'coefficients':[[str(x) for x in row] for row in coeffs],
        'coefficient_l1':[str(sum(map(abs,row),Q(0))) for row in coeffs]}

class RepairCheckerTests(unittest.TestCase):
    def test_all_eight_rules_and_exact_full_floor_replay(self):
        m=meter()
        for rule in C.RULES:
            cert=fixture(rule,m);out=C.verify_repair(cert,m)
            self.assertTrue(out['repair_identity_proved']);self.assertEqual(out['rows_checked_per_endpoint'],10)
            for row,c in zip(cert['filled'],cert['coefficients']):
                for d in range(1,14):
                    value=sum((Q(x)*((j+1)//d) for j,x in enumerate(c)),Q(0))
                    self.assertEqual(value,Q(row[d-1]) if d<=10 else 0);m.charge(200)

    def test_unit_and_squareful_coprime_rows_are_retained(self):
        m=meter()
        for rule in C.RULES:
            cert=fixture(rule,m);out=C.verify_repair(cert,m)
            self.assertEqual(cert['filled'][0][0],'1');self.assertEqual(cert['filled'][0][8],'9')
            self.assertEqual(out['first_moment'],['1','-1/3'])
            self.assertTrue(out['unit_preserved']);self.assertTrue(out['all_coprime_rows_including_squareful'])
            self.assertEqual(out['coprime_rows_preserved'],4)

    def test_virtual_H_plus_one_boundary(self):
        m=meter()
        for rule,value in (('right','0'),('linear','9/2'),('reciprocal_linear','81/20')):
            cert=fixture(rule,m);self.assertEqual(cert['filled'][0][-1],value)
            self.assertEqual(C.verify_repair(cert,m)['virtual_endpoint'],{'index':11,'value':'0'})

    def test_reciprocal_interpolation_is_not_linear_in_d(self):
        m=meter();cert=fixture('reciprocal_linear',m)
        self.assertEqual(cert['filled'][0][1],'5/2');self.assertNotEqual(cert['filled'][0][1],'2')
        cert['filled'][0][1]='2'
        with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_core_removes_all_registered_valuations(self):
        m=meter();cert=fixture('core',m)
        self.assertEqual(cert['filled'][0][7],'1') #8 strips2 repeatedly to1.
        self.assertEqual(cert['filled'][0][9],'5') #10 strips2 only.
        self.assertTrue(C.verify_repair(cert,m)['verified'])
        cert['filled'][0][7]='4'
        with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_core_inverse_prices_full_factor(self):
        m=meter();cert=fixture('core_inverse',m)
        self.assertEqual(cert['filled'][0][7],'1/8');self.assertEqual(cert['filled'][0][6],'1/7')
        cert['filled'][0][7]='1/2'
        with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_coprime_fill_mutation_cannot_be_hidden(self):
        m=meter()
        for i in (0,2,4,8):
            cert=fixture('zero',m);cert['filled'][0][i]='0'
            with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_wrong_non_coprime_fill_rule_rejected(self):
        m=meter()
        for rule in C.RULES:
            cert=fixture(rule,m);cert['filled'][1][1]='100'
            with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_dropped_coefficient_or_underpriced_norm(self):
        m=meter()
        cert=fixture('raw',m);cert['coefficients'][0].pop()
        with self.assertRaises(ValueError):C.verify_repair(cert,m)
        cert=fixture('raw',m);cert['coefficient_l1'][0]='0'
        with self.assertRaises(ValueError):C.verify_repair(cert,m)
        cert=fixture('raw',m);cert['coefficients'][0][0]=str(Q(cert['coefficients'][0][0])+1)
        cert['coefficient_l1'][0]=str(sum(map(lambda x:abs(Q(x)),cert['coefficients'][0]),Q(0)))
        with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_non_coprime_floor_rows_are_also_replayed(self):
        m=meter();cert=fixture('zero',m)
        # Modify c4 then compensate c1: unit still recovers, row4 does not.
        cert['coefficients'][0][3]=str(Q(cert['coefficients'][0][3])+1)
        cert['coefficients'][0][0]=str(Q(cert['coefficients'][0][0])-4)
        cert['coefficient_l1'][0]=str(sum((abs(Q(x)) for x in cert['coefficients'][0]),Q(0)))
        with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_H_one_arbitrary_fraction_and_general_mask(self):
        m=meter();cert={'schema':'mobius-short-repair-v1','primes':[3,11],'H':1,'rule':'reciprocal_linear',
            'residuals':[['1/257'],['-257/1026']],'filled':[['1/257'],['-257/1026']],
            'coefficients':[['1/257'],['-257/1026']],'coefficient_l1':['1/257','257/1026']}
        out=C.verify_repair(cert,m);self.assertTrue(out['verified']);self.assertEqual(out['coprime_rows_preserved'],1)

    def test_source_binding_and_uniform_growth_remain_unpaid(self):
        m=meter();out=C.verify_repair(fixture('raw',m),m)
        self.assertTrue(out['whole_candidate_requires_062_admission'])
        self.assertTrue(out['universal_positive_envelope_proved'])
        for key in ('original_source_binding_proved','uniform_N_growth_proved','whole_signed_target_bound_proved','RH_proved','scientific_source_or_LP_evaluated'):
            self.assertIs(out[key],False)

    def test_unknown_rule_and_prime_schema(self):
        m=meter()
        for key,value in (('rule','nearest'),('rule',True),('primes',[7,2]),('primes',[2,2,7]),('primes',[2,9]),('primes',[2])):
            cert=fixture('raw',m);cert[key]=value
            with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_all_two_endpoint_array_shapes(self):
        m=meter()
        for key in ('residuals','filled','coefficients'):
            for remove in ('endpoint','index'):
                cert=fixture('raw',m)
                if remove=='endpoint':cert[key].pop()
                else:cert[key][1].pop()
                with self.assertRaises(ValueError):C.verify_repair(cert,m)
        cert=fixture('raw',m);cert['coefficient_l1'].pop()
        with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_strict_rational_and_horizon_capacity(self):
        m=meter()
        for H in (0,4097,True):
            cert=fixture('raw',m);cert['H']=H
            with self.assertRaises(ValueError):C.verify_repair(cert,m)
        for value in (True,1.0,'1.0','2/2',str(1<<4097)):
            cert=fixture('raw',m);cert['residuals'][0][0]=value
            with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_forged_original_source_or_uniform_flags_rejected(self):
        m=meter()
        for key in ('source_verified','RH_proved','uniform_N_growth_proved'):
            cert=fixture('raw',m);cert[key]=True
            with self.assertRaises(ValueError):C.verify_repair(cert,m)

    def test_charge_only_pipeline_meter_and_work_cap(self):
        m=PipelineMeter();METERS.append(m)
        self.assertTrue(C.verify_repair(fixture('linear',m),m)['verified']);self.assertGreater(m.operations,100)
        prep=meter();cert=fixture('raw',prep);tiny=C.Meter(cap=1);METERS.append(tiny)
        with self.assertRaises(OverflowError):C.verify_repair(cert,tiny)

if __name__=='__main__':
    try:unittest.main()
    finally:print('SYNTHETIC_WORK module=check_mobius_prefix_repair_063 operations='+str(sum(m.operations for m in METERS)))
