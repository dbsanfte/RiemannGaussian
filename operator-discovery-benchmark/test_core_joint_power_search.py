"""Independent finite semantics for the supplied all-real remainder theorem."""
from fractions import Fraction as Q
import unittest
from flint import arb, ctx
from prime_bank_candidates import Meter
import core_joint_power_search as P

M = Meter(50000000, 180)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_core_joint_power_search operations='+str(M.operations))


def ball(q):
    q = Q(q)
    return arb(q.numerator)/q.denominator


def power(n, q):
    return arb(n)**ball(q) if n else arb(0)


def Kprefix(t, theta):
    n = t.numerator//t.denominator
    M.charge(100*(n+1))
    return sum((power(j, Q(theta)-1) for j in range(1, n+1)), arb(0))


def moment(a, theta):
    M.charge(100*len(a))
    return sum((ball(v)/power(d, theta) for d, v in enumerate(a) if d and v), arb(0))


def complete_convolution(a, b):
    values = [Q(0)]*((len(a)-1)*(len(b)-1)+1)
    for d, x in enumerate(a[1:], 1):
        for e, y in enumerate(b[1:], 1):
            values[d*e] += x*y
            M.charge(10)
    return values


def fixture():
    specifications = [('B', 'beta', ['A','A','K'], '1/3'),
                      ('U', '-beta', ['A','B','K'], '1/3'),
                      ('power', '-R_u', ['B','K'], '1/3'),
                      ('V', '-beta', ['A','R'], None)]
    terms, refs, cases = [], [], []
    for name, scalar, factors, shift in specifications:
        key = dict(mode=name, a=int(name == 'V'), b=0)
        terms.append(dict(key=key, source_scalar=scalar, selected_depth=0,
            alternatives=[dict(depth=0,pieces=[dict(expression=factors,coefficient='1',
                energy=dict(constant='1000000', power='4', log_degree=2, uniform_constant=None))])]))
        refs.append(dict(source_key=key,depth=0,piece=0))
        cases.append(dict(mode=dict(name=name,positive_shift=shift)))
    return dict(id=4,alpha='1/6',gamma='5/6',cases=cases), dict(terms=terms), refs


class JointPowerSearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 192

    def test_integral_remainder_fractional_powers_and_small_t(self):
        for theta in P.THETAS:
            for t in (Q(0), Q(1,7), Q(999,1000), Q(1), Q(5,3), Q(2), Q(57,8), Q(31), Q(999,32)):
                leading = ball(t)**ball(theta)/ball(theta) if t else arb(0)
                remainder = Kprefix(t, theta)-leading
                self.assertTrue(remainder <= 0 or remainder.contains(0))
                lower = remainder+1/ball(theta)
                self.assertTrue(lower >= 0 or lower.contains(0))
                M.charge(200)

    def test_signed_complete_remainder_keeps_d_greater_than_n(self):
        h = [Q(0)]+[Q((7*d)%13-6, d%3+1) for d in range(1, 24)]
        h[-1] = Q(11,3)
        for theta in ('1/6','1/3','2/3','1'):
            weighted = moment(h,theta)
            mass = sum(map(abs,h))
            for n in (1,2,3,7,16,23,31):
                original = sum((ball(h[d])*Kprefix(Q(n,d),theta) for d in range(1,len(h))), arb(0))
                center = original-weighted*power(n,theta)/ball(theta)
                literal = sum((ball(h[d])*(Kprefix(Q(n,d),theta)
                    -ball(Q(n,d))**ball(theta)/ball(theta)) for d in range(1,len(h))), arb(0))
                self.assertTrue(center.overlaps(literal))
                self.assertTrue(abs(center) <= ball(mass)/ball(theta))
            incomplete = moment(h[:4],theta)
            self.assertFalse(weighted.overlaps(incomplete))

    def test_finite_convolution_moments_use_full_product_support(self):
        a = [Q(0),Q(-2),Q(1,3),Q(3),Q(0),Q(-1)]
        b = [Q(0),Q(1),Q(-1),Q(2),Q(-1,2)]
        product = complete_convolution(a,b)
        for theta in ('1/3','1/2','2/3','1'):
            self.assertTrue(moment(product,theta).overlaps(moment(a,theta)*moment(b,theta)))
            self.assertFalse(moment(product[:7],theta).overlaps(moment(a,theta)*moment(b,theta)))

    def test_joint_polynomial_cancels_opposite_signed_modes(self):
        common = dict(coefficient='1',factors=['A','C'],kernel_shift='1/3',
            old_energy=dict(constant='100',power='2',log_degree=0,uniform_constant=None))
        pieces = [dict(common,id=0,source_scalar='beta'),dict(common,id=1,source_scalar='-beta')]
        output = P.subset(3,pieces,P.profiles(['1/3']),'1/6','1/3',M)
        self.assertEqual(output['joint_drifts'],[])
        self.assertEqual(len(output['remainders']),2)
        self.assertTrue(all(r['energy']['uniform_constant'] is not None for r in output['remainders']))
        negative = dict(common,source_scalar='-R_u',coefficient='-2')
        powers, coefficient = P.scalar_polynomial(negative)
        self.assertEqual(powers,(1,0,1,1))
        self.assertEqual(coefficient,2)

    def test_profile_matching_and_unsupported_power(self):
        profiles = P.profiles(['1/3'])
        supported = [p for p in profiles if p['status']=='supported']
        self.assertEqual([(p['theta'],p['solved_multiplier']) for p in supported],[('2/3','3/2')])
        row,prefix,refs = fixture()
        for case in row['cases']:
            if case['mode']['positive_shift'] is not None:
                case['mode']['positive_shift']='1/7'
        output = P.search(row,prefix,refs,M)
        self.assertEqual(output['selected_mask'],0)
        self.assertTrue(all(a['status']=='unsupported_power_profile' for a in output['alternatives'][1:]))
        self.assertFalse(output['whole_signed_bound_proved'])

    def test_drift_envelope_retains_lower_power_log(self):
        polynomial = [dict(powers=[1,0,0,0],coefficient='1'),dict(powers=[0,1,0,0],coefficient='-2')]
        bound = P.drift_bound('1/3',polynomial,'1/6','5/6')
        self.assertEqual(bound['log_degree'],1)
        self.assertEqual(bound['power'],'4/9')
        self.assertEqual(P.energy(**bound)['log_degree'],2)

    def test_current_target_partition_and_joint_drift_remain_open(self):
        row,prefix,refs=fixture()
        result=P.search(row,prefix,refs,M)
        parent=dict(remaining_signed_pieces=refs,parent_obligation_id='generic',goal=dict(p='2'))
        construction=dict(channels=[dict(eta='1/6',polynomial=['1','-2','1'])])
        output=P.reduction(parent,construction,result)
        self.assertEqual(len(output['newly_paid']),3)
        self.assertEqual(output['remaining_source_refs'],[refs[-1]])
        self.assertEqual(output['remaining_joint_drifts'],['2/3'])
        self.assertEqual(output['remaining_centered_remainders'],[])
        self.assertTrue(output['full_finite_moments_retained'])
        self.assertTrue(output['transport_error_retained'])
        self.assertTrue(output['all_remaining_crosses_retained'])
        self.assertFalse(output['whole_signed_bound_proved'])
        self.assertEqual(output['goal']['status'],'open')
        parent['goal']['p']='-1/6'
        with self.assertRaises(ValueError): P.reduction(parent,construction,result)
        with self.assertRaises(ValueError): P.resolve(prefix,refs+[refs[0]])


if __name__ == '__main__':
    unittest.main()
