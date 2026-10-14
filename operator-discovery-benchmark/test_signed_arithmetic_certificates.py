import copy
from fractions import Fraction as Q
from math import gcd
import unittest
import signed_arithmetic_certificates as c


class KernelTests(unittest.TestCase):
    def test_radical_integer_square_certificates(self):
        for bits in (1,4,48):
            for numerator in range(31):
                for denominator in range(1,13):
                    value=Q(numerator,denominator)
                    lo,hi=c.sqrt_enclosure(value,bits)
                    self.assertLessEqual(lo*lo,value)
                    self.assertGreaterEqual(hi*hi,value)
        self.assertEqual(c.sqrt_enclosure(Q(9,4)),(Q(3,2),Q(3,2)))

    def test_general_learned_stencils_and_mutation(self):
        for terms in [[(1,-4),(2,1)],[(1,-32),(4,-2),(8,1)],[(1,16),(2,-8),(4,1)]]:
            kernel=c.kernel_from_dilates(terms)
            cert=c.certify_kernel(kernel)
            self.assertEqual(kernel.integral(),Q(3,2)*sum(Q(s)**2*Q(a) for s,a in terms))
            self.assertTrue(cert['admitted_zero_moment_component'])
            self.assertTrue(c.verify_kernel_certificate(cert))
            fake=copy.deepcopy(cert)
            fake['weighted_sqrt_variation_upper']='0'
            self.assertFalse(c.verify_kernel_certificate(fake))
        kernel=c.kernel_from_dilates([(1,-4),(2,1)])
        self.assertEqual(kernel.knots,((Q(0),Q(-2)),(Q(1),Q(-2)),(Q(2),Q(2)),(Q(4),Q(0))))
        self.assertLess(Q(c.certify_kernel(kernel)['weighted_sqrt_variation_upper']),9)
        self.assertFalse(c.certify_kernel(c.kernel_from_dilates([(1,1)]))['admitted_zero_moment_component'])

    def test_general_continuous_polygon(self):
        kernel=c.PiecewiseLinearKernel(((0,0),(1,1),(2,0),(3,-1),(4,0)))
        cert=c.certify_kernel(kernel)
        self.assertTrue(cert['left_endpoint_zero'])
        self.assertTrue(cert['admitted_zero_moment_component'])
        self.assertTrue(c.verify_kernel_certificate(cert))
        with self.assertRaises(ValueError):
            c.PiecewiseLinearKernel(((0,0),(1,1)))
        with self.assertRaises(TypeError):
            c.kernel_from_dilates([(1.0,1)])

    def test_actual_component_bounds_without_floats(self):
        kernels=[c.kernel_from_dilates([(1,-4),(2,1)]),c.PiecewiseLinearKernel(((0,0),(1,1),(2,0),(3,-1),(4,0)))]
        mu=c.actual_mobius(128)
        for kernel in kernels:
            for modulus in (1,2,6,30):
                for r in (1,2,5,7):
                    cert=c.component_certificate(kernel,modulus,r)
                    coefficient=Q(cert['bound_coefficient_before_r_sqrt'])
                    for X in (1,2,3,8,32):
                        observed=sum((mu[g]**2*X*kernel.value(Q(r*g,X)) for g in range(1,128+1) if gcd(g,modulus)==1),Q(0))
                        self.assertLessEqual(observed**2,coefficient**2*X**3/r)
        self.assertEqual(c.modulus_charge(30)['charge'],10)

    def test_full_pair_partition_and_actual_provenance(self):
        mu=c.actual_mobius(64)
        kernels=[c.kernel_from_dilates([(1,-4),(2,1)]),c.kernel_from_dilates([(1,16),(2,-8),(4,1)])]
        for kernel in kernels:
            for X in (1,2,3,4,8):
                for B in (0,1,2,4,100):
                    record=c.primitive_pair_partition(mu,X,B,kernel)
                    limit=record['limit']
                    direct=sum((mu[n]*mu[m]*X*kernel.value(Q(max(n,m),X)) for n in range(1,limit+1) for m in range(1,limit+1)),Q(0))
                    residual=Q(0)
                    for n in range(1,limit+1):
                        for m in range(n+1,limit+1):
                            if m//gcd(n,m)>B:
                                residual+=2*mu[n]*mu[m]*X*kernel.value(Q(m,X))
                    self.assertEqual(Q(record['full']),direct)
                    self.assertEqual(Q(record['residual_pairs']),residual)
                    self.assertFalse(record['dense_signed_bound_proved'])
        fake=mu.copy();fake[8]=1
        with self.assertRaises(ValueError):
            c.primitive_pair_partition(fake,4,2,kernels[0])
        record=c.primitive_pair_partition(mu,2,1,kernels[0])
        self.assertEqual(Q(record['full']),6)

    def test_conditional_bridge_scopes(self):
        cert=c.dilate_bridge_certificate([(1,-4),(2,1)],Q(1,12))
        self.assertTrue(cert['conditional_bridge_admitted'])
        self.assertFalse(cert['signed_inequality_proved'])
        self.assertFalse(cert['RH_proved'])
        for terms in [[(1,16),(2,-8),(4,1)],[(1,-9),(3,1)],[(1,-3),(2,1)]]:
            self.assertFalse(c.dilate_bridge_certificate(terms,Q(1,6))['conditional_bridge_admitted'])
        with self.assertRaises(ValueError):
            c.dilate_bridge_certificate([(1,-4),(2,1)],0)

    def test_positive_transformed_energy_bridge(self):
        for terms,expected in [([(1,-4),(2,1)],['1']), ([(1,-32),(2,8),(4,-4),(8,1)],['8','0','1']), ([(1,32),(2,-12),(4,1)],['-8','1'])]:
            cert=c.positive_energy_transform_certificate(terms,Q(1,12))
            self.assertEqual(cert['factor_coefficients'],expected)
            self.assertTrue(cert['factorization_admitted'])
            self.assertFalse(cert['signed_inequality_proved'])
            self.assertEqual(cert['conditional_bridge_admitted'],all(Q(x)>=0 for x in expected))
            for X in (1,2,4):
                A=lambda n: Q(n**3+n+1)
                H=lambda n: sum(Q(b)*A(scale*n) for scale,b in cert['factor_terms'])
                F=sum(Q(weight)*A(scale*X) for scale,weight in terms)
                self.assertEqual(F,H(2*X)-4*H(X))
        nonzero=c.positive_energy_transform_certificate([(1,-3),(2,1)],Q(1,6))
        self.assertEqual(nonzero['exact_constant_remainder'],'1')
        self.assertFalse(nonzero['factorization_admitted'])
        self.assertFalse(nonzero['conditional_bridge_admitted'])
        self.assertEqual(c.positive_energy_transform_certificate([(1,-9),(3,1)],Q(1,6))['status'],'unsupported_domain')
        self.assertEqual(c.positive_energy_transform_certificate([(1,-16),(4,1)],Q(1,6),max_order=1)['status'],'missing')

    def test_energy_only_bridge_obstructions(self):
        cert=c.energy_bridge_obstruction_certificate([(1,32),(2,-12),(4,1)])
        self.assertTrue(cert['energy_only_critical_bridge_obstructed'])
        self.assertEqual(cert['tests'][0]['exact_dilate_polynomial'],'0')
        self.assertFalse(cert['actual_Mobius_claim_disproved'])
        self.assertFalse(c.energy_bridge_obstruction_certificate([(1,-4),(2,1)])['energy_only_critical_bridge_obstructed'])
        self.assertTrue(c.energy_bridge_obstruction_certificate([(1,36),(2,-13),(4,1)])['tests'][0]['obstruction'])
        fourth=c.energy_bridge_obstruction_certificate([(1,-1)],(4,))
        self.assertFalse(fourth['tests'][0]['compatible_with_actual_trivial_cubic_growth'])
        for X in (1,2,4,8):
            energy=lambda n: sum(j*j for j in range(n,2*n))
            self.assertEqual(32*energy(X)-12*energy(2*X)+energy(4*X),2*X)
        with self.assertRaises(ValueError):
            c.energy_bridge_obstruction_certificate([(1,-4),(2,1)],(2,))

    def test_squarefloor_filtered_actual_calibration(self):
        root={'kind':'floor_root','q':2,'offset':0}
        cert=c.liouville_squarefloor_certificate([(root,Q(1,2)),(root,Q(1,2))])
        self.assertTrue(cert['exact_all_scale_law_proved'])
        self.assertFalse(cert['ordinary_unsmoothed_Mobius_or_Liouville_bound_proved'])
        self.assertFalse(c.liouville_squarefloor_certificate([({'kind':'floor_root','q':2,'offset':1},1)])['exact_all_scale_law_proved'])
        mu=c.actual_mobius(128)
        lam=[0]*129
        for n in range(1,129):
            lam[n]=sum(mu[n//(s*s)] for s in range(1,12) if n%(s*s)==0)
        for x in range(129):
            signed=sum(lam[d]*(x//d) for d in range(1,x+1))
            self.assertEqual(signed,c.isqrt(x))


if __name__=='__main__':
    unittest.main()
