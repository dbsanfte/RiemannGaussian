"""New synthetic mass conservation/copy tests, no scientific060 signature."""
import copy
from fractions import Fraction as Q
import unittest

import mobius_mass_conservation_060 as M

METER=M.Meter()
PARAMETERS={'alpha':'1/257','gamma':'1/3','tau':'3/7','primes':[2,5],'p':2,'q':5}


class MassTests(unittest.TestCase):
    def test_complete_period_and_inferred_identities(self):
        result=M.discover(PARAMETERS,4,METER)
        self.assertEqual(result['weight_vectors_examined'],256)
        self.assertTrue(result['basis_identities']);self.assertTrue(result['positive_copy_certificates'])
        for ident in result['basis_identities']:
            for n in (0,1,3,19,40,41,83):
                lhs=sum(Q(w)*v for w,v in zip(ident['profile_coefficients'],M.profile_vector(n,2,5)))
                rhs=sum(Q(t['c'])*(n//t['d']) for t in ident['floor_coefficients'])
                self.assertEqual(lhs,rhs)

    def test_smooth_convolution_includes_units_and_small_arguments(self):
        signature=M.signature(PARAMETERS,METER)
        ident=M.identity(PARAMETERS,['1','0','1','1'],signature,METER)
        self.assertIsNotNone(ident)
        self.assertEqual(M.smooth_count([2,5],Q(0),METER),0)
        self.assertEqual(M.smooth_count([2,5],Q(1),METER),1)
        self.assertEqual(M.smooth_count([2,5],Q(10),METER),6)
        for N in (2,3,7,11):
            # Independent ordinary-mu trial division in the tiny fixture.
            total=Q(0)
            for d in range(1,4*N+1):
                if d%2==0 or d%5==0:continue
                n=d;mu=1;r=2
                while r*r<=n:
                    if n%r==0:
                        n//=r;mu=-mu
                        if n%r==0:mu=0;break
                    r+=1
                if n>1 and mu:mu=-mu
                index=(4*N)//d
                total+=mu*sum(Q(w)*v for w,v in zip(ident['profile_coefficients'],M.profile_vector(index,2,5)))
                METER.charge(32)
            self.assertEqual(total,M.exact_smooth_mass(ident,N,METER))

    def test_copies_preserve_signed_source_and_exhaust_smaller_mass(self):
        tokens=[{'d':1,'profile':'P','sign':1,'kernel_sign':1,'mu':1,'magnitude':12.0},
                {'d':7,'profile':'Q','sign':-1,'kernel_sign':1,'mu':-1,'magnitude':3.0},
                {'d':11,'profile':'D','sign':-1,'kernel_sign':-1,'mu':1,'magnitude':6.0}]
        weights=[2,1,3,1]
        for mode in ('global','profile_then_global'):
            plan=M.copy_plan(tokens,weights,mode,METER)
            self.assertEqual(plan['copy_count'],6);self.assertEqual(plan['signed_copy_count'],-2)
            self.assertEqual(len(plan['unmatched']),2)
            covered=sum(plan['pairs'],[])+plan['unmatched']
            self.assertEqual(len({tuple(x) for x in covered}),6)
            self.assertGreaterEqual(plan['pair_cost_float']+plan['leftover_cost_float'],3)
            changed=copy.deepcopy(tokens[::-1])
            for t in changed:t['magnitude']*=17
            other=M.copy_plan(changed,weights,mode,METER)
            self.assertEqual(plan['pairs'],other['pairs']);self.assertEqual(plan['unmatched'],other['unmatched'])

    def test_resource_and_nonconservation_gates(self):
        with self.assertRaises(OverflowError):M.signature(dict(PARAMETERS,p=101,q=103),METER)
        with self.assertRaises(ValueError):M.discover(PARAMETERS,17,METER)
        result=M.signature(PARAMETERS,METER)
        self.assertIsNone(M.identity(PARAMETERS,['1','0','0','0'],result,METER))
        with self.assertRaises(ValueError):M.copy_plan([], [1,1,0,2],meter=METER)

    def test_independent_admission_of_inferred_mass_bound(self):
        import check_mobius_mass_conservation_060 as C
        result=M.discover(PARAMETERS,4,METER)
        cm=C.Meter()
        for ident in result['basis_identities']:self.assertTrue(C.verify_identity(ident,cm)['verified'])
        for cert in result['positive_copy_certificates']:
            verdict=C.verify_copy_bound(cert,cm)
            self.assertTrue(verdict['verified'])
            bad=copy.deepcopy(cert);bad['coefficient']='0'
            with self.assertRaises(ValueError):C.verify_copy_bound(bad,cm)
        METER.charge(cm.operations)


if __name__=='__main__':unittest.main()
