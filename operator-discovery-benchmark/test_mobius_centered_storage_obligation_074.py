from fractions import Fraction as Q
import unittest

import mobius_centered_storage_obligation_074 as E


def candidate(theta, directions):
    return dict(schema='signed-prime-storage-candidate-v1',
                spec=dict(profile=[['8','10','1'],['16','20','-1']],theta=theta),
                labels=['Z','unit','omega1','omega2','omega3','omega_ge4']+['smooth:'+t for t in theta],
                q='1',precision=20,rays=[dict(weight='3/7',direction=v) for v in directions],
                C='0',base_upper='0',training_scales=[],training_upper='0',search_metadata={},
                uniform_domination_proved=True,uniform_recurrence_proved=False,
                uniform_head_bound_proved=False,RH_proved=False)


def factors(n):
    original=n;mu=1;largest=1;omega=0;divisor=2
    while divisor*divisor<=n:
        if n%divisor==0:
            largest=divisor;omega+=1;mu=-mu;n//=divisor
            if n%divisor==0:mu=0
            while n%divisor==0:n//=divisor
        divisor+=1
    if n>1:largest=n;omega+=1;mu=-mu
    return mu,largest,omega,original>1 and omega==1 and mu==-1


class ObligationTests(unittest.TestCase):
    def test_exact_prime_blocks_reconstruct_actual_signed_ray_with_units_and_floors(self):
        theta=['1/2','17/31','4/5','31/32']
        v=['1','7','2','2','2','2','1','-3','1','1']
        result=E.export(candidate(theta,[v]),'centered_high')
        ray=result['rays'][0]
        self.assertEqual(ray['target_coefficient'],'3')
        self.assertEqual([b['coefficient'] for b in ray['prime_blocks']],['1','-2','-1'])
        for k in (1,2,5,29,53):
            X=20*k;table=[(0,1,0,False)]+[factors(n) for n in range(1,X+1)]
            prefix=[0]
            for mu,_,_,_ in table[1:]:prefix.append(prefix[-1]+mu)
            def Z(t):
                return sum(s*prefix[(a*t).numerator//(a*t).denominator]
                           for a,s in ((10,1),(8,-1),(20,-1),(16,1)))
            direct=Q(0)
            for n in range(1,X+1):
                mu,largest,omega,_=table[n]
                w=int(8*k<n<=10*k)-int(16*k<n<=20*k)
                sector=1 if n==1 else min(omega,4)+1
                coefficient=Q(v[0])+Q(v[sector])
                for t,c in zip(map(Q,theta),map(Q,v[6:])):
                    if largest**t.denominator<=X**t.numerator:coefficient+=c
                direct+=mu*w*coefficient
            reduced=Q(ray['target_coefficient'])*Z(Q(k))
            for block in ray['prime_blocks']:
                lo,hi=Q(block['lower_theta']),Q(block['upper_theta'])
                for p in range(2,X+1):
                    if table[p][3] and p**lo.denominator>X**lo.numerator and p**hi.denominator<=X**hi.numerator:
                        reduced+=Q(block['coefficient'])*Z(Q(k,p))
            self.assertEqual(direct,reduced,(k,direct,reduced))
        self.assertTrue(result['integer_drift_does_not_control_rational_arguments'])
        self.assertFalse(result['uniform_recurrence_proved'])

    def test_unknown_mixture_is_exported_without_discarding_small_coefficients(self):
        v=['0']*6+['1/1048576','1']
        result=E.export(candidate(['2/7','1/2'],[v]),'open_mixed')
        self.assertEqual(result['rays'][0]['status'],'UNREGISTERED_LOW_CUTOFF_CORRELATION')
        self.assertEqual(result['rays'][0]['original_direction'],v)
        self.assertNotIn('prime_blocks',result['rays'][0])

    def test_later_finite_pass_never_erases_an_earlier_counterexample(self):
        fit=dict(history=[dict(adaptation_status='REFUTED',adaptation_violations=30)])
        final=dict(learned=dict(status='VERIFIED_ON_FINITE_DOMAIN',violating_scales=[]))
        result=E.disposition(fit,final)
        self.assertEqual(result['status'],'REFUTED_ON_KNOWN_ADAPTATION_DOMAIN')
        self.assertFalse(result['promoted_to_uniform_bound'])
        fit['history'][-1]=dict(adaptation_status='VERIFIED_ON_FINITE_DOMAIN',adaptation_violations=0)
        self.assertEqual(E.disposition(fit,final)['status'],'FINITE_SURVIVOR_REQUIRES_ANALYTICAL_PROOF')
        self.assertFalse(E.disposition(fit,final)['uniform_recurrence_proved'])


if __name__=='__main__':unittest.main()
