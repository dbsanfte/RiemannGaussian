from fractions import Fraction as F
import hashlib,json,math
import unittest
import critical_core_grammar as g

FEATURES=[{'core_depth':h,'theta':t} for h in (1,2,3,5) for t in ('1/6','1/3','1/2')]
TARGETS=[{'r':1,'l':0,'filter':[{'divisor':1,'weight':'1'}]},
         {'r':1,'l':1,'filter':[{'divisor':1,'weight':'1'}]},
         {'r':1,'l':1,'filter':[{'divisor':1,'weight':'1'},{'divisor':6,'weight':'-11/4'}]}]


def factors(n):
    out=[];p=2
    while p*p<=n:
        e=0
        while n%p==0:e+=1;n//=p
        if e:out.append((p,e))
        p+=1
    if n>1:out.append((n,1))
    return out


def coefficient(n,target):
    fs=factors(n)
    if target['l']==0:return 0 if any(e>1 for p,e in fs) else (-1)**len(fs)
    return (-1)**sum(e for p,e in fs)*2**len(fs)


def floor_power(X,p):
    p=F(p);value=0
    while (value+1)**p.denominator<=X**p.numerator:value+=1
    return value


class CriticalCoreContracts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.p=g.profile([1,2,4,8,16,32,64],TARGETS,FEATURES,use_numpy=False)

    def test_every_raw_gram_and_cross_arithmetic_coordinate(self):
        self.assertEqual(self.p['status'],'available')
        for row in self.p['value']['rows']:
            X=row['X'];target=next(t for t in TARGETS if g.digest(t)==row['target_id']);T=2*X-1
            base=[0]+[coefficient(n,target) for n in range(1,T+1)]
            for n in range(1,T+1):base[n]+=base[n-1]
            pref=[base]
            for f in FEATURES:
                h=f['core_depth'];z=floor_power(X,f['theta']);u=math.isqrt(X);r=[0]
                for m in range(1,T+1):
                    fs=factors(m)
                    if fs:p,e=fs[0];core=m//p**e
                    else:p,e,core=1,0,1
                    active=m>1 and p<=z and e%2==0 and core<=u and (core==1 or sum(e for p,e in factors(core))>h)
                    r.append(r[-1]+(coefficient(m,{'l':1}) if active else 0))
                pref.append(r)
            Q=math.lcm(*(F(t['weight']).denominator for t in target['filter']))
            cols=[[sum(int(F(t['weight'])*Q)*p[n//t['divisor']] for t in target['filter']) for n in range(X,2*X)] for p in pref]
            matrix=[[sum(a*b for a,b in zip(x,y)) for y in cols] for x in cols]
            self.assertEqual(matrix,row['gram_numerators'])
            self.assertEqual(row['gram_base_denominator'],X*X*Q*Q)
            self.assertEqual(row['feature_ids'],['base_G']+[g.feature_descriptor(f)['feature_id'] for f in FEATURES])
            for f,d in zip(FEATURES,row['correction_denominators'][1:]):
                power=2*(f['core_depth']+1)
                self.assertGreaterEqual(d**power,X)
                self.assertLess((d-1)**power,X)

    def test_reconstruction_covers_all_prefixes_all_even_exponents(self):
        for rec in self.p['value']['source_profiles']:
            X=rec['X'];T=2*X-1;f=next(g.feature_descriptor(f) for f in FEATURES if g.feature_descriptor(f)['feature_id']==rec['feature_id']);h=f['core_depth'];z=rec['cutoffs']['z'];u=rec['cutoffs']['u']
            full=[0];retained=[0];removed=[0];classes=[]
            for m in range(1,T+1):
                fs=factors(m)
                if fs:p,e=fs[0];b=m//p**e
                else:p,e,b=1,0,1
                active=m>1 and p<=z and e%2==0 and b<=u
                k=0 if not active else 1 if b==1 else 2 if sum(e for p,e in factors(b))>h else 3
                classes.append(k);a=coefficient(m,{'l':1}) if active else 0
                full.append(full[-1]+a);retained.append(retained[-1]+(a if k in (1,2) else 0));removed.append(removed[-1]+(a if k==3 else 0))
            self.assertEqual(full,[a+b for a,b in zip(retained,removed)])
            for name,values in [('full',full),('retained',retained),('removed',removed)]:self.assertEqual(rec[name+'_prefix_sha256'],g.digest(values))
            self.assertEqual(rec['class_counts'],[classes.count(i) for i in range(4)])
            self.assertEqual(rec['coverage_sha256'],g.digest(classes))
        # Powers4,16,64 are all retained unit cores at sufficiently large cutoff.
        rec=next(r for r in self.p['value']['source_profiles'] if r['X']==64 and r['feature_id']==g.feature_descriptor({'theta':'1/2','core_depth':5})['feature_id'])
        self.assertGreaterEqual(rec['class_counts'][1],3)

    def test_numpy_raw_integer_gram_matches_python(self):
        other=g.profile([1,8,64],TARGETS,FEATURES,use_numpy=True)
        self.assertEqual(other['status'],'available')
        old={(r['X'],r['target_id']):r for r in self.p['value']['rows']}
        for row in other['value']['rows']:
            original=old[(row['X'],row['target_id'])]
            for name in ('gram_numerators','gram_base_denominator','correction_denominators','source_profile_sha256'):
                self.assertEqual(row[name],original[name])

    def test_resource_failure_never_returns_partial_profile(self):
        for kwargs in ({'work_budget':1},{'max_n':10},{'bit_budget':2}):
            out=g.profile([64],TARGETS,FEATURES,**kwargs)
            self.assertEqual(out['status'],'missing');self.assertIsNone(out['value'])

    def test_invalid_and_noncanonical_features(self):
        for feature in ({'theta':'0','core_depth':1},{'theta':'1/3','core_depth':True},{'theta':0.5,'core_depth':2}):
            self.assertEqual(g.profile([1],TARGETS,[feature])['status'],'invalid')
        descriptor=g.feature_descriptor({'theta':'2/6','core_depth':100})
        self.assertEqual(descriptor['theta'],'1/3')
        descriptor['feature_id']='0'*64
        self.assertEqual(g.profile([1],TARGETS,[descriptor])['status'],'invalid')

    def test_signed_recovery_keeps_original_target_and_charges_norms(self):
        corrections=[{'feature':g.feature_descriptor(FEATURES[0]),'weight':'-3/2'},{'feature':g.feature_descriptor(FEATURES[-1]),'weight':'1/4'}]
        cert=g.recovery_certificate(TARGETS[2],corrections)
        self.assertEqual(cert['corrector_weight_l1'],'7/4')
        self.assertEqual(cert['filter_l1'],'15/4')
        self.assertTrue(cert['cofinal_H_energy_iff_original_G_energy'])
        self.assertFalse(cert['ordinary_Mellin_pole_argument_applies_directly_to_H'])
        self.assertFalse(cert['actual_H_energy_bound_proved']);self.assertFalse(cert['RH_proved'])
        self.assertTrue(cert['conditional_original_G_pole_bridge']['conditional_bridge_admitted'])


if __name__=='__main__':unittest.main()
