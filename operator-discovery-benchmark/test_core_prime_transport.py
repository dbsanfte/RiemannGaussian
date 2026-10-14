import unittest
from flint import arb,ctx
import core_prime_transport as P

TOTAL=0
class Meter:
    def charge(self,n=1):
        global TOTAL
        TOTAL+=n
    def live(self,n):pass
def tearDownModule():print('SYNTHETIC_WORK module=test_core_prime_transport operations='+str(TOTAL))
def program(theta='1'):return dict(cofactor=2,theta=theta,capacity_fraction='1/2',load_multiple=4,keep_failed_windows=True)

class Transports(unittest.TestCase):
    def setUp(self):ctx.prec=192;self.m=Meter()
    def coefficients(self):
        f=[arb(0)]*32;f[1]=arb(-3)
        for p in (2,3,5,7,11,13,17,19,23,29,31):f[p]=arb(-1)
        for t in (6,10,14,22,26):f[t]=arb(8)
        return f
    def test_mass_and_global_log_memory(self):
        f=self.coefficients();s=P.transform(f,program(),self.m);P.exact_scores(s,f,[1,2,4,8,16],self.m)
        for w in s['windows']:
            self.assertTrue(sum((f[n]-s['g'][n] for n in range(w['start'],w['stop'])),arb(0)).contains(0))
            self.assertTrue(s['D'][w['stop']-1].contains(0))
        self.assertTrue(s['g'][1].overlaps(f[1]));self.assertFalse(s['B_D'][31].contains(0))
        literal=sum((a*(arb(t).log()-arb(p).log()) for p,t,a in s['assignments']),arb(0))
        self.assertTrue(s['B_D'][31].overlaps(literal))
        self.assertEqual([(p,t) for p,t,a in s['windows'][-1]['assignments']],[(17,22),(19,26),(23,22),(29,26),(31,22)])
    def test_whole_window_fallback_on_aggregate_capacity(self):
        f=self.coefficients();f[22]=arb(2);s=P.transform(f,program(),self.m)
        self.assertEqual(s['windows'][-1]['reason'],'capacity')
        self.assertTrue(all(s['g'][n].overlaps(f[n]) for n in range(16,32)))
        self.assertTrue(s['g'][11].is_zero())
    def test_fractional_complete_windows_and_conditional_proof_scope(self):
        s=P.transform(self.coefficients(),program('1/2'),self.m)
        self.assertEqual([n for w in s['windows'] for n in range(w['start'],w['stop'])],list(range(1,32)))
        c=P.theory(program('1/2'));self.assertTrue(c['cofinal_recovery']);self.assertFalse(c['eventual_prime_removal_proved'])
        c=P.theory(program('5/6'));self.assertEqual(c['energy_error_power'],'0');self.assertFalse(c['critical_pole_preservation'])
        self.assertFalse(c['whole_transformed_core_bound_proved'])
        rows=P.catalogue(self.m);self.assertEqual(len(rows),90);self.assertEqual(sum(r['admitted'] for r in rows),28)
        for m,positive in ((12,True),(6,False),(4,False)):
            p=program('2/3');p['cofactor']=m;self.assertEqual(P.theory(p)['cofactor_leading_capacity_positive'],positive)
