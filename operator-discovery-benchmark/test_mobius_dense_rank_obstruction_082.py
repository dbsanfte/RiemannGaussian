"""Exact interval invention for registered geometry-only profile families."""
import unittest
from fractions import Fraction as Q
import mobius_dense_rank_obstruction_082 as R

def program(memory=1,scales=('1/4',),extended=False,eta='1'):
    kernel=[dict(divisor=d,weight=w) for d,w in [(4,'-1'),(5,'1'),(8,'1'),(10,'-1')]]
    if extended:kernel+= [dict(divisor=d,weight=w) for d,w in [(12,'-3547/8192'),(15,'3547/8192'),(24,'3547/8192'),(30,'-3547/8192')]]
    return dict(schema='dense-divisor-completion-v1',kernel=sorted(kernel,key=lambda r:r['divisor']),memory=memory,rays=[],drift_multiplier='3/2',profiles=[dict(scale=s,eta=eta) for s in scales],theta=[['0']*(memory+1) for _ in scales],gram_weights=['0']*(memory+1+len(scales)))

class RankIntervalTests(unittest.TestCase):
    def test_pilot_families_exact_moments(self):
        rosters=[('1/4',),('1/4','1/5','1/8','1/10'),('1/4','3/7','7/11','10/13'),('1/4','3/28','7/44','5/26'),('1/4','1/12','1/20','1/28')]
        for extended in (False,True):
            for memory in (1,2,3):
                for scales in rosters:
                    p=program(memory,scales,extended);got=R.discover(p)
                    self.assertEqual(got['status'],'PROPOSED_UNIFORM_RANK_OBSTRUCTION',got)
                    cert=got['certificate'];rows=cert['intervals']
                    self.assertGreater(Q(cert['tau']),0);self.assertEqual(Q(cert['lower_coefficient']),Q(cert['H00'])*Q(cert['tau'])**2)
                    for i in range(memory+1):self.assertEqual(sum(Q(r['t'])*Q(r['source'][i]) for r in rows),int(i==0))
                    for j in range(len(scales)):self.assertEqual(sum(Q(r['t'])*r['profiles'][j] for r in rows),0)
                    for r in rows:
                        self.assertGreater(Q(r['right']),Q(r['left']))
                        self.assertGreaterEqual(cert['threshold'],R.interval_threshold(R.C.parse_program(p),r,R.C.Meter()))
    def test_actual_full_fractional_family(self):
        for extended in (False,True):
            for memory in (1,2,3):
                p=program(memory,('1/4','1','1','1/2'),extended)
                if memory==2:p['rays']=[dict(a=['1','1'],weight='1/4')]
                if memory==3:p['rays']=[dict(a=['1','1','-1'],weight='1')]
                for row,eta in zip(p['profiles'],('1','3/7','7/11','10/13')):row['eta']=eta
                got=R.discover(p)
                self.assertEqual(got['status'],'PROPOSED_UNIFORM_RANK_OBSTRUCTION',got)
                for row in got['certificate']['intervals']:self.assertEqual(row['profiles'][1:],[0,0,0])

    def test_sublinear_threshold_and_duplicate_profiles(self):
        p=program(3,('1/4','1/4'),True,eta='1/2');got=R.discover(p)
        self.assertEqual(got['status'],'PROPOSED_UNIFORM_RANK_OBSTRUCTION',got)
        for r in got['certificate']['intervals']:self.assertEqual(r['profiles'],[0,0])
        self.assertEqual(R._threshold_power(Q(9,4),Q(1,2),R.C.Meter()),6)
    def test_bounded_failure_and_scope(self):
        self.assertEqual(R.discover(program(),max_denominator=2)['status'],'NOT_FOUND_WITHIN_GRAMMAR')
        p=program();p['kernel'][0]['weight']='-2'
        self.assertEqual(R.discover(p)['status'],'REJECTED')
        p=program(eta='999999/1000000')
        self.assertEqual(R.discover(p)['status'],'RESOURCE_LIMIT')

if __name__=='__main__':unittest.main()
