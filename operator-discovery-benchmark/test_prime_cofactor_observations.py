"""Tiny independent divisor fixtures; never open the research archive."""
from copy import deepcopy
from fractions import Fraction as Q
import gzip
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

from flint import arb,ctx
import prime_cofactor_observations as O

METERS=[]
FIXTURES=[]
OriginalMeter=O.Meter


def tracked(cap=O.CAP,seconds=O.SECONDS):
    m=OriginalMeter(cap,seconds);METERS.append(m);return m


def certificate():
    B=[['1','1','1','1'],['0','1','0','0'],['0','0','1','0'],['0','0','0','1']]
    den=[[0,0,'1'],[2,1,'-1']]
    def f(num,denominator=den):return dict(numerator=num,denominator=deepcopy(denominator))
    zero=f([],[[0,0,'1']])
    f0=f([[0,0,'1'],[0,1,'-2'],[0,2,'1']])
    f1=f([[0,0,'1'],[0,1,'-1'],[4,1,'-1'],[4,2,'1']])
    f2=f([[0,0,'1'],[4,1,'-1']])
    fm=f([[0,0,'1'],[0,1,'-1']],[[0,0,'1']])
    transfer=[
        [f0,f([[0,1,'1'],[4,1,'-1'],[4,2,'1'],[0,2,'-1']]),
         f([[0,1,'2'],[4,1,'-1'],[0,2,'-1']]),
         f([[0,1,'1'],[2,1,'-1'],[0,2,'-1'],[2,2,'1']])],
        [zero,f1,zero,zero],[zero,zero,f2,zero],[zero,zero,zero,fm]]
    polys=[[[2,'0','-1'],[4,'9/2','1']],
           [[0,'9/2','0'],[2,'-9/2','0'],[4,'9/2','0']],
           [[2,'0','-1'],[4,'0','1']],[[0,'9/2','0']]]
    units=[dict(constant='-9/2',R='-1'),dict(constant='-9/2',R='0'),
           dict(constant='0',R='-1'),dict(constant='-9/2',R='0')]
    return dict(source=O._source(),basis=B,states=[dict(row=r,program={'op':'synthetic'}) for r in B],
        transfer=transfer,unit=units,target_row=['1','0','0','0'],
        domain=dict(prime=True,cofactor_coprime=True,all_valuations=True),
        frontier_bounds=[dict(state=i,prime_polynomial=p) for i,p in enumerate(polys)])


def fixture(H,meter):
    """Direct tiny divisor sums, independently of local Euler series."""
    FIXTURES.append(dict(H=H,source='tiny_actual_four_channel_core',indices=[1,H],
                         archive_read=False))
    old=ctx.prec;ctx.prec=192
    try:
        mu=[arb(0)]*(H+1);ku=[arb(0)]*(H+1);muv=[arb(0)]*(H+1)
        for n in range(1,H+1):
            meter.charge(80);k=n;sign=1
            for p in range(2,n+1):
                if k%p:continue
                e=0
                while k%p==0:k//=p;e+=1;meter.charge()
                if e>=2:sign=0
                elif e==1:sign=-sign
            mu[n]=arb(sign);ku[n]=1/arb(n).root(3);muv[n]=mu[n]*ku[n]*ku[n]
        def conv(a,b):
            c=[arb(0)]*(H+1)
            for d in range(1,H+1):
                for k in range(1,H//d+1):
                    meter.charge(2);c[d*k]+=a[d]*b[k]
            return c
        modes=[conv(ku,conv(mu,mu)),conv(ku,conv(mu,muv)),conv(ku,muv),mu]
        meter.charge(524);z=(arb(2)/3).zeta();Ru=(arb(9)/2)*((arb(4)/3).zeta()/(z*z)-1/z)
        weights=[arb(9)/2,-arb(9)/2,-Ru,-arb(9)/2]
        core=[sum((w*a[n] for w,a in zip(weights,modes)),arb(0)) for n in range(H+1)]
        F=[arb(0)]*(H+1)
        for n in range(1,H+1):F[n]=F[n-1]+core[n];meter.charge(10)
        values=dict(core=core,F=F,log_prefix=[arb(0)]*(H+1),log_abel=[arb(0)]*(H+1))
        for name,a in zip(O.NAMES,modes):
            values['mode:'+name]=a
            prefix=[arb(0)]*(H+1)
            for n in range(1,H+1):prefix[n]=prefix[n-1]+a[n];meter.charge()
            values['prefix:'+name]=prefix
        return [dict(name=name,values=[v.str(55) for v in values[name]]) for name in O.VECTOR_NAMES],core,F
    finally:ctx.prec=old


def write_archive(path,rows):
    with gzip.open(path,'wt',encoding='utf8') as f:
        for row in rows:f.write(json.dumps(row)+'\n')


class Observations(unittest.TestCase):
    def setUp(self):
        self.patcher=patch.object(O,'Meter',side_effect=tracked);self.patcher.start()
        self.addCleanup(self.patcher.stop)

    def test_full_archive_valuation_and_joint_energy(self):
        records,core,F=fixture(31,tracked())
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'tiny.gz';write_archive(path,records)
            result=O.observe_archive(path,certificate(),(1,2,8,16))
        self.assertTrue(result['verified']);self.assertTrue(result['audit']['verified'])
        self.assertFalse(result['whole_signed_bound_proved']);self.assertFalse(result['RH_proved'])
        self.assertEqual(result['audit']['all_prime_polynomial_checks'],11)
        self.assertGreater(result['audit']['valuation_cofactor_cases'],10)
        self.assertEqual(result['exposure']['decoded_H'],31)
        self.assertTrue(result['exposure']['reused_previously_verified_data'])
        self.assertFalse(result['exposure']['held_out'])
        rows={(r['state'],r['X']):r for r in result['rows']}
        self.assertEqual(rows[0,1]['Ecomp'],0)
        self.assertGreater(rows[0,1]['Erough'],0) # complete negative unit retained
        self.assertEqual(rows[0,16]['primecount'],8)
        self.assertEqual(rows[0,8]['primecount'],4)
        expected=sum(float(x.mid())**2 for x in F[16:32])/256
        self.assertAlmostEqual(rows[0,16]['Efull'],expected,places=9)
        for row in result['rows']:
            self.assertAlmostEqual(row['Efull'],row['Erough']+row['Ecomp']+row['cross_twice'],places=8)

    def test_plain_signed_cross_and_cancelled_full_prefix(self):
        m=tracked();audit=O._Audit()
        # Full zero, rough3, complement-3: both positive squares remain.
        row=O._energy_table(1,0,[arb(0),arb(9),arb(9),arb(-18)],0,audit,m)
        self.assertEqual(row['Efull'],0);self.assertEqual(row['cross_twice'],-18)
        self.assertEqual(row['cross_to_diagonal'],-1)
        with self.assertRaises(ArithmeticError):
            O._energy_table(1,0,[arb(0),arb(9),arb(9),arb(0)],0,audit,m)

    def test_certificate_source_unit_and_polynomial_guards(self):
        good=certificate();bad=[]
        c=deepcopy(good);c['source']['channels'][0]['atoms'][1]['shift']=False;bad.append(c)
        c=deepcopy(good);c['unit'][0]['constant']='0';bad.append(c)
        c=deepcopy(good);c['target_row'][0]='0';bad.append(c)
        c=deepcopy(good);c['frontier_bounds'][0]['prime_polynomial'][0][2]='0';bad.append(c)
        c=deepcopy(good);c['basis'][0][0]='1/1';bad.append(c)
        c=deepcopy(good);c['transfer'][0][0]['denominator']=[];bad.append(c)
        c=deepcopy(good);c['domain']['all_valuations']=1;bad.append(c)
        for c in bad:
            with self.assertRaises(ValueError):O._certificate(c,tracked())

    def test_archive_missing_duplicate_horizon_nonfinite(self):
        records,_,_=fixture(15,tracked());variants=[records[:-1],records+[deepcopy(records[0])]]
        v=deepcopy(records);v[2]['values']=v[2]['values'][:-1];variants.append(v)
        v=deepcopy(records);v[0]['values'][0]='1';variants.append(v)
        v=deepcopy(records);v[0]['values'][2]='nan';variants.append(v)
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'bad.gz'
            for rows in variants:
                write_archive(path,rows)
                with self.assertRaises(ValueError):O.observe_archive(path,certificate(),(8,))

    def test_corrupted_finite_square_law_rejected(self):
        records,_,_=fixture(15,tracked())
        # The square audit checks the full transfer, not the fresh multiplier squared.
        c=certificate();c['transfer'][1][1]['numerator']=[[0,0,'1']]
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'tiny.gz';write_archive(path,records)
            with self.assertRaises(ArithmeticError) as error:O.observe_archive(path,c,(8,))
        self.assertIn('operations',error.exception.observation_counts)

    def test_invalid_scales_and_resource_failure(self):
        for scales in ((),(True,),(0,),(2,1),(1,1),(65537,)):
            with self.assertRaises(ValueError):O.observe_archive('never-opened',certificate(),scales)
        with patch.object(O,'Meter',side_effect=lambda:tracked(0)):
            with self.assertRaises(OverflowError) as error:O.observe_archive('never-opened',certificate(),(1,))
        self.assertGreater(error.exception.observation_counts['operations'],0)


if __name__=='__main__':
    start=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Observations))
    operations=sum(m.operations for m in METERS)
    path=Path(__file__).with_name('prime_cofactor_observations_development.json')
    old=json.loads(path.read_text()) if path.exists() else dict(runs=[])
    old['runs'].append(dict(returncode=0 if result.wasSuccessful() else 1,operations=operations,
        tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),
        elapsed_seconds=time.monotonic()-start,peak_cells=max((m.peak_cells for m in METERS),default=0),
        tiny_actual_source_fixture_runs=FIXTURES,production_archive_read=False))
    old.update(module='test_prime_cofactor_observations',operations=sum(r['operations'] for r in old['runs']))
    path.write_text(json.dumps(old,indent=2,sort_keys=True)+'\n')
    print('SYNTHETIC_WORK module=test_prime_cofactor_observations operations='+str(operations),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
