"""Synthetic finite evidence checks; no research archive/source is accessed."""
from copy import deepcopy
from fractions import Fraction
import gzip
import json
from pathlib import Path
import tempfile
import time
import unittest

import numpy as np
from flint import arb,ctx
import coupled_scale_evidence as C

METERS=[]


def meter(cap=C.CAP,seconds=C.SECONDS):
    value=C.Meter(cap,seconds);METERS.append(value);return value


def handle():
    """Entirely synthetic signed coefficient/profile arrays, including units."""
    m=meter();H=15;core=[arb(0)]+[arb((-1)**n*(n%3+1)) for n in range(1,H+1)]
    F=[arb(0)]*(H+1);sq=[arb(0)]*(H+1)
    profiles=[[arb(0)]*(H+1) for _ in range(2)]
    for n in range(1,H+1):
        m.charge(10);F[n]=F[n-1]+core[n];sq[n]=sq[n-1]+core[n]**2
        for i in range(2):
            profiles[i][n]=profiles[i][n-1]+(arb((i+1)*(-1)**n) if n in (2,3,5,7,11,13) else arb(0))
    return dict(meter=m,H=H,scales=(1,2,4,8),divisors=(1,2,3),dimension=2,
                core=core,F=F,F_float=np.array([float(v.mid()) for v in F]),
                squared_prefix=sq,profiles=profiles,
                profile_float=[np.array([float(v.mid()) for v in p]) for p in profiles],
                unit=[arb(-3),arb(2)],unit_float=[-3.,2.],
                resident_cells=500,source_verified=True)


def candidate(ident=1,Ctext='2'):
    return dict(id=ident,recurrence_C=Ctext,program=[
        dict(state=0,divisor=1,exponent='1/3',coefficient='-2'),
        dict(state=1,divisor=3,exponent='0',coefficient='1/2')])


class EvidenceTests(unittest.TestCase):
    def test_prime_profile_unit_subunit_and_strict_cutoff(self):
        h=handle();self.assertTrue(C._profile(h,0,0,2).is_zero())
        self.assertEqual(C._profile(h,0,1,2),-3)
        self.assertEqual(C._profile(h,0,2,2),-3)
        self.assertEqual(C._profile(h,0,3,2),-4)
        self.assertEqual(C._cutoff(1),2);self.assertEqual(C._cutoff(8),4)

    def test_full_gram_cross_and_floor_domain(self):
        h=handle();features=[dict(state=i,divisor=d) for i in range(2) for d in (1,2,3)]
        for X in (1,2,4,8):
            got=np.array(C._gram(h,X,features));expected=np.zeros_like(got)
            for n in range(X,2*X):
                h['meter'].charge(200)
                values=np.array([float(h['F'][n].mid())]+[
                    float(C._profile(h,f['state'],n//f['divisor'],C._cutoff(X)).mid()) for f in features])
                expected+=np.outer(values,values)/(X*X)
            np.testing.assert_allclose(got,expected,rtol=0,atol=1e-14)
            self.assertTrue(np.linalg.eigvalsh(got).min()>-1e-12)
        self.assertLess(C._gram(h,1,features)[0][4],0) # complete negative mixed term

    def test_interval_audit_independent_complete_energies_and_D(self):
        h=handle();c=candidate();result=C.interval_audit(h,[c])
        self.assertTrue(result['verified']);self.assertFalse(result['uniform_recurrence_proved'])
        self.assertEqual(len(result['candidates']),2)
        row=result['candidates'][1];self.assertEqual(len(row['recurrences']),3)
        for block in row['blocks']:
            X=block['X'];expected=arb(0);EH=arb(0)
            for n in range(X,2*X):
                h['meter'].charge(40)
                # Independently expand the two signed terms; all earlier prefixes survive.
                correction=-2/arb(X).root(3)*C._profile(h,0,n,C._cutoff(X))+C._profile(h,1,n//3,C._cutoff(X))/2
                expected+=(h['F'][n]+correction)**2/(X*X);EH+=correction**2/(X*X)
            self.assertTrue(arb(block['EG']['interval']).overlaps(expected))
            self.assertTrue(arb(block['EH']['interval']).overlaps(EH))
            self.assertAlmostEqual(block['EG']['value'],block['EF']['value']+block['EH']['value']+block['cross_twice']['value'],places=10)
            self.assertLessEqual(block['EF']['value'],2*(block['EG']['value']+block['EH']['value'])+1e-10)
        for recurrence in row['recurrences']:
            X=recurrence['X'];D=sum((v*v for v in h['core'][1:4*X]),arb(0))/X
            self.assertTrue(arb(recurrence['D']['interval']).overlaps(D))
            self.assertIn(recurrence['status'],('pass','fail','unresolved'))

    def test_exact_cancellation_and_interval_status(self):
        h=handle();h['scales']=(1,);h['F'][1]=arb(3)
        # At n1 profile state0=-3, so full square vanishes while both components remain.
        energy=C._energy(h,1,[(0,1,Fraction(0),Fraction(1))])
        self.assertTrue(energy['EG'].is_zero());self.assertEqual(energy['EH'],9)
        self.assertEqual(energy['cross_twice'],-18)
        self.assertEqual(C._status(arb(-1)),'pass');self.assertEqual(C._status(arb(1)),'fail')
        self.assertEqual(C._status(arb('0 +/- 1')),'unresolved')

    def test_strict_domains_rational_candidate_and_budget(self):
        h=handle()
        for scales in ((True,), (3,), (2,1), (1,1), (262144,), ()):
            with self.assertRaises(ValueError):C._scales(scales)
        for ds in ((True,), (0,), (3,2), (1,1)):
            with self.assertRaises(ValueError):C._divisors(ds)
        variants=[]
        c=candidate();c['program'][0]['state']=False;variants.append(c)
        c=candidate();c['program'][0]['exponent']='1/1';variants.append(c)
        c=candidate();c['program'][0]['coefficient']=0.5;variants.append(c)
        c=candidate();c['recurrence_C']='-1';variants.append(c)
        c=candidate();c['program'][0]['divisor']=4;variants.append(c)
        for c in variants:
            with self.assertRaises(ValueError):C.interval_audit(h,[c])
        h['meter']=meter(cap=1)
        with self.assertRaises(OverflowError) as error:C.interval_audit(h,[candidate()])
        self.assertGreater(error.exception.evidence_counts['operations'],1)

    def test_archive_malformed_structure_rejected_before_evaluation(self):
        # Twelve artificial zero rows test the decoder only, not the actual-source model.
        rows=[dict(name=name,values=['0']*16) for name in C.O.VECTOR_NAMES]
        variants=[rows[:-1],rows+[deepcopy(rows[0])]]
        r=deepcopy(rows);r[0]['values'][0]='1';variants.append(r)
        r=deepcopy(rows);r[0]['values'][2]='nan';variants.append(r)
        r=deepcopy(rows);r[1]['values']=r[1]['values'][:-1];variants.append(r)
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'synthetic.gz'
            for records in variants:
                with gzip.open(path,'wt') as stream:
                    for record in records:stream.write(json.dumps(record)+'\n')
                with self.assertRaises(ValueError):C.O._archive(path,15,meter())


if __name__=='__main__':
    started=time.monotonic();old=ctx.prec;ctx.prec=192
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(EvidenceTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    operations=sum(m.operations for m in METERS)
    returncode=0 if result.wasSuccessful() else 1
    path=Path(__file__).with_name('coupled_scale_evidence_development.json')
    receipt=json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1',invocations=[])
    receipt['invocations'].append(dict(returncode=returncode,operations=operations,
        elapsed_seconds=time.monotonic()-started,tests=result.testsRun,
        failures=len(result.failures),errors=len(result.errors),
        source_exposure='synthetic arrays and malformed artificial archive rows only; no actual source or archive'))
    receipt['cumulative_operations']=sum(i['operations'] for i in receipt['invocations'])
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print('SYNTHETIC_WORK module=test_coupled_scale_evidence operations='+str(operations))
    ctx.prec=old
    raise SystemExit(returncode)
