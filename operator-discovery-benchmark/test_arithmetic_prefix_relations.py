"""Tiny exact toy arithmetic; no archive, actual core or response is read."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest

import arithmetic_prefix_relations as P
import check_arithmetic_prefix_relations as C

METERS=[]


def meter(cap=1_000_000):
    m=P.Meter(cap=cap);METERS.append(m);return m


def source():
    def a(kind,shift):return dict(kind=kind,shift=shift)
    return dict(lattice=3,channels=[
        dict(atoms=[a('power',3),a('mu',0),a('mu',0)],weight=['-2','1/3']),
        dict(atoms=[a('mu',0),a('mu',3)],weight=['1','-1']),
        dict(atoms=[a('power',-3),a('power',6),a('mu',3)],weight=['0','2']),
        dict(atoms=[],weight=['3','0'])])


def mu(n,m):
    sign=1;k=n
    for p in range(2,n+1):
        m.charge()
        if k%p:continue
        k//=p;sign=-sign
        if k%p==0:return 0
    return sign


def convolution(left,right,N,m):
    result=[Q(0)]*(N+1)
    for d in range(1,N+1):
        for k in range(1,N//d+1):
            m.charge(3);result[d*k]+=left[d]*right[k]
    return result


def coefficient(atoms,lattice,N,m):
    result=[Q(0)]*(N+1)
    if N:result[1]=1
    for atom in atoms:
        exponent=Q(-atom['shift'],lattice)
        if exponent.denominator!=1:raise ValueError('toy exact integer-exponent fixture')
        values=[Q(0)]+[Q(n)**exponent.numerator*(mu(n,m) if atom['kind']=='mu' else 1) for n in range(1,N+1)]
        result=convolution(result,values,N,m)
    return result


def evaluate(expression,m):
    result=Q(0)
    for term in expression['terms']:
        value=Q(term['coefficient']);m.charge()
        for factor in term['factors']:
            exponent=Q(factor['exponent']);m.charge(3)
            if exponent.denominator!=1:raise ValueError('toy integer-exponent expression')
            value*=Q(factor['argument'])**exponent.numerator
        result+=value
    return result


class Relations(unittest.TestCase):
    def test_global_euler_repetition_shift_and_weights(self):
        s=source();m=meter();cert=P.generate(s,m)
        self.assertTrue(C.verify_certificate(s,cert,m))
        self.assertEqual(cert['relations'][0]['local_identity']['left_numerator'],[0,0])
        self.assertEqual(cert['relations'][1]['kernel']['factors'],[
            dict(op='power',exponent='0'),dict(op='power',exponent='-1')])
        self.assertEqual(cert['relations'][2]['rhs']['factors'],[
            dict(op='power',exponent='1'),dict(op='power',exponent='-2')])
        self.assertEqual(cert['relations'][0]['weight'],['-2','1/3'])
        self.assertFalse(cert['uniform_bound_proved']);self.assertFalse(cert['RH_proved'])

    def test_complete_floor_identity_independent_convolution(self):
        s=source();m=meter();cert=P.generate(s,m);parameter=Q(7)
        for N in (0,1,3,9,12):
            rows=P.prefix_rows(cert,N,m)
            for channel,row in zip(s['channels'],rows):
                self.assertTrue(C.verify_prefix_row(s,cert,row,m))
                values=coefficient(channel['atoms'],s['lattice'],N,m)
                weight=Q(channel['weight'][0])+parameter*Q(channel['weight'][1])
                lhs=sum((evaluate(term['coefficient'],m)*weight*sum(values[1:term['prefix_floor']+1])
                         for term in row['lhs']),Q(0))
                rhs=weight*evaluate(row['rhs']['coefficient'],m)
                self.assertEqual(lhs,rhs)
                if N:self.assertEqual(row['lhs'][0]['kernel_argument'],1)

    def test_reordering_and_delta_unit(self):
        s=source();s['channels'].reverse()
        for c in s['channels']:c['atoms'].reverse()
        m=meter();cert=P.generate(s,m);rows=P.prefix_rows(cert,5,m)
        self.assertTrue(C.verify_certificate(s,cert,m))
        for row in rows:self.assertTrue(C.verify_prefix_row(s,cert,row,m))
        delta=rows[0];self.assertEqual(len(delta['lhs']),1)
        self.assertEqual(delta['lhs'][0]['prefix_floor'],5)
        self.assertEqual(delta['rhs']['coefficient']['terms'],[dict(coefficient='1',factors=[])])

    def test_arbitrary_denominator_and_signed_shift(self):
        s=dict(lattice=257,channels=[dict(atoms=[dict(kind='mu',shift=1),dict(kind='power',shift=-2)],weight=['1','0'])])
        m=meter();cert=P.generate(s,m)
        self.assertEqual(cert['relations'][0]['kernel']['factors'][0]['exponent'],'-1/257')
        rows=P.prefix_rows(cert,3,m)
        self.assertTrue(C.verify_prefix_row(s,cert,rows[0],m))

    def test_omitted_factor_unit_floor_and_source_mutations_rejected(self):
        s=source();m=meter();good=P.generate(s,m)
        bad=deepcopy(good);bad['relations'][0]['kernel']['factors'].pop()
        with self.assertRaises(ValueError):C.verify_certificate(s,bad,m)
        bad=deepcopy(good);bad['relations'][0]['scope']['all_primes']=1
        with self.assertRaises(ValueError):C.verify_certificate(s,bad,m)
        with self.assertRaises(ValueError):P.prefix_rows(bad,3,m)
        row=P.prefix_rows(good,5,m)[0]
        for mutation in ('unit','floor','weight','bool'):
            badrow=deepcopy(row)
            if mutation=='unit':badrow['lhs'].pop(0)
            elif mutation=='floor':badrow['lhs'][1]['prefix_floor']+=1
            elif mutation=='weight':badrow['rhs']['weight'][0]='2'
            else:badrow['channel']=False
            with self.assertRaises(ValueError):C.verify_prefix_row(s,good,badrow,m)
        changed=deepcopy(s);changed['channels'][0]['atoms'][1]['shift']=3
        with self.assertRaises(ValueError):C.verify_certificate(changed,good,m)

    def test_strict_schema_and_resource_failures(self):
        variants=[]
        s=source();s['lattice']=True;variants.append(s)
        s=source();s['channels'][0]['weight'][0]='2/2';variants.append(s)
        s=source();s['channels'][0]['atoms'][0]['shift']=0.5;variants.append(s)
        s=source();s['channels'][0]['atoms'][0]['kind']='lambda';variants.append(s)
        for s in variants:
            m=meter()
            with self.assertRaises(ValueError):P.generate(s,m)
            with self.assertRaises(ValueError):C.verify_certificate(s,{},m)
        good=P.generate(source(),meter())
        with self.assertRaises(ValueError):P.prefix_rows(good,True,meter())
        with self.assertRaises(ValueError):P.prefix_rows(good,-1,meter())
        limited=meter(cap=10)
        with self.assertRaises(OverflowError):P.prefix_rows(good,1000,limited)
        self.assertGreater(limited.operations,10)


if __name__=='__main__':
    started=time.monotonic();result=unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(Relations))
    work=sum(m.operations for m in METERS);code=0 if result.wasSuccessful() else 1
    path=Path(__file__).with_name('arithmetic_prefix_relations_development.json')
    receipt=json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1',invocations=[])
    receipt['invocations'].append(dict(returncode=code,operations=work,tests=result.testsRun,
        failures=len(result.failures),errors=len(result.errors),elapsed_seconds=time.monotonic()-started,
        exposure='tiny toy integer-exponent Mobius convolution only; no actual core/source archive or responses'))
    receipt['cumulative_operations']=sum(v['operations'] for v in receipt['invocations'])
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print('SYNTHETIC_WORK module=test_arithmetic_prefix_relations operations='+str(work))
    raise SystemExit(code)
