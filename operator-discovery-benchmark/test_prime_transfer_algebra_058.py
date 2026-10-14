"""One/two-prime exact synthetic identity tests only; no pilot matrix."""
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import time
import unittest
from unittest.mock import patch
import prime_transfer_algebra_058 as S

METERS=[]


def meter(**kwargs):
    work=S.Meter(**kwargs);METERS.append(work);return work


def valuation(n,p):
    e=0
    while n%p==0:
        n//=p;e+=1
    return e


def factors(n):
    out=[];rest=n
    for p in range(2,math.isqrt(n)+1):
        if rest%p==0:
            out.append(p)
            while rest%p==0:rest//=p
    if rest>1:out.append(rest)
    return out


def z(p):
    return Q(1,p+1)


def G(integer,subset):
    return math.prod(1-z(p) for p in set(factors(integer))|set(subset))


def atom_n(atom,n):
    d=atom['divisor']
    if n%d:return Q(0)
    atten=atom['attenuation'];monomial=Q(1)
    for p in factors(atten):monomial*=z(p)**valuation(atten,p)
    return monomial*G(n//d,atom['primes'])


def v(x,n):
    return int(2*x<n<=4*x)-2*int(x<n<=2*x)


def H(atom,x,unit=True):
    d=atom['divisor'];total=Q(0)
    for n in range(1,int(4*x)+1):
        if unit or n//d!=1:
            total+=v(x,n)*atom_n(atom,n)
    return total


def replay(signature,coefficients):
    return [sum(Q(entry['value'])*coefficients[entry['column']] for entry in row['entries'])
            for row in signature['rows']]


class TransferTests(unittest.TestCase):
    def test_grammar_declared_complexity_and_arbitrary_prime_choice(self):
        work=meter()
        for primes in ([2],[3,7]):
            grammar=S.grammar(primes,work)
            expected=2**len(primes)*(len(primes)+1)*math.comb(len(primes)+2,len(primes))
            self.assertEqual(len(grammar['atoms']),expected)
            self.assertEqual(len({(tuple(a['primes']),a['divisor'],a['attenuation']) for a in grammar['atoms']}),expected)
            self.assertFalse(grammar['metadata']['winner_identity_supplied'])
        wider=S.grammar([11],work,max_attenuation_degree=5)
        self.assertEqual(len(wider['atoms']),24)
        self.assertEqual(wider['metadata']['max_attenuation_degree'],5)

    def test_signature_replays_actual_integer_terms_and_outside_factors(self):
        work=meter()
        atoms=[{'primes':s,'divisor':d,'attenuation':a}
               for s,d,a in (([],1,1),([2],2,3),([3],8,4),([2,3],6,9))]
        sig=S.signature([2,3],atoms,work)
        caps=sig['valuation_caps']
        self.assertEqual(caps,[4,2])
        for n in range(1,41):
            state=[min(valuation(n,p),cap) for p,cap in zip([2,3],caps)]
            actual=[Q(0)]*len(atoms)
            for row in sig['rows']:
                if row['valuations']==state:
                    value=math.prod(z(p)**e for p,e in zip([2,3],row['monomial']))
                    for entry in row['entries']:
                        actual[entry['column']]+=entry['value']*value
            common=math.prod(1-z(p) for p in factors(n) if p not in (2,3))
            self.assertEqual([common*a for a in actual],[atom_n(a,n) for a in atoms])
            work.charge(len(sig['rows'])*4)
        self.assertTrue(sig['unit_state_included'])

    def test_known_one_prime_relation_is_inferred_as_nullspace_span(self):
        work=meter();context=S.prepare_context(work)
        atoms=S.grammar([2],work)['atoms']
        sig=S.signature([2],atoms,work,context)
        found=S.discover([2],atoms,work,context)
        # H_p(x)-(1-z_p)H_empty(x)-z_p H_p(x/p)=0.
        target=[Q(0)]*len(atoms)
        for atom,c in (({'primes':[2],'divisor':1,'attenuation':1},1),
                       ({'primes':[],'divisor':1,'attenuation':1},-1),
                       ({'primes':[],'divisor':1,'attenuation':2},1),
                       ({'primes':[2],'divisor':2,'attenuation':2},-1)):
            target[atoms.index(atom)]=Q(c)
        self.assertTrue(all(value==0 for value in replay(sig,target)))
        basis=[[Q(q) for q in row['coefficients']] for row in found['relations']]
        reconstructed=[sum(target[f]*b[j] for f,b in zip(found['free_columns'],basis))
                       for j in range(len(atoms))]
        self.assertEqual(reconstructed,target)
        for x in (Q(1,3),Q(3,4),Q(2),Q(17,4)):
            self.assertEqual(sum(c*H(a,x) for c,a in zip(target,atoms)),0)
            work.charge(len(atoms)*100)

    def test_every_two_prime_basis_vector_replays_all_rows(self):
        work=meter();context=S.prepare_context(work)
        atoms=S.grammar([2,5],work)['atoms']
        sig=S.signature([2,5],atoms,work,context)
        result=S.discover([2,5],atoms,work,context)
        self.assertEqual(result['rank']+result['nullity'],len(atoms))
        for relation in result['relations']:
            coeffs=[Q(text) for text in relation['coefficients']]
            self.assertTrue(all(q==0 for q in replay(sig,coeffs)))
            self.assertEqual(coeffs[relation['free_column']],1)
            for f in result['free_columns']:
                if f!=relation['free_column']:self.assertEqual(coeffs[f],0)
            work.charge(sig['nonzero_entries']*4)
        pivots=result['pivot_columns']
        for row in result['rref_rows']:
            values={e['column']:Q(e['value']) for e in row['entries']}
            self.assertEqual(values[row['pivot_column']],1)
            for p in pivots:
                if p!=row['pivot_column']:self.assertEqual(values.get(p,0),0)
        self.assertFalse(result['norm_bound_proved'])
        self.assertFalse(result['rh_proved'])
        self.assertFalse(result['scientific_source_values_evaluated'])

    def test_squarefree_only_fake_identity_is_rejected(self):
        work=meter()
        atoms=[{'primes':[],'divisor':4,'attenuation':1}]
        sig=S.signature([2],atoms,work)
        self.assertTrue(all(not row['entries'] for row in sig['rows'] if row['valuations'][0]<=1))
        self.assertTrue(any(row['valuations'][0]==2 and row['entries'] for row in sig['rows']))
        result=S.discover([2],atoms,work)
        self.assertEqual(result['nullity'],0)
        self.assertEqual(sig['valuation_caps'],[3])

    def test_inclusive_unit_and_exact_lower_state_counterterms(self):
        work=meter()
        atoms=[{'primes':[2],'divisor':1,'attenuation':1},
               {'primes':[],'divisor':1,'attenuation':1},
               {'primes':[],'divisor':1,'attenuation':2},
               {'primes':[2],'divisor':2,'attenuation':2}]
        sig=S.signature([2],atoms,work)
        coefficients=[Q(1),Q(-1),Q(1),Q(-1)]
        self.assertTrue(all(q==0 for q in replay(sig,coefficients)))
        x=Q(3,4)
        inclusive=sum(c*H(a,x) for c,a in zip(coefficients,atoms))
        removed=sum(c*H(a,x,unit=False) for c,a in zip(coefficients,atoms))
        self.assertEqual(inclusive,0)
        self.assertNotEqual(removed,0)
        self.assertTrue(any(row['valuations']==[0] for row in sig['rows']))
        work.charge(200)

    def test_fraction_rref_and_cache_public_mutation_safety(self):
        work=meter();context=S.prepare_context(work)
        pivots,rows=S._rref((((0,),(0,),((0,3),(1,2))),),2,work,0)
        self.assertEqual(pivots,(0,));self.assertEqual(rows[0][1],Q(2,3))
        atoms=S.grammar([3],work)['atoms']
        first=S.signature([3],atoms,work,context)
        first['rows'][0]['entries'][0]['value']=99
        second=S.signature([3],atoms,work,context)
        self.assertNotEqual(second['rows'][0]['entries'][0]['value'],99)
        self.assertEqual(second['counts']['total_primitive_counts']['cache_hits'],1)
        self.assertEqual(second['counts']['total_primitive_counts']['polynomial_terms'],0)
        uncached=S.prepare_context(work,max_bytes=0)
        S.signature([3],atoms,work,uncached)
        self.assertEqual(uncached.bytes_estimate,0)

    def test_adversarial_domains_and_prospective_caps(self):
        work=meter()
        for primes in ([4],[2,2],[3,2],[True],[]):
            with self.assertRaises(ValueError):S.grammar(primes,work)
        good={'primes':[],'divisor':1,'attenuation':1}
        bads=[dict(good,divisor=5),dict(good,attenuation=0),dict(good,primes=[3]),
              dict(good,divisor=True),dict(good,extra=0)]
        for atom in bads:
            with self.assertRaises(ValueError):S.signature([2],[atom],work)
        with self.assertRaises(ValueError):S.signature([2],[good,good],work)
        with self.assertRaises(OverflowError):S.signature([2],[dict(good,divisor=2**17)],work)
        with self.assertRaises(OverflowError):S.grammar([2,3],work,max_attenuation_degree=8)
        with patch.object(S,'MAX_STATES',300):
            with self.assertRaises(OverflowError):
                S.signature([2,3],[dict(good,divisor=2**16*3**16)],work)
        with self.assertRaises(OverflowError):S.grammar([2],meter(cap=0))
        expired=meter();expired.deadline=time.monotonic()-1
        with self.assertRaises(TimeoutError):S.grammar([2],expired)
        with self.assertRaises(MemoryError):work.reserve(S.MAX_WORKING_BYTES+1)


if __name__=='__main__':
    path=Path(__file__).with_name('prime_transfer_algebra_058_development.json')
    if path.exists():raise SystemExit('retain prior focused receipt')
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(TransferTests))
    counts=[m.counts() for m in METERS]
    receipt={'schema':'prime-transfer-algebra-058-development-v1','invocations':[{
        'returncode':0 if result.wasSuccessful() else 1,'tests':result.testsRun,
        'failures':len(result.failures),'errors':len(result.errors),
        'elapsed_seconds':time.monotonic()-started,'operations':sum(c['operations'] for c in counts)}],
        'total_primitive_counts':{k:sum(c['total_primitive_counts'][k] for c in counts)
                                 for k in S.Meter().primitives},
        'peak_bytes_estimate':max((c['peak_bytes_estimate'] for c in counts),default=0),
        'scope':'one/two-prime exact synthetic signatures only; no three-prime scientific pilot matrix',
        'scientific_pilot_applied':False,'old_suites_or_studies_replayed':False,
        'checker_imported':False,'norm_bound_or_rh_claimed':False}
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
