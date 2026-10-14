"""Synthetic source/factor proofs and tiny power-kernel identities only."""
from collections import Counter
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest
import sys

from flint import arb,ctx
import finite_normalization_backend_040 as P

METERS=[]


def meter(cap=2_000_000):
    m=P.Meter(cap=cap,seconds=120);METERS.append(m);return m


def source():
    def a(kind,shift):return dict(kind=kind,shift=shift)
    return dict(lattice=6,channels=[
        dict(atoms=[a('power',2),a('mu',0),a('mu',0)],weight=['3','0']),
        dict(atoms=[a('power',2),a('mu',0),a('mu',4)],weight=['-3','0']),
        dict(atoms=[a('power',2),a('mu',4)],weight=['0','-1']),
        dict(atoms=[a('mu',0)],weight=['-3','0']),
        dict(atoms=[a('power',3),a('power',2)],weight=['2','1'])])


def factors(atoms):
    result=Counter()
    for atom in atoms:
        shift=Q(atom['shift']);result[shift]+=1 if atom['kind']=='mu' else -1
    return {k:v for k,v in result.items() if v}


class FiniteNormalization(unittest.TestCase):
    def test_source_generated_multiple_factor_and_exact_shifted_quotients(self):
        s=source();m=meter();records=P.factor_candidates(s,m,kernel_v_values=('5/7','4/3'))
        self.assertEqual({f['kernel_r'] for f in records},{'1/3','1/2'})
        for factor in records:
            kernel=[dict(kind='power',shift=factor['kernel_r'])]
            if factor['kernel_v'] is not None:kernel.append(dict(kind='mu',shift=factor['kernel_v']))
            self.assertEqual(factor['uncovered'],[3]) if factor['kernel_r']=='1/3' else None
            for residual in factor['residual_source']['channels']:
                original=s['channels'][residual['source_channel']]
                original_atoms=[dict(kind=a['kind'],shift=str(Q(a['shift'],6))) for a in original['atoms']]
                self.assertEqual(factors(original_atoms),factors(kernel+residual['atoms']))
                self.assertEqual(residual['weight'],original['weight'])
                self.assertEqual(len(factor['covered'])+len(factor['uncovered']),len(s['channels']))
        actual_shift=next(f for f in records if f['kernel_r']=='1/3' and f['kernel_v']=='2/3')
        self.assertEqual(actual_shift['residual_source']['channels'][2]['atoms'],[]) # delta retained

    def test_arbitrary_requested_rational_no_lattice_inflation(self):
        s=source();m=meter();v=str(Q(1,3)+Q(1,257))
        records=P.factor_candidates(s,m,kernel_v_values=(v,'5/7',v))
        chosen=[f for f in records if f['kernel_r']=='1/3' and f['kernel_v']==v]
        self.assertEqual(len(chosen),1);self.assertEqual(s['lattice'],6)
        self.assertTrue(any(a['shift']==v for c in chosen[0]['residual_source']['channels'] for a in c['atoms']))
        self.assertEqual(chosen[0]['main_multiplier']['argument'],'258/257')
        self.assertTrue(chosen[0]['main_multiplier']['auxiliary_mu_moment_converges'])
        self.assertEqual(chosen[0]['main_multiplier']['moment_source'],'mu_v')
        self.assertNotIn('ordinary_kernel_moment_converges',chosen[0]['main_multiplier'])

    def test_all_real_pure_kernel_envelope_including_subunit(self):
        m=meter()
        for theta in ('1/2','2/3','1/257'):
            for x in ('1/3','1','3/2','9/2','8'):
                error=P.kernel_error(theta,x,m)
                value=float(error.mid());bound=1/float(Q(theta))
                self.assertLessEqual(value,1e-12);self.assertGreaterEqual(value,-bound-1e-12)
        self.assertEqual(P.kernel_error('1/2','1',m),-1)

    def test_complete_finite_bridge_arbitrary_analytic_scalar_and_lookahead(self):
        m=meter();coeff=[arb(0),arb(2),arb(-1),arb(0),arb(3),arb(-2),arb(1),arb(0),arb(4),arb(-5)]
        for x in ('1/2','1','7/2','6'):
            N=int(Q(x));expected=arb(0)
            for d in range(1,N+1):
                for k in range(1,N//d+1):
                    m.charge(64);expected+=coeff[d]/arb(k).root(2)
            for U in (0,1,3,9):
                for G in (arb(0),arb(7)):
                    result=P.finite_bridge(coeff,x,U,'1/2',G,m)
                    self.assertTrue(result['reconstructed'].overlaps(expected))
                    self.assertFalse(result['ordinary_series_convergence_asserted'])
        self.assertEqual(P.finite_bridge(coeff,'1',0,'1/2',arb(7),m)['finite_moment'],0)

    def test_kernel_regions_and_automatic_head_thresholds(self):
        m=meter();s=source();compiled=P.compile_bridges(s,('0','1/6','1/3'),parameter_domain=('1','5'),meter=m,kernel_v_values=('1','4/3'))
        shifted=next((i,f) for i,f in enumerate(compiled['factors']) if f['kernel_r']=='1/3' and f['kernel_v']=='2/3')
        provider=P.kernel_provider(shifted[1],6,m)
        self.assertEqual(provider['error_constant'],'21/2');self.assertEqual(provider['error_power'],'1/3')
        programs=[p for p in compiled['programs'] if p['factor']==shifted[0]]
        self.assertEqual([p['costs']['finite_head_energy_terms'][0]['X_power'] for p in programs],['-1/3','-1/9','1/9'])
        self.assertTrue(programs[1]['costs']['finite_head_energy_terms'][0]['paid_subpower'])
        self.assertFalse(programs[2]['costs']['finite_head_energy_terms'][0]['paid_subpower'])
        for f in compiled['factors']:
            if f['kernel_v']=='1':self.assertEqual(P.kernel_provider(f,6,m)['error_log_degree'],1)
            if f['kernel_v']=='4/3':self.assertEqual(P.kernel_provider(f,6,m)['error_power'],'0')
        self.assertFalse(compiled['whole_bound_proved']);self.assertFalse(compiled['observations_used'])

    def test_nullspace_scales_drift_and_scope_guards(self):
        m=meter();f=P.factor_candidates(source(),m)[0]
        templates=P.scale_templates(f,(1,2,3),('0','1/3'),m)
        self.assertGreater(len(templates),4)
        for t in templates:
            self.assertEqual(sum(map(Q,t['main_nullspace']),Q(0)),0)
            self.assertEqual(sum((Q(term['coefficient']['rational']) for term in t['terms']),Q(0)),0)
            self.assertEqual(len(t['complete_moment_drift']),len(t['terms']))
            self.assertIn('OPEN',t['inverse_recovery'])
            self.assertTrue(t['unit_and_uncovered_terms_retained'])
        for bad in (('1/1',), (0.5,), ('-1',)):
            with self.assertRaises(ValueError):P.compile_bridges(source(),bad,meter=m)
        with self.assertRaises(ValueError):P.factor_candidates(source(),m,kernel_v_values=(0.5,))
        with self.assertRaises(ValueError):P.finite_bridge([arb(0)],'1',1,'1/2',arb(0),m)
        low=meter(cap=1)
        with self.assertRaises(OverflowError):P.compile_bridges(source(),meter=low)


if __name__=='__main__':
    started=time.monotonic();old=ctx.prec;ctx.prec=192
    suite=unittest.TestSuite(FiniteNormalization(name) for name in sys.argv[1:]) if sys.argv[1:] else unittest.defaultTestLoader.loadTestsFromTestCase(FiniteNormalization)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    work=sum(m.operations for m in METERS);code=0 if result.wasSuccessful() else 1
    path=Path(__file__).with_name('finite_normalization_backend_040_development.json')
    receipt=json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1',invocations=[])
    receipt['invocations'].append(dict(returncode=code,operations=work,tests=result.testsRun,
        failures=len(result.failures),errors=len(result.errors),elapsed_seconds=time.monotonic()-started,
        exposure='synthetic source AST, arbitrary finite signed arrays and power kernels only; no actual source or archive'))
    receipt['cumulative_operations']=sum(v['operations'] for v in receipt['invocations'])
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print('SYNTHETIC_WORK module=test_finite_normalization_backend_040 operations='+str(work))
    ctx.prec=old
    raise SystemExit(code)
