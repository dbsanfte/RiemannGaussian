"""Owned tiny adapter tests; no actual archive or hidden challenge is opened."""
from copy import deepcopy
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import tempfile
import time
import unittest

from flint import arb, ctx
from prime_bank_candidates import Meter
import multiscale_bound_sources as S

METERS = []


def meter(cap=100000000):
    result = Meter(cap=cap, seconds=600)
    METERS.append(result)
    return result


def sample():
    # This simple public toy is not one of the future hidden instances.
    return dict(base=2, matrices=[[['1','0'],['0','1']],
                                  [['0','1'],['-1','0']]],
                initial=['1','1'], output=['1','-1'])


def archive(path, rows=None):
    if rows is None:
        rows = [dict(name=name, values=['0','[3.0 +/- 0.01]','-2','5'])
                for name in S.VECTOR_NAMES]
    with gzip.open(path, 'wt', encoding='utf8') as stream:
        for row in rows:
            stream.write(json.dumps(row)+'\n')


class Sources(unittest.TestCase):
    def test_exact_digit_order_zero_and_coupled_output(self):
        m = meter(); model = sample()
        self.assertTrue(S.validate_model(model,m))
        source = S.model_source(model,m)
        self.assertEqual([source(n) for n in range(8)],
                         [F(0),F(2),F(2),F(0),F(2),F(0),F(0),F(-2)])
        # Noncommuting base3 branches ensure digit orientation is checked.
        model = dict(base=3, matrices=[[['1','0'],['0','1']],
                    [['0','1'],['1','0']], [['1','0'],['0','0']]],
                    initial=['1','2'],output=['1','0'])
        self.assertEqual(S.evaluate_model(model,5,m),F(2))
        self.assertEqual(S.evaluate_model(model,7,m),F(0))
        self.assertEqual(S.evaluate_model(model,0,m),F(1))

    def test_fractional_contractivity_and_compiled_snapshot(self):
        m=meter(); model=dict(base=2, matrices=[[['1']], [['-1/2']]],
                            initial=['3/2'],output=['2/3'])
        source=S.model_source(model,m)
        self.assertEqual(source(7),F(-1,8))
        model['matrices'][1][0][0]='1'
        self.assertEqual(source(7),F(-1,8))
        self.assertEqual(S.evaluate_model(model,7,m),F(1))

    def test_strict_model_validation(self):
        m=meter()
        bad=[]
        x=sample();x['base']=True;bad.append(x)
        x=sample();x['initial'][0]='1/1';bad.append(x)
        x=sample();x['matrices'][1][0]=['1','1/2'];bad.append(x)
        x=sample();x['matrices'][0][0]=['0','0'];bad.append(x)
        x=sample();x['output']=['1'];bad.append(x)
        x=sample();x['extra']=0;bad.append(x)
        x=sample();x['matrices'][0][0][0]=False;bad.append(x)
        x=sample();x['initial'][0]=str(2**4096);bad.append(x)
        x=dict(base=2,matrices=[],initial=['1']*13,output=['1']*13);bad.append(x)
        for model in bad:
            with self.assertRaises(ValueError):S.validate_model(model,m)

    def test_index_and_resource_failure(self):
        m=meter(); source=S.model_source(sample(),m)
        for n in (True,-1,1.0,'1',2**4096):
            with self.assertRaises(ValueError):source(n)
        with self.assertRaises(OverflowError):S.model_source(sample(),meter(0))

    def test_archive_preserves_full_core_unit_and_last_index(self):
        m=meter(); old=ctx.prec;ctx.prec=192
        try:
            with tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'checker_vectors.jsonl.gz';archive(path)
                source,meta=S.load_complete_core(path,3,m)
                self.assertTrue(source(0).contains(arb(3)))
                self.assertFalse(source(0).is_zero())
                self.assertEqual(source(1),arb(-2));self.assertEqual(source(2),arb(5))
                self.assertEqual(meta['max_source_index'],2)
                self.assertTrue(meta['includes_unit']);self.assertTrue(meta['includes_all_four_signed_modes'])
                self.assertFalse(meta['stage033_component_isolated'])
                self.assertFalse(meta['universal_closure_verified'])
                for n in (True,-1,3):
                    with self.assertRaises(ValueError):source(n)
                clipped,metadata=S.load_complete_core(path,1,m)
                self.assertTrue(clipped(0).contains(arb(3)))
                self.assertEqual(metadata['archive_H'],3)
        finally:ctx.prec=old

    def test_archive_incomplete_malformed_or_nonfinite_rejected(self):
        m=meter(); old=ctx.prec;ctx.prec=192
        try:
            base=[dict(name=name,values=['0','1','2']) for name in S.VECTOR_NAMES]
            variants=[base[:-1],base+[deepcopy(base[0])]]
            bad=deepcopy(base);bad[1]['values']=['0','1'];variants.append(bad)
            bad=deepcopy(base);bad[0]['values'][0]='1';variants.append(bad)
            bad=deepcopy(base);bad[0]['values'][1]='nan';variants.append(bad)
            bad=deepcopy(base);bad[0]['values'][1]=True;variants.append(bad)
            bad=deepcopy(base);bad[0]['extra']='bad';variants.append(bad)
            with tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'vectors.gz'
                for rows in variants:
                    archive(path,rows)
                    with self.assertRaises(ValueError):S.load_complete_core(path,2,m)
                with self.assertRaises(ValueError):S.load_complete_core(path,True,m)
        finally:ctx.prec=old

    def test_hidden_instances_require_external_freeze(self):
        m=meter()
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):S.create_challenges(directory,20261010,m,frozen=False)
            self.assertFalse((Path(directory)/'private').exists())
        # Do not call the accepted builder before the real generator freeze.


if __name__=='__main__':
    start=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Sources))
    operations=sum(m.operations for m in METERS)
    receipt=Path(__file__).with_name('multiscale_bound_sources_development.json')
    previous=json.loads(receipt.read_text()) if receipt.exists() else {'runs':[]}
    previous['runs'].append(dict(returncode=0 if result.wasSuccessful() else 1,
        operations=operations,tests=result.testsRun,failures=len(result.failures),
        errors=len(result.errors),elapsed_seconds=time.monotonic()-start,
        peak_cells=max((m.peak_cells for m in METERS),default=0)))
    previous.update(module='test_multiscale_bound_sources',
                    operations=sum(r['operations'] for r in previous['runs']))
    receipt.write_text(json.dumps(previous,sort_keys=True,indent=2)+'\n')
    print('SYNTHETIC_WORK module=test_multiscale_bound_sources operations='+str(operations),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
