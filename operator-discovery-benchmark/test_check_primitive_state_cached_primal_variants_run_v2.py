import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_primitive_state_cached_primal_variants_run_v2 as I
import test_check_primitive_state_cached_primal_variants_run as F


write=F.write


class SupplementalAuditTests(unittest.TestCase):
    def test_large_protocol_is_explicit_correction_not_old_contract_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);write(d/'protocol.json',{'parent_assembly':'x'*100000})
            with self.assertRaises(OverflowError):I.V1.read(d/'protocol.json',65536)
            report=I.protocol_envelope(d)
            self.assertFalse(report['original_audit_contract_satisfied'])
            self.assertEqual(report['supplemental_max_bytes'],262144)
            self.assertEqual(report['sha256'],I.sha(d/'protocol.json'))

    def test_oversized_protocol_rejected_before_parse(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);(d/'protocol.json').write_bytes(b'x'*262145)
            with self.assertRaisesRegex(ValueError,'bounded supplemental'):I.protocol_envelope(d)

    def test_inventory_changes_only_protocol_limit(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);write(d/'protocol.json',{'license':'x'*100000})
            receipt=dict(files_sha256={'protocol.json':I.sha(d/'protocol.json')},**I.FLAGS)
            I.verify_inventory(d,receipt)
            with self.assertRaisesRegex(ValueError,'bounded cached'):I.V1.verify_inventory(d,receipt)
            job=d/'jobs/prepare/job.json';write(job,{'too_large':'x'*70000})
            receipt['files_sha256']['jobs/prepare/job.json']=I.sha(job)
            with self.assertRaisesRegex(ValueError,'bounded cached'):I.verify_inventory(d,receipt)

    def test_inventory_still_rejects_tampering_and_unknown_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);write(d/'protocol.json',{})
            receipt=dict(files_sha256={'protocol.json':I.sha(d/'protocol.json')},**I.FLAGS)
            write(d/'protocol.json',{'changed':True})
            with self.assertRaisesRegex(ValueError,'artifact hash'):I.verify_inventory(d,receipt)
            receipt['files_sha256']['protocol.json']=I.sha(d/'protocol.json')
            write(d/'unlisted.json',{})
            with self.assertRaisesRegex(ValueError,'inventory'):I.verify_inventory(d,receipt)

    def test_actual_frozen_protocol_envelope_and_math_contract(self):
        d=I.ROOT/'cancellation-arithmetic-results/primitive-state-cached-primal-variants-001'
        protocol=I.read(d/'protocol.json',I.PROTOCOL_MAX_BYTES)
        I.verify_protocol(protocol)
        result=I.protocol_envelope(d)
        self.assertEqual(result['actual_bytes'],137531)
        self.assertFalse(result['original_audit_contract_satisfied'])
        self.assertEqual(protocol['limits']['max_work'],450000000)
        self.assertEqual(protocol['limits']['max_metadata_bytes'],65536)

    def test_full_supplemental_audit_rebuilds_once_and_preserves_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);d=root/'run';f=F.WholeVariantTests().fixture(d)
            (d/'frozen_source').mkdir();names=list(f['sources'])
            for name in names:
                (root/name).write_bytes((I.ROOT/name).read_bytes())
                (d/'frozen_source'/name).write_bytes((root/name).read_bytes())
            for name in I.INPUTS:write(root/name,dict(files={}) if name.endswith('manifest.json') else dict(schema=15))
            protocol=copy.deepcopy(f['protocol']);protocol.update(gram_specs={'gram':1},envelope_fixture='x'*100000)
            write(d/'protocol.json',protocol);write(d/'source_seal.json',f['sources'])
            write(d/'input.json',dict(input_sha256={n:I.sha(root/n) for n in I.INPUTS}))
            write(d/'seal.json',{n+'_sha256':I.sha(d/(n+'.json')) for n in ('protocol','source_seal','input')})
            write(d/'run_started.json',dict(protocol_sha256=I.sha(d/'protocol.json')))
            write(d/'tests.json',dict(returncode=0,stdout='',stderr='Ran 8 tests in 0.1s\n\nOK\n'))
            write(d/'preparation-execution.json',f['prep']);write(d/'execution.json',f['execution'])
            files={str(p.relative_to(d)):I.sha(p) for p in d.rglob('*') if p.is_file() and 'frozen_source' not in p.parts}
            write(d/'receipt.json',dict(files_sha256=files,source_count=len(names),**I.FLAGS))
            with patch.object(I,'ROOT',root),patch.object(I,'source_names',return_value=names),patch.object(I.ORIGINAL,'rebuild',return_value=({},f['geometry'])) as rebuild,patch.object(I,'verify_parent',return_value=f['parent']),patch.object(I.ORIGINAL.B,'gram_specs',return_value={'gram':1}),patch.object(I.CORE.CORE,'reconstruct',wraps=I.CORE.CORE.reconstruct) as reconstruct:
                review=I.audit(d,write=True)
                self.assertTrue(review['all_passed'])
                self.assertEqual(review['schema'],I.SCHEMA)
                self.assertFalse(review['original_audit_contract_satisfied'])
                self.assertFalse(review['RH_proved'])
                self.assertEqual(rebuild.call_count,1);self.assertEqual(reconstruct.call_count,1)
                self.assertTrue((d/I.REVIEW_NAME).is_file())
                self.assertFalse((d/'independent_verification.json').exists())
                I.verify_inventory(d,I.read(d/'receipt.json'))
                with self.assertRaises(FileExistsError):I.audit(d,write=True)


if __name__=='__main__':unittest.main()
