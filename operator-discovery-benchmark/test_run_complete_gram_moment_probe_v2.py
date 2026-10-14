import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import run_complete_gram_moment_probe_v2 as R


class ProbeRunner(unittest.TestCase):
    def test_frozen_full_completion_and_no_overwrite(self):
        with tempfile.TemporaryDirectory() as td:
            d = R.freeze(Path(td) / 'run'); R.validate(d)
            p = json.loads((d / 'protocol.json').read_text())
            self.assertEqual(p['gram_specs'], {'full_child': 14, 'full_parent': 14})
            self.assertEqual(p['scales'], [1, 2, 3, 5])
            self.assertEqual(p['parallel']['worker_memory_bytes'], 6*1024**3)
            self.assertFalse(p['larger_cone_feasibility_proved'])
            with self.assertRaises(FileExistsError):
                R.freeze(d)
            p['missing_policy'] = 'fill zeros'
            (d / 'protocol.json').write_text(json.dumps(p))
            with self.assertRaisesRegex(ValueError, 'seal changed'):
                R.validate(d)

    def test_optimized_runtime_rejected_before_write(self):
        with tempfile.TemporaryDirectory() as td:
            d = Path(td) / 'run'
            result = subprocess.run([sys.executable, '-O', str(R.ROOT / 'run_complete_gram_moment_probe_v2.py'),
                                     'freeze', str(d)], capture_output=True, text=True, timeout=30)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(d.exists())
            self.assertIn('assertions enabled', result.stderr)


if __name__ == '__main__':
    unittest.main()
