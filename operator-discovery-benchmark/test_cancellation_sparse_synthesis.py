import copy
import json
import os
import subprocess
import sys
from pathlib import Path
from fractions import Fraction as F
import unittest
import grouped_arithmetic_language as L
import cancellation_sparse_synthesis as S
import cancellation_arithmetic_synthesis as OLD
from exact_polynomial_column_cache import ColumnCache
from check_grouped_arithmetic_sparse import verify_joint_result

class Tests(unittest.TestCase):
    def test_exact_rational_shared_solution_and_cache(self):
        p=L.add(L.variable(2),L.constant(1))
        i=dict(target='mu',horizon=2,lhs=L.dump_poly(L.add(L.scale(L.mul(p,p),F(3,7)),L.constant(4))),
               square_groups=[[dict(weight='1',poly=L.dump_poly(p))]],relation_groups=[])
        cache=ColumnCache(max_entries=1)
        new=S.synthesize([i],column_cache=cache); old=OLD.synthesize([i])
        for k in ('status','weights','constant_slacks','certificates'):self.assertEqual(old[k],new[k])
        self.assertTrue(verify_joint_result([i],new,allow_constant_slack=True)['verified'])
        i=copy.deepcopy(i);i['lhs']=L.dump_poly(L.add(L.scale(L.mul(p,p),F(3,7)),L.constant(9)))
        hit=S.synthesize([i],column_cache=cache)
        self.assertTrue(hit['diagnostics']['column_cache']['cache_hit'])
        self.assertEqual(hit['constant_slacks'],['9'])
        self.assertTrue(verify_joint_result([i],hit,allow_constant_slack=True)['verified'])
    def test_negative_and_resource_states(self):
        i=dict(target='mu',horizon=1,lhs=[dict(m=[],c='-1')],square_groups=[],relation_groups=[])
        self.assertEqual(S.synthesize([i])['status'],'no_certificate_found')
        self.assertEqual(S.synthesize([i],time_limit=1e-12)['status'],'missing_resource')
        j=dict(i,lhs=[dict(m=[1,1],c='1')],square_groups=[[dict(weight='1',poly=[dict(m=[1],c='1')])]])
        self.assertEqual(S.synthesize([j],max_exact_cells=1)['status'],'missing_resource')
    def test_sparse_matrix_full_coefficients(self):
        cols=[{(1,):F(3,7)}, {}, {():F(-4)}]
        a=S.sparse_matrix(cols,[(),(1,)])
        self.assertEqual(a.toarray().tolist(),[[0,0,-4],[float(F(3,7)),0,0]])
        self.assertEqual(a.nnz,2)
    @unittest.skipUnless(Path('/proc/self/task').is_dir(),'Linux thread observation')
    def test_native_solver_stays_single_thread_in_fresh_worker(self):
        env=dict(os.environ)
        for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS','BLIS_NUM_THREADS'):env[key]='1'
        code="""
import json
from pathlib import Path
from cancellation_sparse_synthesis import synthesize
i=dict(target='mu',horizon=1,lhs=[dict(m=[1,1],c='1')],square_groups=[[dict(weight='1',poly=[dict(m=[1],c='1')])]],relation_groups=[])
r=synthesize([i])
print(json.dumps(dict(status=r['status'],threads=len(list(Path('/proc/self/task').iterdir())),highs_threads=r['diagnostics']['highs_threads'])))
"""
        done=subprocess.run([sys.executable,'-B','-c',code],cwd=Path(__file__).resolve().parent,env=env,capture_output=True,text=True,timeout=30)
        self.assertEqual(done.returncode,0,done.stderr)
        self.assertEqual(json.loads(done.stdout),dict(status='finite_certificate',threads=1,highs_threads=1))

if __name__=='__main__':unittest.main()
