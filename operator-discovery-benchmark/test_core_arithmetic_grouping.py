"""New grammar and signed-matrix identities, on unrelated synthetic inputs."""
import json
from pathlib import Path
import unittest
from flint import arb,ctx
import core_arithmetic_grouping as P
from prime_bank_candidates import Meter

TOTAL=0
def tearDownModule(): print('SYNTHETIC_WORK module=test_core_arithmetic_grouping operations='+str(TOTAL))


class ArithmeticGroupingTests(unittest.TestCase):
    def test_fractional_index_semantics_and_invalid_domain(self):
        for n in range(257):
            for k in (1,2,3,6):
                r=P.floor_root(n,k)
                self.assertLessEqual(r**k,n);self.assertGreater((r+1)**k,n)
        with self.assertRaises(ValueError): P.floor_root(-1,3)
        with self.assertRaises(ValueError): P.rational_power_floor(16,'3/2')

    def test_complete_prime_cancellation_drives_generic_mutations(self):
        global TOTAL
        ctx.prec=192;m=Meter(1000000,60)
        source=json.loads(Path('core-signed-work-results/pilot-001/source_program.json').read_text())
        z=(arb(2)/3).zeta();Ru=arb(9)/2*((arb(4)/3).zeta()/(z*z)-1/z)
        c=P.prime_frontier_certificate(source,Ru);rows=P.generate(c,m)
        self.assertEqual(c['leading_exponent'],'1/3');self.assertEqual(c['forced_absolute_power'],'1/3')
        self.assertEqual(c['complete_prime_terms'][0],dict(exponent='1/3',beta='0',R_u='-1'))
        self.assertTrue(all(r['proof_gate']=='ruled_out_prime_frontier' for r in rows if r['round']==0))
        self.assertEqual(set(r['lane'] for r in rows if r['round']==1),{'prime_cofactor','fractional_interval','residue'})
        self.assertTrue(any(r['proof_gate']=='eventually_one_bucket_restatement' for r in rows))
        self.assertTrue(any(r['proof_gate']=='ruled_out_prime_only_coarsening' for r in rows))
        for r in rows:
            if r['proof_gate']=='eventually_one_bucket_restatement':
                label=P.labels(r['program'],1024,m);self.assertEqual(set(label[1:]),{1})
        self.assertFalse(c['whole_signed_bound_proved']);TOTAL+=m.operations

    def test_full_group_matrix_matches_cell_integrals_and_coarsening(self):
        global TOTAL
        ctx.prec=192;m=Meter(10000000,60);X=3
        f=[arb(0)]+[arb((7*n+2)%11-5) for n in range(1,4*X)]
        fine=[0]+list(range(1,4*X));coarse=[0]+[n%3 for n in range(1,4*X)]
        out=P.grouped_arb(f,coarse,X,m,eta='1/2',rho='1/3')
        numeric=P.grouped_float([float(v) for v in f],coarse,X,m,eta='1/2',rho='1/3')
        values=sorted(set(coarse[1:]));literal=[[arb(0) for _ in values] for _ in values]
        for Y,weight in ((X,-arb(1)/3),(2*X,arb(1))):
            for n in range(Y,2*Y):
                A=[arb(0)]*len(values);B=[arb(0)]*len(values)
                for h in range(1,n+1):
                    j=values.index(coarse[h]);A[j]+=f[h];B[j]+=f[h]*arb(h).log()
                ell=(-arb(n+1).log()).ei()-(-arb(n).log()).ei()
                for i in range(len(values)):
                    for j in range(len(values)):
                        literal[i][j]+=weight*(A[i]*A[j]/(2*n*(n+1))+(A[i]*B[j]+A[j]*B[i])*ell/4)
        for i in range(len(values)):
            for j in range(len(values)):
                self.assertTrue(out['group_matrix'][i][j].overlaps(literal[i][j]))
                self.assertAlmostEqual(float(literal[i][j]),numeric['matrix'][i,j],places=10)
        atomic=P.grouped_arb(f,fine,X,m,eta='1/2',rho='1/3')
        self.assertTrue(atomic['sum_abs']>out['sum_abs'])
        one=P.grouped_arb(f,[0]+[1]*(4*X-1),X,m,eta='1/2',rho='1/3')
        self.assertTrue(one['sum_abs'].overlaps(abs(out['signed_total'])))
        self.assertTrue(out['negative_sum']<0);self.assertTrue(out['positive_sum']>0)
        TOTAL+=m.operations+200000


if __name__=='__main__':unittest.main()
