import copy
import unittest
from unittest.mock import patch
import check_grouped_arithmetic_sparse as S
import check_grouped_arithmetic as G

class SparseTests(unittest.TestCase):
    def fixture(self):
        sq={'weight':'1','poly':[{'m':[1],'c':'1'}]}
        rel={'spec':{'kind':'norm','n':1,'factors':[]},'multiplier':[{'m':[],'c':'1'}]}
        i=dict(target='mu',horizon=2,lhs=[{'m':[],'c':'1'}],square_groups=[[sq],[sq]],relation_groups=[[rel],[rel]])
        cert=dict(target='mu',horizon=2,lhs=i['lhs'],squares=[sq],relations=[dict(spec=rel['spec'],multiplier=[{'m':[],'c':'-1'}])])
        r=dict(status='finite_certificate',weights=dict(square_weights=['1','0'],relation_weights=['-1','0']),certificates=[cert],constant_slacks=['0'])
        return i,r
    def test_equivalence_and_zero_expansion(self):
        i,r=self.fixture()
        a=G.verify_joint_result([i],r,allow_constant_slack=True)
        with patch.object(S.P,'multiply',wraps=S.P.multiply)as mul:
            b=S.verify_joint_result([i],r,allow_constant_slack=True,expected_instance_sha256=[S.digest(i)])
        self.assertEqual(a['instances'],b['instances']);self.assertEqual(mul.call_count,2)
        self.assertEqual(b['skipped_zero_groups'],2)
    def test_tampering(self):
        for kind in ['weight','target','premise','inactive_premise','inactive_poly','certificate','source','slack','promotion']:
            i,r=self.fixture();hashes=[S.digest(i)]
            if kind=='weight':r['weights']['square_weights'][0]='-1'
            if kind=='target':i['lhs']=[{'m':[2],'c':'1'}];hashes=[S.digest(i)]
            if kind=='premise':i['relation_groups'][0][0]['spec']['factors']=[[2,1]];hashes=[S.digest(i)]
            if kind=='inactive_premise':i['relation_groups'][1][0]['spec']['factors']=[[2,1]];hashes=[S.digest(i)]
            if kind=='inactive_poly':i['square_groups'][1][0]['poly']=[{'m':[3],'c':'1'}];hashes=[S.digest(i)]
            if kind=='certificate':r['certificates'][0]['squares']=[]
            if kind=='source':i['square_groups'][1]=[]
            if kind=='slack':r['constant_slacks']=['1']
            if kind=='promotion':r['RH_proved']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError):S.verify_joint_result([i],r,allow_constant_slack=True,expected_instance_sha256=hashes)
    def test_exact_weight_and_schema(self):
        for v in [True,1.0,'1e100000','01','1/0']:
            i,r=self.fixture();r['weights']['square_weights'][1]=v
            with self.subTest(v=v),self.assertRaises((ValueError,OverflowError)):S.verify_joint_result([i],r)
        i,r=self.fixture();i['square_groups'][1]=[{'unexpected':[]}]
        with self.assertRaises(ValueError):S.verify_joint_result([i],r)
    def test_work_cap(self):
        i,r=self.fixture()
        with self.assertRaises(OverflowError):S.verify_joint_result([i],r,max_operations=1)

if __name__=='__main__':unittest.main()
