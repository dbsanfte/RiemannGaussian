import copy,unittest
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_coupled_outer_control_083 as O
import check_mobius_coupled_completion_083 as C

def fixture(arithmetic='all'):
    weight=dict(kind='product',arithmetic=arithmetic,i=0,j=0)
    def term(comp,theta='2'):return dict(cut=dict(scale='1',n_exponent='1',u_exponent='0',complement=comp,unit_balance=True),weight=dict(weight),theta=theta)
    p=dict(schema='coupled-divisor-completion-v1',kernel=[dict(divisor=4,weight='-1'),dict(divisor=5,weight='1'),dict(divisor=8,weight='1'),dict(divisor=10,weight='-1')],memory=1,rays=[],drift_multiplier='3/2',coupled_terms=[term(False),term(True)],gram_weights=['0','0'])
    cert=dict(schema='coupled-outer-control-v1',Astar='1',prime_gain='2',composite_gain='2',matched_groups=[dict(weight=weight,outer_value='1',normal_indices=[0],complement_indices=[1],theta_total='2')],zero_outer_terms=[],uniform_bound_coefficient='1',minimum_u=1,complete_outer_block_admitted=True,full_remaining_kernel_unpaid=True)
    return p,cert
class Tests(unittest.TestCase):
    def test_complete_uniform_outer_and_unpaid_flags(self):
        p,c=fixture();r=O.verify_certificate(p,c)
        self.assertEqual(r['status'],'VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL');self.assertTrue(r['uniform_whole_outer_absolute_price_proved']);self.assertTrue(r['whole_program_closure_verified']);self.assertFalse(r['uniform_full_completion_price_proved']);self.assertFalse(r['uniform_source_bound_proved']);self.assertFalse(r['RH_proved'])
        with patch.object(C.D,'squarefree_prefix',side_effect=AssertionError('uniform theorem must not query populations')):self.assertEqual(O.verify_certificate(p,c)['status'],'VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL')
    def test_literal_all_low_and_small_outer_matrices(self):
        p,c=fixture()
        for u in range(1,81):
            model=C.build_model(p,u);A=C.corrected_matrix(model);indices=[g for g,n in enumerate(model['coordinates'])if Q(u,5)<n<=Q(u,4)];N=model['N'];price=sum(A[g][g]for g in indices)+2*sum(abs(A[g][h])for k,g in enumerate(indices)for h in indices[k+1:])
            self.assertLessEqual(price,u)
            if u>=16:
                for g in indices:
                    n=model['coordinates'][g];self.assertEqual(A[g][g],1+Q(2*(n!=N),N-1))
                    for h in indices:
                        if g!=h:self.assertEqual(A[g][h],Q(2-(n==N)-(model['coordinates'][h]==N),N-1))
        # u4 includesactualunit; u24 mixedprime5/composite6 andboundaryN.
        self.assertEqual(C.build_model(p,4)['coordinates'],(1,));model=C.build_model(p,24);self.assertIn(5,model['coordinates']);self.assertIn(6,model['coordinates'])
    def test_prime_composite_complete_cross_gain(self):
        p,c=fixture('prime');q,d=fixture('composite');p['coupled_terms']+=q['coupled_terms'];c['matched_groups']=[dict(d['matched_groups'][0],normal_indices=[2],complement_indices=[3]),c['matched_groups'][0]]
        self.assertEqual(O.verify_certificate(p,c)['status'],'VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL')
        m=C.build_model(p,24);A=C.corrected_matrix(m);g=m['coordinates'].index(5);h=m['coordinates'].index(6);self.assertEqual(A[g][h],Q(1,5))
        p['coupled_terms'][3]['theta']='1';self.assertEqual(O.verify_certificate(p,c)['status'],'INVALID')
    def test_exact_equality_system_and_aggregate_matching(self):
        p,c=fixture();p['coupled_terms'][0]['theta']='1';p['coupled_terms'].append(copy.deepcopy(p['coupled_terms'][0]));c['matched_groups'][0].update(normal_indices=[0,2])
        system=O.equality_constraints(p);self.assertEqual(system['rows'],[['1','-1','1','0','0'],['1','0','1','-2','0'],['1','0','1','-2','0']]);self.assertEqual(system['rhs'],['0','2','2'])
        self.assertEqual(O.verify_certificate(p,c)['status'],'VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL')
        p['coupled_terms'][1]['theta']='3';self.assertEqual(O.verify_certificate(p,c)['status'],'INVALID')
    def test_source_and_gram_Astar_and_zero_weight_remainder(self):
        p,c=fixture();p['gram_weights']=['1/2','4']
        self.assertEqual(O.verify_certificate(p,c)['status'],'INVALID')
        for term in p['coupled_terms']:term['theta']='3'
        c.update(Astar='3/2',prime_gain='3',composite_gain='3',uniform_bound_coefficient='3/2');c['matched_groups'][0]['theta_total']='3'
        p['coupled_terms'].append(dict(cut=dict(scale='2/3',n_exponent='-17/31',u_exponent='1',complement=False,unit_balance=False),weight=dict(kind='source',arithmetic='all',i=1),theta='16'));c['zero_outer_terms']=[2]
        self.assertEqual(O.verify_certificate(p,c)['status'],'VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL')
        p['coupled_terms'][2]['weight']['i']=0;self.assertEqual(O.verify_certificate(p,c)['status'],'INVALID')
    def test_negative_source_weight_and_band_constant(self):
        for weight,val,theta in [(dict(kind='source',arithmetic='all',i=0),'-1','-2'),(dict(kind='band',arithmetic='all',left='1/6',right='1/3'),'1','2'),(dict(kind='one',arithmetic='all'),'1','2')]:
            p,c=fixture()
            for term in p['coupled_terms']:term.update(weight=weight,theta=theta)
            c['matched_groups'][0].update(weight=weight,outer_value=val,theta_total=theta)
            self.assertEqual(O.verify_certificate(p,c)['status'],'VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL')
        p,c=fixture();p['coupled_terms'][0]['weight']=dict(kind='band',arithmetic='all',left='11/50',right='1/4');self.assertEqual(O.verify_certificate(p,c)['status'],'INVALID')
    def test_changed_binding_cut_missing_class_and_certificate_tampering(self):
        for mode in ['binding','balance','cut','class','gain','group','bool','scope']:
            p,c=fixture()
            if mode=='binding':p['kernel'][0]['weight']='-2'
            if mode=='balance':p['coupled_terms'][0]['cut']['unit_balance']=False
            if mode=='cut':p['coupled_terms'][0]['cut']['n_exponent']='1/2'
            if mode=='class':
                for term in p['coupled_terms']:term['weight']['arithmetic']='prime'
            if mode=='gain':c['prime_gain']='3'
            if mode=='group':c['matched_groups'][0]['normal_indices']=[]
            if mode=='bool':c['minimum_u']=True
            if mode=='scope':c['full_remaining_kernel_unpaid']=False
            self.assertEqual(O.verify_certificate(p,c)['status'],'INVALID')
    def test_generic_outer_binding_and_resources(self):
        p,c=fixture();p['kernel'].append(dict(divisor=20,weight='123/17'));self.assertEqual(O.verify_certificate(p,c)['status'],'VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL')
        p['kernel'][0]['divisor']=3;self.assertEqual(O.verify_certificate(p,c)['status'],'INVALID')
        p,c=fixture();self.assertTrue(O.verify_certificate(p,c,O.Meter(limit=1))['resource_limit']);c['matched_groups'][0]['normal_indices']=[0]*10000;self.assertEqual(O.verify_certificate(p,c)['status'],'INVALID')
if __name__=='__main__':unittest.main()
