import unittest
from flint import arb,ctx
import core_increment_projection as P

TOTAL=0
class Meter:
    def charge(self,n=1):
        global TOTAL
        TOTAL+=n
    def live(self,n):pass
def tearDownModule():print('SYNTHETIC_WORK module=test_core_increment_projection operations='+str(TOTAL))

class Projection(unittest.TestCase):
    def setUp(self):ctx.prec=192;self.m=Meter()
    def state(self):
        f=list(map(arb,[0,-3,2,-1,4,0,-2,1,3,-1,2,-3,4,-2,-1,1]))
        G=[arb(0)];B=[arb(0)]
        for n in range(1,16):G.append(G[-1]+f[n]);B.append(B[-1]+f[n]*arb(n).log())
        return dict(H=15,g=f,G=G,Bg=B,D=list(map(arb,[0,0,1,-1,0,2,-2,0,1,0,-1,0,2,0,-2,0])))
    def test_exact_variance_matches_literal_pairs_and_path(self):
        p=dict(auxiliary=dict(kind='half_delay',alpha='0'),mix='-1',reserve='1/3')
        t=P.prepare(self.state(),p,self.m)
        for r in ('1/3','1/2','1'):
            result=P.project(t,8,r,self.m);pair=arb(0);path=arb(0)
            for cell in result['cell_means']:
                lo,hi=cell['start'],cell['stop'];L=hi-lo
                for i in range(lo,hi):
                    for j in range(i+1,hi):pair+=((t['U'][i]-t['U'][j])**2+t['weight']*(t['Q'][i]-t['Q'][j])**2)/L;self.m.charge(20)
                for n in range(lo+1,hi):path+=(n-lo)*(hi-n)/2*((t['U'][n]-t['U'][n-1])**2+t['weight']*(t['Q'][n]-t['Q'][n-1])**2);self.m.charge(20)
            self.assertTrue(result['detail_storage'].overlaps(pair/64));self.assertTrue(result['path_bound'].overlaps(path/64))
            self.assertTrue(result['identity_residual'].contains(0));self.assertNotEqual(result['path_comparison'],'fail')
    def test_complete_head_survives_and_projection_is_nested(self):
        p=dict(auxiliary=None,mix='0',reserve='1');t=P.prepare(self.state(),p,self.m)
        one=P.project(t,1,'1/2',self.m);self.assertTrue(one['full_storage'].overlaps(arb(9)));self.assertTrue(one['detail_storage'].is_zero())
        a=P.project(t,8,'1/3',self.m);b=P.project(t,8,'1',self.m)
        self.assertTrue(b['coarse_storage']<=a['coarse_storage'])
        self.assertEqual(b['cell_means'][0]['start'],8)
        self.assertTrue(b['cell_means'][0]['U_mean'].overlaps(sum(t['U'][8:16],arb(0))/8))
    def test_fractional_auxiliary_and_payment_frontier(self):
        p=dict(auxiliary=dict(kind='log_bank',alpha='1/6'),mix='1',reserve='3');t=P.prepare(self.state(),p,self.m)
        expected=self.state()['Bg'][7]/arb(14).log()/arb(7).root(6)
        self.assertTrue(t['Q'][7].overlaps(expected))
        a=P.certificate(p,'1/3',self.m);b=P.certificate(p,'1/2',self.m);c=P.certificate(p,'2/3',self.m)
        self.assertEqual(a['auxiliary_derivative_factor'],'13/3');self.assertEqual(a['detail_power'],'-1/3')
        self.assertEqual(a['effective_detail_log_degree'],0);self.assertEqual(b['effective_detail_log_degree'],3)
        self.assertFalse(c['cofinal_recovery']);self.assertFalse(a['coarse_bound_proved'])
    def test_proof_selection_uses_open_input_and_preserves_obligation(self):
        p=dict(auxiliary=None,mix='0',reserve='1')
        ob=dict(id='actual_open_leaf',schema='detector-generated-core-control-obligation-v1',status='open_uniform_increment',uniform_premise_established=False,
                storage_program=p,transport_program=dict(theta='5/6'))
        rows=P.generate([ob],self.m);chosen=P.proof_select(rows)
        self.assertEqual([r['mesh_power'] for r in chosen],['1/3','1/2'])
        for row in chosen:self.assertFalse(P.obligation(row)['coarse_bound_proved'])
        with self.assertRaises(ValueError):P.mesh(3,'1/2',15)
        with self.assertRaises(ValueError):P.mesh(16,'1/2',15)
        with self.assertRaises(ValueError):P.certificate(dict(auxiliary=dict(kind='log_bank',alpha='1/2'),mix='1',reserve='1'),'1/3',self.m)
    def test_mean_zero_guard_and_scoped_weak_fact_countermodels(self):
        p=dict(auxiliary=None,mix='0',reserve='1')
        row=dict(mesh_power='2/3',transport_program=dict(theta='5/6'))
        guard=P.coarse_pole_guard(row,True,self.m)
        self.assertEqual(guard['detail_mellin_holomorphic_Re_s_greater_than'],'1/3')
        self.assertEqual(guard['coarse_minimum_log_degree'],2)
        self.assertTrue(guard['stronger_holomorphy_is_not_automatically_a_critical_energy_bound'])
        counter=P.weak_fact_countermodels(p,self.m)[0]
        self.assertEqual((counter['start'],counter['projected_storage_lower_constant']),(64,'1/16'))
        H=[arb(0)]*128;g=[arb(0)]*128;g[1]=arb(-9)
        for n in range(2,128):g[n]=arb(int(n>=4 and n%2==0))
        for n in range(1,128):H[n]=H[n-1]+g[n]
        t=P.prepare(dict(H=127,g=g,G=H,Bg=[arb(0)]*128,D=[arb(0)]*128),p,self.m)
        self.assertTrue(P.project(t,64,'1/2',self.m)['coarse_storage']>=4)
        self.assertFalse(counter['actual_core_bound_disproved']);self.assertFalse(counter['complete_actual_source_AST_satisfied'])
    def test_source_specific_analytic_lane_keeps_energy_scope_separate(self):
        source=dict(terms=[dict(name='leading',coefficient='b',zeta_factors=[['0','-2'],['1/3','1']]),
                           dict(name='lower',coefficient='c',zeta_factors=[['0','-1'],['2/3','-1']])])
        scalars=dict(b=arb(2),c=arb(-1));bridge=P.source_holomorphy_bridge(source,scalars,self.m)
        self.assertTrue(bridge['verified']);self.assertEqual(bridge['zero_orders_per_multiplicity'],[2,1])
        ob=dict(id='full_source',schema='detector-generated-core-control-obligation-v1',status='open_uniform_increment',uniform_premise_established=False,
                storage_program=dict(auxiliary=None,mix='0',reserve='1'),transport_program=dict(theta='5/6'))
        rows=P.generate([ob],self.m)
        for row in rows:row['analytic_recovery']=P.analytic_recovery(row,bridge,self.m)
        chosen=P.proof_select(rows);self.assertEqual([r['mesh_power'] for r in chosen],['1/3','1/2','2/3'])
        result=P.obligation(chosen[-1]);self.assertFalse(result['detail_certificate']['cofinal_recovery'])
        self.assertTrue(result['analytic_recovery']['admitted']);self.assertFalse(result['analytic_recovery']['RH_proved'])
        self.assertIsNone(result['original_recovery']['conditional_original_log_degree'])
        tied=dict(terms=[source['terms'][0],dict(name='tie',coefficient='c',zeta_factors=[['0','-2']])])
        self.assertFalse(P.source_holomorphy_bridge(tied,scalars,self.m)['verified'])
        negative=dict(terms=[dict(name='unsafe',coefficient='b',zeta_factors=[['0','-2'],['-1/3','1']])])
        self.assertFalse(P.source_holomorphy_bridge(negative,scalars,self.m)['verified'])
