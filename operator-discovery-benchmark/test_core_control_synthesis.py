import unittest
from flint import arb,ctx
import core_control_synthesis as P

TOTAL=0
class Meter:
    def charge(self,n=1):
        global TOTAL
        TOTAL+=n
    def live(self,n):pass
def tearDownModule():print('SYNTHETIC_WORK module=test_core_control_synthesis operations='+str(TOTAL))

class Controls(unittest.TestCase):
    def setUp(self):ctx.prec=192;self.m=Meter()
    def test_complete_cross_domination_and_float_agreement(self):
        state=dict(H=7,G=list(map(arb,[0,-3,2,-1,4,-2,6,-5])),Bg=list(map(arb,[0,0,-4,2,-8,6,1,-3])),D=list(map(arb,[0,0,1,-2,0,3,-1,0])))
        tables=P.float_tables(state,[1,2,4],self.m)
        for row in P.catalogue(self.m):
            program=row['program'];a=P.real(program['mix']);w=P.real(program['reserve']);c=1+a*a/w
            values=P.float_storage(program,tables)
            for X in (1,2,4):
                actual=P.exact_measure(state,program,X,self.m);base=sum((v*v for v in state['G'][X:2*X]),arb(0))/X**2
                self.assertGreaterEqual(float(c*actual-base),-1e-14)
                self.assertAlmostEqual(values[X],float(actual),places=11)
    def test_proof_composition_and_fractional_recurrence(self):
        p=dict(auxiliary=dict(kind='half_delay',alpha='1/6'),mix='-1',reserve='1/3')
        for theta,expected in [('7/12',True),('5/6',True),('1',False)]:
            c=P.certificate(p,dict(rho='1',log_power='1/2'),dict(theta=theta),True)
            self.assertEqual(c['domination_constant'],'4');self.assertEqual(c['conditional_log_degree'],'3/2')
            self.assertEqual(c['pole_excluded'],expected);self.assertFalse(c['uniform_premise_established'])
    def test_frozen_constant_can_fail_later_and_graph_stays_open(self):
        shape=dict(rho='1',log_power='1');storage={1:arb(1),2:arb(2),4:arb(3),8:arb(100)}
        C=P.fit({k:float(v) for k,v in storage.items()},[1,2],shape,self.m)
        verdict=P.exact_test(storage,[1,2,4],shape,C,self.m)
        self.assertEqual([v['status'] for v in verdict],['pass','pass','fail'])
        p=dict(auxiliary=None,mix='0',reserve='1');transport=dict(theta='5/6')
        record=dict(transport_id=1,storage_id=0,storage_program=p,transport_program=transport,shape=shape,constant=C,certificate=P.certificate(p,shape,transport,True))
        graph=P.proof_obligation(record)
        self.assertEqual(graph['next_search_target']['status'],'open');self.assertFalse(graph['whole_signed_bound_proved'])
    def test_invalid_reserve_and_dropped_blocks(self):
        for w in ('0','-1','2/2'):
            with self.assertRaises(ValueError):P.validate(dict(auxiliary=dict(kind='log_bank',alpha='0'),mix='1',reserve=w))
        with self.assertRaises(ValueError):P.exact_measure(dict(H=3),dict(auxiliary=None,mix='0',reserve='1'),4,self.m)
