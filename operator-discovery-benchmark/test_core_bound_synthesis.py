"""Finite semantics and proof-scope tests for automatic core bound synthesis."""
from fractions import Fraction as Q
import unittest
from flint import arb,ctx
import core_bound_synthesis as P

METERS=[]


class Meter:
    def __init__(self,cap=10000000):
        self.operations=0;self.cap=cap;self.peak_cells=0;METERS.append(self)
    def charge(self,n=1):
        if type(n)is not int or n<0:raise ValueError('nonnegative integer charge')
        if n>self.cap-self.operations:raise OverflowError('work cap')
        self.operations+=n
    def live(self,n):
        self.charge();self.peak_cells=max(self.peak_cells,n)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_core_bound_synthesis operations='+str(sum(m.operations for m in METERS)))


def synthetic(H,meter):
    prefixes={name:[arb(0)]*(H+1) for name in P.NAMES}
    core=[arb(0)]*(H+1);F=[arb(0)]*(H+1)
    c=[arb(9)/2,-arb(9)/2,-arb(4),-arb(9)/2]
    for n in range(1,H+1):
        for i,name in enumerate(P.NAMES):
            value=arb((n+i)%5-2)
            prefixes[name][n]=prefixes[name][n-1]+value
            core[n]+=c[i]*value
            meter.charge(5)
        F[n]=F[n-1]+core[n]
    return P.assemble_state(prefixes,core,F,arb(4),H,meter)


def literal(program,X,state,meter):
    target=filtered=auxiliary=arb(0)
    f=program['target_filter'];aux=program['auxiliary']
    for n in range(X,2*X):
        F=state['F'][n]
        if f['kind']=='log_abel':
            if n<64:G=F
            else:
                B=sum((state['core'][k]*arb(k).log() for k in range(1,n+1)),arb(0))
                G=B/arb(n).log();meter.charge(70*n)
        else:
            a=f['sign']*arb(2)**(arb(Q(f['theta']).numerator)/Q(f['theta']).denominator)
            G=F-a*state['F'][n//2]
        h=arb(0)
        if aux is not None:
            t=aux['theta'];b=arb(0) if t is None else arb(2)**(arb(Q(t).numerator)/Q(t).denominator)
            for text,name in zip(aux['coefficients'],P.NAMES):
                q=Q(text)
                h+=arb(q.numerator)/q.denominator*(state['prefixes'][name][n]-b*state['prefixes'][name][n//2])
            alpha=Q(aux['alpha']);h*=arb(n)**(-arb(alpha.numerator)/alpha.denominator)
        target+=F*F;filtered+=G*G;auxiliary+=h*h;meter.charge(250)
    target/=X*X;filtered/=X*X;auxiliary/=X*X
    w=Q(0) if aux is None else Q(aux['weight'])
    return dict(energy_target=target,energy_filtered=filtered,energy_auxiliary=auxiliary,
                majorant=filtered+arb(w.numerator)/w.denominator*auxiliary)


class BoundSynthesisTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.old=ctx.prec;ctx.prec=160
    @classmethod
    def tearDownClass(cls):ctx.prec=cls.old

    def test_enumeration_is_source_response_free_and_diverse(self):
        m=Meter();rows=P.catalogue(m)
        self.assertEqual(len(rows),14*769)
        self.assertEqual([r['id'] for r in rows],list(range(len(rows))))
        self.assertEqual({r['program']['target_filter']['kind'] for r in rows},{'delay','log_abel'})
        self.assertTrue(any(r['program']['auxiliary'] and '-1' in r['program']['auxiliary']['coefficients'] for r in rows))
        self.assertTrue(all(not r['whole_signed_bound_proved'] and not r['RH_proved'] for r in rows))
        self.assertEqual(len({str(r['program']) for r in rows}),len(rows))

    def test_streaming_gram_matches_literal_complete_expressions(self):
        m=Meter();state=synthetic(127,m);scales=[1,3,8,32,33,64]
        tables=P.gram_tables(state,scales,m);cache={}
        programs=[dict(target_filter=dict(kind='delay',sign=-1,theta='1/6'),auxiliary=None),
                  dict(target_filter=dict(kind='delay',sign=1,theta='1/2'),
                       auxiliary=dict(coefficients=['1','-1','0','1/3'],theta='2/3',alpha='1/6',weight='3')),
                  dict(target_filter=dict(kind='log_abel',cutoff=64),
                       auxiliary=dict(coefficients=['0','1','-1','0'],theta=None,alpha='1/2',weight='1/3'))]
        for p in programs:
            rows=P.energies(p,tables,state,m,cache)
            for X in scales:
                direct=literal(p,X,state,m)
                for key,value in direct.items():self.assertTrue(rows[X][key].overlaps(value),(X,key,rows[X][key],value))
        with self.assertRaises(ValueError):P.gram_tables(state,[65],m)

    def test_late_counterexample_does_not_recalibrate_or_prove(self):
        m=Meter();rows={X:dict(majorant=arb(v)) for X,v in ((1,2),(2,2),(4,2),(8,2),(16,20))}
        C=P.fit(rows,[1,2,4],'1','0',0,m)
        self.assertEqual(C,'0')
        training=P.score(rows,[1,2,4],'1','0',0,C,m)
        test=P.score(rows,[8],'1','0',0,C,m)
        self.assertEqual(training['failed'],0);self.assertEqual(test['decisions'][0]['status'],'counterexample')
        self.assertFalse(test['uniform_premise_proved']);self.assertEqual(C,'0')

    def test_conditional_recovery_does_not_close_missing_step(self):
        for theta,admitted,degree in (('1/3',True,1),('1/2',True,3),('2/3',False,None)):
            p=dict(target_filter=dict(kind='delay',sign=1,theta=theta),auxiliary=None)
            c=P.implication(p,'1','0',0,'2','3')
            self.assertEqual(c['conditional_core_cofinal'],admitted)
            self.assertEqual(c['conditional_core_log_degree'],degree)
            self.assertFalse(c['uniform_premise_proved']);self.assertFalse(c['RH_proved'])
        p=dict(target_filter=dict(kind='log_abel',cutoff=64),auxiliary=None)
        self.assertEqual(P.implication(p,'1/2','0',0,'2','3')['conditional_core_log_degree'],1)
        c=P.implication(p,'1/2','1/6',1,'2','3')
        self.assertFalse(c['conditional_core_cofinal'])
        self.assertEqual(P.coarse_certificate(p)['gamma'],'1')

    def test_pole_obstruction_retains_boundary_and_zero_modes(self):
        m=Meter();base=dict(target_filter=dict(kind='delay',sign=0,theta='0'),auxiliary=None)
        aux=dict(coefficients=['1','0','0','0'],theta=None,alpha='0',weight='1')
        self.assertTrue(P.pole_gate(dict(base,auxiliary=aux),m)['cofinal_obstructed'])
        for variation in (dict(aux,alpha='1/6'),dict(aux,theta='2/3'),dict(aux,coefficients=['0','0','0','1'])):
            self.assertFalse(P.pole_gate(dict(base,auxiliary=variation),m)['cofinal_obstructed'])

    def test_real_candidate_obligation_is_scoped_and_open(self):
        m=Meter();r=P.catalogue(m)[0]
        fit=dict(decisions=[],failed=0,uniform_premise_proved=False)
        h=P.hypothesis_record(r,'1','0',0,'2','3',fit,fit,dict(cofinal_obstructed=False))
        obligation=P.obligation(h,r)
        self.assertEqual(obligation['program'],r['program'])
        self.assertIn('all dyadic',obligation['uniformity'])
        self.assertEqual(obligation['status'],'open')
        self.assertFalse(obligation['whole_signed_bound_proved'])
        self.assertTrue(obligation['is_stronger_sufficient_intermediate_lemma'])
        rejected=P.obligation(dict(h,status='finite_counterexample'),r)
        self.assertEqual(rejected['status'],'counterexample_found')


if __name__=='__main__':unittest.main()
