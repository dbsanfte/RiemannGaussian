"""Synthetic exact source tests only; no actual promoted-state observations."""
import copy
from fractions import Fraction as Q
import unittest
import check_floor_residual_transition_source_050 as C
import check_floor_residual_drift_045 as OLD_CHECK
import floor_residual_transition_search_050 as P
import floor_residual_drift_045 as DRIFT_PRODUCER
from prime_bank_candidates import Meter as ExternalMeter

CHECKER=C.Meter(cap=50000000,seconds=180)
PRODUCER=P.Meter(cap=50000000,seconds=180)
DRIFT_METER=DRIFT_PRODUCER.Meter(cap=50000000,seconds=180)
COMPILER=P.StateCompiler(PRODUCER,DRIFT_METER)


def request(p=2,N=8,d='7/13',theta='6/11',a='1',terms=None):
    terms=terms or [('1','4'),('2','-6'),('3','4'),('4','-1')]
    return {'source_recipe':{'id':'synthetic_transition','base':{
        'kind':'drift_mixture','a':a,'theta':theta,
        'terms':[{'rate':r,'weight':w} for r,w in terms]},'auxiliary':None},
        'prime':p,'parent_support':N,'d':d,'rounding':copy.deepcopy(C.ROUNDING)}


def certify(r):return COMPILER.compile(r)
def verify(r,c):return C.verify_state(r,c,CHECKER)


def set_column(program,n,value):
    rows={row['n']:row['value'] for row in program['coefficients']};rows[n]=value
    program['coefficients']=[{'n':j,'value':v} for j,v in sorted(rows.items()) if Q(v)]


class SourceStateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.r=request();cls.c=certify(cls.r)

    def reject(self,r,c):
        with self.assertRaises((ValueError,OverflowError,ArithmeticError)):
            verify(r,c)

    def test_actual_separate_signed_rounding_and_complete_recovery(self):
        result=verify(self.r,self.c)
        self.assertTrue(result['verified']);self.assertTrue(result['actual_source_profiles_verified'])
        self.assertFalse(result['uniform_bound_proved']);self.assertFalse(result['rh_claim'])
        self.assertEqual(result['counters']['profile_values_verified'],24)
        # Independent trusted045 per-value admission on a few exact profiles.
        for n,N,key in ((1,8,'parent_values'),(4,8,'parent_values'),(3,16,'child_values'),(16,16,'child_values')):
            OLD_CHECK.verify_compilation(self.r['source_recipe']['base'],n,N,self.c[key][n-1],CHECKER)

    def test_general_fractional_exponents_d_and_signed_profiles(self):
        requests=(request(p=3,N=5,d='11/13',theta='4/9',terms=[('3/7','2'),('11/5','-1')]),
                  request(N=2,d='1/257',theta='123/257',terms=[('1/3','3'),('5/7','-2')]),
                  request(N=4,d='-1/3',theta='1/2',a='3/7',terms=[('2/5','1')]),
                  request(N=4,d='0',theta='2/3',terms=[('1','1')]))
        for r in requests:self.assertTrue(verify(r,certify(r))['verified'])

    def test_mu_zero_values_independently_source_bound(self):
        for key,index in (('parent_values',3),('child_values',3),('child_values',7)):
            c=copy.deepcopy(self.c);c[key][index]=str(Q(c[key][index])+Q(1,4096))
            self.reject(self.r,c)

    def test_prime_square_and_unit_step_not_dropped(self):
        verify(self.r,self.c)
        coeff={row['n']:Q(row['value']) for row in self.c['programs']['h']['coefficients']}
        # At n=4 the child mu term vanishes, but the parent n=2 survives.
        self.assertEqual(coeff[4],Q(self.c['parent_values'][1]))
        self.assertNotIn(8,coeff)
        c=copy.deepcopy(self.c);set_column(c['programs']['h'],4,'0');self.reject(self.r,c)
        c=copy.deepcopy(self.c);set_column(c['programs']['h'],8,'1/16');self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['programs']['h']['steps']=[];self.reject(self.r,c)

    def test_auxiliary_indicator_and_f_p_normalizer(self):
        lam=Q(self.c['child_values'][1]);d=Q(self.r['d'])
        self.assertEqual(Q(self.c['programs']['A']['steps'][0]['value']),lam-1)
        self.assertEqual(Q(self.c['programs']['v']['steps'][0]['value']),-1-d*(lam-1))
        for name in ('h','A','v'):
            c=copy.deepcopy(self.c);set_column(c['programs'][name],2,'0');self.reject(self.r,c)
        for name in ('A','v'):
            c=copy.deepcopy(self.c);c['programs'][name]['steps']=[];self.reject(self.r,c)

    def test_missing_tail_or_unit_values(self):
        for key in ('parent_values','child_values'):
            c=copy.deepcopy(self.c);c[key].pop();self.reject(self.r,c)
            c=copy.deepcopy(self.c);c[key][0]='0';self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['child_values'][-1]=str(Q(c['child_values'][-1])+Q(1,65536))
        self.reject(self.r,c)

    def test_source_recipe_and_rounding_swaps(self):
        r=copy.deepcopy(self.r);r['source_recipe']['base']['theta']='1/2';self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['source_recipe']['base']['terms'][0]['weight']='5';self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['source_recipe']['auxiliary']={'kind':'fitted'};self.reject(r,self.c)
        for key,val in (('bits_multiplier',3),('bits_multiplier',4.0),('product','round_after_signed_sum')):
            r=copy.deepcopy(self.r);r['rounding'][key]=val;self.reject(r,self.c)
        c=copy.deepcopy(self.c);c['request']['source_recipe']['id']='swapped';self.reject(self.r,c)

    def test_program_target_identity_and_scope_swaps(self):
        for name in ('h','A','v'):
            c=copy.deepcopy(self.c);c['programs'][name]['id']+='forged';self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['programs']['h'],c['programs']['v']=c['programs']['v'],c['programs']['h']
        self.reject(self.r,c)
        for field,value in (('identity_only',False),('uniform_bound_proved',True),('rh_claim',True),('rh_claim',0)):
            c=copy.deepcopy(self.c);c[field]=value;self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['recurrence_proved']=True;self.reject(self.r,c)
        c=copy.deepcopy(self.c);c['programs']['A']['lambda']='1';self.reject(self.r,c)

    def test_invalid_inputs_and_resource_gates(self):
        for field,value in (('prime',4),('prime',True),('prime',2.0),('parent_support',1),
                            ('parent_support',2501),('d','2/4'),('d',0.5)):
            r=copy.deepcopy(self.r);r[field]=value;self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['source_recipe']['base']['terms'].reverse();self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['source_recipe']['base']['terms'][0]['rate']='0';self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['source_recipe']['base']['theta']='1';self.reject(r,self.c)
        r=copy.deepcopy(self.r);r['source_recipe']['base']['a']=str(2**4097);self.reject(r,self.c)
        with self.assertRaises(OverflowError):C.verify_state(self.r,self.c,C.Meter(1))

    def test_charge_only_external_meter(self):
        m=ExternalMeter(cap=5000000,seconds=60)
        self.assertTrue(C.verify_state(self.r,self.c,m)['verified'])
        CHECKER.charge(m.operations)

    def test_exact_zero_normalization_and_capacity_5000(self):
        # This deliberately synthetic high-rate profile is EXACTLY zero at
        # every n>=2 under the fixed dyadic rounding. It tests index capacity
        # without computing the promoted scientific candidate at new scales.
        r=request(N=2500,d='2',theta='1/2',terms=[('200','1')])
        prefix='prime_transition_2_2500'
        def program(name,Ctext,step):
            return {'id':prefix+'_'+name,'constant':Ctext,'coefficients':[],
                    'steps':[] if not step else [{'q':2,'value':step}]}
        c={'schema':'floor-prime-transition-state-v1','request':copy.deepcopy(r),
           'parent_values':['1']+['0']*2499,'child_values':['1']+['0']*4999,
           'programs':{'h':program('h','1','-1'),'A':program('A','0','-1'),'v':program('v','1','1')},
           'identity_only':True,'uniform_bound_proved':False,'rh_claim':False}
        result=verify(r,c)
        self.assertEqual(result['child_support'],5000)
        self.assertTrue(result['division_free_matched_recovery_verified'])
        c['child_values'][4998]='1/65536';self.reject(r,c)


class ExactAtomTests(unittest.TestCase):
    def test_nontrivial_integer_root_agreement_and_high_index(self):
        for n,exponent,bits in ((3,Q(2,3),9),(5,Q(7,11),12),(7,Q(3,17),10),
                                 (4999,Q(3,7),12),(3,Q(1,257),8),(16,Q(1,2),8)):
            self.assertEqual(C._atom(n,exponent,bits,CHECKER),
                OLD_CHECK.rounded_twist(n,exponent,bits,CHECKER))

    def test_floor_zero_and_exact_equality_boundaries(self):
        # Equality at the minimum-bit lower bound must retain the smallest
        # nonzero dyadic atom. Strict inequality alone licenses zero.
        self.assertEqual(C._atom(2,Q(8),8,CHECKER),Q(1,256))
        self.assertEqual(C._atom(2,Q(9),8,CHECKER),0)
        self.assertEqual(C._atom(4,Q(4),8,CHECKER),Q(1,256))
        self.assertEqual(C._atom(4,Q(5),8,CHECKER),0)
        self.assertEqual(C._atom(1,Q(1,257),8,CHECKER),1)

    def test_exact_ceiling_jump_not_smooth_drift(self):
        spec=request(theta='1/2',terms=[('1','1')])['source_recipe']['base']
        terms=C.DRIFT.parse_spec(spec,CHECKER)[2]
        a=C._profile(spec,15,terms,{},CHECKER)
        b=C._profile(spec,16,terms,{},CHECKER)
        self.assertEqual(a[1],Q(1,2));self.assertEqual(b[1],Q(3,5))
        self.assertGreater(b[1],a[1])

    def test_distinct_precision_cache_keys(self):
        spec=request(theta='1/2',terms=[('1','1')])['source_recipe']['base']
        terms=C.DRIFT.parse_spec(spec,CHECKER)[2];cache={}
        a=C._profile(spec,9,terms,cache,CHECKER)
        b=C._profile(spec,33,terms,cache,CHECKER)
        self.assertEqual(a[1],b[1]);self.assertNotEqual(a[2],b[2])
        self.assertNotEqual(a[0][3],b[0][3])
        # Replaying the same functional context reuses every licensed atom.
        c=C._profile(spec,9,terms,cache,CHECKER)
        self.assertEqual(c[0],a[0]);self.assertEqual(c[3],0);self.assertEqual(c[4],9)

    def test_new_program_index_and_input_bit_limits(self):
        program={'id':'synthetic_high_index','constant':'0',
                 'coefficients':[{'n':4999,'value':'1/2'}],'steps':[]}
        self.assertEqual(C._decode(program,CHECKER)[1],{4999:Q(1,2)})
        bad=copy.deepcopy(program);bad['coefficients'][0]['n']=5001
        with self.assertRaises(ValueError):C._decode(bad,CHECKER)
        bad=copy.deepcopy(program);bad['coefficients'][0]['value']=str(2**4097)
        with self.assertRaises(ValueError):C._decode(bad,CHECKER)
        with self.assertRaises(OverflowError):C._atom(3,Q(1,20000),52,CHECKER)


def tearDownModule():
    total=CHECKER.operations+PRODUCER.operations+DRIFT_METER.operations
    print('SYNTHETIC_WORK module=test_check_floor_residual_transition_source_050 operations='+str(total))
    print('SYNTHETIC_SPLIT checker='+str(CHECKER.operations)+' fixture='+str(PRODUCER.operations+DRIFT_METER.operations))

if __name__=='__main__':unittest.main()
