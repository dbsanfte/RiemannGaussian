"""Hand-derived exact and nonexact divisions; abstract rational calibration."""
from copy import deepcopy
from fractions import Fraction as Q
import json
import resource
import sys
import time
import unittest

import check_core_frame_bounds as CHECK
from potential_candidate_language import Meter

START=time.monotonic()
WORK=Meter(50000000,deadline=START+180,max_cells=1000000)


def plus(left,right,scale=Q(1)):
    out=left.copy()
    for key,c in right.items():
        out[key]=out.get(key,Q(0))+scale*c
        if not out[key]:del out[key]
    return out


def times(left,right):
    out={}
    for key,c in left.items():
        for other,d in right.items():
            monomial=tuple(sorted(key+other));out[monomial]=out.get(monomial,Q(0))+c*d;WORK.charge(20)
    return {k:c for k,c in out.items() if c}


def encode(poly):return [dict(monomial=list(k),coefficient=str(c)) for k,c in sorted(poly.items())]


def value(poly,point):
    total=Q(0)
    for key,c in poly.items():
        for i in key:c*=point[i];WORK.charge(5)
        total+=c
    return total


def fixture(transformed=False):
    # Two rational kernel vectors, with nonexact two-vector division worked
    # out by hand. The transformed singleton tests ordered witness fallback.
    x,y,z={(0,):Q(1)},{(1,):Q(1)},{(2,):Q(1)}
    if transformed:
        vectors=[[y,plus(x,z,Q(1)),y]]
        vectors[0][1]={k:-c for k,c in vectors[0][1].items()}
    else:vectors=[[y,{(0,):Q(-1)},{}],[z,{}, {(0,):Q(-1)}]]
    basis=[];sums=[]
    for ident,vector in enumerate(vectors):
        rows=[];summed={}
        for v in vector:
            rows.append(['0']+[str(v.get((j,),0)) for j in range(3)]);summed=plus(summed,v)
        sums.append(summed)
        basis.append(dict(id=ident,vector=rows,sum=['0']+[str(summed.get((j,),0)) for j in range(3)]))
    frames=[];certificates=[];exact_count=0;sos_count=0
    for mask in range(1,2**len(vectors)):
        ids=[i for i in range(len(vectors)) if mask&(1<<i)];W=[{}, {}, {}];S={};A={}
        for j in ids:
            S=plus(S,times(sums[j],sums[j]))
            for i,v in enumerate(vectors[j]):W[i]=plus(W[i],times(sums[j],v));A=plus(A,times(v,v))
        P={}
        for w in W:P=plus(P,times(w,w))
        if len(ids)==1:
            branch='exact_quotient';quotient=A;remainder={};B=A;sos=[];exact_count+=1
        else:
            branch='cauchy_quotient';B=A
            # Graded-lex quotient and remainder of the star frame, hand-derived.
            quotient={(0,0):Q(1),(1,1):Q(1,2),(1,2):Q(1),(2,2):Q(1,2)}
            remainder={(0,1,1,1):Q(-1),(0,1,1,2):Q(1),(0,1,2,2):Q(1),(0,2,2,2):Q(-1),
                       (1,1,1,1):Q(1,2),(1,1,1,2):Q(-1),(1,1,2,2):Q(1),
                       (1,2,2,2):Q(-1),(2,2,2,2):Q(1,2)}
            witnesses=[{(0,1):Q(1),(0,2):Q(-1)}, {(0,0):Q(-1),(0,2):Q(1)},
                       {(0,0):Q(1),(0,1):Q(-1)}]
            sos=[dict(coordinate=i,left=0,right=1,polynomial=encode(p)) for i,p in enumerate(witnesses)]
        slack=plus(times(S,B),P,Q(-1));sos_count+=len(sos)
        frame=dict(id=mask-1,basis_ids=ids,weights=list(map(encode,W)),normalizer=encode(S),
            sos_linear_forms=[basis[i]['sum'] for i in ids],active_coordinates=[i for i,w in enumerate(W) if w],
            normalizer_nonnegative_proved=True,normalizer_positive_proved=False)
        frames.append(frame)
        points=[[Q(1),Q(2),Q(3)]]+[[Q(int(i==j)) for i in range(3)] for j in range(3)]
        point=next(p for p in points if value(S,p)>0 and value(B,p)>0)
        Sv=value(S,point);Pv=value(P,point);Bv=value(B,point);weights=[value(w,point)/Sv for w in W]
        certificates.append(dict(id=mask-1,recovery_numerator=encode(P),division=dict(quotient=encode(quotient),remainder=encode(remainder)),
            branch=branch,bound_numerator=encode(B),slack=encode(slack),sos=sos,
            common_mode=dict(unnormalized_G_coefficient=encode(S),unnormalized_J_coefficient=[],
                unnormalized_paid_coefficients=[encode({k:-c for k,c in w.items()}) for w in W],normalized_G_coefficient='1',
                classification='equivalent_to_full_core_modulo_paid_vector_and_recovery_cost',remaining_signed_bound='open',
                uniform_signed_control_added=False),
            arithmetic_condition=dict(positive_denominator=encode(S),left=encode(S),right_factor=encode(B),
                rho='c*(1+log2X)^(-q)',parameters='one fixed c>0, one fixed q>=0, one fixed finite dyadic X0',
                quantifier='EVERY dyadic X>=X0, N=4X-1',required='S>0 and S>=rho*B',
                conclusion='K<=c^(-1)*(1+log2X)^q',status='open'),
            countermodel=dict(drifts=list(map(str,point)),normalizer=str(Sv),numerator=str(Pv),bound_numerator=str(Bv),
                recovery_cost=str(Pv/Sv**2),rho=str(Sv/(2*Bv)),margin=str(Sv/2),weights=list(map(str,weights)),
                common_mode_slope='1',residual_energy='T^2 for arbitrary real T on a unit abstract Hilbert vector H',
                source_AST_satisfied=False,actual_source_bound_disproved=False,recovery_condition_satisfied=True),
            universal_recovery_reduction_proved=True,uniform_actual_recovery_proved=False,uniform_actual_residual_proved=False))
    catalogue=dict(schema='core-cutoff-frame-v1',dimension=3,basis=basis,candidates=frames)
    result=dict(schema='core-frame-bound-synthesis-v1',dimension=3,certificates=certificates,
        statistics=dict(candidates=len(frames),exact_quotients=exact_count,cauchy_quotients=len(frames)-exact_count,sos_squares=sos_count),
        whole_signed_bound_proved=False,RH_proved=False)
    return catalogue,result


def source_fixture():
    _,result=fixture();certificate=result['certificates'][-1]
    representations=[dict(geometry_id=i,alpha='1/3',gamma=gamma,drift=dict(theta='2/3',
        polynomial=[dict(powers=[2,0,0,0],coefficient='2'),dict(powers=[0,1,0,1],coefficient='-3')]))
        for i,gamma in enumerate(['1/3','2/3','1/3'])]
    variables=[dict(id=i,kind='complete_mobius_moment',family=family,moment_power=power,cutoff_exponent=cutoff,
        definition='sum_(1<=n<=floor(N^cutoff_exponent)) mu(n)*n^(-moment_power)',unit_and_prime_powers_retained=True)
        for i,(family,power,cutoff) in enumerate([('a','2/3','1/3'),('b','4/3','1/3'),('b','4/3','2/3')])]
    variables.append(dict(id=3,kind='source_scalar',name='R_u',
        definition='(9/2)*(zeta(4/3)/zeta(2/3)^2-1/zeta(2/3))'))
    images=[{(0,0):Q(2),(1,3):Q(-3)},{(0,0):Q(2),(2,3):Q(-3)}, {(0,0):Q(2),(1,3):Q(-3)}]
    # Explicit hand expansion: D0=D2=2a²-3b1Ru, D1=2a²-3b2Ru.
    S={(1,1,3,3):Q(9),(1,2,3,3):Q(-18),(2,2,3,3):Q(9)}
    B={(0,0,0,0):Q(16),(0,0,1,3):Q(-36),(0,0,2,3):Q(-12),
       (1,1,3,3):Q(27),(2,2,3,3):Q(9)}
    condition=certificate['arithmetic_condition']
    item=dict(candidate_id=certificate['id'],variables=variables,geometry_order=[0,1,2],
        complete_drift_polynomials=list(map(encode,images)),denominator=encode(S),recovery_bound_numerator=encode(B),
        rho=condition['rho'],parameters=condition['parameters'],quantifier=condition['quantifier'],
        required='S>0 and S>=rho*B',common_horizon='N=4X-1',all_shared_moments_identified=True,
        algebraic_substitution_proved=True,arithmetic_inequality_proved=False,status='open')
    return representations,[certificate],[item]


class FrameBoundCheckerTests(unittest.TestCase):
    def test_exact_and_nonexact_hand_divisions_and_all_candidates(self):
        catalogue,result=fixture();summary=CHECK.verify(catalogue,result,WORK)
        self.assertEqual(summary['exact_quotients'],2)
        self.assertEqual(summary['cauchy_quotients'],1)
        self.assertEqual(summary['sos_squares'],3)
        self.assertEqual(result['certificates'][-1]['countermodel']['recovery_cost'],'69/25')

    def test_transformed_basis_uses_exact_ordered_countermodel(self):
        catalogue,result=fixture(True)
        summary=CHECK.verify(catalogue,result,WORK)
        self.assertEqual(summary['candidates'],1)
        self.assertEqual(result['certificates'][0]['countermodel']['drifts'],['1','0','0'])
        self.assertEqual(result['certificates'][0]['countermodel']['recovery_cost'],'1')

    def test_exact_quotient_branch_is_mandatory(self):
        catalogue,result=fixture();result['certificates'][0]['branch']='cauchy_quotient'
        with self.assertRaises(ValueError):CHECK.verify(catalogue,result,WORK)

    def test_division_numerator_quotient_and_remainder_tamper(self):
        for field in ('recovery_numerator','quotient','remainder','bound_numerator','slack'):
            catalogue,result=fixture();cert=result['certificates'][-1]
            if field in ('quotient','remainder'):cert['division'][field][0]['coefficient']='99'
            else:cert[field][0]['coefficient']='99'
            with self.subTest(field=field),self.assertRaises(ValueError):CHECK.verify(catalogue,result,WORK)

    def test_SOS_cross_terms_and_order_are_not_omitted(self):
        for kind in ('omit','sign','coordinate','order'):
            catalogue,result=fixture();sos=result['certificates'][-1]['sos']
            if kind=='omit':sos.pop()
            if kind=='sign':sos[0]['polynomial'][0]['coefficient']='-1'
            if kind=='coordinate':sos[0]['coordinate']=1
            if kind=='order':sos.reverse()
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.verify(catalogue,result,WORK)

    def test_common_mode_expansion_keeps_full_G_and_paid_signs(self):
        for kind in ('G','J','paid','classification','credit'):
            catalogue,result=fixture();common=result['certificates'][-1]['common_mode']
            if kind=='G':common['normalized_G_coefficient']='0'
            if kind=='J':common['unnormalized_J_coefficient']=[dict(monomial=[0],coefficient='1')]
            if kind=='paid':common['unnormalized_paid_coefficients'][0][0]['coefficient']='99'
            if kind=='classification':common['classification']='new bound for the full source'
            if kind=='credit':common['uniform_signed_control_added']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.verify(catalogue,result,WORK)

    def test_conditional_arithmetic_and_actual_source_stay_open(self):
        for kind in ('domain','rho','condition','actual_recovery','actual_residual','RH'):
            catalogue,result=fixture();cert=result['certificates'][0]
            if kind=='domain':cert['arithmetic_condition']['required']='S>=rho*B'
            if kind=='rho':cert['arithmetic_condition']['rho']='observed fitted constant'
            if kind=='condition':cert['arithmetic_condition']['status']='proved'
            if kind=='actual_recovery':cert['uniform_actual_recovery_proved']=True
            if kind=='actual_residual':cert['uniform_actual_residual_proved']=True
            if kind=='RH':result['RH_proved']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.verify(catalogue,result,WORK)

    def test_missing_duplicate_or_reordered_candidate_rejected(self):
        for kind in ('missing','duplicate','reordered','statistics'):
            catalogue,result=fixture()
            if kind=='missing':result['certificates'].pop()
            if kind=='duplicate':result['certificates'][1]=deepcopy(result['certificates'][0])
            if kind=='reordered':result['certificates'].reverse()
            if kind=='statistics':result['statistics']['sos_squares']=2
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.verify(catalogue,result,WORK)

    def test_abstract_countermodel_retains_arbitrary_common_mode(self):
        _,result=fixture()
        for cert in result['certificates']:
            model=cert['countermodel'];weights=list(map(Q,model['weights']));drifts=list(map(Q,model['drifts']))
            K=Q(model['recovery_cost']);rho=Q(model['rho'])
            self.assertLessEqual(K,1/rho)
            self.assertGreaterEqual(Q(model['margin']),0)
            for T in map(Q,['-7','1/2','1000000000000']):
                residual=sum((w*(T-d) for w,d in zip(weights,drifts)),Q(0));WORK.charge(100)
                self.assertEqual(residual,T);self.assertEqual(residual**2,T**2)
            self.assertFalse(model['source_AST_satisfied'])
            self.assertFalse(model['actual_source_bound_disproved'])

    def test_countermodel_value_scope_and_witness_selection_tamper(self):
        for kind in ('cost','margin','slope','source','disproof','point'):
            catalogue,result=fixture(True);model=result['certificates'][0]['countermodel']
            if kind=='cost':model['recovery_cost']='0'
            if kind=='margin':model['margin']='0'
            if kind=='slope':model['common_mode_slope']='0'
            if kind=='source':model['source_AST_satisfied']=True
            if kind=='disproof':model['actual_source_bound_disproved']=True
            if kind=='point':model['drifts']=['1','2','3']
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.verify(catalogue,result,WORK)

    def test_opposite_drift_unconditional_calibration_separate_from_source(self):
        catalogue,result=fixture();cert=result['certificates'][0]
        S=CHECK._decode(catalogue['candidates'][0]['normalizer'],3,WORK,2)
        P=CHECK._decode(cert['recovery_numerator'],3,WORK)
        B=CHECK._decode(cert['bound_numerator'],3,WORK,2)
        for t in map(Q,['-9','-1/3','1/7','100']):
            point=[t,-t,Q(0)];s=CHECK._value(S,point,WORK);p=CHECK._value(P,point,WORK);b=CHECK._value(B,point,WORK)
            self.assertGreater(s,0);self.assertEqual(p/s**2,Q(1,2));self.assertEqual(s,2*b)
        self.assertFalse(cert['uniform_actual_recovery_proved'])

    def test_exact_division_signed_rational_and_nonzero_remainder(self):
        # (x-y)*(3x/2+2y) and x² divided by x-y, independent expected answers.
        divisor={(1,0):Q(1),(0,1):Q(-1)}
        numerator={(2,0):Q(3,2),(1,1):Q(1,2),(0,2):Q(-2)}
        quotient,remainder=CHECK.divide(numerator,divisor,WORK)
        self.assertEqual(quotient,{(1,0):Q(3,2),(0,1):Q(2)});self.assertEqual(remainder,{})
        quotient,remainder=CHECK.divide({(2,0):Q(1)},divisor,WORK)
        self.assertEqual(quotient,{(1,0):Q(1),(0,1):Q(1)});self.assertEqual(remainder,{(0,2):Q(1)})

    def test_complete_source_substitution_identifies_shared_moments(self):
        representations,certificates,items=source_fixture()
        summary=CHECK.verify_source_conditions(representations,certificates,items,WORK)
        self.assertEqual(summary['moment_variables'],3)
        self.assertEqual(len(items[0]['variables']),4)
        self.assertEqual(items[0]['complete_drift_polynomials'][0],items[0]['complete_drift_polynomials'][2])
        self.assertTrue(all(0 not in t['monomial'] for t in items[0]['denominator']))
        self.assertFalse(items[0]['arithmetic_inequality_proved'])

    def test_source_substitution_moment_crosses_and_open_scope_tamper(self):
        for kind in ('variable','image','denominator','numerator','source_order','unit','proved','scope'):
            representations,certificates,items=source_fixture();item=items[0]
            if kind=='variable':item['variables'][1]['moment_power']='2/3'
            if kind=='image':item['complete_drift_polynomials'][0][0]['coefficient']='99'
            if kind=='denominator':item['denominator'][1]['coefficient']='-9'
            if kind=='numerator':item['recovery_bound_numerator'][1]['coefficient']='0'
            if kind=='source_order':item['geometry_order'].reverse()
            if kind=='unit':item['variables'][0]['unit_and_prime_powers_retained']=False
            if kind=='proved':item['arithmetic_inequality_proved']=True
            if kind=='scope':item['required']='S>=rho*B'
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.verify_source_conditions(representations,certificates,items,WORK)

    def test_source_substitution_rejects_unrepresented_c_or_negative_power(self):
        for kind in ('c','negative','theta','missing'):
            representations,certificates,items=source_fixture()
            if kind=='c':representations[0]['drift']['polynomial'][0]['powers'][2]=1
            if kind=='negative':representations[0]['drift']['polynomial'][0]['powers'][0]=-1
            if kind=='theta':representations[0]['drift']['theta']='1/3'
            if kind=='missing':representations.pop()
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.verify_source_conditions(representations,certificates,items,WORK)

    def test_strict_rational_types_operation_cap_and_zero_S(self):
        for text in ('2/4','01','+1','-0','1.0','1/0',True):
            with self.subTest(text=text),self.assertRaises(ValueError):CHECK._rational(text,WORK)
        with self.assertRaises(OverflowError):CHECK._rational('1',Meter(1))
        with self.assertRaises(ValueError):CHECK.divide({(1,):Q(1)}, {},WORK)
        catalogue,result=fixture();catalogue['candidates'][0]['normalizer']=[]
        with self.assertRaises(ValueError):CHECK.verify(catalogue,result,WORK)


def tearDownModule():
    print(f'SYNTHETIC_WORK module=test_check_core_frame_bounds operations={WORK.operations} elapsed_seconds={time.monotonic()-START:.6f}')


if __name__=='__main__':
    resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024))
    if len(sys.argv)>1:suite=unittest.defaultTestLoader.loadTestsFromNames(['__main__.FrameBoundCheckerTests.'+n for n in sys.argv[1:]])
    else:suite=unittest.defaultTestLoader.loadTestsFromTestCase(FrameBoundCheckerTests)
    outcome=unittest.TextTestRunner(verbosity=2).run(suite)
    run=dict(returncode=0 if outcome.wasSuccessful() else 1,operations=WORK.operations,tests=outcome.testsRun,
        elapsed_seconds=time.monotonic()-START,failures=len(outcome.failures),errors=len(outcome.errors),
        failure_details=[dict(test=str(t),traceback=trace) for t,trace in outcome.failures+outcome.errors])
    try:
        with open('core_frame_bounds_checker_development.json') as source:previous=json.load(source)
    except FileNotFoundError:previous=dict(runs=[])
    runs=previous['runs']+[run]
    receipt=dict(schema='core-frame-bounds-checker-development-v1',runs=runs,operations=sum(r['operations'] for r in runs),
        success=outcome.wasSuccessful(),peak_live_cells=WORK.peak_live_cells,maximum_rational_bits=WORK.maximum_rational_bits,
        memory_limit_bytes=512*1024*1024,operation_limit=50000000,elapsed_limit_seconds=180,
        no_source_observations=True,edits_stopped=outcome.wasSuccessful())
    with open('core_frame_bounds_checker_development.json','w') as output:json.dump(receipt,output,indent=2);output.write('\n')
    raise SystemExit(run['returncode'])
