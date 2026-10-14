"""Independent paper-cost fixtures, generic rational identities and rejection tests."""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb, prod
from collections import Counter
import json
import resource
import sys
import time
import unittest

import check_core_prefix_proof_search as CHECK
from potential_candidate_language import Meter

START = time.monotonic()
WORK = Meter(50000000,deadline=START+180,max_cells=1000000)


def fixture():
    # Complete four-mode polynomial at alpha=gamma=1/2, multiplied by hand.
    modes = [('B','beta',2,0,'1/3',[(0,0,1),(1,0,2)]),
             ('U','-beta',1,1,'1/3',[(0,0,1),(0,1,1),(1,0,1)]),
             ('V','-beta',1,0,None,[(0,0,1),(1,0,1)]),
             ('power','-R_u',0,1,'1/3',[(0,0,1),(0,1,1)])]
    row = dict(id=12,alpha='1/2',gamma='1/2',component_count=9,cases=[])
    nodes=[]; cache={}
    # Paper critical costs, including actual shifted inverse tail.
    atomic={'A':(2,Q(1,4),0,'A_critical'), 'B':(7,Q(0),0,'B_critical'),
            'C':(2,Q(0),0,'C_critical'), 'E':(6,Q(1,2),1,'E_critical'),
            'K':(6,Q(1,6),0,'K_critical'), 'O':(2,Q(1,2),0,'O_critical'),
            'R':(2,Q(1,2),1,'R_critical'), 'S':(84,Q(-1,12),0,'S_critical_tail')}
    def node(expr,norm,rule,children=(),value=None,atom_rule=None):
        key=(expr,norm)
        if key in cache:return cache[key]
        if value is None:
            c=prod(Q(nodes[i]['constant']) for i in children)
            e=sum((Q(nodes[i]['power']) for i in children),Q(0))+Q(rule=='critical_to_prefix',2)
            h=sum(nodes[i]['log_degree'] for i in children)
        else:c,e,h=value
        data=dict(id=len(nodes),expression=list(expr),norm=norm,rule=rule,children=list(children),
                  constant=str(c),power=str(e),log_degree=h,proof_size=1+sum(nodes[i]['proof_size'] for i in children))
        if atom_rule is not None:data['atom_rule']=atom_rule
        cache[key]=len(nodes);nodes.append(data);return data['id']
    def critical(expr):
        if (expr,'critical') in cache:return cache[expr,'critical']
        if len(expr)==1:
            c,e,h,r=atomic[expr[0]]
            return node(expr,'critical','atom',value=(c,e,h),atom_rule=r)
        return node(expr,'critical','critical_convolution',(critical(expr[:1]),critical(expr[1:])))
    def prefix(expr):
        if expr==('A',):
            m=node(expr,'mass','atom',value=(1,Q(1,2),0),atom_rule='A_mass')
            return node(expr,'prefix','mass_to_prefix',(m,))
        if expr==('A','E'):
            m=node(('A',),'mass','atom',value=(1,Q(1,2),0),atom_rule='A_mass')
            p=node(('E',),'prefix','atom',value=(2,Q(1,2),0),atom_rule='E_prefix')
            return node(expr,'prefix','prefix_convolution',(m,p))
        return node(expr,'prefix','critical_to_prefix',(critical(expr),))
    terms=[]
    for name,scalar,p,q,shift,polynomial in modes:
        mode=dict(name=name,coefficient=scalar,p=p,q=q,positive_shift=shift)
        row['cases'].append(dict(mode=mode,program=dict(alpha='1/2',gamma='1/2',p=p,q=q,
            terms=[dict(a=a,b=b,coefficient=str(c)) for a,b,c in polynomial])))
        for a,b,c in polynomial:
            alternatives=[]
            for depth in range(a+1):
                pieces=[]
                for j in range(depth+1):
                    expr=tuple(sorted(['A']*p+['B']*q+['K']*int(shift is not None)+['S']*b+
                                      ['R']*(a-depth)+['E']*j+['C','O']*(depth-j)))
                    coefficient=c*comb(depth,j)*(-1)**(depth-j)
                    proof=prefix(expr);bound=nodes[proof]
                    constant=4*(Q(bound['constant'])*coefficient*(5 if scalar=='-R_u' else Q(9,2)))**2
                    power=2*Q(bound['power'])-1;degree=2*bound['log_degree']
                    # This half-cutoff fixture pays precisely the A source term.
                    uniform=str(constant) if power==0 and degree==0 else None
                    pieces.append(dict(coefficient=str(coefficient),expression=list(expr),prefix_proof=proof,
                                       energy=dict(constant=str(constant),power=str(power),log_degree=degree,uniform_constant=uniform)))
                alternatives.append(dict(depth=depth,pieces=pieces))
            terms.append(dict(key=dict(mode=name,a=a,b=b),source_scalar=scalar,inverse_coefficient=str(c),
                              alternatives=alternatives,selected_depth=0))
    applications=0
    for n in nodes:
        counts=Counter(n['expression']);oriented=prod(v+1 for v in counts.values())-2
        symmetric=int(bool(counts) and all(v%2==0 for v in counts.values()))
        splits=(oriented+symmetric)//2 if counts else 0
        atoms=int(len(n['expression'])==1 or not n['expression'])
        if n['norm']=='prefix' and n['expression'] not in ([],['C'],['E']):atoms=0
        if n['expression']==['S'] and n['norm']=='critical':atoms=2
        applications+=atoms+2*int(n['norm']=='prefix')+(2*splits-symmetric if n['norm']=='prefix' else splits)
    result=dict(schema='core-prefix-proof-search-v1',geometry_id=12,alpha='1/2',gamma='1/2',nodes=nodes,terms=terms,
        statistics=dict(proof_nodes=len(nodes),rule_applications=applications,original_terms=9,alternatives=12,
                        selected_centerings=0,selected_pieces=9,uniformly_paid_pieces=1),
        whole_signed_bound_proved=False,RH_proved=False)
    return row,result


def convolve(f,g):
    WORK.charge(len(f)*len(g))
    return [Q(0)]+[sum((f[d]*g[n//d] for d in range(1,n+1) if n%d==0),Q(0)) for n in range(1,len(f))]


def prefix_norm(f):
    values=[];running=Q(0)
    for v in f[1:]:running+=v;values.append(abs(running));WORK.charge(2)
    return max(values,default=Q(0))


class IndependentPrefixCheckerTests(unittest.TestCase):
    def test_hand_derived_complete_source_certificate(self):
        row,result=fixture()
        verified=CHECK.verify_search(row,result,WORK)
        self.assertTrue(verified['exhaustive_prefix_optima_verified'])
        self.assertEqual(verified['expanded_pieces'],15)

    def test_missing_unit_source_mode_or_drift_rejected(self):
        row,result=fixture()
        bad=deepcopy(result);bad['terms'].pop(0)
        with self.assertRaises(ValueError):CHECK.verify_search(row,bad,WORK)
        bad=deepcopy(row);bad['cases'].pop()
        with self.assertRaises(ValueError):CHECK.verify_search(bad,result,WORK)
        bad=deepcopy(row);bad['cases'][0]['program']['terms'].pop(0)
        with self.assertRaises(ValueError):CHECK.verify_search(bad,result,WORK)
        bad=deepcopy(result);bad['terms'][1]['alternatives'][1]['pieces'].pop(0)
        with self.assertRaises(ValueError):CHECK.verify_search(row,bad,WORK)

    def test_false_centered_support_and_signed_coefficient_rejected(self):
        row,result=fixture()
        for mutate in ('factor','coefficient','scalar','depth','paid'):
            bad=deepcopy(result);piece=bad['terms'][1]['alternatives'][1]['pieces'][0]
            if mutate=='factor':piece['expression'].remove('O')
            if mutate=='coefficient':piece['coefficient']='2'
            if mutate=='scalar':bad['terms'][1]['source_scalar']='beta2'
            if mutate=='depth':bad['terms'][1]['alternatives'].pop()
            if mutate=='paid':piece['energy']['uniform_constant']='1'
            with self.subTest(mutate=mutate),self.assertRaises(ValueError):CHECK.verify_search(row,bad,WORK)

    def test_proof_rules_do_not_allow_critical_companion_or_E_gap(self):
        _,result=fixture()
        for field,value in [('constant','1'),('power','0'),('proof_size',2),('atom_rule','E_support_gap')]:
            bad=deepcopy(result['nodes']);target=next(n for n in bad if n.get('atom_rule')=='E_critical')
            target[field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):CHECK.verify_nodes(bad,Q(1,2),Q(1,2),WORK)
        bad=deepcopy(result['nodes']);target=next(n for n in bad if n['rule']=='critical_convolution')
        target['rule']='prefix_convolution';target['norm']='prefix'
        with self.assertRaises(ValueError):CHECK.verify_nodes(bad,Q(1,2),Q(1,2),WORK)
        bad=deepcopy(result['nodes']);bad[0]['children']=[bad[-1]['id']]
        with self.assertRaises(ValueError):CHECK.verify_nodes(bad,Q(1,2),Q(1,2),WORK)

    def test_unpaid_valid_but_suboptimal_proof_rejected(self):
        row,result=fixture();bad=deepcopy(result)
        n=next(n for n in bad['nodes'] if n.get('atom_rule')=='S_critical_tail')
        n.update(constant='50',power='0',atom_rule='S_critical_direct')
        with self.assertRaises(ValueError):CHECK.verify_search(row,bad,WORK)

    def test_generic_signed_rational_prefix_convolution(self):
        # Hundreds of sequences, including cancellation and nonzero full unit.
        for seed in range(1,41):
            f=[Q(0)]+[Q(((seed*n)%11)-5,n%3+1) for n in range(1,17)]
            g=[Q(0)]+[Q(((seed+3*n)%13)-6,n%4+1) for n in range(1,17)]
            fg=convolve(f,g)
            mass_f=sum(map(abs,f));mass_g=sum(map(abs,g))
            self.assertLessEqual(prefix_norm(fg),prefix_norm(f)*mass_g)
            self.assertLessEqual(prefix_norm(fg),mass_f*prefix_norm(g))
            self.assertLessEqual(sum(map(abs,fg)),mass_f*mass_g)

    def test_fixed_U_floor_remainder_includes_d_greater_than_n(self):
        # Möbius inverse checked literally to avoid using an external producer.
        mu=[0,1,-1,-1,0,-1,1,-1,0,0,1,-1,0]
        H=12;U=10;one=[Q(0)]+[Q(1)]*H;delta=[Q(0),Q(1)]+[Q(0)]*(H-1)
        A=[Q(mu[n]) if 1<=n<=U else Q(0) for n in range(H+1)]
        self.assertEqual(convolve(one,list(map(Q,mu))),delta)
        R=[d-v for d,v in zip(delta,convolve(one,A))];c=sum((Q(mu[d],d) for d in range(1,U+1)),Q(0))
        E=[r+c*o for r,o in zip(R,one)]
        running=Q(0)
        for n in range(1,H+1):
            running+=E[n]
            remainder=1+sum((mu[d]*(Q(n,d)-n//d) for d in range(1,U+1)),Q(0))
            self.assertEqual(running,remainder)
        wrong=1+sum((mu[d]*(Q(1,d)-1//d) for d in range(1,2)),Q(0))
        self.assertNotEqual(E[1],wrong)
        self.assertNotEqual(E[1],0) # E cannot inherit R's support gap.

    def test_generic_all_binomial_drift_terms_recover(self):
        H=12;one=[Q(0)]+[Q(1)]*H;delta=[Q(0),Q(1)]+[Q(0)]*(H-1)
        R=[Q(0)]+[Q((n*7)%9-4,5) for n in range(1,H+1)];c=Q(-7,11)
        E=[r+c*o for r,o in zip(R,one)]
        def power(f,k):
            out=delta
            for _ in range(k):out=convolve(out,f)
            return out
        for a in range(5):
            for depth in range(a+1):
                total=[Q(0)]*(H+1)
                for j in range(depth+1):
                    term=convolve(power(R,a-depth),convolve(power(E,j),power(one,depth-j)))
                    factor=comb(depth,j)*(-c)**(depth-j)
                    total=[x+factor*y for x,y in zip(total,term)];WORK.charge(4*(H+1))
                self.assertEqual(total,power(R,a))

    def test_uniform_log_payment_and_boundary(self):
        self.assertIsNone(CHECK._uniform(Q(7),Q(0),1,WORK))
        self.assertEqual(CHECK._uniform(Q(7),Q(0),0,WORK),7)
        self.assertEqual(CHECK._uniform(Q(3),Q(-1,2),2,WORK),204)
        self.assertIsNone(CHECK._uniform(Q(1),Q(1,100),0,WORK))

    def test_partial_selection_and_retained_failures(self):
        def alt(k,powers):
            return dict(depth=k,pieces=[dict(energy=dict(power=str(e),log_degree=h,
                       uniform_constant='1' if e<0 or e==0 and h==0 else None)) for e,h in powers])
        options=[alt(0,[(Q(2),0)]),alt(1,[(Q(3),0),(Q(-1),0)]),alt(2,[(Q(1),0)]),alt(3,[(Q(1),0)])]
        self.assertEqual(CHECK.selection_depth(options,WORK),1) # More paid first.
        self.assertEqual(CHECK.selection_depth([alt(0,[(Q(0),1)]),alt(1,[(Q(0),0)])],WORK),1)
        self.assertEqual(CHECK.selection_depth([alt(0,[(Q(2),1)]),alt(1,[(Q(2),0)])],WORK),0)

    def test_reduction_abel_and_complete_partition(self):
        _,result=fixture()
        # Isolated synthetic reduction tests exercise two new paid pieces and
        # the complete Cauchy count, independent of the source proof fixture.
        result['terms'][0]['alternatives'][0]['pieces'][0]['energy']['uniform_constant']='2'
        result['terms'][2]['alternatives'][0]['pieces'][0]['energy']['uniform_constant']='3'
        parent=dict(parent_obligation_id='synthetic',source_geometry_ref=12,source_geometry=dict(alpha='1/2',gamma='1/2'),
            paid_component_reduction=dict(paid_components=[dict(mode='V',a=0,b=0)],whole_signed_bound_proved=False,
                older_fixed_recurrence_discharged=False,new_sufficient_goal=dict(p='3',status='open',same_finite_constant=True)))
        construction=dict(channels=[dict(eta='1/2',polynomial=['1','-2','3']),dict(eta='0',polynomial=['-2'])])
        paid=[];remaining=[];old=[]
        for term in result['terms']:
            ref=dict(source_key=term['key'],depth=0,piece=0);piece=term['alternatives'][0]['pieces'][0]
            if term['key']==dict(mode='V',a=0,b=0):old.append(ref)
            elif piece['energy']['uniform_constant'] is None:remaining.append(ref)
            else:paid.append(dict(ref,uniform_energy_constant=piece['energy']['uniform_constant']))
        reduction=dict(schema='core-prefix-proof-reduction-v1',parent_obligation_id='synthetic',geometry_id=12,
            channel_abel_constant='488',old_paid_excluded=old,newly_paid=paid,remaining_signed_pieces=remaining,
            combined_new_paid_constant='4880',exact_split='Z_old=P_new+Z_new; Z_new=sum(all remaining signed pieces)-e; e=f-g',
            recovery='S_old<=2*S_new+2*C_new; S_new<=2*S_old+2*C_new',transport_error_retained=True,
            all_remaining_crosses_retained=True,common_horizon='N=4X-1 for both parent and child',
            goal=dict(expression='S_new(X)<=C*(1+log2X)^p for every dyadicX>=1',p='3',same_finite_constant=True,status='open'),
            analyst_nominated_selected_formula=False,proof_rules_are_supplied=True,original_fixed_recurrence_discharged=False,
            whole_signed_bound_proved=False,RH_proved=False)
        self.assertEqual(CHECK.verify_reduction(parent,construction,result,reduction,WORK)['new_paid_pieces'],2)
        for field,value in [('transport_error_retained',False),('channel_abel_constant','196'),
                            ('combined_new_paid_constant','2440'),('old_paid_excluded',[]),('remaining_signed_pieces',[]),
                            ('whole_signed_bound_proved',True)]:
            bad=deepcopy(reduction);bad[field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):CHECK.verify_reduction(parent,construction,result,bad,WORK)

        bad_parent=deepcopy(parent);bad_parent['paid_component_reduction']['new_sufficient_goal']['p']='-1'
        bad=deepcopy(reduction);bad['goal']['p']='-1'
        with self.assertRaises(ValueError):CHECK.verify_reduction(bad_parent,construction,result,bad,WORK)

    def test_parser_strict_types_and_operation_cap(self):
        for value in ['2/4','+1','-0','1.0','01','1/0',True]:
            with self.subTest(value=value),self.assertRaises(ValueError):CHECK._rational(value,WORK)
        with self.assertRaises(OverflowError):CHECK._rational('1',Meter(1))
        with self.assertRaises(OverflowError):CHECK._rational('256',Meter(100,max_bits=8))


def tearDownModule():
    print(f'SYNTHETIC_WORK module=test_check_core_prefix_proof_search operations={WORK.operations} elapsed_seconds={time.monotonic()-START:.6f}')


if __name__=='__main__':
    resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024))
    if len(sys.argv)>1:
        suite=unittest.defaultTestLoader.loadTestsFromNames(['__main__.IndependentPrefixCheckerTests.'+name for name in sys.argv[1:]])
    else:
        suite=unittest.defaultTestLoader.loadTestsFromTestCase(IndependentPrefixCheckerTests)
    outcome=unittest.TextTestRunner(verbosity=2).run(suite)
    receipt=dict(schema='core-prefix-proof-checker-development-v1',tests=outcome.testsRun,success=outcome.wasSuccessful(),
        failures=len(outcome.failures),errors=len(outcome.errors),elapsed_seconds=time.monotonic()-START,
        charged_operations=WORK.operations,peak_live_cells=WORK.peak_live_cells,maximum_rational_bits=WORK.maximum_rational_bits,
        memory_limit_bytes=512*1024*1024,operations_limit=50000000,elapsed_limit_seconds=180,
        no_numerical_source_or_study_read=True,edits_stopped=outcome.wasSuccessful(),operations=WORK.operations,
        runs=[dict(returncode=0 if outcome.wasSuccessful() else 1,operations=WORK.operations,
                   tests=outcome.testsRun,elapsed_seconds=time.monotonic()-START)])
    try:
        with open('core_prefix_proof_checker_development.json') as previous_input:previous=json.load(previous_input)
    except FileNotFoundError:
        previous=None
    if previous is not None:
        receipt['runs']=previous['runs']+receipt['runs']
        receipt['operations']=sum(run['operations'] for run in receipt['runs'])
        receipt['initial_failures_retained']=dict(failures=previous['failures'],errors=previous['errors'],
            descriptions=['Expected15 expanded pieces, initially asserted18','Atom-size tamper initially assigned correct size1'])
    with open('core_prefix_proof_checker_development.json','w') as output:json.dump(receipt,output,indent=2);output.write('\n')
    raise SystemExit(0 if outcome.wasSuccessful() else 1)
