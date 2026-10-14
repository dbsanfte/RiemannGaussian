"""Synthetic certificate challenges; no arithmetic archive or source measurements."""
import copy
import math
import time
import unittest
from fractions import Fraction as Q
from unittest.mock import patch

import check_core_complete_convolution_search as C
import core_complete_convolution_search as P
from prime_bank_candidates import Meter

STARTED=time.monotonic()
METER=Meter(100000000,180)


def convolutions(a,b):
    n=len(a)-1;out=[Q(0)]*(n+1)
    for d in range(1,n+1):
        for k in range(1,n//d+1):
            out[d*k]+=a[d]*b[k];METER.charge()
    return out


def expand(rows,states):
    n=len(next(iter(states.values())))-1
    out=[Q(0)]*(n+1)
    for row in rows:
        value=[Q(0),Q(1)]+[Q(0)]*(n-1)
        for name in row['key']:value=convolutions(value,states[name])
        out=[x+Q(row['value'])*y for x,y in zip(out,value)]
    return out


def cutoff(n,a):
    a=Q(a)
    return max(k for k in range(n+1) if k**a.denominator<=n**a.numerator)


class IndependentCompleteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.library=P.prefix_library('mobius','1/24',METER)
        cls.generic=P.prefix_library('bounded','1/24',METER)
        cls.geometry=P.complete_geometry('1/6','5/6',cls.library,METER)
        cls.old=P.OLD.hyperbola_synthesize('1/6','5/6',METER)
        cls.normalization=P.normalize(cls.old,METER)
        cls.transfer=P.transfer_search(2,'2/3','1/24',METER)

    def reject(self,call):
        with self.assertRaises((ValueError,TypeError,KeyError,OverflowError)):call()

    def test_pair_cube_unconditional_constants_and_generic_logs(self):
        for lib in (self.library,self.generic):
            self.assertTrue(C.verify_prefix_library(lib,METER)['verified'])
        self.assertEqual(self.library['levels'][1]['bound'],C.collect([
            C.term(12,1,Q(1,2),lx=1),C.term(4,2)]))
        self.assertEqual(self.library['levels'][2]['bound'],C.collect([
            C.term(270,1,Q(2,3),lx=2),C.term(36,2,Q(1,3),lx=1),C.term(8,3)]))
        self.assertEqual([(r['U_power'],r['X_power']) for r in self.library['levels'][2]['bound']],
                         [(r['U_power'],r['X_power']) for r in self.generic['levels'][2]['bound']])
        self.assertTrue(any(r['logU_degree'] for r in self.generic['levels'][2]['bound']))

    def test_lower_power_dependencies_are_acyclic_and_complete(self):
        four=P.prefix_library('mobius','1/24',METER,maximum=4)
        self.assertTrue(C.verify_prefix_library(four,METER)['verified'])
        bad=copy.deepcopy(self.library)
        level=bad['levels'][2];candidate=level['candidates'][level['selected']]
        candidate['priced_terms'][0]['pricing']['premise_power']=3
        self.reject(lambda:C.verify_prefix_library(bad,METER))

    def test_large_cutoff_scale_changes_the_selected_prefix_argument(self):
        wide=P.prefix_library('mobius','3/4',METER)
        self.assertTrue(C.verify_prefix_library(wide,METER)['verified'])
        level=wide['levels'][2]
        self.assertEqual(level['candidates'][level['selected']]['rule'],'coefficient_mass')
        bad=copy.deepcopy(wide);bad['levels'][2]['selected']=self.library['levels'][2]['selected']
        self.reject(lambda:C.verify_prefix_library(bad,METER))
        bad=copy.deepcopy(self.library);bad['levels'][1]['candidates'].pop()
        self.reject(lambda:C.verify_prefix_library(bad,METER))

    def test_certificate_identity_holds_for_arbitrary_signed_sequences_all_prefixes(self):
        for level in self.library['levels'][1:]:
            chosen=level['candidates'][level['selected']]
            for n in (1,8,19):
                f=[Q(0)]+[Q((-1)**k*(k%5+1),k%3+1) for k in range(1,n+1)]
                t=cutoff(n,chosen['alpha'])
                states={'E':f,'T':f[:t+1]+[Q(0)]*(n-t)}
                columns=chosen['basis']+[chosen['ideal']]
                reconstructed=[Q(0)]*(n+1)
                for entry in chosen['certificate']['solution']:
                    value=expand(columns[entry['column']],states)
                    reconstructed=[a+Q(entry['coefficient'])*b for a,b in zip(reconstructed,value)]
                self.assertEqual(reconstructed,expand(chosen['source'],states))
                self.assertEqual(expand(chosen['ideal'],states),[0]*(n+1))

    def test_weighted_lift_keeps_critical_logs_and_rejects_wrong_decay(self):
        self.assertEqual(C.finite_lift([C.term(5,0,1)],['1/3','2/3'],'mobius'),[C.term(45,0,1,lx=4)])
        self.assertEqual(C.finite_lift([C.term(1,0,Q(1,2))],['1/2'],'bounded'),
                         [C.term(6,0,Q(3,4),lu=1,lx=1)])
        for power in ('-1/3','4/3'):
            self.reject(lambda:C.finite_lift([C.term(x=power)],['1/2'],'mobius'))
        bad=copy.deepcopy(self.library)
        trial=bad['levels'][1]['candidates'][-1]
        trial['bound'][0]['logX_degree']=0
        self.reject(lambda:C.verify_prefix_library(bad,METER))

    def test_rectangle_uses_evaluated_prefix_not_only_the_horizon(self):
        cheap=C.monomial_price(('T',)*3,Q(1,3),Q(1,2),self.library,METER)
        costly=C.monomial_price(('R',)*3,Q(1,6),Q(5,6),self.library,METER)
        self.assertTrue(any(c['rule']=='complete_rectangle' for c in cheap['candidates']))
        self.assertFalse(any(c['rule']=='complete_rectangle' for c in costly['candidates']))
        self.reject(lambda:C.monomial_price(('E',)*3,Q(1,3),Q(1,2),self.library,METER))
        # At the earlier prefix x=3 the complete product mass is not its prefix.
        f=[Q(0),Q(1),Q(1),Q(1)];product=convolutions(f,f)
        self.assertNotEqual(sum(product),sum(f)**2)

    def test_affine_normalization_collects_unit_and_mean_before_specializing(self):
        self.assertTrue(C.verify_normalization(self.old,self.normalization,METER)['verified'])
        self.assertEqual(C.polynomial(self.normalization['normalized_join'],METER),{
            ('E','T','T'):Q(3),('R','R','R'):Q(1),('R','T','T'):Q(-3)})
        for n in (1,9,24):
            f=[Q(0)]+[Q((-1)**k*(1+k%3),2) for k in range(1,n+1)]
            t,r=cutoff(n,'1/6'),cutoff(n,'5/6')
            states=dict(E=f,T=f[:t+1]+[Q(0)]*(n-t),R=f[:r+1]+[Q(0)]*(n-r))
            self.assertEqual(expand(self.normalization['normalized_join'],states),
                             expand([{'key':['E']*3,'value':'1'}],states))
        bad=copy.deepcopy(self.normalization);bad['affine_join'].append({'key':['C'],'value':'1'})
        self.reject(lambda:C.verify_normalization(self.old,bad,METER))
        bad=copy.deepcopy(self.normalization);bad['normalized_remainder']=[]
        self.reject(lambda:C.verify_normalization(self.old,bad,METER))

    def test_every_finite_head_has_an_independent_cost(self):
        self.assertTrue(C.verify_geometry(self.geometry,self.library,METER)['verified'])
        names=[row[0]['key'] for row in self.geometry['basis']]
        self.assertIn(['R']*3,names)
        self.assertNotIn(['E']*3,names)
        rprice=self.geometry['monomial_prices'][names.index(['R']*3)]
        self.assertTrue(any(c.get('base')=='R' and c['premise_power']==3 for c in rprice['candidates']))
        bad=copy.deepcopy(self.geometry)
        bad['monomial_prices'][names.index(['R']*3)]['bound']=[]
        self.reject(lambda:C.verify_geometry(bad,self.library,METER))

    def test_primal_dual_must_cover_all_affordable_columns(self):
        infeasible=next(t for t in self.geometry['trials'] if t['certificate']['status']=='infeasible')
        bad=copy.deepcopy(self.geometry)
        index=self.geometry['trials'].index(infeasible)
        bad['trials'][index]['certificate']['dual'][0]['value']='0'
        self.reject(lambda:C.verify_geometry(bad,self.library,METER))
        bad=copy.deepcopy(self.geometry);bad['trials'][-1]['allowed']=[]
        self.reject(lambda:C.verify_geometry(bad,self.library,METER))
        bad=copy.deepcopy(self.geometry)
        chosen=bad['trials'][bad['selected']]
        chosen['certificate']['solution'][0]['coefficient']='99'
        self.reject(lambda:C.verify_geometry(bad,self.library,METER))

    def test_outer_source_head_and_every_energy_cross_are_retained(self):
        bound=C.outer_lift(self.library['levels'][2]['bound'],2,3,'mobius')
        self.assertIn(C.term(8,1),bound)
        self.assertEqual(C.cost(C.squared(bound),Q(1,24))[0],Q(17,36))
        mixed=C.squared([C.term(2,1,Q(1,2)),C.term(3,2,0)])
        self.assertIn(C.term(12,3,Q(-1,2)),mixed)
        for p,m in ((0,3),(2,2),(3,2)):
            self.reject(lambda:C.outer_lift(bound,p,m,'mobius'))

    def test_centered_transfer_constants_floor_energy_and_shortest_cutoff(self):
        self.assertTrue(C.verify_transfer(self.transfer,METER)['verified'])
        self.assertEqual((self.transfer['C1'],self.transfer['C2']),('26244','27216'))
        chosen=self.transfer['trials'][self.transfer['selected']]
        self.assertEqual((chosen['alpha'],chosen['beta'],chosen['base']),('1/4','3/4','T'))
        self.assertEqual([r['N_power'] for r in chosen['normalized_error_energy']],['-7/36','-3/4'])
        old=next(t for t in self.transfer['trials'] if (t['alpha'],t['beta'],t['base'])==('1/6','5/6','T'))
        self.assertEqual([r['N_power'] for r in old['normalized_error_energy']],['-5/12','-3/4'])
        for field in ('full_finite_cube_bound_proved','global_fixed_U_Mellin_bound_proved'):
            bad=copy.deepcopy(self.transfer);bad[field]=True
            self.reject(lambda:C.verify_transfer(bad,METER))
        bad=copy.deepcopy(self.transfer)
        bad['trials'][bad['selected']]['normalized_error_energy'][0]['constant']=str(4*26244**2)
        self.reject(lambda:C.verify_transfer(bad,METER))

    def test_nonzero_analytic_defect_is_not_inferred_from_local_identity(self):
        # All support <=8 coefficients agree, but the global ordinary moment at
        # theta=1/2 sees a tail at9. Perfect-square indices keep this test exact.
        E,R,S=Q(1)+Q(1,2)+Q(1,3),Q(1)+Q(1,2),Q(1)
        defect=E**3-R**3-3*S*S*(E-R)
        self.assertEqual(defect,(E-R)*(E*E+E*R+R*R-3*S*S))
        self.assertNotEqual(defect,0)
        bad=copy.deepcopy(self.transfer)
        bad['trials'][bad['selected']]['moment_defect']='0'
        self.reject(lambda:C.verify_transfer(bad,METER))

    def test_centered_small_arguments_and_all_divisors_must_survive(self):
        # h supported at4 and J at9, theta=1/2; n=1 gives n/d<1.
        # Raw prefixes vanish but centered contributions do not.
        n,theta,h,J=Q(1),Q(1,2),Q(2),Q(1,3)
        centered_hJ=-h*Q(1,2)*J*n/theta
        all_divisors=h*(-J*Q(1,2)/theta)
        self.assertEqual(centered_hJ,all_divisors)
        self.assertNotEqual(centered_hJ,0)
        bad=copy.deepcopy(self.transfer);bad['domain']='only x>=1, discard d>x'
        self.reject(lambda:C.verify_transfer(bad,METER))

    def test_generic_transfer_has_same_powers_and_explicit_log_losses(self):
        generic=P.transfer_search(2,'2/3','1/24',METER,profile='bounded')
        self.assertTrue(C.verify_transfer(generic,METER)['verified'])
        self.assertEqual(self.transfer['selected'],generic['selected'])
        chosen=generic['trials'][generic['selected']]
        actual=self.transfer['trials'][self.transfer['selected']]
        self.assertEqual([r['N_power'] for r in actual['normalized_error_energy']],
                         [r['N_power'] for r in chosen['normalized_error_energy']])
        self.assertEqual([r['log_degree'] for r in chosen['normalized_error_energy']],[8,4])
        self.assertEqual(generic['C2'],'33048')
        bad=copy.deepcopy(generic);bad['trials'][bad['selected']]['normalized_error_energy'][1]['log_degree']=0
        self.reject(lambda:C.verify_transfer(bad,METER))

    def test_fractional_kernel_and_strict_payment_boundary(self):
        for theta in ('1/2','3/4'):
            changed=P.transfer_search(1,theta,'1/24',METER)
            self.assertTrue(C.verify_transfer(changed,METER)['verified'])
        # Solve tail exponent=0 at alpha1/4,beta3/4,p2,theta2/3.
        critical=P.transfer_search(2,'2/3','1/10',METER)
        self.assertTrue(C.verify_transfer(critical,METER)['verified'])
        row=next(t for t in critical['trials'] if (t['alpha'],t['beta'],t['base'])==('1/4','3/4','T'))
        self.assertEqual(row['normalized_error_energy'][0]['N_power'],'0')
        self.assertFalse(row['subcritical_padding'])
        bad=copy.deepcopy(critical);bad['trials'][critical['trials'].index(row)]['subcritical_padding']=True
        self.reject(lambda:C.verify_transfer(bad,METER))
        for theta in ('0','1','-1/4'):
            bad=copy.deepcopy(self.transfer);bad['theta']=theta
            self.reject(lambda:C.verify_transfer(bad,METER))

    def test_source_binding_is_tied_to_current_prior_binding(self):
        binding={'target_id':'synthetic','unit_present':True}
        parent={'schema':'core-convolution-argument-feedback-v1','convolution_argument_search':{'binding':binding}}
        with patch.object(C.PRIOR,'source_binding',return_value=binding) as binder:
            self.assertEqual(C.source_binding(parent,METER),binding)
            self.assertEqual(binder.call_args.args[0]['schema'],'core-bound-argument-feedback-v1')
            bad=copy.deepcopy(parent);bad['convolution_argument_search']['binding']['unit_present']=False
            self.reject(lambda:C.source_binding(bad,METER))

    def test_complete_wrapper_preserves_source_tasks_and_never_promotes_core(self):
        binding={'target_id':'synthetic-current','complete_source':True}
        old=[P.OLD.hyperbola_synthesize(a,b,METER) for a,b in C.PRIOR.geometry_grid()]
        parent=dict(schema='core-convolution-argument-feedback-v1',
            convolution_argument_search=dict(binding=binding,geometries=old),
            cutoff_work_targets=[dict(p=2,m=3,theta='2/3',sigma='9/20',
                original_low_obligation=dict(parameters=dict(alpha='1/24'),signed_crosses='ALL'))],
            next_search_tasks=[dict(priority=0,search_kind='full_signed_core',status='open'),
                               dict(priority=1,search_kind='old_unresolved_head',status='open')],
            original_source=dict(unit='delta',transport='retained',drifts=['all']),
            source_bindings=[dict(channel=i,status='open') for i in range(144)],RH_proved=False)
        with patch.object(P,'source_binding',return_value=binding),patch.object(C,'source_binding',return_value=binding):
            result=P.search(parent,METER);out=P.feedback(parent,result,'synthetic-proof.json')
            self.assertTrue(C.verify_feedback(parent,result,out,'synthetic-proof.json',METER)['verified'])
            self.assertFalse(result['full_component_bound_proved'])
            # Feedback verification includes the complete proof audit; keep
            # mutation failures early by replacing that audit with its receipt.
            with patch.object(C,'verify_search',return_value={'verified':True}):
                for field in ('source_bindings','original_source'):
                    bad=copy.deepcopy(out);bad.pop(field)
                    self.reject(lambda:C.verify_feedback(parent,result,bad,'synthetic-proof.json',METER))
                bad=copy.deepcopy(out);bad['next_search_tasks'][1]['status']='proved'
                self.reject(lambda:C.verify_feedback(parent,result,bad,'synthetic-proof.json',METER))

    def test_charge_only_meter_and_resource_guard(self):
        meter=Meter(1000000,60)
        self.assertFalse(hasattr(meter,'number'))
        self.assertTrue(C.verify_prefix_library(self.library,meter)['verified'])
        METER.charge(meter.operations)
        self.reject(lambda:C.number(str(1<<5000),METER))
        with self.assertRaises(OverflowError):C.verify_prefix_library(self.library,Meter(0,60))


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_complete_convolution_search operations='+
          str(METER.operations)+' elapsed_seconds='+str(time.monotonic()-STARTED))


if __name__=='__main__':unittest.main()
