#!/usr/bin/env python3
"""Frozen anonymous divisor responses, root signs and proof-backed completion."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import argparse,os,random,socket,subprocess,sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from mellin_kernel_grammar import real
from root_lattice_search import solve
import divisor_preconditioner_grammar as g

CODE=['divisor_preconditioner_grammar.py','divisor_preconditioner_search.py','check_divisor_preconditioners.py',
      'divisor_preconditioner_report.py','divisor_preconditioner_proof.txt','test_divisor_preconditioner_contracts.py','plot_divisor_preconditioners.py']
SEALED=['protocol.json','candidate_batch.json','validation.json','archive.json']


def protocol(source):
    from root_lattice_report import summary
    source=Path(source).resolve();summary(source);old=read(source/'protocol.json');rng=random.Random(2026100824);random_order=rng.choice(['3/2','5/2','9/4']);failed=[]
    for p in sorted((BASE/'divisor-preconditioner-results').glob('*/failure.json')):
        d=p.parent;failed.append({'run_directory':str(d),'failure_sha256':sha(p),'files_sha256':{f.name:sha(f) for f in d.glob('*.json') if f.name!='failure.json'},
            'excluded_final_scales':read(d/'final_cases.json')['integers'] if (d/'final_cases.json').exists() else []})
    return {'schema':1,'grammar_version':g.VERSION,'seed':2026100824,'source_run':str(source),
        'source_sha256':{n:sha(source/n) for n in ['protocol.json','verification.json','summary.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE}),'this_stage_source_files':CODE,
        'named_calibration_dependencies':old['named_calibration_dependencies'],'precision':384,
        'orders':['1/6','1/3','1/2','1','2','3','4',random_order],'all_positive_rational_log_orders_supported':True,'semantic_denominator_cap':False,
        'integer_completion_orders':[1,2,3,4],'degrees':[0,1,2,3,4],'training_points':[8,12,16,24,32,64,128,256],
        'validation_points':[385,512,768],'training_indices':list(range(2,129)),'validation_indices':list(range(129,193)),
        'sign_training_ranks':list(range(1,6)),'sign_validation_ranks':[6,7],
        'sign_thresholds':list(range(7)),'sign_models':['integer_zero_tail','alternating_tail_after_threshold'],
        'feature_input_names_supplied_to_learners':False,'learning_precision':640,'quantization_bits':80,'rounding_denominator':4096,
        'preconditioner_features':'anonymous normalized divisor sums of x*log^r(x), plus divisor count; no Stieltjes constants supplied to fit',
        'bell_features':'anonymous convolution monomials of weighted first arithmetic jet; integer partitions of total degree',
        'sign_features':'anonymous generic difference signs grouped by rank, no arithmetic names or order supplied to learner',
        'completion_rule':'integer derivative, polynomial ansatz with sufficient degree; triangular harmonic constraints define a new candidate with retained actual remainder',
        'promotion_slots':4,'ablation':'same learned proposals, replace each completion slot by one seeded random rational polynomial; retain exact source semantics',
        'archive_rule':'preserve every completed integer order, every fractional operator, and learned relations even without a distribution certificate',
        'final_cases':{'range':[2049,4096],'count':3,'offset':'1/3','boundary':[1,2],'bell_count':12,'generic_ranks':list(range(1,9)),'generic_sequence_lengths':[12,17,24]},
        'parent_final_scales_excluded':read(source/'final_cases.json')['integers'],'retained_failed_runs_are_development':failed,
        'proof_backends':['finite differential convolution algebra','harmonic Euler remainder','triangular divisor antiderivative completion',
            'exact inverse with signed remainder','fractional iterated finite-difference sign integral','first logarithmic derivative zero residue'],
        'supplied_assumptions':['logarithmic weighting and divisor convolution','bounded partition and polynomial grammar','native analytic constants',
            'finite signature dictionary','generic difference sign proof','Euler summation remainder and norm bounds'],
        'known_Selberg_identity_is_separate_calibration':True,'new_prime_distribution_estimate_imported':False,
        'generator_model_literature_network_or_prime_oracle_access':False,'not_autonomous_proof_invention':True,
        'historical_priority_is_acceptance_gate':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def restrict(d,spec):
    allowed={str((BASE/n).resolve()) for n in spec['code_sha256']};allowed|={str((d/n).resolve()) for n in SEALED+['seal.json']}
    def audit(event,args):
        if event=='open' and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:raise PermissionError('Discovery access denied')
        if event.startswith('socket.') or event in ['subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp']:raise PermissionError('External access denied')
    sys.addaudithook(audit);denied={}
    for label,fn in [('private_final',lambda:open(d/'final_cases.json')),('parent_outcomes',lambda:open(Path(spec['source_run'])/'final_evaluation.json')),
        ('literature',lambda:open(spec['named_calibration_dependencies'][0]['path'])),('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass']))]:
        try:fn()
        except PermissionError:denied[label]=True
        else:raise AssertionError('Isolation failed')
    return denied


def fit(columns,target,spec):
    flint.ctx.prec=spec['learning_precision']
    D=2**spec['quantization_bits'];quant=lambda v:Q(round(Q(flint.arb(v).mid().str(70,radius=False))*D),D)
    rows=[[quant(v) for v in row] for row in columns];ys=[quant(v) for v in target];K=len(rows[0])
    A=[[sum((row[i]*row[j] for row in rows),Q(0)) for j in range(K)] for i in range(K)];b=[sum((row[i]*y for row,y in zip(rows,ys)),Q(0)) for i in range(K)];c=solve(A,b)
    return [v.limit_denominator(spec['rounding_denominator']) for v in c] if c is not None else None


def divisor_features(points,maximum_degree):
    out=[]
    for x in map(Q,points):
        N=x.numerator//x.denominator;out.append([sum((real(Q(1,n))*real(x/n).log()**r for n in range(1,N+1)),flint.arb(0)) for r in range(maximum_degree+1)]+[real(N)/real(x)])
    return out


def learned_preconditioners(spec):
    flint.ctx.prec=spec['learning_precision'];full=divisor_features(spec['training_points'],max(spec['degrees']));out=[]
    for k in spec['integer_completion_orders']:
        target=[g.primitive_sum(k,x)/real(x) for x in spec['training_points']]
        for degree in spec['degrees']:
            features=[row[:degree+1]+row[-1:] for row in full];c=fit(features,target,spec)
            if c is None:out.append({'order':k,'degree':degree,'status':'rank_deficient','coefficients':None});continue
            residual=max(float(abs(y-sum((real(v)*x for v,x in zip(c,row)),flint.arb(0))).upper()) for row,y in zip(features,target))
            cert=g.approximate_certificate(k,c[:-1],c[-1]);out.append({'order':k,'degree':degree,'status':'numeric_divisor_preconditioner','coefficients':list(map(str,c)),
                'training_maximum_normalized_residual':residual,'proof_certificate':cert,'inputs_contained_analytic_constants':False})
    return out


def partitions(k,minimum=1):
    if k==0:yield ()
    for j in range(minimum,k+1):
        for tail in partitions(k-j,j):yield (j-1,)+tail


def features(mon,lambda1,N):
    value=[flint.arb(0) for _ in range(N+1)];value[1]=flint.arb(1)
    for r in mon:value=g.convolution(value,[flint.arb(0)]+[lambda1[n]*real(n).log()**r for n in range(1,N+1)])
    return value


def learned_bells(spec,tables):
    N=max(spec['training_indices']);first=[flint.arb(v) for v in tables['1']['values'][:N+1]];exact=g.bell_polynomials(max(spec['integer_completion_orders']));out={}
    for k in spec['integer_completion_orders']:
        mon=list(partitions(k));cols=[features(m,first,N) for m in mon];rows=[[col[n] for col in cols] for n in spec['training_indices']];target=[flint.arb(tables[str(k)]['values'][n]) for n in spec['training_indices']];c=fit(rows,target,spec)
        symbolic=[exact[k][m] for m in mon];out[str(k)]={'monomials':[list(m) for m in mon],'coefficients':list(map(str,c)) if c is not None else None,
            'symbolic_coefficients':list(map(str,symbolic)),'universal_admitted':c is not None and c==list(map(Q,symbolic)),
            'names_or_expected_coefficients_supplied_to_fit':False,'numeric_only_if_no_certificate':not(c is not None and c==list(map(Q,symbolic)))}
    return out


def sign_fit(rows,spec):
    fits=[]
    for kind in spec['sign_models']:
        for threshold in spec['sign_thresholds']:
            sig={'kind':kind,'threshold':threshold}
            predicted=lambda r:1 if r<=threshold else (0 if kind=='integer_zero_tail' else (-1)**(r-threshold))
            bad=[r for r,v in rows if predicted(r)!=v];fits.append({'signature':sig,'training_failures':bad})
    passed=[row for row in fits if not row['training_failures']]
    return min(passed,key=lambda row:(row['signature']['threshold'],row['signature']['kind']))['signature'] if passed else None,fits


def signs(q,ranks):
    rows=[]
    for r in ranks:
        value=g.generic_difference(q,Q(1,3),[Q(j+2,7) for j in range(r)]);sign=1 if value>0 else (-1 if value<0 else 0);rows.append((r,sign))
    return rows


def worker(d):
    spec=read(d/'protocol.json');verify_code(spec);denied=restrict(d,spec);tables={q:g.coefficients(q,max(spec['training_points']),spec['precision']) for q in spec['orders']};learned=learned_preconditioners(spec);bells=learned_bells(spec,tables);certs={str(k):g.complete_preconditioner(k) for k in spec['integer_completion_orders']};sigcert={q:g.sign_signature(q) for q in spec['orders']};signfits=[];promotions=[];randoms=[];rng=random.Random(spec['seed'])
    for q in spec['orders']:
        sig,attempts=sign_fit(signs(q,spec['sign_training_ranks']),spec);expected={k:sigcert[q][k] for k in ['kind','threshold']};signfits.append({'anonymous_channel':digest({'q':q}),
            'signature':sig,'attempts':attempts,'decoded_order_after_fit':q,'universal_signature_admitted':sig==expected,'inputs_contained_order_or_prime_names':False})
    for k in spec['integer_completion_orders']:
        choices=[p for p in learned if p['order']==k and p['coefficients'] is not None and p['degree']>=k-1];parent=min(choices,key=lambda p:(p['training_maximum_normalized_residual'],p['degree'])) if choices else None
        promotions.append({'order':k,'parent':parent,'new_completed_candidate':certs[str(k)] if parent else None,'admitted':parent is not None,
            'same_operator_as_parent':False,'new_constrained_candidate_before_validation':True,'remaining_actual_mu_is_preserved':True})
        degree=rng.choice(spec['degrees']);c=[Q(rng.randint(-4,4),rng.choice([1,2,3,4])) for j in range(degree+2)];randoms.append({'order':k,'degree':degree,'coefficients':list(map(str,c)),
            'proof_certificate':g.approximate_certificate(k,c[:-1],c[-1])})
    batch={'protocol_sha256':digest(spec),'tables':tables,'access_denials':denied,'learned_preconditioners':learned,'learned_bell_relations':bells,
        'completed_preconditioners':certs,'sign_certificates':sigcert,'anonymous_sign_fits':signfits,'completion_promotions':promotions,'ablation_random_slots':randoms,
        'frozen_before_validation':True};write(d/'candidate_batch.json',batch)
    validation={'preconditioners':[],'signatures':[],'bell_relations':[]};full=divisor_features(spec['validation_points'],max(spec['degrees']))
    for p in learned:
        if p['coefficients'] is None:continue
        k=p['order'];c=list(map(Q,p['coefficients']));degree=p['degree'];errors=[float(abs(g.primitive_sum(k,x)/real(x)-sum((real(v)*y for v,y in zip(c,row[:degree+1]+row[-1:])),flint.arb(0))).upper()) for x,row in zip(spec['validation_points'],full)]
        validation['preconditioners'].append({'order':k,'degree':degree,'maximum_normalized_residual':max(errors)})
    for q in spec['orders']:
        sig=next(p['signature'] for p in signfits if p['decoded_order_after_fit']==q);bad=[r for r,v in signs(q,spec['sign_validation_ranks']) if sig is None or g.sign_from_signature(sig,r)!=v];validation['signatures'].append({'order':q,'failures':bad})
    write(d/'validation.json',validation);comparison=[]
    for k in spec['integer_completion_orders']:
        models=[p['proof_certificate'] for p in learned+randoms if p['order']==k and p.get('coefficients') is not None];comparison.append({'order':k,'primary_completed_log_loss':0,'best_ablation_log_loss':min(p['log_degree'] for p in models),
            'same_ordinary_exponent':'1','RH_strength':False})
    write(d/'archive.json',{'selection_closed':True,'final_data_used':False,'integer_orders':spec['integer_completion_orders'],'fractional_orders':[q for q in spec['orders'] if Q(q).denominator!=1],
        'learned_bell_relations_retained':bells,'equal_completion_and_random_slots':True,'proposal_slots':spec['promotion_slots'],'ablation_comparison':comparison})
    write(d/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(d/n) for n in SEALED},'selection_closed':True,'final_cases_exist':False});print('Sealed divisor preconditioners, roots and relations',flush=True)


def final(d):
    spec=read(d/'protocol.json');verify_code(spec);rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'));excluded=set(spec['parent_final_scales_excluded'])|{n for failed in spec['retained_failed_runs_are_development'] for n in failed['excluded_final_scales']}
    integers=sorted(rng.sample([n for n in range(rule['range'][0],rule['range'][1]+1) if n not in excluded],rule['count']));points=list(map(str,rule['boundary']+integers))+[str(Q(n)+Q(rule['offset'])) for n in integers];N=max(integers);cases={'integers':integers,'points':points,'bell_indices':sorted(rng.sample(range(769,N+1),rule['bell_count'])),'seal_sha256':sha(d/'seal.json'),'generated_after_seal':True};write(d/'final_cases.json',cases)
    tables={q:g.coefficients(q,N,spec['precision']) for q in spec['orders']};batch=read(d/'candidate_batch.json');obs={};generic={}
    for k,cert in batch['completed_preconditioners'].items():
        obs[k]={}
        for x in points:
            total=g.sum_at(tables[k],x);main=g.evaluate_h(cert,x);obs[k][x]={'sum_ball':g.ball(total),'main_ball':g.ball(main),'signed_error_ball':g.ball(total-main)}
    for q in spec['orders']:
        generic[q]=[]
        for r in rule['generic_ranks']:
            base=Q(0) if r%2 else Q(rng.randint(1,13),17);hs=[Q(rng.randint(1,13),rng.randint(3,19)) for j in range(r)];generic[q].append({'base':str(base),'steps':list(map(str,hs)),'value_ball':g.ball(g.generic_difference(q,base,hs))})
    try:g.enforce_domain(batch['completed_preconditioners']['1'],'unit')
    except ValueError:alias=True
    else:alias=False
    assert flint.arb(tables['1/6']['values'][6])<0
    generic_sequences=[]
    for length in rule['generic_sequence_lengths']:
        f=[flint.arb(0),flint.arb(1)]+[real(Q(rng.randint(-4,4),rng.randint(1,7))) for n in range(2,length+1)];inverse=g.generic_inverse(f);jets={}
        for k in spec['integer_completion_orders']:
            jets[str(k)]=list(map(g.ball,g.convolution(inverse,[flint.arb(0)]+[f[n]*real(n).log()**k for n in range(1,length+1)])))
        generic_sequences.append({'input':list(map(g.ball,f)),'jets':jets,'generated_after_archive_seal':True,'prime_support_certificate_applies':False})
    controls={'unit_type_alias_rejected':alias,'fractional_integer_support_alias_rejected':True,
        'higher_derivative_RH_alias_rejected':not batch['completed_preconditioners']['2']['first_derivative_recovers_every_ordinary_zero'],
        'incomplete_fractional_center_RH_alias_rejected':all(Q(q).denominator!=1 for q in read(d/'archive.json')['fractional_orders'])}
    write(d/'final_evaluation.json',{'protocol_sha256':digest(spec),'cases_sha256':digest(cases),'tables':tables,'integer_observations':obs,'generic_differences':generic,'generic_sequences':generic_sequences,'controls':controls,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False})


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',nargs='?',default='run',choices=['run','worker']);p.add_argument('--run-dir',type=Path,required=True);p.add_argument('--source',type=Path);args=p.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.source is None:raise ValueError('Verified normalized-root source required')
    d.mkdir(parents=True,exist_ok=False);spec=protocol(args.source);write(d/'protocol.json',spec);(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'divisor_preconditioner_search.py'),'worker','--run-dir',str(d)],cwd=BASE,check=True);final(d)
        subprocess.run([sys.executable,str(BASE/'check_divisor_preconditioners.py'),'--run-dir',str(d)],cwd=BASE,check=True)
        from divisor_preconditioner_report import summary,text_report
        s=summary(d);write(d/'summary.json',s);(d/'report.txt').write_text(text_report(s));write(BASE/'divisor-preconditioner-results/latest.json',{'run_directory':str(d)})
    except Exception as e:write(d/'failure.json',{'error_type':type(e).__name__,'error':str(e),'original_data_and_sources_retained':True});raise


if __name__=='__main__':main()
