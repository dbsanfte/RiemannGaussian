"""Frozen actual-source discovery of centered, recoverable product-band operators."""
import argparse
from concurrent.futures import ProcessPoolExecutor,as_completed
from fractions import Fraction as Q
import json
import math
import multiprocessing as mp
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

from flint import arb,ctx
import prime_bank_candidates as S
import centered_product_fibers as P
import check_centered_product_fibers as C

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'occupancy-transfer-results/pilot-001'
INPUT='candidate10_occupancy_joint_forcing_obligation.json'
TESTS=['test_centered_product_fibers','test_check_centered_product_fibers']
RECEIPTS=['centered_product_producer_development.json','centered_product_checker_development.json']
REVIEWS=['OCCUPANCY_POLE_RECOVERY_REVIEW_002.txt','PRIME_EXIT_RECURRENCE_REVIEW_002.txt']
SOURCES=['centered_product_fibers.py','check_centered_product_fibers.py',
         'run_centered_product_fibers.py','centered_product_protocol.txt','prime_bank_candidates.py',INPUT]+REVIEWS+[t+'.py' for t in TESTS]+RECEIPTS
DISCOVERY=[64,128,256]
VALIDATION=[512,1024]
CAPS={64:50000000,128:100000000,256:300000000,512:400000000,1024:750000000}
TOTAL=3000000000
AUDIT_CAP=200000000
MAIN_CAP=50000000
SECONDS=1800
_STATE=None
_CHECK_STATE=None


def read(path):return json.loads(Path(path).read_text())
def write(path,data):
    with Path(path).open('x') as stream:
        json.dump(data,stream,sort_keys=True,indent=2);stream.write('\n')


def development():
    receipts={name:read(ROOT/name) for name in RECEIPTS}
    for row in receipts.values():
        if not row['runs'] or row['runs'][-1]['returncode'] or row['operations']!=sum(r['operations'] for r in row['runs']):
            raise ValueError('complete passed cumulative development receipts')
    return receipts


def parent_input():
    parent=read(ROOT/INPUT)
    if (parent['schema']!='occupancy-joint-forcing-obligation-v1' or parent['source']!='actual_mu_candidate10' or
        parent['equivalence_class']!='candidate10_complete_prime_bank_covariance' or
        parent['whole_signed_bound_proved'] or parent['RH_proved']):raise ValueError('same open complete target')
    if parent!=read(PARENT/'next_search_input.json'):raise ValueError('unchanged prior obstruction')
    for name in read(PARENT/'source_files.json'):
        if (ROOT/name).read_bytes()!=(PARENT/'source_snapshot'/name).read_bytes():raise ValueError('changed immutable parent '+name)
    return parent


def specification():
    return dict(schema='centered-product-band-discovery-v1',parent=parent_input(),
        center='b(n)=a(n)-m_u*(n^(2/3)-(n-1)^(2/3)); b(1)=-m_u',
        original_target_bridge='full leading-centered R=R_new+Lv, using the retained two-direction paid Lv norm comparison',
        sectors=list(P.SECTORS),all_units_valuations_and_crosses=True,
        kernel='max(0,2X-max(X,h,k))',product_support='1<=h*k<=(2X-1)^2',
        gamma_grid=list(P.GAMMAS),grammar=P.stencils(),
        discovery_scales=DISCOVERY,validation_scales=VALIDATION,
        partial_cutoffs='ALL exact rational breakpoints m/2^ceil(log2(m)), batch simultaneous jumps, same t in every shifted band',
        selection='one operator per gamma by smallest worst discovery dyadic log slope of U_X; then smaller inverse log degree, stencil l1 and ordinal',
        validation_policy='selected pairs plus unfiltered calibration at each gamma; selection is saved before validation kernels are evaluated',
        source_policy='one read-only actual-source table through2047; each kernel worker reads only its declared prefix; larger-scale kernel responses are withheld until selection',
        source_precision_bits=160,independent_precision_bits=192,
        independent_checker='direct Mobius/Dirichlet convolutions and weighted prefix/multiples cutoff queries, not pair scatter',
        maximality_scope='complete producer enumeration; independent direct-query checks of every reported witness, plus fixed cutoff and full-energy checks',
        proof_scope='conditional polylog full-target recovery; no uniform arithmetic estimate is inferred from finite extrema or ranks',
        superseded_premise='the old isolated uncentered squarefree product-band target; its nonzero double pole must be compensated jointly',
        stronger_than_whole_moment=True,development=development(),
        total_work_limit=TOTAL,producer_caps=CAPS,independent_cap_per_scale=AUDIT_CAP,main_cap=MAIN_CAP,
        worker_seconds=SECONDS,workers=3,memory_bytes_per_process=4*1024**3,aggregate_memory_limit=16*1024**3,
        metadata_reserve=1000000,hashes=False,whole_signed_bound_proved=False,RH_proved=False)


def freeze(directory):
    directory=Path(directory).resolve();protocol=specification()
    raw={name:(ROOT/name).read_bytes() for name in SOURCES}
    if directory.exists():raise FileExistsError('new immutable centered-source experiment')
    directory.mkdir(parents=True);(directory/'source_snapshot').mkdir()
    for name,value in raw.items():(directory/'source_snapshot'/name).write_bytes(value)
    write(directory/'source_files.json',SOURCES);write(directory/'protocol.json',protocol)


def verify_sources(directory):
    if read(directory/'source_files.json')!=SOURCES:raise ValueError('complete frozen source manifest')
    for name in SOURCES:
        if (ROOT/name).read_bytes()!=(directory/'source_snapshot'/name).read_bytes():raise ValueError('changed source '+name)
    if read(directory/'protocol.json')!=specification():raise ValueError('changed protocol or target')


def limit():
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))


def witness_cutoffs(search):
    cutoffs={0,1,search['N']**2}
    for j in range(search['J']+1):cutoffs.add(min(1<<j,search['N']**2))
    for row in search['candidates']:
        j=row['witness']['j'];t=Q(row['witness']['t'])
        for offset in range(3):
            band=j-offset
            if band<0:continue
            top=1<<band
            cutoffs.add(top//2);cutoffs.add(min(search['N']**2,(top*t.numerator)//t.denominator))
    return sorted(cutoffs)


def produce(task):
    X,pairs=task;ctx.prec=160;start=time.monotonic();meter=S.Meter(CAPS[X],SECONDS)
    rows=P.scatter(X,_STATE,meter)
    search=P.search_bands(X,rows,_STATE,P.stencils(),meter,None if pairs is None else set(map(tuple,pairs)))
    numeric=P.profiles(X,rows,_STATE,witness_cutoffs(search),meter)
    diagnostics=P.prefix_diagnostics(X,_STATE,meter)
    for gamma in P.GAMMAS:
        if not (numeric[search['N']**2][gamma]['centered']-diagnostics['weighted_energy'][gamma]).contains(0):
            raise ArithmeticError('complete weighted prefix moment')
    for row in search['candidates']:
        if row['recovered_energy_upper']<diagnostics['original_energy'].lower():
            raise ArithmeticError('finite exact recovery upper bound fails')
    result=P.serialize(dict(search=search,queries=numeric,diagnostics=diagnostics))
    result['resources']=dict(operations=meter.operations,peak_cells=meter.peak_cells,
        elapsed_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    return result


def production_stage(directory,scales,pairs,label):
    results={}
    with ProcessPoolExecutor(max_workers=min(3,len(scales)),mp_context=mp.get_context('fork'),initializer=limit) as pool:
        futures={pool.submit(produce,(X,pairs)):X for X in scales}
        for future in as_completed(futures):
            X=futures[future];value=future.result();write(directory/(label+'-'+str(X)+'.json'),value);results[X]=value
            print(json.dumps(dict(stage=label,X=X,operations=value['resources']['operations'],seconds=value['resources']['elapsed_seconds'])),flush=True)
    return results


def recovery_degree(coefficients):
    _,c1,c2=coefficients
    return 1 if c1==c2==0 else 3 if c2==1 and abs(c1)==2 else 2


def choose(training):
    grammar={row['id']:row for row in P.stencils()};ranks=[]
    byscale={X:{(r['stencil_id'],r['gamma']):r for r in case['search']['candidates']} for X,case in training.items()}
    for key in sorted(byscale[DISCOVERY[0]]):
        values=[float(arb(byscale[X][key]['upper']).mid()) for X in DISCOVERY]
        if any(value<=0 or not math.isfinite(value) for value in values):raise ArithmeticError('positive finite discovery norm')
        slope=max(math.log(values[j+1]/values[j],2) for j in range(len(values)-1))
        coefficients=grammar[key[0]]['coefficients']
        ranks.append(dict(stencil_id=key[0],gamma=key[1],worst_discovery_slope=slope,
                          inverse_log_degree=recovery_degree(coefficients),coefficient_l1=sum(map(abs,coefficients)),
                          uniform_signed_bound_proved=False))
    selected=[]
    for gamma in P.GAMMAS:
        selected.append(min((row for row in ranks if row['gamma']==gamma),
                            key=lambda r:(r['worst_discovery_slope'],r['inverse_log_degree'],r['coefficient_l1'],r['stencil_id'])))
    identity=next(row['id'] for row in P.stencils() if row['coefficients']==[1,0,0])
    pairs=sorted({(row['stencil_id'],row['gamma']) for row in selected}|{(identity,gamma) for gamma in P.GAMMAS})
    return dict(ranking=ranks,selected=selected,validation_pairs=[list(pair) for pair in pairs],
                adaptation_after_validation=False,whole_signed_bound_proved=False,RH_proved=False)


def compare(old,new,meter):
    previous=arb(old);meter.charge(8)
    if not P.tight(previous) or not P.tight(new) or not previous.overlaps(new):raise ArithmeticError('independent tight interval disagreement')


def audit_grammar(meter):
    for row in P.stencils():
        _,c1,c2=row['coefficients'];discriminant=c1*c1-4*c2
        independently_stable=(c2<=1) if discriminant<0 else (abs(c1)<=2 and discriminant<=(2-abs(c1))**2)
        meter.charge(12)
        if row['cofinal_inverse_admitted']!=independently_stable:raise ValueError('independent quadratic root criterion')


def audit_case(case):
    ctx.prec=192;meter=S.Meter(AUDIT_CAP,SECONDS);start=time.monotonic()
    _CHECK_STATE._cache={};_CHECK_STATE._cache_cells=0
    search=case['search'];X=search['X'];N=2*X-1;J=(N*N-1).bit_length()
    if search['N']!=N or search['J']!=J:raise ValueError('complete product horizon and tail')
    checked={};queries=case['queries']
    for T_text,row in queries.items():
        T=int(T_text)
        for gamma,values in row.items():
            fresh=C.cutoff(X,T,gamma,_CHECK_STATE,meter)
            for key,value in values.items():compare(value,fresh[key],meter)
            checked[(T,gamma)]=fresh
    grammar={r['id']:r for r in P.stencils()}
    for row in search['candidates']:
        coefficients=grammar[row['stencil_id']]['coefficients'];gamma=Q(row['gamma'])
        j=row['witness']['j'];t=Q(row['witness']['t'])
        if not 0<=j<=J or not Q(1,2)<=t<=1:raise ValueError('complete witness domain')
        value=arb(0)
        for offset,c in enumerate(coefficients):
            band=j-offset
            if band<0 or not c:continue
            top=1<<band;T=min(N*N,(top*t.numerator)//t.denominator);low=top//2
            upper=checked[(T,row['gamma'])]['centered'];lower=checked[(low,row['gamma'])]['centered']
            power=arb(top).root(6)**int(6*gamma)
            value+=c*power*(upper-lower);meter.charge(80)
        compare(row['witness']['value'],value,meter)
        if arb(row['lower']).lower()>value.abs_upper() or arb(row['upper']).upper()<value.abs_lower():
            raise ArithmeticError('attainable extremum interval')
        inverse=row['inverse_coefficients']
        if len(inverse)!=J+1:raise ValueError('complete inverse head')
        for n in range(J+1):
            residual=sum(coefficients[k]*inverse[n-k] for k in range(3) if n>=k)
            if residual!=int(n==0) or abs(inverse[n])>n+1:raise ValueError('exact causal inverse certificate')
            meter.charge(12)
        inverse_sum=sum((J-n+1)*abs(v) for n,v in enumerate(inverse))
        if inverse_sum!=row['inverse_l1_sum']:raise ValueError('complete inverse l1 recovery cost')
        cost=(2-arb(2)**(-arb(gamma.numerator)/gamma.denominator))*inverse_sum
        compare(row['recovery_constant'],cost,meter)
        expected=cost*arb(row['upper']);reported=arb(row['recovered_energy_upper'])
        meter.charge(16)
        if (not P.tight(reported) or reported.upper()<expected.lower() or
                (reported-expected).abs_upper()>arb(2)**-65*(1+expected.abs_upper())):
            raise ArithmeticError('reported recovery bound must equal cost times the finite band norm, up to enclosure rounding')
        if (reported.upper()<checked[(N*N,'0')]['centered'].lower() or
                any(row[k] for k in ('uniform_in_X_proved','whole_signed_bound_proved','RH_proved')) or
                not row['all_partial_breakpoints_examined']):raise ValueError('finite recovery and global proof scope')
    direct=sum((_CHECK_STATE['R'][n]**2 for n in range(X,2*X)),arb(0))/(X*X)
    meter.charge(4*X)
    compare(case['diagnostics']['original_energy'],direct,meter)
    for gamma in P.GAMMAS:compare(case['diagnostics']['weighted_energy'][gamma],checked[(N*N,gamma)]['centered'],meter)
    return dict(X=X,status='INDEPENDENT_PREFIX_AND_CENTERING_CHECKS_PASSED',
                checked_product_queries=len(checked),checked_candidate_witnesses=len(search['candidates']),
                operations=meter.operations,peak_cells=meter.peak_cells,elapsed_seconds=time.monotonic()-start,
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                maximality_independently_reenumerated=False,whole_signed_bound_proved=False,RH_proved=False)


def next_input(parent,selection,report):
    return dict(schema='centered-product-band-obligation-v1',status='open',source=parent['source'],scope=parent['scope'],
        required_bound=parent['required_bound'],equivalence_class=parent['equivalence_class'],centering_feedback=parent['centering_feedback'],
        prior_obligation=parent,
        corrected_centering='b(n)=a(n)-m_u*(n^(2/3)-(n-1)^(2/3)), including n=1; retain six SF/NS AA/cross/MM sectors',
        supersedes='isolated uncentered SF product-band recovery premise; the earlier low-contour component theorem remains valid',
        pole_feedback=dict(nonzero_squarefree_double_residue=True,physical_poles=['2/3','2/3'],
            weighted_sixth_root_poles=['1/2','1/2'],unconditional_diagonal_asymptotic_proved=False,
            compensation='only the unrestricted complete centered sum has proved pole cancellation; no separate centered-SF bound is assumed'),
        selected=selection['selected'],finite_results=report,
        new_auxiliary=dict(
            band='D_j,gamma(t)=2^(j*gamma)/X^2 sum_(2^(j-1)<hk<=t*2^j,h,k<=N) b(h)b(k)W_X(h,k)*(hk)^(-gamma)',
            N='2X-1',J='ceil(log2(N^2))',t_domain='1/2<=t<=1',negative_bands='zero',
            operator='D_j+c1*D_(j-1)+c2*D_(j-2), same t on all bands',
            needed_bound='for every epsilon>0, U_X=max_j sup_t |operator|<=C_epsilon X^epsilon uniformly in X',
            recovery='E_R(X)<=(2-2^-gamma)*sum_(l=0)^J (J-l+1)*abs(g_l)*U_X',
            inverse='g coefficients of 1/(1+c1*z+c2*z^2); |g_l|<=l+1 for admitted roots',
            recovery_is_polylogarithmic=True,uniform_arithmetic_bound_proved=False,
            stronger_than_whole_moment=True,stencils_share_auxiliary_equivalence_class=True,
            generic_bounded_source_counterexample_to_reverse_implication='lacunary +/- blocks in OCCUPANCY_POLE_RECOVERY_REVIEW_002.txt; not an actual-mu counterexample'),
        alternative_normalized_abel=dict(
            expression='F_gamma(t)=t^gamma sum_(h<=t)b(h)h^-gamma',
            inverse='B=F_gamma-gamma integral_1^t F_gamma(u) du/u',
            inverse_norm_at_most_one='0<=gamma<=2sigma in truncated weighted L2 norm',
            forward_norm='sigma/(sigma-gamma), gamma<sigma',
            fractional_prime_gain='cancels under normalized pullback; no double credit',bound_proved=False),
        fixed_prime_feedback=dict(delayed_contraction='q>=3 gives rho<=17/18 at sigma>=1/2',
            paid='exact pole-floor, unit and same-prime forcing',
            open='current-scale q-free source frontier; not an independently paid smaller argument'),
        reviewed_inputs=REVIEWS,whole_signed_bound_proved=False,RH_proved=False)


def run(directory):
    global _STATE,_CHECK_STATE
    directory=Path(directory).resolve();verify_sources(directory);limit();start=time.monotonic()
    write(directory/'started.json',dict(attempt=1,monotonic=start))
    test=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=60)
    matches=re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$',test.stdout,re.M)
    frozen=sum(int(n) for _,n in matches)
    write(directory/'frozen_tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr,operations=frozen))
    if test.returncode or sorted(k for k,_ in matches)!=sorted(TESTS):raise RuntimeError('complete passed frozen suite')
    preparation=1000000+frozen+sum(r['operations'] for r in development().values())
    if preparation+MAIN_CAP+sum(CAPS.values())+len(DISCOVERY+VALIDATION)*AUDIT_CAP>TOTAL:raise ValueError('aggregate work reserves exceed total')
    main=S.Meter(MAIN_CAP,4*SECONDS);ctx.prec=160;_STATE=P.source(2*max(VALIDATION)-1,main)
    write(directory/'source_values.json',P.serialize({key:_STATE[key] for key in ('H','mu','a','a_u','a_v','p','m','R','m_u')}))
    audit_grammar(main)
    training=production_stage(directory,DISCOVERY,None,'discovery')
    selection=choose(training);write(directory/'selection.json',selection)
    print(json.dumps(dict(stage='selection_frozen',pairs=selection['validation_pairs'])),flush=True)
    validation=production_stage(directory,VALIDATION,selection['validation_pairs'],'validation')
    cases=dict(training);cases.update(validation)
    ctx.prec=192;_CHECK_STATE=C.source(_STATE['H'],main)
    for key in ('a','a_u','a_v','p','m','R'):
        for old,new in zip(_STATE[key],_CHECK_STATE[key]):compare(P.encode(old),new,main)
    if _STATE['mu']!=_CHECK_STATE['mu']:raise ArithmeticError('independent source masks')
    compare(P.encode(_STATE['m_u']),_CHECK_STATE['c'],main)
    audits={}
    with ProcessPoolExecutor(max_workers=3,mp_context=mp.get_context('fork'),initializer=limit) as pool:
        futures={pool.submit(audit_case,case):X for X,case in cases.items()}
        for future in as_completed(futures):
            X=futures[future];value=future.result();audits[X]=value;write(directory/('audit-'+str(X)+'.json'),value)
            print(json.dumps(dict(stage='independent_audit',X=X,operations=value['operations'])),flush=True)
    producer_work=sum(case['resources']['operations'] for case in cases.values())
    audit_work=sum(row['operations'] for row in audits.values())
    total=preparation+main.operations+producer_work+audit_work
    if total>TOTAL:raise OverflowError('complete charged work limit')
    report=dict(status='CENTERED_PRODUCT_BAND_CANDIDATES_FINITELY_VERIFIED',
        stencil_grammar_size=25,cofinal_inverse_stencils=sum(r['cofinal_inverse_admitted'] for r in P.stencils()),
        discovery_scales=DISCOVERY,validation_scales=VALIDATION,
        all_partial_breakpoints=True,selected=selection['selected'],validation_pairs=selection['validation_pairs'],
        original_energy={str(X):case['diagnostics']['original_energy'] for X,case in sorted(cases.items())},
        product_counts={str(X):case['search']['distinct_products'] for X,case in sorted(cases.items())},
        checked_source_horizon=_STATE['H'],independent_source_precision_bits=192,
        finite_candidate_checks=sum(len(case['search']['candidates']) for case in cases.values()),
        proof_status='conditional polylog recovery is proved analytically; uniform source bound remains open',
        stronger_auxiliary_than_original=True,preparation_operations=preparation,main_operations=main.operations,
        producer_operations=producer_work,audit_operations=audit_work,total_operations=total,
        elapsed_seconds=time.monotonic()-start,
        peak_rss_kib=max([resource.getrusage(resource.RUSAGE_SELF).ru_maxrss]+[c['resources']['peak_rss_kib'] for c in cases.values()]+[a['peak_rss_kib'] for a in audits.values()]),
        whole_signed_bound_proved=False,RH_proved=False)
    verify_sources(directory);write(directory/'report.json',report)
    write(directory/'next_search_input.json',next_input(parent_input(),selection,report))
    print(json.dumps(report),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('action',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();globals()[args.action](args.directory)
