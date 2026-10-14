"""Frozen occupancy and fractional auxiliary discovery with independent audit."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

import prime_slide_discovery as S
import occupancy_transfer_discovery as P
import check_occupancy_transfer as C

ROOT = Path(__file__).resolve().parent
PARENT = ROOT / 'prime-exchange-results/pilot-001'
INPUT = 'candidate10_prime_exchange_joint_recovery_obligation.json'
TESTS = ['test_occupancy_transfer_discovery', 'test_check_occupancy_transfer']
RECEIPTS = ['occupancy_producer_development.json', 'occupancy_checker_development.json']
REVIEWS = ['OCCUPANCY_TRANSFER_REVIEW_001.txt', 'PRIME_PARITY_FULL_RECOVERY_REVIEW_001.txt']
SOURCES = ['occupancy_transfer_discovery.py', 'check_occupancy_transfer.py',
           'run_occupancy_transfer_discovery.py', 'occupancy_transfer_protocol.txt',
           'prime_slide_discovery.py', INPUT] + REVIEWS + [t+'.py' for t in TESTS] + RECEIPTS
GRID = [str(Q(i, 6)) for i in range(-12, 13)]
GAMMAS = ['0', '1/6', '1/3', '1/2', '2/3', '1']
ANGLES = ['1/8', '1/4', '1/2', '1']
FIXTURES = [(1,2,1,1), (8,3,1,5), (8,3,5,1), (8,3,17,1), (8,5,2,3), (16,7,4,9)]
TARGET = ['0']*15 + ['1']
TOTAL = 100000000
SECONDS = 900


def read(path):
    return json.loads(Path(path).read_text())


def write(path, data):
    with Path(path).open('x') as stream:
        json.dump(data, stream, sort_keys=True, indent=2)
        stream.write('\n')


def development():
    receipts = {name: read(ROOT/name) for name in RECEIPTS}
    for row in receipts.values():
        if (not row['runs'] or row['runs'][-1]['returncode'] or
                row['operations'] != sum(r['operations'] for r in row['runs'])):
            raise ValueError('complete passed development receipts')
    return receipts


def parent_input():
    parent = read(ROOT/INPUT)
    if (parent['schema'] != 'prime-exchange-joint-recovery-obligation-v1' or
            parent['status'] != 'open' or parent['source'] != 'actual_mu_candidate10' or
            parent['equivalence_class'] != 'candidate10_complete_prime_bank_covariance' or
            parent['whole_signed_bound_proved'] or parent['RH_proved']):
        raise ValueError('same open whole signed target')
    if parent != read(PARENT/'next_search_input.json'):
        raise ValueError('complete unchanged next obstruction')
    if read(PARENT/'report.json')['status'] != 'JOINT_FACTORS_AND_COMPLETE_EDGE_CORRECTIONS_VERIFIED':
        raise ValueError('verified parent experiment')
    for name in read(PARENT/'source_files.json'):
        if (ROOT/name).read_bytes() != (PARENT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed immutable parent source '+name)
    return parent


def specification():
    return dict(schema='occupancy-fractional-discovery-v1', parent=parent_input(),
                bin_primitives=[dict(leg=leg,power=power) for leg,power in P.BINS],
                powers_refer_to='z=q^(-1/6)', masks=list(range(16)),
                source_laws_supplied=True,
                prior_analytical_nomination='occupancy transfer, union spectrum and fractional product weighting',
                eigenvalue_grid=GRID, gamma_grid=GAMMAS, phase_half_width_grid=ANGLES,target=TARGET,
                coefficient_field='exact rationals', proposed_eigenvalue_pairs=len(GRID)**2,
                bernstein_domain=['0','9/10'], partition_depths=list(range(5)),
                kernel_fixtures=[list(f) for f in FIXTURES], all_masks_checked=True,
                selection='retain all modes; prioritize complete bulk/phase auxiliary coverage by smaller pointwise inverse power, then wider certified phase cone',
                fixtures_are='synthetic exact kernel semantics; no source response table',
                new_actual_source_evaluations=0, development=development(),
                work_limit=TOTAL, seconds=SECONDS, metadata_reserve=250000,
                memory_bytes=4*1024**3, aggregate_memory_limit=16*1024**3,
                hashes=False, energy_contraction_proved=False,
                whole_signed_bound_proved=False, RH_proved=False)


def freeze(directory):
    directory = Path(directory).resolve()
    protocol = specification()
    raw = {name:(ROOT/name).read_bytes() for name in SOURCES}
    if directory.exists():
        raise FileExistsError('fresh immutable occupancy experiment')
    directory.mkdir(parents=True)
    (directory/'source_snapshot').mkdir()
    for name, content in raw.items():
        (directory/'source_snapshot'/name).write_bytes(content)
    write(directory/'source_files.json', SOURCES)
    write(directory/'protocol.json', protocol)


def verify_sources(directory):
    if read(directory/'source_files.json') != SOURCES:
        raise ValueError('complete source manifest')
    for name in SOURCES:
        if (ROOT/name).read_bytes() != (directory/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)
    if read(directory/'protocol.json') != specification():
        raise ValueError('changed scope or input')


def audit_modes(modes, rejected, meter):
    keys = [(row['eigen_u'], row['eigen_v']) for row in modes]
    rejected_keys = [tuple(row) for row in rejected]
    if (len(set(rejected_keys)) != len(rejected_keys) or
            set(keys) & set(rejected_keys) or
            set(keys) | set(rejected_keys) != set(product(GRID, repeat=2))):
        raise ValueError('complete grid and disjoint rejection accounting')
    for index, row in enumerate(modes):
        if row['id'] != index:
            raise ValueError('canonical mode order')
        checked = C.verify_mode(row['potential'], row['eigen_u'], row['eigen_v'], meter)
        if any(checked[key] != value for key, value in row.items() if key != 'id'):
            raise ValueError('independent mode certificate mismatch')
    # A literal reconstruction of every coordinate provides an independent
    # completeness certificate; it does not trust the producer's nullity.
    coordinate_certificates = []
    for mask in range(16):
        target = ['1' if i == mask else '0' for i in range(16)]
        coefficients = P.recover(modes, target, meter)
        if coefficients is None:
            return dict(complete_basis=False, coordinate_certificates=coordinate_certificates)
        C.verify_recovery([row['potential'] for row in modes], coefficients, target, meter)
        coordinate_certificates.append(dict(mask=mask, coefficients=coefficients))
    return dict(complete_basis=True, coordinate_certificates=coordinate_certificates)


def audit_kernels(modes, meter):
    potential_rows = [dict(id='target', potential=TARGET)] + modes
    outputs = []
    checks = 0
    for mode in potential_rows:
        compiled = P.compile_kernel(mode['potential'], meter)
        for X, q, h, k in FIXTURES:
            kernel = P.kernel_counts(X, q, h, k, meter)
            for mask, row in enumerate(compiled):
                check = C.verify_kernel(mode['potential'], X, q, h, k, mask, meter)
                for key in ('W', 'W_L', 'W_R'):
                    if kernel[key] != check[key]:
                        raise ValueError('independent complete prefix count')
                if (kernel['left_exit'] != check['left_exit_count'] or
                        kernel['right_exit'] != check['right_exit_count'] or
                        row['bulk'] != check['bulk_multiplier'] or
                        row['left_exit'] != check['left_transfer'] or
                        row['right_exit'] != check['right_transfer']):
                    raise ValueError('complete kernel/birth/exit identity')
                checks += 1
        outputs.append(dict(mode_id=mode['id'], potential=mode['potential'], kernel=compiled))
    return outputs, checks


def audit_fractional(records, modes, meter):
    pairs = sorted({(Q(r['eigen_u']), Q(r['eigen_v'])) for r in modes})
    expected = [(str(a),str(b),g) for (a,b),g in product(pairs,GAMMAS)]
    if [(r['eigen_u'],r['eigen_v'],r['gamma']) for r in records] != expected:
        raise ValueError('complete fractional construction family')
    certificates = 0
    for index, row in enumerate(records):
        a,b,gamma = map(Q,(row['eigen_u'],row['eigen_v'],row['gamma']))
        power = int(6*gamma)
        coefficients = {0:Q(1)}
        for exponent,value in ((power,-a-b),(power+2,a),(power+4,b)):
            coefficients[exponent] = coefficients.get(exponent,Q(0)) + value
        expected_poly = [[p,str(v)] for p,v in sorted(coefficients.items()) if v]
        meter.charge(32)
        if (row['id'] != index or row['polynomial'] != expected_poly or
                row['product_recovery_power'] != str(2*gamma) or
                row['signed_sum_recovery_from_scalar_factor'] or
                row['original_target_recovered'] or row['energy_contraction_proved'] or
                row['whole_signed_bound_proved'] or not row['boundary_terms_retained']):
            raise ValueError('fractional source/recovery scope')
        certificate = row['certificate']
        if certificate['status'] == 'CERTIFIED_ALGEBRAIC_BULK_ENVELOPE':
            depth = certificate['depth']
            if type(depth) is not int or not 0 <= depth <= 4 or len(certificate['segments']) != 1 << depth:
                raise ValueError('frozen partition menu')
            for j,segment in enumerate(certificate['segments']):
                if (Q(segment['left']) != Q(9*j,10*(1<<depth)) or
                        Q(segment['right']) != Q(9*(j+1),10*(1<<depth))):
                    raise ValueError('canonical frozen partition')
            C.verify_bernstein(row['polynomial'],certificate['segments'],meter)
            certificates += 1
        elif certificate != dict(status='NO_CERTIFICATE_IN_FROZEN_PARTITIONS',depth_limit=4,segments=[]):
            raise ValueError('unproved bound must remain unproved')
    return certificates


def audit_phases(records, fractional, modes, admission, meter):
    if [(r['fractional_id'],r['phase_half_width']) for r in records] != [(f['id'],a) for f,a in product(fractional,ANGLES)]:
        raise ValueError('complete phase auxiliary menu')
    if [r['mode_id'] for r in admission] != [r['id'] for r in modes]:
        raise ValueError('every mode needs individual-union admission')
    for row, mode in zip(admission,modes):
        vector = list(map(Q,mode['potential']))
        eigenvalues = row['individual_union_eigenvalues']
        if row['scalar_phase_admissible']:
            if eigenvalues is None or len(eigenvalues) != 4:
                raise ValueError('all four union generators')
            for bit,text in enumerate(eigenvalues):
                value = Q(text)
                if value not in (0,1):
                    raise ValueError('idempotent generator spectrum')
                for mask in range(16):
                    meter.charge(3)
                    if vector[mask | (1<<bit)] != value*vector[mask]:
                        raise ValueError('individual union-mode relation')
            if (Q(eigenvalues[0])+Q(eigenvalues[2]) != Q(mode['eigen_u']) or
                    Q(eigenvalues[1])+Q(eigenvalues[3]) != Q(mode['eigen_v'])):
                raise ValueError('nonnegative two-leg weights must sum to the scalar mode')
        elif eigenvalues is not None:
            raise ValueError('inadmissible mode has a claimed scalar splitting')
    verified = 0
    for index,row in enumerate(records):
        source = fractional[row['fractional_id']]
        delta = Q(row['phase_half_width'])
        center = delta*delta/2
        original = {p:Q(c) for p,c in source['polynomial']}
        transformed = {p:Q(c) for p,c in row['transformed_polynomial']}
        recovered = {p:(1-center)*c for p,c in transformed.items()}
        recovered[0] = recovered.get(0,Q(0)) + center
        recovered = {p:c for p,c in recovered.items() if c}
        meter.charge(32+8*len(recovered))
        if (recovered != original or row['id'] != index or
                any(row[k] != source[k] for k in ('gamma','eigen_u','eigen_v')) or
                row['sufficient_rho_bound'] != str(2-delta*delta) or
                row['source_recovery_power'] != source['product_recovery_power'] or
                any(row[k] for k in ('arithmetic_operator_norm_proved','prime_free_projection_closure',
                                     'energy_contraction_proved','whole_signed_bound_proved'))):
            raise ValueError('phase interval transform and arithmetic scope')
        certificate = row['certificate']
        if certificate['status'] == 'CERTIFIED_ALGEBRAIC_BULK_ENVELOPE':
            depth = certificate['depth']
            if type(depth) is not int or not 0<=depth<=4 or len(certificate['segments']) != 1<<depth:
                raise ValueError('frozen phase partitions')
            for j,segment in enumerate(certificate['segments']):
                if (Q(segment['left']) != Q(9*j,10*(1<<depth)) or
                        Q(segment['right']) != Q(9*(j+1),10*(1<<depth))):
                    raise ValueError('canonical frozen phase partition')
            C.verify_bernstein(row['transformed_polynomial'],certificate['segments'],meter)
            verified += 1
        elif certificate != dict(status='NO_CERTIFICATE_IN_FROZEN_PARTITIONS',depth_limit=4,segments=[]):
            raise ValueError('unproved phase bound')
    return verified


def next_input(parent, modes, recovery, selected, phase_selected, kernel):
    return dict(schema='occupancy-joint-forcing-obligation-v1',status='open',
                source=parent['source'],scope=parent['scope'],equivalence_class=parent['equivalence_class'],
                required_bound=parent['required_bound'],centering_feedback=parent['centering_feedback'],
                prior_obligation=parent,
                construction=dict(modes=modes,target_recovery=recovery,
                                  target_bulk_and_both_exits=kernel[0],fractional_auxiliaries=selected,
                                  phase_cone_auxiliaries=phase_selected),
                exact_new_target=dict(
                    expression='X^-2 sum_(m squarefree,q not dividing m) mu(m)*[(1-2*t_q)*Phi_X(m)+t_q*Boundary_X,q(m)-Birth_X,q(m)]',
                    t_q='2-q^(-1/3)-q^(-2/3)',
                    Phi='sum_(h*k=m) gamma(h)*gamma(k)*W_X(h,k)',
                    gamma='beta*(prod_(p|h)(r_p+s_p)-prod_(p|h)r_p-prod_(p|h)s_p+delta(h))',
                    Boundary='sum_(h*k=m) gamma(h)*gamma(k)*(2*W_X(h,k)-W_X(q*h,k)-W_X(h,q*k))',
                    Birth='sum_(h*k=m)[G_q(h)*gamma(k)*W_X(q*h,k)+gamma(h)*G_q(k)*W_X(h,q*k)]',
                    G='beta*(s_q*prod_(p|h)r_p+r_q*prod_(p|h)s_p-t_q*delta(h))',
                    W='max(0,2X-max(X,h,k))',r_p='1-p^(-1/3)',s_p='1-p^(-2/3)',beta='9/2',
                    scope='exact squarefree-product projection only; not positive and not the complete target'),
                dependencies=[
                    dict(id='full_centered_moment',status='OPEN',kind='original target',
                         requires=['joint_squarefree_and_repeated_valuation_forcing','complete_center_and_cross']),
                    dict(id='joint_squarefree_and_repeated_valuation_forcing',status='OPEN',
                         requires=['birth_and_exit_correlations','all_valuation_complement']),
                    dict(id='birth_and_exit_correlations',status='OPEN',
                         expression='joint signed birth and BOTH exit terms at every required scale/prime; include high-frequency and moving prime-free projection control; scalar/phase-cone bounds alone are insufficient',
                         requires=[]),
                    dict(id='all_valuation_complement',status='OPEN',
                         expression='full rational local prime-valuation transition, shared gcds and source prime-power correction',requires=[]),
                    dict(id='complete_center_and_cross',status='OPEN',
                         expression='original smooth/pole compensation kept jointly with source square',requires=[])],
                dependency_policy='no RH-strength companion estimate is a paid leaf; a smaller-scale induction needs uniform constants and an independently bounded forcing',
                fractional_recovery='need uniform product-cutoff partial sums for signed Abel recovery; pointwise inverse m^gamma<= (2X)^(2gamma) is not a signed-sum estimate',
                reviewed_low_contour_component=dict(
                    provenance='OCCUPANCY_TRANSFER_REVIEW_001.txt',
                    source='entire squarefree-product projection, weighted by m^(-1/6)',
                    finite_prime_product='Z_N(s,t)=e_full^T product_(q prime<=N)[I-r_q*q^(-gamma-s)*A_hu-s_q*q^(-gamma-s)*A_hv-r_q*q^(-gamma-t)*A_ku-s_q*q^(-gamma-t)*A_kv] e_empty',
                    N='2X-1',gamma='1/6',real_line='c=1/log(N)',X_minimum=2,
                    low_rectangle='|Im(s)|,|Im(t)|<=c/4',
                    bound='beta^2*exp(4)/(pi^2*X)',beta='9/2',
                    full_prefix_compilation='finite Euler product and double Perron with n+1/2 endpoints',
                    high_complement='entire conditional Perron limit minus the low rectangle; includes one or both high frequencies',
                    high_complement_proved=False,
                    product_cutoff_recovery=dict(
                        required='S_gamma(T)=beta^2/X^2 sum_(sf m<=T) mu(m)*Psi_full,X(m)*m^(-gamma), uniformly over 1<=T<=N^2',
                        abel_identity='S_0(N^2)=N^(2*gamma)*S_gamma(N^2)-gamma*integral_1^(N^2) t^(gamma-1)*S_gamma(t) dt',
                        sufficient_new_lemma='for each dyadic product band (T,2T] and every partial subinterval, weighted signed sum <=C_epsilon*X^epsilon*T^(-gamma)',
                        lemma_proved=False),
                    projection_is_positive_energy=False,whole_signed_bound_proved=False,
                    proof_status='separate reviewed analytical component theorem, not proof-text execution or an implication of scalar certificates alone'),
                reviewed_full_valuation_feedback=dict(
                    provenance='PRIME_PARITY_FULL_RECOVERY_REVIEW_001.txt',
                    rational_transition='product_i [I-E_i*(1-t_i)*z_leg(i)/(1-t_i*z_leg(i))]',
                    t_u='q^(-1/3)',t_v='q^(-2/3)',
                    local_parity='negative at first occupation of each color at this prime; positive on its subsequent valuation increments',
                    same_prime_correction='0<=D(n)<=beta*sqrt(n); full centered p/a norm comparison, with finite mixed term retained',
                    paid_shared_valuation_sector=dict(
                        domain='union of h,k<=n sharing q^j on both legs for some prime q>n^rho, j>=2',
                        constant='C_j=beta^2*(j+1)^2*(1+1/(2*j-1))',
                        bound='C_j*2^max(2-(2*j-1)*rho,0)*X^(1-(2*j-1)*rho)*(1+log(2X))^2',
                        cofinal_threshold='rho>=1/(2*j-1)',square_example='j=2,rho=1/3: 24*beta^2*(1+log(2X))^2',
                        overlap_policy='subtract the union once; do not subtract overlapping prime sectors repeatedly',
                        full_energy_proved=False),
                    complete_prime_chain='sum_(e>=0) a(q^e*H)=-d(H) for q-free H>1; zero at H=1',
                    complete_exit='Exit_(e,f)=W_X(H,K)-W_X(q^e*H,q^f*K)',
                    joint_exit_identity='sum a(h)*a(k)*W = sum_(q-free H,K) d(H)*d(K)*W - sum_(q-free H,K,e,f) a(q^e*H)*a(q^f*K)*Exit_(e,f)',
                    exit_center='A(n)-M(n)=-[D_qfree(n)+L_exit,q(n)+M(n)]',
                    exit_reparametrization_is_equivalent_target=True,
                    exit_forcing_proved=False,proof_status='reviewed analytical argument; not execution of proof text'),
                reviewed_inputs=[dict(file=name,status='analytical review; not proof-text execution') for name in REVIEWS],
                complete_repeated_prime_transition_implemented=False,
                new_actual_prime_distribution_estimate=False,
                energy_contraction_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def run(directory):
    directory = Path(directory).resolve()
    verify_sources(directory)
    start = time.monotonic()
    _,hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))
    write(directory/'started.json',dict(attempt=1,monotonic=start))
    tests = subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=60)
    work = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$',tests.stdout,re.M)
    frozen = sum(int(n) for _,n in work)
    write(directory/'frozen_tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr,operations=frozen))
    if tests.returncode or sorted(name for name,_ in work) != sorted(TESTS):
        raise RuntimeError('passed complete frozen suite required')
    preparation = 250000 + frozen + sum(r['operations'] for r in development().values())
    meter = S.Meter(TOTAL-preparation,SECONDS)
    meter.deadline = start + SECONDS
    modes,rejected = P.spectral_search(GRID,meter)
    recovery = P.recover(modes,TARGET,meter)
    stable = [row for row in modes if row['stable']]
    stable_recovery = P.recover(stable,TARGET,meter)
    fractional = P.fractional_search(modes,GAMMAS,meter)
    phase_admission = P.individual_union_modes(modes,meter)
    phases = P.phase_search(fractional,ANGLES,meter)
    meter.live(65536+256*len(modes)+512*len(fractional)+1024*len(phases))
    producer_work = meter.operations
    write(directory/'modes.json',modes)
    write(directory/'rejected_eigenvalues.json',rejected)
    write(directory/'fractional_constructions.json',fractional)
    write(directory/'phase_constructions.json',phases)
    write(directory/'phase_mode_admission.json',phase_admission)
    completeness = audit_modes(modes,rejected,meter)
    if recovery is not None:
        C.verify_recovery([r['potential'] for r in modes],recovery,TARGET,meter)
    if stable_recovery is not None:
        C.verify_recovery([r['potential'] for r in stable],stable_recovery,TARGET,meter)
    stable_obstruction = stable_recovery is None and all(Q(r['potential'][15]) == 0 for r in stable)
    if stable_recovery is None and not stable_obstruction:
        raise ValueError('missing independent stable-span obstruction witness')
    kernels,kernel_checks = audit_kernels(modes,meter)
    certified = audit_fractional(fractional,modes,meter)
    phase_certified = audit_phases(phases,fractional,modes,phase_admission,meter)
    selected = []
    for gamma in GAMMAS:
        rows = [row for row in fractional if row['gamma'] == gamma]
        if rows and all(row['certificate']['status'] == 'CERTIFIED_ALGEBRAIC_BULK_ENVELOPE' for row in rows):
            selected.append(dict(gamma=gamma,construction_ids=[r['id'] for r in rows],
                                 pointwise_inverse_power=str(2*Q(gamma)),
                                 covers_every_discovered_mode=True,
                                 complete_occupancy_basis=completeness['complete_basis'],
                                 signed_sum_recovery_proved=False,energy_contraction_proved=False,
                                 full_target_recovered=False))
    selected.sort(key=lambda r:(Q(r['pointwise_inverse_power']),Q(r['gamma'])))
    phase_selected = []
    for gamma,angle in product(GAMMAS,ANGLES):
        rows = [row for row in phases if row['gamma']==gamma and row['phase_half_width']==angle]
        if (rows and all(row['scalar_phase_admissible'] for row in phase_admission) and
                all(row['certificate']['status']=='CERTIFIED_ALGEBRAIC_BULK_ENVELOPE' for row in rows)):
            phase_selected.append(dict(gamma=gamma,phase_half_width=angle,
                                       construction_ids=[r['id'] for r in rows],
                                       pointwise_inverse_power=str(2*Q(gamma)),
                                       formal_dilation_symbol_bounded=True,
                                       arithmetic_operator_norm_proved=False,
                                       prime_free_projection_closure=False,
                                       energy_contraction_proved=False,full_target_recovered=False))
    phase_selected.sort(key=lambda r:(Q(r['pointwise_inverse_power']),-Q(r['phase_half_width'])))
    eigen_counts = Counter((r['eigen_u'],r['eigen_v']) for r in modes)
    report = dict(status='OCCUPANCY_IDENTITIES_AND_FRACTIONAL_BULK_CERTIFICATES_VERIFIED',
                  proposed_eigenvalue_pairs=len(GRID)**2,rejected_eigenvalue_pairs=len(rejected),
                  discovered_modes=len(modes),eigenvalue_multiplicities=[dict(u=a,v=b,modes=n) for (a,b),n in sorted(eigen_counts.items())],
                  complete_occupancy_basis=completeness['complete_basis'],
                  scalar_stable_modes=len(stable),stable_target_recovery=stable_recovery is not None,
                  stable_span_obstruction_independently_verified=stable_obstruction,
                  full_coordinate_recovery_verified=recovery is not None,
                  fractional_constructions=len(fractional),bulk_certificates=certified,
                  all_mode_weights=[r['gamma'] for r in selected],
                  phase_constructions=len(phases),phase_certificates=phase_certified,
                  all_mode_phase_pairs=[[r['gamma'],r['phase_half_width']] for r in phase_selected],
                  complete_kernel_fixture_checks=kernel_checks,
                  new_actual_source_evaluations=0,new_actual_prime_distribution_estimate=False,
                  preparation_operations=preparation,producer_operations=producer_work,
                  audit_operations=meter.operations-producer_work,total_operations=preparation+meter.operations,
                  peak_cells=meter.peak_cells,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  elapsed_seconds=time.monotonic()-start,
                  energy_contraction_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    verify_sources(directory)
    write(directory/'coordinate_recovery.json',dict(target=TARGET,coefficients=recovery,completeness=completeness))
    write(directory/'compiled_kernels.json',kernels)
    write(directory/'selected_auxiliaries.json',selected)
    write(directory/'selected_phase_auxiliaries.json',phase_selected)
    write(directory/'report.json',report)
    write(directory/'next_search_input.json',next_input(parent_input(),modes,recovery,selected,phase_selected,kernels))
    print(json.dumps(report),flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action',choices=['freeze','run'])
    parser.add_argument('directory')
    args = parser.parse_args()
    globals()[args.action](args.directory)
