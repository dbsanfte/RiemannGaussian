"""Interpret saved058 relations and compile the exact next signed target.

No new matrix, source values, fitted constants, old study or hash. This
post-run interpretation does not change the frozen search or its ranking.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
import json

import run_prime_transfer_058 as RUN
from prime_transfer_search_058 import canonical, Meter


def read(name):
    return json.loads((RUN.OUT/name).read_text())


def main():
    destination = RUN.OUT/'mechanism_feedback.json'
    if destination.exists(): raise FileExistsError('preserve prior058 interpretation')
    meter = Meter()
    universe = read('grammar.json')['universe']
    atoms = read('grammar.json')['atoms']
    basis = read('inferred_relations.json')['relations']
    rows = read('proof_candidates.json')['rows']
    positions = {(tuple(a['primes']), a['divisor'], a['attenuation']): i for i,a in enumerate(atoms)}
    templates = {}
    for p in universe:
        others = [q for q in universe if q != p]
        for size in range(len(others)+1):
            for subset in combinations(others, size):
                forced = tuple(sorted(subset+(p,)))
                for attenuation in [1]+universe:
                    raw = {(forced, 1, attenuation): 1,
                        (subset, 1, attenuation): -1,
                        (subset, 1, attenuation*p): 1,
                        (forced, p, attenuation*p): -1}
                    key = canonical({positions[k]: c for k,c in raw.items()}, meter)
                    templates[key] = {'p': p, 'S': list(subset), 'attenuation': attenuation,
                        'unique_lower_column': positions[(forced, p, attenuation*p)]}
    basis_keys = [canonical({i:Q(c) for i,c in enumerate(b['coefficients'])}, meter) for b in basis]
    if set(basis_keys) != set(templates) or len(set(basis_keys)) != len(basis):
        raise ValueError('do not label a different nullspace as prime insertion')
    # Every template has its own lower column, so they are independent.
    # The saved exact rank/nullity certificate already proves spanning.
    if len({t['unique_lower_column'] for t in templates.values()}) != len(templates):
        raise ValueError('independence argument needs distinct lower pivots')
    classified = []
    for r in rows:
        row = r['candidate']; origin = row['origin']; indices = origin['basis_indices']
        target = canonical({t['column']:Q(t['coefficient']) for t in row['terms']}, meter)
        if origin['kind'] == 'basis':
            reconstructed = basis_keys[indices[0]]
        elif origin['kind'] == 'pair_current_elimination':
            a,b = (dict(basis_keys[i]) for i in indices); anchor = origin['anchor_column']
            reconstructed = canonical({k:b[anchor]*a.get(k,0)-a[anchor]*b.get(k,0)
                for k in a.keys() | b.keys()}, meter)
        else: raise ValueError('unknown saved origin')
        if target != reconstructed: raise ValueError('complete operator differs from recorded argument')
        classified.append({'id':row['id'], 'insertion_generators':[templates[basis_keys[i]] for i in indices],
            'complete_origin_reconstruction_equal':True})
    chosen = next(r for r in rows if r['interpretation'].get('R') == [2]
        and r['interpretation'].get('p') == 3 and r['interpretation'].get('q') == 5)
    endpoint = next(r for r in read('endpoint_programs.json')['rows']
        if r['id'] == chosen['candidate']['id'] and r['program']['request']['alpha'] == '1/5')
    if endpoint['verification']['both_end_region_bounds_proved'] is not True:
        raise ValueError('independently paid endpoints required')
    result = {'schema':'prime-transfer-mechanism-feedback-v1',
        'phase':'post-run exact interpretation; original ranking and archive preserved',
        'basis_classification':{'basis_count':len(basis), 'insertion_generator_count':len(templates),
            'basis_equals_all_degree_one_attenuated_prime_insertions':True,
            'template':'b^-t [H_(S+p)(x,t) -(1-p^-t)H_S(x,t) -p^-t H_(S+p)(x/p,t)] = 0',
            'scope':'this320-column finite-valuation polynomial signature only',
            'all_arithmetic_identities_classified':False},
        'operators_classified':classified,
        'origins':dict(Counter(r['candidate']['origin']['kind'] for r in rows)),
        'signed_lower_operators':sum(r['candidate']['signed_lower_terms'] for r in rows),
        'new_unexplained_identity_mechanisms':0,
        'interpretation_note':'unclassified_transfer_operator meant no exchange label, not novelty or independence',
        'all_operators_cancel_free_sector':all(r['proof_attempt']['free_sector_canceled'] for r in rows),
        'literal_closed_source_recurrences':sum(r['proof_attempt']['literal_self_state_recurrence'] for r in rows),
        'next_signed_target':{'operator_id':chosen['candidate']['id'],
            'reason':'same H6/H10 source pair as the refuted057 unweighted claim, now with a verified common-cofactor transfer',
            'current':'C(N,t)=(1-5^-t)H6(N,t)-(1-3^-t)H10(N,t)',
            'transfer':'C(N,t)=3^-t H30(N/3,t)-5^-t H30(N/5,t)',
            'source':'ordinary Mobius mu(d), every d coprime to30 within the complete range',
            'W':'W(x)=floor(4x)-3floor(2x)+2floor(x)',
            'joined_cofactor_identity':'C(N,t)=G30(t)*sum_(1<=d<=floor(4N/3),gcd(d,30)=1) mu(d)*d^-t*[3^-t W(N/(3d))-5^-t W(N/(5d))]',
            'G30':'(1-2^-t)*(1-3^-t)*(1-5^-t)',
            'd1_term_retained':True, 'real_argument_units_retained':True,
            'q_range_exit':'W(N/(5d))=0 when d>4N/5; keep the remaining p term',
            'alpha':endpoint['program']['request']['alpha'],
            'gamma':endpoint['program']['request']['gamma'], 'tau':'1/2',
            'epsilon':'min(1/2,N^(-5/28))',
            'normalization':'c_alpha=(alpha*I_alpha)^-1 as in051',
            'middle':'J(N)=c_alpha*integral_epsilon^(1/2) C(N,t)*t^(-1-alpha)dt',
            'bound_to_discover':'for every kappa>0, exists C_kappa<infinity independent of integerN>=2: |J(N)|<=C_kappa*N^(1/2+kappa)',
            'sufficient_stronger_target':'|J(N)|<=C*sqrt(N)*(log(2N))^A for fixed finite C,A',
            'paid_microscopic':endpoint['program']['microscopic'],
            'paid_tail':endpoint['program']['tail'],
            'conditional_RH_bridge':'PRIME_TRANSFER_REVIEW_058.txt section4; analytic review, conditional on the missing bound',
            'uniform_middle_bound_proved':False},
        'next_search_requirements':[
            'Search coupled inequalities or auxiliary recurrences for the joined ordinary-mu expression, retaining both scales inside the same sum.',
            'Use properties of the actual outside cofactor arithmetic: a provider invariant under replacing it by arbitrary numbers in[0,1] is insufficient.',
            'Keep all quotient-block boundaries, d1, real heads, prime powers and range exits.',
            'Record every correlation or source norm used as an obligation; a renamed target or unproved square-root Mobius estimate is not a paid leaf.',
            'Rank proved exponent/recurrence improvements before numerical constants or extra fixed-prime vanishing.',
            'Changing the prime triple alone gives the same signature and is not a new discovery experiment.'],
        'analysis_operations':meter.operations, 'scientific_matrix_repeated':False,
        'source_arrays_evaluated':False, 'hashes_used':False,
        'uniform_full_source_bound_proved':False, 'RH_proved':False}
    destination.write_text(json.dumps(result,indent=2)+'\n')
    return result


if __name__ == '__main__':
    result = main()
    print(json.dumps({'basis_classification':result['basis_classification'],
        'operators_classified':len(result['operators_classified']),
        'next_operator_id':result['next_signed_target']['operator_id'],
        'analysis_operations':result['analysis_operations']}))
