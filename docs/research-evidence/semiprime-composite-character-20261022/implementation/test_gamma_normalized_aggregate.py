"""Exact normalized Gauss controls; factored inputs occur only in the oracle."""
import argparse
import json
from math import gcd
from pathlib import Path
from composite_gauss_aggregate import load_packed, rows
from gamma_normalized_aggregate import (acquire_normalized, ce_inverse,
                                        expand_normalized_pair_for_test)
from test_composite_gauss_aggregate import field_primes, generator, evaluate


def run(repo_root):
    frozen = load_packed(repo_root)
    counts = dict(parameter_cases=0, character_components=0, proper_divisor_components=0,
                  direct_pair_checks=0, whole_checks=0, weighted_checks=0,
                  inverse_vector_checks=0, inverse_component_checks=0,
                  public_factor_checks=0, saturation_checks=0, negative_E_checks=0, even_order_rejections=0)
    max_degree = 0
    for m, ell, t in ((3,7,2), (9,19,2), (15,31,3), (9,37,5)):
        p, q = field_primes(m*ell)
        N = p*q
        assert gcd(t,N) == 1
        out = acquire_normalized(N,ell,m,t,repo_root)
        assert out['status'] == 'NORMALIZED_AGGREGATE'
        assert out['counts']['expanded_pair_vectors'] == 0
        pg = frozen.PackedGauss(N,ell,m)
        unit_rows = rows(N,m)
        exponents = sorted(set((0,1,2,3,m,2*m,N)))
        quotient_inverses = []
        for E in exponents:
            CE = pg.quotient(E)
            inv = ce_inverse(pg,E,CE)
            assert pg.mul(CE,inv) == pg.one()
            assert inv == ce_inverse(pg,E)
            quotient_inverses.append((E,CE,inv))
            counts['inverse_vector_checks'] += 1
        for field in (p,q):
            g = generator(field,frozen)
            zm = pow(g,(field-1)//m,field)
            ze = pow(g,(field-1)//ell,field)
            for character in range(m):
                z = pow(zm,character,field)
                gauss = [sum(pow(z,tag*pg.logs[x],field)*pow(ze,x,field)
                             for x in range(1,ell)) % field for tag in range(m)]
                hs = [t*gauss[tag]*pow(gauss[-tag % m],-1,field) % field
                      for tag in range(m)]
                targets, weighted = {}, 1
                for row in unit_rows:
                    j,a = row['j'],row['a']
                    targets[j] = (pow(hs[1],row['ell'],field)*pow(hs[j],a,field)
                                  *pow(hs[pow(j,-1,m)],N,field)) % field
                    Aj = pow(hs[1],j,field)*pow(hs[j],-1,field) % field
                    weighted = weighted*pow(Aj,a,field) % field
                whole = 1
                for value in targets.values():
                    whole = whole*value % field
                assert evaluate(out['whole'],z,field) == whole
                assert evaluate(out['weighted_A'],z,field) == weighted
                assert evaluate(out['V'],z,field) == pow(hs[1],m,field)
                assert evaluate(out['qh'],z,field) == pow(hs[1],m*m,field)
                assert evaluate(out['V_inverse'],z,field)*evaluate(out['V'],z,field) % field == 1
                assert evaluate(out['qh_inverse'],z,field)*evaluate(out['qh'],z,field) % field == 1
                for pair in out['pairs']:
                    expected = targets[pair['j']]*targets[pair['opposite']] % field
                    assert evaluate(expand_normalized_pair_for_test(out,pair),z,field) == expected
                    counts['direct_pair_checks'] += 1
                for E,CE,inv in quotient_inverses:
                    direct_CE = pow(gauss[1],E,field)*pow(gauss[E % m],-1,field) % field
                    assert evaluate(CE,z,field) == direct_CE
                    assert evaluate(inv,z,field) == pow(direct_CE,-1,field)
                    counts['inverse_component_checks'] += 1
                counts['character_components'] += 1
                counts['whole_checks'] += 1
                counts['weighted_checks'] += 1
                if 1 < m//gcd(character,m) < m:
                    counts['proper_divisor_components'] += 1
        counts['parameter_cases'] += 1
        max_degree = max(max_degree,m-1)
    for N,ell,m,t in ((101*103,19,9,101), (15,31,15,2)):
        result = acquire_normalized(N,ell,m,t,repo_root)
        assert result['status'] == 'PUBLIC_FACTOR'
        assert 1 < result['factor'] < N and N % result['factor'] == 0
        counts['public_factor_checks'] += 1
    for t in (0,101*103,-101*103):
        result = acquire_normalized(101*103,19,9,t,repo_root)
        assert result['status'] == 'SATURATED_PUBLIC_UNIT'
        counts['saturation_checks'] += 1
    try:
        ce_inverse(frozen.PackedGauss(101*103,19,9),-1)
    except ValueError:
        counts['negative_E_checks'] += 1
    else:
        raise AssertionError('negative quotient exponent accepted')
    try:
        ce_inverse(frozen.PackedGauss(101*103,7,2),1)
    except ValueError as exc:
        assert 'odd character order' in str(exc)
        counts['even_order_rejections'] += 1
    else:
        raise AssertionError('even-order inverse contract accepted')
    return dict(status='PASS',counts=counts,max_packed_degree=max_degree,
                core_expanded_pair_vectors=0,
                scope='exact conventions/exceptions, not coverage or certified runtime')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root',required=True)
    parser.add_argument('--json-out')
    args = parser.parse_args()
    text = json.dumps(run(args.repo_root),indent=2,sort_keys=True)
    print(text)
    if args.json_out:
        Path(args.json_out).write_text(text+'\n')
