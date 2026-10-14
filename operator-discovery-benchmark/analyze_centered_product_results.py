"""Read-only arithmetic diagnostics of saved witnesses; no candidate retuning."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from flint import arb, ctx
import centered_product_fibers as P
from prime_bank_candidates import Meter


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    with path.open('x') as stream:
        json.dump(P.serialize(value), stream, indent=2, sort_keys=True)
        stream.write('\n')


def analyze(directory):
    ctx.prec = 192
    meter = Meter(100000, 60)
    report = read(directory / 'report.json')
    if report['status'] != 'CENTERED_PRODUCT_BAND_CANDIDATES_FINITELY_VERIFIED':
        raise ValueError('completed independent checks required')
    output = directory / 'witness_analysis_001'
    output.mkdir()
    script = Path(__file__)
    (output / script.name).write_bytes(script.read_bytes())
    grammar = {row['id']: row['coefficients'] for row in P.stencils()}
    selected = {(row['stencil_id'], row['gamma']) for row in report['selected']}
    rows = []
    for X in report['discovery_scales'] + report['validation_scales']:
        stage = 'discovery' if X in report['discovery_scales'] else 'validation'
        case = read(directory / (stage + '-' + str(X) + '.json'))
        N = case['search']['N']
        for candidate in case['search']['candidates']:
            pair = (candidate['stencil_id'], candidate['gamma'])
            if pair not in selected and candidate['stencil_id'] != 12:
                continue
            gamma = Fraction(candidate['gamma'])
            j = candidate['witness']['j']
            t = Fraction(candidate['witness']['t'])
            sectors = {key: arb(0) for key in P.SECTORS}
            bands = []
            for offset, coefficient in enumerate(grammar[pair[0]]):
                band = j - offset
                if band < 0 or not coefficient:
                    continue
                top = 1 << band
                high = min(N*N, (top*t.numerator)//t.denominator)
                low = top//2
                hi = case['queries'][str(high)][pair[1]]
                lo = case['queries'][str(low)][pair[1]]
                scale = coefficient*arb(top).root(6)**int(6*gamma)
                contribution = {}
                for key in P.SECTORS:
                    contribution[key] = scale*(arb(hi[key])-arb(lo[key]))
                    sectors[key] += contribution[key]
                    meter.charge(8)
                signed = sum(contribution.values(), arb(0))
                bands.append(dict(band=band, coefficient=coefficient,
                                  signed_contribution=signed))
                meter.charge(80)
            joint = sum(sectors.values(), arb(0))
            witness = arb(candidate['witness']['value'])
            if not P.tight(joint) or not joint.overlaps(witness):
                raise ArithmeticError('saved six-sector filtered witness must agree')
            if joint.contains(0):
                raise ArithmeticError('diagnostic ratio requires a nonzero witness')
            same_sign = (all(row['signed_contribution'] > 0 for row in bands) or
                         all(row['signed_contribution'] < 0 for row in bands))
            filter_ratio = sum((abs(row['signed_contribution']) for row in bands), arb(0))/abs(joint)
            center_ratio = sum((abs(v) for v in sectors.values()), arb(0))/abs(joint)
            rows.append(dict(X=X, stage=stage, stencil_id=pair[0], gamma=pair[1],
                             coefficients=grammar[pair[0]],
                             selected=pair in selected,
                             norm=arb(candidate['upper']),
                             original_energy=arb(case['diagnostics']['original_energy']),
                             recovered_energy_upper=arb(candidate['recovered_energy_upper']),
                             recovery_cost=arb(candidate['recovery_constant']),
                             witness=dict(j=j,t=str(t),bands=bands,sectors=sectors,joint=joint,
                                          all_band_contributions_same_sign=same_sign,
                                          sum_band_magnitudes_over_joint=filter_ratio,
                                          sum_sector_magnitudes_over_joint=center_ratio)))
            meter.charge(100)
    result = dict(
        status='SAVED_WITNESS_DECOMPOSITIONS_VERIFIED', rows=rows,
        interpretation={
            'equivalence': 'all admitted filters have the same cofinal uniform-band auxiliary up to logarithmic costs',
            'ranking_limitation': 'smallest finite norm slope need not improve recovered-energy bound or prove an exponent gain',
            'same_sign_scope': 'only the saved attaining witnesses; no assertion about all partial cutoffs',
            'followup': 'search for a signed arithmetic correlation mechanism and account for recovery before numerical ranking',
        },
        finite_results_retuned=False, new_source_evaluations=0,
        operations=meter.operations,
        combined_with_parent_operations=report['total_operations']+meter.operations,
        whole_signed_bound_proved=False, RH_proved=False,
    )
    write(output/'report.json',result)
    print(json.dumps(dict(rows=len(rows), operations=meter.operations,
                         selected_witnesses_same_sign=sum(r['selected'] and r['witness']['all_band_contributions_same_sign'] for r in rows))))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('directory',type=Path)
    args = parser.parse_args()
    analyze(args.directory)
