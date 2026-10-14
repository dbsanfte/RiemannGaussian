#!/usr/bin/env python3
"""Post-run generic root-semantics calibration; no discovery or reselection."""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import flint
from stable_scale_report import BASE,read,sha
from lattice_synthesis_report import summary
import lattice_synthesis_grammar as producer
import check_lattice_synthesis as independent


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run-dir',type=Path,required=True);args=parser.parse_args();d=args.run_dir.resolve();summary(d)
    destination=d/'fractional_root_calibration.json'
    if destination.exists():raise FileExistsError('Retain the semantic calibration')
    counts=defaultdict(int);cases=[];points=[Q(1),Q(17,3),Q(31)];shape=producer.shape([[0,1],[1,Q(-2,7)],[2,Q(1,11)]])
    for denominator in [2,3,6,10007]:
        params=['3',str(Q(1,denominator)),'5/4'];table=producer.complete_table(*params,'2',points,N=256,maximum_moment=2)
        native=independent.independent_table(table,points,counts);residues=producer.residues(shape,params);p={'shape':shape,'parameters':params,'residues':residues}
        res=independent.residues(p,counts);saved=producer.responses(shape,table,points,residues)
        checked=independent.observations(p,native,points,saved,res,counts)
        cert=producer.reference_decay(shape,params,Q(1,37));p['reference_decay_certificates']={'1/37':cert};independent.reference_check(p,{},counts)
        flint.ctx.prec=768
        for X,row in checked.items():assert abs(row['unit_two_residue_residual_ball'])<=flint.arb(cert['constant_ball'])*independent.powq(independent.a(X),Q(-1,37))
        cases.append({'root_order':denominator,'parameters':params,'shape':shape,'table':table,'residues':residues,'observations':saved,
            'reference_global_certificate':cert,'complete_independent_arithmetic_passed':True,'reference_global_witnesses_passed':True,
            'actual_critical_uniform_estimate_proved':False})
    result={'phase':'post_run_generic_semantic_calibration','source_protocol_sha256':sha(d/'protocol.json'),'source_verification_sha256':sha(d/'verification.json'),
        'calibrator_sha256':sha(BASE/'lattice_fractional_root_audit.py'),'producer_grammar_sha256':sha(BASE/'lattice_synthesis_grammar.py'),
        'independent_checker_sha256':sha(BASE/'check_lattice_synthesis.py'),'cases':cases,'counts':dict(counts),
        'square_cube_sixth_and_large_denominator_roots_checked':True,'selection_or_fitted_constants_changed':False,
        'new_fresh_discovery_claim':False,'no_expected_search_winner_asserted':True,'all_passed':True,'RH_proved':False}
    destination.write_text(__import__('json').dumps(result,indent=2)+'\n');print('Independent complete arithmetic calibrated for square, cube, sixth and 10007th roots.')


if __name__=='__main__':main()
