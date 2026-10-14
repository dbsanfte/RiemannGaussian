#!/usr/bin/env python3
"""Read-only costs at the new q values; no candidate repair or reselection."""
import argparse
from fractions import Fraction as Q
from pathlib import Path
import subprocess,sys
import flint
from stable_scale_report import BASE,read,sha,digest
from mellin_kernel_report import summary
from mellin_kernel_grammar import charged_cost


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);args=p.parse_args();d=args.run_dir.resolve()
    summary(d);spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json')
    bs={b['id']:b for b in batch['banks']};ps={p['id']:p for p in batch['programs']};qs=read(d/'parameter_cases.json')['fresh_q']
    constants={c['candidate_id']:c['constants'] for c in read(d/'parameter_calibration.json')['illustrative_free_constants']};flint.ctx.prec=spec['precision'];records=[]
    for c in arc['archive']:
        if not c['RH_sufficient_if_uniform']:continue
        b=bs[c['bank_id']];ids=b['member_ids']
        cost=charged_cost([ps[i]['kernel'] for i in ids],b['recovery_certificate'],*map(Q,b['parameters']),
            c['frontier'],constants[c['id']],qs,[batch['global_certificates'][i] for i in ids],spec['cost_query'])
        records.append({'candidate_id':c['id'],'bank_id':b['id'],'approach_power':c['frontier']['approach_power'],
            'training_observer_status':c['recovery_cost']['status'],'fresh_parameter_cost':cost})
    destination=d/'fresh_observer_costs.json'
    if destination.exists():raise FileExistsError('Retain observer diagnostic')
    output={'source_sha256':{n:sha(d/n) for n in ['protocol.json','archive.json','verification.json','parameter_cases.json','parameter_calibration.json','calibration_seal.json']},
        'audit_source_sha256':{n:sha(BASE/n) for n in ['mellin_kernel_observer_audit.py','check_mellin_kernel_observers.py']},
        'records':records,'q':qs,'selection_or_constants_changed':False,'no_new_fresh_validation_claim':True,
        'conditional_global_premises_still_unproved':True,'RH_proved':False}
    import json
    destination.write_text(json.dumps(output,indent=2)+'\n')
    subprocess.run([sys.executable,str(BASE/'check_mellin_kernel_observers.py'),'--run-dir',str(d)],check=True,cwd=BASE)


if __name__=='__main__':main()
