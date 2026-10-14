"""Independent original-polynomial/PSD audit of the fixed-support native retry."""
import json
import sys
from pathlib import Path
from fractions import Fraction as Q
import check_cancellation_arithmetic_run as B
import check_cancellation_factor_search as F
import check_cancellation_gram as G

EXTRA=['run_cancellation_factor_native_dual.py','check_cancellation_factor_native_dual.py',
       'native_exact_support.py','test_native_exact_support.py']


def audit(parent):
    parent=Path(parent); original=parent/'factor-probe-001'; d=original/'native-dual-001'
    names=['protocol','source_seal','seal','tests','result','producer_receipt']
    hashes={n:B.sha(d/(n+'.json')) for n in names}
    spec=B.read(d/'protocol.json'); output=B.read(d/'result.json'); dual=output['dual']
    def binding():
        B.require(B.read(d/'seal.json')==dict(protocol_sha256=B.sha(d/'protocol.json'),source_seal_sha256=B.sha(d/'source_seal.json')),'seal')
        src=B.read(d/'source_seal.json')['hashes'];B.require(set(src)==set(EXTRA),'source coverage')
        for n,h in src.items():B.require(B.sha(Path(__file__).parent/n)==h and B.sha(d/'frozen_source'/n)==h,'native source '+n)
        for n,h in B.read(original/'source_seal.json')['hashes'].items():B.require(B.sha(Path(__file__).parent/n)==h and B.sha(original/'frozen_source'/n)==h,'original source '+n)
        B.require(spec['inputs_sha256']=={n:B.sha(original/(n+'.json')) for n in ['dual','training','source_seal','independent_verification']},'inputs')
    binding()
    B.require(B.read(original/'independent_verification.json')['all_passed'],'original independent verification')
    old=B.read(original/'dual.json')['result']
    B.require(old['status']=='missing_resource' and spec['saved_support']==old['diagnostics']['support'],'preserved original support/failure')
    B.require(spec['training_scales']==[1,2,3,5] and spec['program']==B.read(original/'protocol.json')['programs'][0],'unchanged original program')
    B.require(output['saved_support_sha256']==B.digest(spec['saved_support']),'support binding')
    instances=[F.build(spec['program'],X)['instance'] for X in [1,2,3,5]]+[F.auxiliary()['instance']]
    if dual.get('certified'):
        B.require(output['case_hashes']==list(map(B.digest,instances)),'complete exact original cases')
        G.verify_dual(instances,[1,2,3,5],dual)
        y={(r['instance'],tuple(r['m'])):Q(w) for r,w in zip(dual['monomials'],dual['weights'])}
        constants=[str(y.get((i,()),Q(0))) for i in range(5)]
        B.require(dual['ordinary_constant_coordinates']==constants[:4],'constant coordinates')
    else:
        B.require(dual['status'] in ['missing_resource','uncertified'],'unproved result')
        constants=None
    B.require(B.read(d/'tests.json')['returncode']==0,'native tests')
    for n in ['result','tests','protocol','source_seal']:B.require(B.read(d/'producer_receipt.json')[n+'_sha256']==hashes[n],'receipt')
    B.require(output['RH_proved'] is False and output['global_bound_proved'] is False,'no global admission')
    binding();B.require(hashes=={n:B.sha(d/(n+'.json')) for n in names},'end hashes')
    return dict(all_passed=True,input_sha256=hashes,status=dual['status'],certified=dual.get('certified',False),
                constant_dual_coordinates=constants,global_bound_proved=False,RH_proved=False)


if __name__=='__main__':
    p=Path(sys.argv[1]);r=audit(p)
    with (p/'factor-probe-001/native-dual-001/independent_verification.json').open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps(r))
