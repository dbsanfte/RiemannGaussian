"""Post-design detector/checker integration, algebra only; no source mu queries."""
from pathlib import Path
from fractions import Fraction as Q
import json,time,traceback
import mobius_dense_rank_obstruction_082 as P
import check_mobius_dense_rank_obstruction_082 as C

def audit():
    kernels=[[{'divisor':4,'weight':'-1'},{'divisor':5,'weight':'1'},{'divisor':8,'weight':'1'},{'divisor':10,'weight':'-1'}]]
    kernels.append(sorted(kernels[0]+[{'divisor':12,'weight':'-3547/8192'},{'divisor':15,'weight':'3547/8192'},{'divisor':24,'weight':'3547/8192'},{'divisor':30,'weight':'-3547/8192'}],key=lambda x:x['divisor']))
    families=[[(Q(1,4),Q(1))],[(Q(1,4),Q(1)),(Q(1,5),Q(1)),(Q(1,8),Q(1)),(Q(1,10),Q(1))],[(Q(1,4),Q(1)),(Q(1),Q(3,7)),(Q(1),Q(7,11)),(Q(1,2),Q(10,13))],[(Q(1,4),Q(1)),(Q(1,12),Q(1)),(Q(1,20),Q(1)),(Q(1,28),Q(1))]]
    cases=[]
    for source,kernel in enumerate(kernels):
        for depth in [1,2,3]:
            rays=[]if depth==1 else [dict(a=['1']*depth if depth==2 else ['1','1','-1'],weight='1/4'if depth==2 else '1')]
            for family,profiles in enumerate(families):
                program=dict(schema='dense-divisor-completion-v1',kernel=kernel,memory=depth,rays=rays,drift_multiplier='3/2',profiles=[dict(scale=str(s),eta=str(e))for s,e in profiles],theta=[['0']*(depth+1)for _ in profiles],gram_weights=['0']*(depth+1+len(profiles)))
                discovery=P.discover(program)
                # Only declared effective certificate is admitted, not search existence.
                certificate=discovery['certificate']
                verdict=C.verify_obstruction(program,certificate)
                assert verdict['status']=='VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION',verdict
                cases.append(dict(source=source,memory=depth,family=family,certificate=certificate,admission=verdict))
    return dict(status='PASS',cases=cases,case_count=len(cases),actual_arithmetic_drift_refuted=False,uniform_original_source_bound_proved=False,RH_proved=False,scientific_source_queries=False,old_tests_run=False,hashes_used=False)
if __name__=='__main__':
    start=time.monotonic()
    try:result=audit()
    except Exception:result=dict(status='FAIL',traceback=traceback.format_exc())
    result['elapsed_seconds']=time.monotonic()-start
    p=Path('mobius_dense_rank_obstruction_independent_audit_082.json')
    if p.exists():p=Path('mobius_dense_rank_obstruction_independent_audit_082_attempt_'+str(time.time_ns())+'.json')
    with p.open('x')as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(p,result['status']);print(result.get('traceback',''))
