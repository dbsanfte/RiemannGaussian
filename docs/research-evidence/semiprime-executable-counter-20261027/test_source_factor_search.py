"""Adapter/control tests, not a semiprime performance campaign."""
from types import SimpleNamespace
from fractions import Fraction as F
from unittest.mock import patch
import argparse,json
import source_factor_search as search
from source_layout import construct_layout,ResourceLimit
from source_parameters import Parameters


class TinyNetwork:
    """Diagnostic two-scope network, accepts original P bits representing 2 or 3."""
    def __init__(self,fixed=None):
        self.N=6;self.parameters={'L':3};self.edges=(0,1,2)
        self.input_bits={'P':(0,1,2),'Q':(0,1,2)};self.hosts=((0,0),(0,1),(0,2));self.fixed=dict(fixed or {})
        def first(bits):
            return int(sum(x<<i for i,x in enumerate(bits)) in (2,3) and all(bits[e]==v for e,v in self.fixed.items()))
        self.vertices=(SimpleNamespace(ports=(0,1,2),entry=first),SimpleNamespace(ports=(0,1,2),entry=lambda _:1))
    def restrict(self,fixed):return TinyNetwork(fixed)


def run():
    compiler,_=search.frozen_factor_modules();results=[]
    # Real compiled public-bit/host metadata, no expensive counter or factor search.
    network=compiler.compile(91);coverage=search.check_input_coverage(network)
    before=tuple(v.ports for v in network.vertices)
    fixed={edge:(7>>i)&1 for i,edge in enumerate(network.input_bits['P'])}
    restricted=network.restrict(fixed)
    assert tuple(v.ports for v in restricted.vertices)==before
    witness=network.witness(7,13);assert witness['valid']
    assert restricted.validate(witness['assignment'])['valid']
    assert all(sum(edge in v.ports for v in network.vertices)==2 for edge in network.input_bits['P'])
    results.append(dict(test='actual_compiler_input_coverage_and_same_scope_prefix',coverage=coverage,
                        edges=len(network.edges),supplied_witness_only=True))
    # Production guard failure must not allocate any layout.
    with patch.object(search,'construct_layout',side_effect=AssertionError('layout allocated before guard')):
        result=search.factor(91)
    assert result['method']=='explicit_invalid_guard_trial_division' and result['count_queries']==0
    assert result['factors']==(7,13)
    results.append(dict(test='production_guard_before_layout_explicit_trial_fallback',result=result))
    # Actual shared counter on a clearly diagnostic small source layout.
    tiny=TinyNetwork();p=Parameters(2,2,1,F(1,4));layout=construct_layout(3,((0,1,2),)*2,p,require_guard=False)
    factors,queries,calls=search.recover_with_layout(tiny,layout,require_quantitative=False)
    assert factors==(2,3) and queries==4 and len(calls)==4
    results.append(dict(test='diagnostic_actual_counter_prefix_recovery',factors=factors,queries=queries,
                        same_layout_reused=True,not_a_production_guard_fixture=True))
    # Exercise resource exit control with a synthetic accepted guard; not a claim
    # that any small actual network meets the strong schedule.
    with patch.object(search,'scheduled_guard',return_value=(p,{'accepted':True,'synthetic_control_only':True})),\
         patch.object(search,'construct_layout',side_effect=ResourceLimit('test explicit cap')):
        limited=search.factor(91,max_dimension=1)
    assert limited['status']=='resource_limit_no_result' and limited['factors'] is None and limited['count_queries']==0
    results.append(dict(test='synthetic_guard_resource_exit_no_counter_no_result',result=limited))
    return dict(status='PASS',scope='adapter and exact small diagnostic counter; no factoring benchmark',tests=results)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='factor-search-tests.json');args=parser.parse_args()
    result=run()
    with open(args.output,'w') as f:json.dump(result,f,indent=2)
    print(json.dumps(dict(status=result['status'],tests=len(result['tests']),output=args.output)))
