"""Factor-search entrypoint using the ACTUAL pinned-source layout constructor.

Only an accepted production guard enters the counter path. Finite guard failure
uses labelled trial division. Explicit resource caps return no result.
The frozen compiler, restriction policy and prefix recovery are imported intact.
"""
from pathlib import Path
from fractions import Fraction
import importlib.util
import sys
import argparse,json
from source_layout import construct_layout,frozen_counter,ResourceLimit,FROZEN
from source_parameters import scope_statistics,scheduled_guard


def frozen_factor_modules():
    directory=FROZEN.parent
    # Frozen factor_solver has ordinary sibling imports. Load those exact siblings
    # first and verify any pre-existing standard module names, avoiding shadowing.
    for name in ('factor_network','shared_parameters'):
        target=directory/(name+'.py')
        if name in sys.modules:
            if Path(sys.modules[name].__file__).resolve()!=target.resolve():
                raise ImportError('conflicting frozen sibling '+name)
        else:
            spec=importlib.util.spec_from_file_location(name,target)
            module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module)
    name='_source_frozen_factor_solver_20261026'
    if name not in sys.modules:
        spec=importlib.util.spec_from_file_location(name,directory/'factor_solver.py')
        module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module)
    return sys.modules['factor_network'],sys.modules[name]


def check_input_coverage(network):
    """Actual public input edges have designated hosts in unchanged local scopes."""
    L=network.parameters['L'];n=len(network.edges)
    for name in ('P','Q'):
        edges=network.input_bits[name]
        if len(edges)!=L or len(set(edges))!=L:raise ArithmeticError('input bit coverage failed')
        for edge in edges:
            if type(edge) is not int or not 0<=edge<n:raise ArithmeticError('invalid public input edge')
            vertex,port=network.hosts[edge]
            if network.vertices[vertex].ports[port]!=edge:raise ArithmeticError('input host is not original local port')
    return dict(public_bits_per_operand=L,covered=True,policy='frozen designated original endpoint restriction')


def recover_with_layout(network,layout,*,require_quantitative=True):
    """Reuse one layout for every actual-scope prefix count; no count oracle input."""
    _,solver=frozen_factor_modules();counter=frozen_counter()
    original=tuple(tuple(v.ports) for v in network.vertices);n=len(network.edges);calls=[]
    def contraction(restricted):
        scopes=tuple(tuple(v.ports) for v in restricted.vertices)
        if scopes!=original or len(restricted.edges)!=n:raise ArithmeticError('prefix changed original scopes')
        factors=tuple(counter.Factor(tuple(v.ports),v.entry) for v in restricted.vertices)
        result=counter.count(n,factors,layout,validate_design=True,require_quantitative=require_quantitative)
        value=Fraction(result.value)
        if value.denominator!=1 or value<0:raise ArithmeticError('count is not a nonnegative integer')
        calls.append(result.stats)
        return value.numerator
    factors,queries=solver.recover_from_counter(network,contraction)
    if queries>network.parameters['L']+1:raise ArithmeticError('prefix query bound failed')
    if factors is not None:
        p,q=factors
        if not 1<p<network.N or p*q!=network.N:raise ArithmeticError('final divisor check failed')
    return factors,queries,calls


def factor(N,*,max_dimension=None):
    if type(N) is not int or N<2:raise ValueError('N must be an integer at least two')
    if max_dimension is not None and (type(max_dimension) is not int or max_dimension<1):
        raise ValueError('positive auxiliary dimension cap required')
    compiler,solver=frozen_factor_modules();network=compiler.compile(N)
    coverage=check_input_coverage(network)
    scopes=tuple(tuple(v.ports) for v in network.vertices);stats=scope_statistics(len(network.edges),scopes)
    if not stats['covered'] or stats['M']!=2*stats['n'] or stats['B']!=2:
        raise ArithmeticError('actual network lost exact two-incidence coverage')
    p,guard=scheduled_guard(stats['n'],stats['M'],stats['B'],stats['w'])
    basic=dict(N=N,network=dict(n=stats['n'],M=stats['M'],B=stats['B'],w=stats['w']),input_coverage=coverage,guard=guard)
    if not guard['accepted']:
        factors=solver.direct_factor(N)
        return dict(basic,status='factored' if factors else 'no_nontrivial_factor',factors=factors,
                    method='explicit_invalid_guard_trial_division',count_queries=0)
    try:layout=construct_layout(stats['n'],scopes,p,require_guard=True,max_dimension=max_dimension)
    except ResourceLimit as exc:
        return dict(basic,status='resource_limit_no_result',factors=None,count_queries=0,
                    method='no_counter_or_trial_division_executed',reason=str(exc))
    factors,queries,calls=recover_with_layout(network,layout)
    return dict(basic,status='factored' if factors else 'no_nontrivial_factor',factors=factors,
                method='pinned_complete_bucket_layout_prefix_counter',count_queries=queries,
                layout_constructions=1,setup=layout.work.output(),counter_calls=calls)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('N',type=int);parser.add_argument('--max-universal-dimension',type=int)
    args=parser.parse_args()
    print(json.dumps(factor(args.N,max_dimension=args.max_universal_dimension),indent=2,default=str))

if __name__=='__main__':main()
