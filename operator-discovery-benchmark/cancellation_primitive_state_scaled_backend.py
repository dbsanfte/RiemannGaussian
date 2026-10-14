"""Reuse the verified full15 solvers with the extended arithmetic grammar bound.

Only result/checkpoint grammar metadata changes here. Complete input columns,
targets, shared weights, matrices, exact reconstruction and resource limits are
handled by the existing solvers and the independent localizer checker.
"""
import copy
import cancellation_primitive_state_scaled_synthesis as S
import cancellation_primitive_state_scaled_dual as D
import cancellation_affine_storage as A
import cancellation_primitive_state_localizers as L
import check_cancellation_primitive_state_localizers as C

prepare=S.prepare
compilation_charge=S.compilation_charge
instantiate_certificate=S.instantiate_certificate


def translated(value):
    out=copy.deepcopy(value)
    if 'grammar_hash' in out:
        if out['grammar_hash']!=S.digest(A.SPEC):raise ValueError('original full15 solver grammar')
        out['grammar_hash']=S.digest(L.SPEC)
    if out.get('proposal_checkpoint')is not None:
        out['proposal_checkpoint']=translated(out['proposal_checkpoint'])
    return out


def _run(kind,instances,blocks,storage,*,on_checkpoint=None,verification_callback=None,**limits):
    if on_checkpoint is not None and not callable(on_checkpoint):raise ValueError('optional bounded checkpoint callback')
    if verification_callback is not None and not callable(verification_callback):raise ValueError('optional independent checker callback')
    def emit(value):
        if on_checkpoint is not None:on_checkpoint(translated(value))
    def verify(ins,bs,ss,specs,value):
        method=verification_callback or getattr(C,'verify_'+kind)
        return method(ins,bs,ss,specs,translated(value))
    function=S.synthesize if kind=='primal' else D.propose
    result=function(instances,blocks,storage,on_checkpoint=emit if on_checkpoint is not None else None,
                    verification_callback=verify,**limits)
    return translated(result)


def synthesize(instances,blocks,storage,**limits):return _run('primal',instances,blocks,storage,**limits)
def propose(instances,blocks,storage,**limits):return _run('dual',instances,blocks,storage,**limits)
