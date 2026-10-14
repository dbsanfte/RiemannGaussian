"""Independent fixed-kernel PNT obstruction for pure terminal-prime energy rays.

No producer import or numerical source query. This verifier imports the classical
PNT explicitly; exact finite kernel/fold algebra is independently reconstructed.
"""
from fractions import Fraction
import check_mobius_residual_fold_077 as F
from check_mobius_prime_storage_073 import AdmissionError,ResourceLimit,_rational,_add,_mul,_divide
PNT_REFERENCE='https://people.mpim-bonn.mpg.de/zagier/files/doi/10.2307/2975232/fulltext.pdf'
MAX_TERMS=100000
class Meter(F.Meter):pass

def _kernel(raw,m):
    if type(raw) is not list or len(raw)>MAX_TERMS:raise AdmissionError('invalid finite kernel')
    cost=4096
    for row in raw:
        if type(row) is not dict or set(row)!={'divisor','weight'}:raise AdmissionError('invalid kernel entry')
        F._integer(row['divisor'],'divisor',1,(1<<4096)-1)
        if type(row['weight']) is str:cost+=2048+4*len(row['weight'])
    m.reserve(32*cost);result={}
    for row in raw:
        d=row['divisor'];a=_rational(row['weight'],'kernel weight',m)
        new=_add(result.get(d,Fraction(0)),a,m)
        if new:result[d]=new
        else:result.pop(d,None)
    return result

def _saved(kernel):return [{'divisor':d,'weight':str(a)} for d,a in sorted(kernel.items())]
def _finish(out,m,error=None):
    if error is not None:
        out.update(status='INVALID',reason=str(error))
        if isinstance(error,ResourceLimit):out['resource_limit']=True
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_source_bound_proved=False,RH_proved=False,arithmetic_residual_refuted=False,uniform_bound_proved=False,finite_u_threshold_supplied=False)
    return out

def verify_kernel(base_kernel,source_program,derived_kernel):
    """Bind a generic source prefix kernel to a fixed-direct076 residual G-L.

    Input kernel is BEFORE excluded-prime coefficient folds. Full source program
    admission is separate; this verifies the exact fixed-kernel compilation.
    """
    import check_mobius_prime_moment_075 as S
    m=Meter();out={'status':'INVALID'}
    try:
        base=_kernel(base_kernel,m);actual=_kernel(derived_kernel,m)
        p=source_program
        if type(p) is not dict or not {'spec','atoms','operator'}<=set(p):raise AdmissionError('invalid source program')
        ts,ds=S.spec_parse(p['spec'],m);split=len(ts)-1;size=split+len(ds)
        atoms=p['atoms'];operator=p['operator']
        if type(atoms) is not list or type(operator) is not list or len(atoms)!=len(operator) or len(atoms)>MAX_TERMS:raise AdmissionError('invalid source atom/operator shape')
        m.reserve(4096+16384*(len(base)+len(actual)+len(atoms)))
        parsed=[];previous=None
        for atom,value in zip(atoms,operator):
            if type(atom) is not dict or set(atom)!={'column','gamma'}:raise AdmissionError('invalid source atom')
            column=F._integer(atom['column'],'column',0,size-1);gamma=_rational(atom['gamma'],'atom gamma',m);a=_rational(value,'operator',m)
            if gamma<0:raise AdmissionError('negative count exponent')
            key=(column,gamma)
            if previous is not None and key<=previous:raise AdmissionError('source atoms must be sorted unique')
            previous=key;parsed.append((column,gamma,a))
        if any(column<split and a for column,gamma,a in parsed):
            out.update(status='UNSUPPORTED',reason='active prime-block source operator is outside fixed-direct kernel grammar')
            return _finish(out,m)
        planned=len(base)*(1+sum(bool(a) for column,gamma,a in parsed))
        if planned>MAX_TERMS:raise ResourceLimit('prospective derived kernel term gate')
        m.reserve(4096+32768*planned);expected=dict(base)
        for column,gamma,a in parsed:
            if not a:continue
            dilation=ds[column-split]
            for d,weight in base.items():
                divisor=d*dilation
                if divisor.bit_length()>100000:raise ResourceLimit('derived divisor bit gate')
                coefficient=-_mul(a,weight,m)
                new=_add(expected.get(divisor,Fraction(0)),coefficient,m)
                if new:expected[divisor]=new
                else:expected.pop(divisor,None)
        if expected!=actual:raise AdmissionError('fixed-direct derived kernel mismatch')
        out.update(status='VERIFIED_FIXED_KERNEL',normalized_base_kernel=_saved(base),normalized_derived_kernel=_saved(expected),source_program_admission_still_required=True,kernel_is_before_excluded_prime_folds=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

def _energy(program,m):
    keys={'schema','q','tau','rays','innovation_C'}
    if type(program) is not dict or set(program)!=keys or program['schema']!='rough-energy-program-v1':raise AdmissionError('invalid energy schema')
    q=_rational(program['q'],'q',m);tau=_rational(program['tau'],'tau',m);C=_rational(program['innovation_C'],'C',m)
    if not 1<=q<2 or not 0<=tau<=1 or C<0:raise AdmissionError('invalid q/tau/C')
    if type(program['rays']) is not list or len(program['rays'])>1024:raise AdmissionError('invalid rays')
    m.reserve(4096+131072*len(program['rays']));rays=[]
    for ray in program['rays']:
        if type(ray) is not dict or set(ray)!={'a','eta','lambda'} or type(ray['a']) is not list or len(ray['a'])!=10:raise AdmissionError('invalid ray')
        a=[_rational(x,'ray coefficient',m) for x in ray['a']];eta=_rational(ray['eta'],'eta',m);weight=_rational(ray['lambda'],'lambda',m)
        if eta<0 or weight<=0 or all(x==a[0] for x in a):raise AdmissionError('invalid zero/projection-only ray or eta/lambda')
        rays.append((a,eta,weight))
    return q,tau,rays

def verify_prime_mass_gate(kernel,excluded_primes,gamma,energy_program,certificate):
    """Admit an eventual PNT obstruction, never a finite-scale counterexample."""
    m=Meter();out={'status':'INVALID','uniform_drift_obstructed':False}
    try:
        normalized=_kernel(kernel,m);P=F._primes(excluded_primes,m)
        if type(excluded_primes) is not list or list(P)!=sorted(P):raise AdmissionError('excluded primes must be sorted list')
        g=_rational(gamma,'gamma',m)
        if not 0<g<1:raise AdmissionError('prime mass gate requires0<gamma<1')
        q,tau,rays=_energy(energy_program,m)
        keys={'mass','delta','leading_prime','sigma','eventual_lower_coefficient','ray_index'}
        if type(certificate) is not dict or set(certificate)!=keys:raise AdmissionError('invalid exact prime-mass certificate schema')
        mass=Fraction(0)
        for d,a in normalized.items():mass=_add(mass,_divide(a,Fraction(d),m),m)
        if not mass:
            out.update(status='UNSUPPORTED',reason='zero kernel first moment; no leading-prime obstruction admitted')
            return _finish(out,m)
        index=F._integer(certificate['ray_index'],'ray index',0,max(0,len(rays)-1))
        if not rays or index>=len(rays):
            out.update(status='UNSUPPORTED',reason='no active pure-prime ray')
            return _finish(out,m)
        a,eta,weight=rays[index]
        if not a[1] or any(value for j,value in enumerate(a) if j!=1):
            out.update(status='UNSUPPORTED',reason='selected ray is not a pure terminal-prime coordinate')
            return _finish(out,m)
        sigma=_add(_add(Fraction(2),-_mul(Fraction(2),eta,m),m),-q,m)
        if sigma<=0:
            out.update(status='UNSUPPORTED',reason='selected eta is not under the strict critical exponent')
            return _finish(out,m)
        delta=Fraction(1)
        for p in P:delta=_mul(delta,Fraction(p-1,p),m)
        leading=-_mul(mass,delta,m);amplitude=_mul(a[1],leading,m)
        lower=_divide(_mul(weight,_mul(amplitude,amplitude,m),m),Fraction(4),m)
        expected={'mass':mass,'delta':delta,'leading_prime':leading,'sigma':sigma,'eventual_lower_coefficient':lower}
        for key,value in expected.items():
            if _rational(certificate[key],key,m)!=value:raise AdmissionError('prime-mass certificate '+key+' mismatch')
        out.update(status='VERIFIED_PRIME_MASS_OBSTRUCTION',uniform_drift_obstructed=True,normalized_kernel=_saved(normalized),**{key:str(value) for key,value in expected.items()},ray_index=index,imported_theorem={'name':'Classical Prime Number Theorem','statement':'pi(x)~x/log(x)','source':'D. Zagier, Newmans Short Proof of the Prime Number Theorem, American Mathematical Monthly104(1997),705-708','url':PNT_REFERENCE},kernel_is_before_excluded_prime_folds=True,cutoff_gamma=str(g),q=str(q),tau=str(tau),eventual_energy_lower='E(u)/u^q >= eventual_lower_coefficient*u^sigma/(log u)^2 for all sufficiently large integer u',scope='fixed pure-prime energy ray obstructs all-integer constant dyadic drift with finite base; signed arithmetic residual and RH unrefuted')
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

verify_gate=verify_prime_mass_gate
