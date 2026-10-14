"""Prime-local producer for exact divisor preconditioning of the full source."""
from fractions import Fraction as Q
from flint import arb,ctx


def convolution(left,right,H,meter):
    out=[arb(0)]*(H+1)
    for d in range(1,H+1):
        meter.charge()
        if left[d].is_zero():continue
        value=left[d]
        for k in range(1,H//d+1):
            out[d*k]+=value*right[k]
            meter.charge(3)
    return out


def _scalar(value):
    value=Q(value)
    return arb(value.numerator)/value.denominator


def _local_series(factors,root,length,meter):
    values=[arb(0)]*length
    values[0]=arb(1)
    log_derivative=[arb(0)]*length
    for j in range(1,length):
        for shift,exponent in factors:
            power=6*Q(shift)
            if power.denominator!=1:raise ValueError('sixth-root shift lattice')
            log_derivative[j]+=_scalar(exponent)/root**(int(power)*j)
            meter.charge(12)
        values[j]=sum((log_derivative[k]*values[j-k] for k in range(1,j+1)),arb(0))/j
        meter.charge(4*j+2)
    return values


def prepare(state,program,meter):
    H=state['H'];v,r=Q(program['shift']),Q(program['power'])
    if (6*v).denominator!=1 or not program['recovery']['cofinal']:
        raise ValueError('declared recoverable sixth-root preconditioner')
    if any(len(state[key])!=H+1 for key in ('a','d','tilde_b','spf')):
        raise ValueError('complete original source with all prime powers')
    kernel=[arb(0)]*(H+1);inverse=[arb(0)]*(H+1)
    kernel[1]=inverse[1]=arb(1)
    mode_arrays={term['name']:[arb(0)]*(H+1) for term in program['terms']}
    for values in mode_arrays.values():values[1]=arb(1)
    exponents=[0]*(H+1);cores=[0]*(H+1);cores[1]=1
    locals_by_prime={}
    meter.live(state.get('_resident_cells',14*(H+1))+18*(H+1)+4096)
    for p in state['primes']:
        length=1;power=p
        while power<=H:
            length+=1;power*=p;meter.charge(2)
        root=arb(p).root(6);weight=1/root**int(6*v);meter.charge(70)
        forward=[arb(1)];backward=[arb(1)];binomial_f=binomial_b=Q(1)
        for e in range(1,length):
            binomial_f*=-(r-e+1)/e
            binomial_b*=-(-r-e+1)/e
            forward.append(_scalar(binomial_f)*weight**e)
            backward.append(_scalar(binomial_b)*weight**e)
            meter.charge(18)
        modes={term['name']:_local_series(term['zeta_factors'],root,length,meter)
               for term in program['terms']}
        locals_by_prime[p]=(forward,backward,modes)
    for n in range(2,H+1):
        p=state['spf'][n];previous=n//p
        if previous%p==0:
            exponents[n]=exponents[previous]+1;cores[n]=cores[previous]
        else:
            exponents[n]=1;cores[n]=previous
        e,core=exponents[n],cores[n]
        forward,backward,modes=locals_by_prime[p]
        kernel[n]=kernel[core]*forward[e];inverse[n]=inverse[core]*backward[e]
        for name,values in mode_arrays.items():values[n]=values[core]*modes[name][e]
        meter.charge(16+2*len(mode_arrays))
    w=convolution(kernel,state['tilde_b'],H,meter)
    d_image=convolution(state['d'],kernel,H,meter)
    beta=arb(9)/2
    source_scalars={'beta':beta,'-beta':-beta,'-R_u':-state['R_u']}
    correction=[arb(0)]*(H+1);core=[arb(0)]*(H+1)
    prefix=[arb(0)]*(H+1);core_prefix=[arb(0)]*(H+1);correction_prefix=[arb(0)]*(H+1)
    mode_prefixes={name:[arb(0)]*(H+1) for name in mode_arrays}
    norm_w=[arb(0)]*(H+1);mass_f=[arb(0)]*(H+1);mass_b=[arb(0)]*(H+1)
    for n in range(1,H+1):
        correction[n]=beta*kernel[n]-d_image[n]
        core[n]=sum((source_scalars[term['coefficient']]*mode_arrays[term['name']][n]
                     for term in program['terms']),arb(0))
        if not (w[n]-core[n]-correction[n]).contains(0):
            raise ArithmeticError('entire unit/prime-power correction must be retained')
        prefix[n]=prefix[n-1]+w[n]
        core_prefix[n]=core_prefix[n-1]+core[n]
        correction_prefix[n]=correction_prefix[n-1]+correction[n]
        for name,values in mode_arrays.items():mode_prefixes[name][n]=mode_prefixes[name][n-1]+values[n]
        norm_w[n]=norm_w[n-1]+prefix[n]**2/(n*(n+1))
        root=arb(n).sqrt()
        mass_f[n]=mass_f[n-1]+abs(kernel[n])/root
        mass_b[n]=mass_b[n-1]+abs(inverse[n])/root
        meter.charge(105)
    meter.live(state.get('_resident_cells',14*(H+1))+26*(H+1)+4096)
    return dict(H=H,precision=ctx.prec,kernel=kernel,inverse=inverse,w=w,prefix=prefix,
                modes=mode_arrays,mode_prefixes=mode_prefixes,core=core,core_prefix=core_prefix,
                correction=correction,correction_prefix=correction_prefix,
                weighted_norm_w=norm_w,forward_mass=mass_f,inverse_mass=mass_b,
                uniform_signed_bound_proved=False,RH_proved=False)


def query(X,state,transformed,tables,program,meter):
    N=2*X-1
    if N>state['H'] or transformed['precision']!=ctx.prec:
        raise ValueError('complete block at original precision')
    W,F,P=transformed['prefix'],transformed['core_prefix'],transformed['correction_prefix']
    energy_w=energy_f=energy_p=cross=arb(0)
    names=[term['name'] for term in program['terms']]
    gram=[[arb(0)]*len(names) for _ in names]
    for n in range(X,N+1):
        energy_w+=W[n]**2;energy_f+=F[n]**2;energy_p+=P[n]**2;cross+=2*F[n]*P[n]
        for i,left in enumerate(names):
            for j in range(i,len(names)):
                gram[i][j]+=transformed['mode_prefixes'][left][n]*transformed['mode_prefixes'][names[j]][n]
        meter.charge(28+3*len(names)*(len(names)+1)//2)
    for i in range(len(names)):
        for j in range(i,len(names)):
            gram[i][j]/=X*X
            gram[j][i]=gram[i][j]
    energy_w/=X*X;energy_f/=X*X;energy_p/=X*X;cross/=X*X
    if not (energy_w-energy_f-energy_p-cross).contains(0):
        raise ArithmeticError('preconditioned core/correction cross')
    # This is a finite consistency check for the separately proved Minkowski bounds.
    norm_t=sum((tables['tilde_R'][n]**2/(n*(n+1)) for n in range(1,N+1)),arb(0))
    norm_w=transformed['weighted_norm_w'][N]
    forward=transformed['forward_mass'][N];backward=transformed['inverse_mass'][N]
    if norm_w.lower()>(forward**2*norm_t).upper() or norm_t.lower()>(backward**2*norm_w).upper():
        raise ArithmeticError('finite truncated critical-norm recovery consistency')
    meter.charge(5*N+200)
    return dict(X=X,energy_w=energy_w,energy_core=energy_f,energy_correction=energy_p,
                core_correction_cross=cross,mode_names=names,mode_gram=gram,
                critical_norm_tilde=norm_t,critical_norm_w=norm_w,
                forward_mass=forward,inverse_mass=backward,
                complete_source_recovered_conditionally=True,
                signed_core_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)
