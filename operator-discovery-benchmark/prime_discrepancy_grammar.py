"""Periodic floor certificates, actual prime density and signed correlations."""
from fractions import Fraction as Q
from math import floor,lcm,ceil
import flint
from prime_error_grammar import real,serialize

VERSION="floor-density-and-signed-prime-discrepancy-energy-v1"


def carry_certificate(coefficients):
    c=list(map(Q,coefficients))
    if not c or c[0]!=1:raise ValueError("Normalize the unit-delay coefficient to one")
    drift=sum((v/(j+1) for j,v in enumerate(c)),Q(0))
    if drift:return {"status":"nonzero_linear_drift","drift":str(drift)}
    period=lcm(*(j+1 for j,v in enumerate(c) if v))
    cells=[sum(v*(k//(j+1)) for j,v in enumerate(c)) for k in range(period)]
    if min(cells)<0:return {"status":"negative_period_cell","cell":next(k for k,v in enumerate(cells) if v<0)}
    if cells[1]<1:raise ArithmeticError("The normalized unit-delay first cell was lost")
    entropy=-sum((real(v)/real(j+1)*real(j+1).log() for j,v in enumerate(c)),real(0))
    if not entropy>0:return {"status":"entropy_sign_unresolved"}
    S=sum(map(abs,c),Q(0))
    return {"status":"proved_nonnegative_periodic_carry","coefficients":list(map(str,c)),
            "period":period,"period_cells":list(map(str,cells)),"entropy_ball":serialize(entropy),
            "coefficient_cost":str(S),"unit_interval_coverage":["1","2"],
            "universal_domain":"every real u>=0","proof":"period drift is exactly zero and all half-open unit cells are nonnegative"}


def psi_prefix(f):
    result=[real(0)]
    for n,v in enumerate(f[1:],1):result.append(result[-1]+real(v)*real(n).log())
    return result


def density_certificate(certificate,psi,k):
    if certificate.get("status")!="proved_nonnegative_periodic_carry":raise ValueError("A proved full-period floor certificate is required")
    if k<4:raise ValueError("The tail monotonicity proof requires k>=4")
    threshold=2**(k-1)
    if threshold>=len(psi):raise ValueError("A complete initial prime-weight prefix is required")
    H=flint.arb(certificate["entropy_ball"]);S=real(certificate["coefficient_cost"])
    tail=4*H+2*S*(k+real(2).log()*real(Q(k*(k+1),2)))/2**k
    initial=max((psi[n]/n).upper() for n in range(1,threshold+1))
    top=max(tail.upper(),initial)
    C=Q(int((top*1024).ceil().fmpz()),1024)
    return {"constant":str(C),"tail_index":k,"initial_cutoff":threshold,
            "tail_constant_ball":serialize(tail),"initial_maximum_ball":serialize(initial),
            "uniform_prime_weight_bound":"psi(x)<=C*x for every real x>=1",
            "uniform_prime_weight_bound_proved":True,"RH_sufficient":False,
            "imported_prime_distribution_estimate":False}


def integer_error_values(f,beta):
    beta=Q(beta);counts=Q(0);values=[real(0)]*len(f)
    for n in range(1,len(f)):
        if n>=2:values[n]=real(n).log().ei()-real(beta*counts)
        counts+=f[n]
    return values


def increments(values):
    return [real(0)]+[values[n]-values[n-1] for n in range(1,len(values))]


def discrepancy_density(a,beta,psi_C,threshold):
    beta=Q(beta);threshold=int(threshold)
    if threshold<8 or threshold>=len(a):raise ValueError("A complete discrepancy prefix and threshold>=8 are required")
    squares=real(0);maximum=real(0)
    for n in range(1,threshold+1):
        squares+=a[n]*a[n]
        maximum=max(maximum,(squares*(flint.arb.const_e()+n).log()/n).upper())
    N=real(threshold);lnN=N.log();logN=(flint.arb.const_e()+N).log();ln2=real(2).log()
    tail=real(2).log().ei()**2*logN/N+2*(1/ln2**2+real(beta**2))*logN/N.sqrt()+8*logN/lnN**2+4*real(beta**2*Q(psi_C))*logN/lnN
    C=Q(int((max(tail.upper(),maximum)*1024).ceil().fmpz()),1024)
    return {"beta":str(beta),"constant":str(C),"initial_cutoff":threshold,
            "tail_majorant_ball":serialize(tail),"initial_maximum_ball":serialize(maximum),
            "uniform_coefficient_square_bound":"sum_(n<=N) a(n)^2 <= C*N/log(e+N), every integer N>=1",
            "all_scale_coefficient_square_bound_proved":True,"signed_pair_bound_proved":False}


def interpolate(values,t):
    t=Q(t)
    if t<=1:return real(0)
    n=t.numerator//t.denominator;u=t-n
    if n>=len(values) or (u and n+1>=len(values)):raise ValueError("The complete interpolation prefix is too short")
    return values[n] if not u else values[n]*(1-real(u))+values[n+1]*real(u)


def response(atoms,values,t):
    return sum((real(c)*interpolate(values,Q(t)/Q(d)) for d,c in atoms),real(0))


def complete_energy(atoms,values,X):
    X=Q(X);end=2*X
    boundaries={X,end}
    for d,c in atoms:
        d=Q(d)
        for n in range(floor(X/d)+1,ceil(end/d)):
            boundaries.add(d*n)
    points=sorted(boundaries);result=real(0)
    u=response(atoms,values,points[0])
    for left,right in zip(points,points[1:]):
        v=response(atoms,values,right)
        result+=real((right-left)/3)*(u*u+u*v+v*v)
        u=v
    return result


def square_prefix(a):
    count=[real(0)];weighted=[real(0)]
    for n,v in enumerate(a[1:],1):
        square=v*v;count.append(count[-1]+square);weighted.append(weighted[-1]+n*square)
    return count,weighted


def integrated(a,count,weighted,d,t,power):
    d,t=Q(d),Q(t);n=floor(t/d);r=t-d*n
    total=real(t)*count[n]-real(d)*weighted[n]+real(d/Q(power+1))*count[n]
    if r:total+=a[n+1]*a[n+1]*real(r**(power+1)/((power+1)*d**power))
    return total


def ramp_product(n,d,e,X):
    """Exact rational Gram entry for two scaled ramps, for independent checks."""
    d,e,X=map(Q,(d,e,X));points=sorted({X,2*X}|{v for v in (d*(n-1),d*n,e*(n-1),e*n) if X<v<2*X})
    def ramp(t,scale):return max(Q(0),min(Q(1),t/scale-(n-1)))
    result=Q(0)
    for l,r in zip(points,points[1:]):
        u,v,w,z=ramp(l,d),ramp(r,d),ramp(l,e),ramp(r,e)
        result+=(r-l)*(2*u*w+u*z+v*w+2*v*z)/6
    return result


def diagonal(atoms,a,count,weighted,X):
    X=Q(X);total=real(0)
    def square(d):return integrated(a,count,weighted,d,2*X,2)-integrated(a,count,weighted,d,X,2)
    def linear(d):return integrated(a,count,weighted,d,2*X,1)-integrated(a,count,weighted,d,X,1)
    for i,(d,c) in enumerate(atoms):
        d,c=Q(d),Q(c);total+=real(c*c)*square(d)
        for e,b in atoms[:i]:
            e,b=Q(e),Q(b);fast,slow=min(d,e),max(d,e)
            if fast==slow:
                total+=real(2*c*b)*square(d)
                continue
            cross=linear(slow)
            # Beyond this finite cutoff the fast ramp is already one
            # whenever the slower ramp is positive, so the product is slow.
            cutoff=ceil(slow/(slow-fast))
            for n in range(1,min(cutoff,len(a)-1)+1):
                actual=ramp_product(n,fast,slow,X)
                # The base expression integrates the slow ramp itself.
                def F(t):
                    y=Q(t)/slow-(n-1)
                    return Q(0) if y<=0 else (slow*y*y/2 if y<1 else slow*(y-Q(1,2)))
                old=F(2*X)-F(X)
                cross+=a[n]*a[n]*real(actual-old)
            total+=real(2*c*b)*cross
    return total


def off_diagonal_transfer(program,rho,gamma,B,coefficient_density):
    rho,gamma,B=map(Q,(rho,gamma,B))
    if gamma<0 or B<0:raise ValueError("Nonnegative defect exponent and cost are required")
    beta=Q(program["beta"])
    if not coefficient_density.get("all_scale_coefficient_square_bound_proved") or Q(coefficient_density["beta"])!=beta:
        raise ValueError("A matching actual-prime coefficient-density certificate is required")
    if not program["atoms"] or program["atoms"][0]!=["1","1"] or any(Q(d)<1 for d,c in program["atoms"]):
        raise ValueError("A normalized causal finite filter is required")
    eta=Q(gamma-1,2) if rho<=-1 else max(Q(1,2),Q(gamma-1,2))
    eta=max(eta,Q(0))
    if beta!=1 and eta<1:status="uniform_claim_ruled_out_by_pole_logarithm"
    elif beta==1 and eta<Q(1,2):status="uniform_claim_ruled_out_by_actual_critical_zero"
    elif beta==1 and eta<=Q(1,2):status="RH_sufficient_signed_correlation_obligation_missing_uniform_proof"
    else:status="signed_correlation_obligation_above_RH_threshold"
    S=sum((abs(Q(c)) for d,c in program["atoms"]),Q(0))
    return {"rho":str(rho),"gamma":str(gamma),"constant":str(B),"mellin_exponent":str(eta),
            "premise":"For every integer X>=1, C_off(X)<=rho*D(X)+B*X^gamma",
            "diagonal_coefficient":str(3*Q(coefficient_density["constant"])*S*S),
            "diagonal_bound":"D(X)<=diagonal_coefficient*X^2/log(e+X), every real X>=1",
            "all_scale_diagonal_bound_proved":True,"analytic_status":status,
            "RH_sufficient_if_uniform":beta==1 and eta<=Q(1,2),
            "ordinary_zero_bridge":"first-jet logarithmic meromorphic residue proof; isolated multiplier zeros allowed",
            "uniform_signed_correlation_premise_proved":False,"RH_proved":False}
