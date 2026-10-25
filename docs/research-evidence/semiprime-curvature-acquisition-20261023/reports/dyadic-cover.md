# Exact dyadic quotient cover and carry-preserving consumer fold

22 October 2026. Let m=2^k, k>=2, H=m^2, M=m/2, and L=2m, so H=LM. Assume N is odd. This note gives elementary exact proofs. It does not acquire a new soft-m factoring query.

## 1. The quotient, kernel, and small-multiplier bijection

For odd c define

    q(c) = ((c^(m/2)-1)/(2m)) mod M.

The numerator is divisible by 2m. Repeated squaring gives

    v_2(c^(m/2)-1)=v_2(c^2-1)+k-2.

Thus q is well-defined on units modulo H, is a multiplicative-to-additive homomorphism, and has kernel

    c=+1 or -1 modulo 2m.

Indeed q(c)=0 exactly when v_2(c^2-1)>=k+2; since one of c-1,c+1 has valuation exactly one, the other must be divisible by 2^(k+1)=2m. The two residue classes each have H/(2m)=m/2 representatives modulo H, so the kernel has m elements and the quotient has M elements. Equivalently, q(5) is odd, so the homomorphism has full cyclic image Z/MZ.

There is no need for a prime-energy bound or a greedy cyclic cover. On

    C={c:1<=c<m, c odd},

q is a bijection onto Z/MZ. If q(c)=q(d), then c/d is in the kernel, hence c=+d or -d modulo 2m. The given ranges force c=d. Since |C|=M, injectivity proves bijectivity.

Consequently A={0} is an exact quotient cover. For every odd P there is a unique c in C with

    cP=+1 or -1 modulo L.

The covered catalog is simply S={s:s=+1 or -1 mod L}, represented modulo H. Thus this quotient cover is modular inversion up to sign, rather than a pseudorandomness phenomenon.

## 2. The two arithmetic progressions in the linear consumer

The inverse catalog B=-N/S modulo H consists of the two classes

    b=+N or -N modulo L.

Choose their representatives b0^+,b0^- in {1,...,L-1}. For either sign, enumerate

    b=b0+L*j,      0<=j<M.

These are ordinary positive representatives below H; centering is unnecessary for the O(m) bound. If cP=s mod H and b=-N/s mod H, then bc=-Q mod H, so

    bc+Q=H*sigma.

When P,Q are each within fixed multiples of m^3, c<m and b<H give sigma=O(m). The exact exponent consumer is

    beta^(N+bc) = (beta^H)^sigma modulo P,

because N-Q=Q(P-1). Put theta=beta^N, gamma=beta^L, and Q0=beta^H=gamma^M.

## 3. Exact carry fold for a fixed c

For odd c, multiplication by c permutes Z/MZ. Write

    c*j=M*u_c(v)+v,    0<=v<M,
    j_c(v)=[c^(-1)*v]_M,
    u_c(v)=(c*j_c(v)-v)/M.

Here 0<=u_c(v)<c. Then

    beta^(N+bc)-Q0^sigma
      =Q0^u_c(v) *
        (beta^(N+b0*c+L*v)-Q0^(sigma-u_c(v))).

This retains every carry. Replacing sigma-u_c(v) by an unshifted fixed interval is not an equality of products. An O(m)-sized enlarged interval contains all shifted intervals but inserts additional factors.

If tau=sigma-u_c(v), define

    z=M*tau-v.

Then the collision becomes

    beta^(N+b0*c)=gamma^z.

For tau in an O(m) interval and 0<=v<M, z lies in an O(m^2) interval. Moreover the exact candidate factor represented by this leaf is

    T=L*z-b0*c=H*sigma-b*c.

For a genuine covered prime leaf, T=Q. Thus the carry fold supplies a direct candidate decoder; it does not require reconstruction of the discarded j before checking T|N.

The two resulting geometric progressions have lengths O(m) and O(m^2). Ordinary blocking/baby-step–giant-step uses O(m^(3/2)) ring operations: a block of length m^(3/2) balances the long progression's block count against the m short nodes. A soft-m acquisition of this query is not established by the fold.

## 4. Stronger exact fold: all odd candidates are represented once

There is an exact way to avoid enlargement of intervals and identify what the catalog is doing. Fix any interval J of positive odd candidate factors T. Suppose throughout J, T=Theta(m^3). Every T in J has one and only one representation using the following data:

    sign branch b0=+N or -N mod L,
    odd c with 1<=c<m,
    0<=j<M,
    integer sigma,
    T=H*sigma-(b0+L*j)*c.

Proof/construction:

1. Because N is odd, -T/N modulo L is a unit. Each odd unit modulo L=2m is uniquely a sign times an odd c in [1,m). This selects the sign branch and c such that T+b0*c is divisible by L.
2. Set z=(T+b0*c)/L.
3. Choose the unique j=[-z*c^(-1)]_M.
4. Set sigma=(z+c*j)/M.

All are integers, and substituting gives the desired identity. The ranges imply |sigma|=O(m). Conversely any representation of T forces each of these choices, proving uniqueness.

Therefore the full dyadic catalog with the exact candidate-window filter is a radix parameterization of **all odd candidate factors in J**. In particular, each original difference equals

    beta^(N+bc)-beta^(H*sigma)
      =beta^(H*sigma)*(beta^(N-T)-1).

Since beta is a unit, the aggregate product over the exact window J is, up to a unit modulo N,

    product_(T odd in J) (beta^(N-T)-1).

This is one geometric-progression product of length Theta(m^3), not a new product of only O(m) factors. The reindexing preserves the original differences and their local vanishing. For restricted row subsets, however, the corresponding condition on T is the modular j(T) filter in the construction above; it is not generally a contiguous interval.

## 5. Public Euclidean relation does not remove a variable for free

Take the branch b0=-N mod L and define kappa=(N+b0)/L. For odd c=2d+1,

    N+b0*c-L*z = L*(kappa-z)+2*b0*d.

For a base of odd local order one may divide the exponent by two, obtaining the exact equivalent collision

    (beta^2)^(b0*d)=(beta^2)^(m*(z-kappa)).

The ranges are d=O(m) and z in an O(m^2) interval, but kappa is of size Theta(m^5). Extended Euclid for b0,m reindexes this integer linear form. It does not shorten the candidate T interval: Section 4 proves that the combined sign branches already enumerate every odd T in J once. Any improved algorithm must therefore do more than discard the public linear dependence among the bases.

This statement is not a lower bound on interval products or factoring. It identifies precisely the object a new algorithm would need to acquire.

## 6. Why the existing cyclic dyadic norm does not directly enumerate the GP

The paid constructor handles a single cyclic algebra X^a=Y and its roots-of-unity orbit. The AP step in b gives nodes gamma^j, 0<=j<M. Their M-th powers are

    (gamma^j)^M=Q0^j.

For the prepared odd local orders, Q0 has the same local order as beta, and these M monodromies are distinct. Thus these nodes do not lie in one fiber X^M=Y. A norm with one supplied Y cannot simply treat them as its conjugates. Allowing Y to vary as Q0^j is precisely an additional multi-point operation; no soft-m bound for that operation follows from the paid single-fiber norm theorem.

The binomial-polynomial special case of the constructor is allowed, but it changes neither this monodromy identity nor the carry shift in Section 3.

## 7. Finer dyadic and fixed-prime-power characters

The finer dyadic quotient

    q_f(c)=((c^(m/2)-1)/(2m)) mod m

has kernel c=+1 or -1 mod 4m and image Z/mZ. Its small odd set C has m/2 distinct quotient values. In fact Q_C and Q_C+m/2 partition Z/mZ: a difference m/2 would force c/d=+(1+2m) or -(1+2m) mod4m, impossible for 1<=c,d<m. Thus two fixed target values suffice, and their combined catalog is exactly the coarser kernel +/-1 mod2m. Greedy covering does not improve this structure.

For an odd fixed prime p, m=p^k, H=m^2, the quotient

    q_p(c)=((c^phi(m)-1)/m) mod m

is onto Z/mZ. Its kernel has (p-1)m/p elements: the p-1 Teichmuller classes modulo pm, each lifted m/p times. Taking A={j*m/p:0<=j<p} gives a trivial cover by multipliers 1<=c<m coprime to p, because q_p(c) modulo m/p is already surjective on those small units. The resulting catalog has p-1 arithmetic progressions of step m, each of length m. For fixed p this again admits the same candidate-residue radix interpretation. Letting p grow restores the larger Teichmuller component; it does not automatically provide a small structured exponent carrier.

## Outcome

The dyadic cover is exact, simpler, and admits a fully carry-preserving reduction. Its full balanced consumer is equivalent to a long interval geometric product with Theta(m^3) factors, for which the standard blocked query costs soft-m^(3/2). The existing roots-of-unity norm acquisition does not yet yield soft-m work for that product or its row restrictions. No new sixth-rate factoring claim follows.
