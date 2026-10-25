# Arithmetic selection: root review and scope

23 October 2026. This checkpoint does not acquire a soft-r collision
query, a factor witness in that bound, or an improved factoring exponent.
The source construction from the preceding checkpoint remains valid.
Here r=Theta(N^(1/6)), H=r^2, M=r^4 and P,Q>16H, so N>256M.

## Exact identities checked independently

The integral gauge is a leafwise equality. For an observed pair (a,b),
where b is the residue of B modulo 2a rather than the original quadratic
row's middle coefficient, put

    t=(B-b)/(2a), d_b=M^(-1)b^2 mod 4a,
    e=(b^2-M*d_b)/(4a), k=(D-d_b)/(4a).

The public inverse exists because a<r and r is odd. Since
B^2-4aCN=M*D, all displayed quotients are integers. Direct expansion gives

    a(c+t)^2+b(c+t)+e-M*(sigma+k)
      =a*c^2+B*c+CN-M*sigma.

Thus the exact intervals translate to j=t+[1,r-1] and
tau=k+[-4r,4r]. No collision factor is inverted or discarded. In the
monic branch there are two possible b values. The original carry has
become an explicit interval translation, not disappeared.

For two rows in one (a,b) branch, B=-2a mod r implies t'-t is a nonzero
multiple of r. Equality of B would force equality of C, using the
congruence modulo M and |C-C'|<M. Moreover

    M*(k'-k)=(B+B')*(t'-t)/2-N*(C'-C),
    |k'-k|+|t'-t|/2 >= N*r/M >256r.

The first-coordinate windows are disjoint. If their possible starts
differ by r, their second-coordinate centers differ by more than
255.5r, far beyond their seed widths. This rules out the proposed
literal short-edge overlap cancellation. It is not a complexity lower
bound for the translated product or for another representation.

The paired-label equation also has exact recovery for arbitrary
candidate solutions, without relying on a candidate being prime. Write

    H*ell=s+b_t*c*d, h=c*tau-ell,
    X=H*tau-b_t*d, g(h)=sigma*X.

Then Hh+s=cX and

    M*g(h)=a(Hh+s)^2+B(Hh+s)+CN

imply X divides CN directly. When X is in the positive factor window,
X>|C| and X<N. If gcd(X,N)=1, divisibility would force X|C, a
contradiction; gcd(X,N)=N is excluded by X<N. Every acquired solution
therefore gives a proper factor. Independently X=c^(-1) mod r, so the
r-unit condition holds even on false candidates. This consumer does
not acquire the two short seeds or the row/multiplier label.

Monicization introduces no hidden square-root oracle. For
g(h)=a*h^2+b*h+d0, the polynomial z^2+b*z+a*d0 has the two known roots
-as/H and -(as+B)/H modulo N. The true z=ah is below 2sqrt(N)/r.
Multiplying a root difference by H gives Hz+as or Hz+as+B; each is
nonzero modulo r and has absolute value below 3M<N. A leaf gcd is
therefore proper. The explicit shared interval evaluator costs
soft(sqrt(JL)+J), with J=O(r), L=O(r^2), giving soft r^(3/2), not soft r.
For a=1 the first-root family is exactly the old AP product, via
Hz+1+ru=r(rz+u)+1. Neither this overcover nor its known roots is a new
acquisition bound. On the branch gcd(D,N)=1, gcd(B,N)=1 already follows
from B^2=M*D modulo N.

## The definite square-form shortcut fails uniformly

The square-form transfer uses a different discriminant from D:

    delta=4aCN, Delta=4delta,
    G=(H,2B,DH), F=(D,2B,H^2), G^2 ~ F^(-1).

The small split prime ideal above r is r_B=(r,sqrt(delta)-B). The norm
form of its square is G^(-1), and the norm form of its fourth power is
properly equivalent to F. Thus the principal-square premise requires
r_B^4 to be principal with the appropriate positive-norm convention.
For positive Delta, equivalence/principality here uses proper SL2
equivalence and the narrow class. An oriented generator
u+v*sqrt(delta) would have norm r^4.

When C<0 and v is nonzero,

    u^2+4a|C|N*v^2 >=4N>1024r^4.

When v=0, u=+/-r^2 gives the balanced rational ideal
r_B^2*conjugate(r_B)^2, not r_B^4. Hence no negative-C descriptor can
satisfy this particular principal-square premise. This is a uniform
arithmetic obstruction. The independent definite-reduction proof in
the ideal report gives the same conclusion without a norm generator.

For positive C, the one inherited true-row replay refutes only the
claim that every short sigma forces this premise. It does not refute
the existence of another principal positive-C row, nor prove that such
a row must exist or have a cheap return computation. Those distinctions
must survive any future use of this checkpoint.

## Acquired coefficient factorizations and unresolved selection

The coefficient factorization is genuinely affordable. Sieve through r.
Prime-product refinement finds every divisor at most r of all O(r)
coefficients C in soft r total work: at each tree depth there are only
O(r log r) surviving integer/node incidences, each of logarithmic bit
length. Repeated division at the leaves obtains all valuations. After
removing these factors, a residual greater than one is prime because
|C|<r^2 and two primes greater than r would exceed that bound. The a
values are below r. This strengthens the available input but does not
identify the hidden small-cofactor ideal or ratio.

The public relation of norm aCN and the true hidden relation of norm
aP*sigma are carefully distinguished in the ideal report. They live
in the order of discriminant D; the SQUFOF transfer lives in the order
of discriminant Delta. No cross-order class-recognition theorem is
assumed. Full coefficient factorization does not pay that recognition.

The reciprocal-identity report has a similarly narrow conclusion:
screening all row-clock differences costs soft r, after which an
ordinary Vandermonde minor proves the actual denominator matrix is not
rank two. The tested rank-two reciprocal identities therefore do not
specialize directly. Its exact Bezout resultant requires the full
product residue as an input, which is still unacquired. This does not
rule out other zero-preserving transformations or determinant methods.

No further finite success campaign, Lean backend extension, or broad
build is part of this checkpoint. The next substantive result must
acquire a bounded integer witness or a restricted product/count in
soft r for every surviving input. All explicit recovery implications
above remain conditional on that acquisition.
