# Native local square lifts and a fully costed direct detector

24 October 2026. Root derivation, independently checked in discussion by
recurrence_review; exact-file review still required. These are explicit
tests of local specialization, not a new query exponent.

Use the actual prime-cube family k=d r^3, m=d r^2, H=k^2=m^2 r^2.
The source residue-block.md has SHA256
`359dba948c766eea58d9b6f2e556a851d0e1354fb860126122afacb842e4d7f9`.
The inverse class arguments are z_h=C D^h E^(h^2), where
theta=pi^(m^2), E=theta^a and E^(r^2)=q^a. The signed integer
a=-ell2/m^2 is known and a unit modulo r^2. Write A=A_c and use its
public lift J0, with A J0^2=N mod H and 0<=J0<H. All stated inverses
mod H or r^2 exist by the prepared prefix and conductor guards.

The known centered coefficients have exact integer carries

    ell0=-2A J0+H u0, ell1=-2m J0+H u1,
    a=-J0/A mod r^2.

The last relation follows from a=-N^2 s0^(-3) mod r^2,
s0=A J0 mod H and N=A J0^2 mod H. The common inverse shift is
q^(-B), B=r^2+r+12, so C=q^(-B)pi^(-ell0)barpi^(-N-A)
and D=pi^(-ell1)barpi^(-2m).

At the good smaller nonsplit prime P, pi^P=barpi and pi^(P^2-1)=1.
Thus barpi^N=pi^Q because N=PQ. Suppose this is the class containing
P mod m and put t=(P-J0)/m. Define the DISTINGUISHED INTEGER

    c=-(A P+Q-2A J0)/m^2.

It is an integer: multiplying the numerator by P gives
A(P-J0)^2+(N-AJ0^2), both divisible by m^2, and gcd(P,m)=1.
The actual local identities are

    C=q^(-B-u0) theta^c, D=q^(-u1) theta^(-2t).

Moreover, putting K=(N-AJ0^2)/H gives

    P c=-A t^2-r^2 K,
    c=t^2/a mod r^2.

Here P=J0 mod r^2, because r^2 divides m. This proof uses integer
divisibility followed by reduction mod r^2. It does NOT invert P
modulo ord(pi) and then reduce that inverse modulo r^2.

Consequently, after separating the displayed q powers, the exponent
quadratic c-2th+a h^2 is a(h-t/a)^2 mod r^2. This is a genuine local
arithmetic relation. Its c,t are not acquired public exponents.

## Attempted finite character execution

The prepared local order of pi is coprime to k: its odd beta and
norm-one factors have been cleaned of every prime at most k. Therefore
powering by m^2 and by H are automorphisms of <pi>, giving

    <theta>=<q>=<pi>.

In particular <theta>/<q> is trivial. There is no nontrivial character
of this local cyclic group sending theta to a primitive r^2-th root
while killing q. Exponent residue mod r^2 is not a well-defined
function of the supplied local group value. The distinguished bounded
integer lift is essential; replacing it by any discrete logarithm
modulo the local order would lose this arithmetic statement.

The finite algebra B[T]/(T^(r^2)-q) is constructible, with rank r^2<=k
and evaluation T->theta. But the canonical constant lifts of actual
C,D do not become T^c and T^(-2t), with their required q carries.
Those lifts require the unknown distinguished exponents. A root-of-unity
branch sum applied to constant lifts therefore does not evaluate the
claimed stationary-phase character. No infinite Tate specialization or
unknown-order scalar field is supplied. The earlier Tate, cyclotomic
projection and auxiliary-input DLP audits remain credited, rather than
being asserted again as new general obstructions.

## A direct bounded detector can be executed, but retains the old cost

There is a useful precise comparison with an actually initialized
algorithm. Acquire, for each class,

    T_c=D q^(u1)=pi^(2m J0)barpi^(-2m),
    g=pi^(-2m^2).

Compare T_c with g^t for all integers t with
1<=P'=J0+mt<=k^3. On the good nonsplit component equality is equivalent
to pi^[2m(P'-P)]=1. Since |2m(P'-P)|<2k^4 while the prepared order
exceeds256k^4, a hit forces P'=P. Conversely the correct class and t
do hit. Thus a saturated leaf has the explicit bounded scalar consumer
gcd(P',N), a proper factor; P'<N by the prepared prefix. Norm-proper
branches already factor. Stored indices identify the correct P'.

For the full class menu, the number of classes is M<=m and each interval
has length O(1+k^3/m). Every start and the common base are supplied,
and the existing monic product/MPE collision method costs

    soft(sqrt(M*(1+k^3/m))+M)=O-tilde(k^(3/2)).

No assumption that the actual class count is Theta(m) is needed for
this upper bound. It gives no uniform exponent improvement: no theorem
in this attempt makes the full class count smaller by a power of k.
The comparisons have simply arranged the ordinary factor interval into
residue classes. They have not exploited the unacquired exponent c or
the square-lift relation to reduce its acquisition cost.

No numerical examples, new backend lemmas, or full sixth-rate claim
are used. Any future square-phase detector must acquire the relevant
bounded lift information or provide a different valid observable;
formal quotient characters alone do not do so.
