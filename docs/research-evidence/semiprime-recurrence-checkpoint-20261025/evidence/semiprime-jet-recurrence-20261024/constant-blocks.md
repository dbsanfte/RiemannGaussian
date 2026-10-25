# Paid constant-size native blocks by modulus inflation

24 October 2026. Root construction, checked independently in discussion
by recurrence_adjoint_attempt and recurrence_review. Exact-file review
is still required. This changes the acquired family to constant triples
or pairs. It does not acquire their long products or prove a new query
exponent. The algebraic flexibility was implicit in the earlier proofs;
the earlier literal supplier did not use it.

## Inputs, guards, and actual scale

Use the actual conductor palette from orientation-palette.md SHA256
`97db9cf0004dac3ec2c6c9cc341b27531fb90c51d5f6739e6b121c6bc4e20fbf`.
Each negative fundamental D has known conductor c0=|D|, known
factorization, gcd(c0,N)=1, Jacobi(D,N)=-1, and
c0=O(N^(5/32) polylog N). The good smaller-nonsplit orientation remains
conditional on the SAME analytic import. No orientation is recognized
or made unconditional here. Let K0=ceil(N^(1/6)).

The preferred nontrivial-curvature construction uses FIXED r=3. Guard
54c0<=K0; choose the least e>=3 for which

    k=2c0*3^e>=K0, m=k/3, d=k/27.

Then K0<=k<3K0. Here d is even and MAY be divisible by 3. That is an
explicit relaxation of the earlier r-coprime-d hypothesis, proved
below rather than assumed from its statement. All factors of k are
known from c0 and 3, and finding e costs polynomial(log N).

An optional pair construction guards 16c0<=K0 and chooses the least
s>=0 for which

    k=16c0*2^s>=K0, r=2, m=k/2, d=k/8.

Then K0<=k<2K0 and d is even. This also explicitly relaxes the old
odd-r and r>=3 hypotheses. No new prime search is required in either
construction. The scale guards hold eventually uniformly over the
old polylogarithmic palette because 1/6-5/32=1/96>0. Failures retain
the inherited finite-input and bounded whole-algorithm fallback.

FIRST run one common integer prefix screen through16(3K0)^2 if both
options or triples are used, or16(2K0)^2 for pairs alone. The actual
degree-square-root integer product/MPE construction costs soft K0;
when this endpoint is >=N use the finite-input trial-division fallback.
On the continuing branch all leaves are below N, and nonunit leaves
give proper factors. NoHit certifies P,Q>16k^2 for every new modulus.

Rebuild beta,W, all native rows and the actual coupled q=pi^(k^2)
screen through16k^2. The existing rough suppliers require even k,
N<=k^6, the paid prime prefix and c0|k/2 with known factors; they do
not require a cyclic unit group modulo k or bounded prime valuations.
Their costs remain soft k, multiplied by only polylogarithmically many
conductor labels. No old base or q guard is reused without its screen.

## Reprove the finite phase algebra under the relaxed hypotheses

The authoritative phase source is residue-block.md SHA256
`359dba948c766eea58d9b6f2e556a851d0e1354fb860126122afacb842e4d7f9`.
For both constructions H=k^2, m=k/r, c0|m, gcd(N,k)=1, and

    2k | m^2, k | m^2/2, H | m^3, H | m^4/4.

For triples these follow from54|k, with m^3/H=k/27=d and
m^4/(4H)=k^2/324. For pairs16|k gives the corresponding quotients
k/8, k/8 and k^2/64. All divisions by2 in these expressions are
integer divisions; no inverse of2 modulo an even public modulus is used.

Canonical parity repair is A_j=[N j^(-2)]_(2k). In a class j=j0+mt,
the inverse-square expansion modulo2k truncates after the linear term:

    A_j=[A_j0-2mN j0^(-3)t]_(2k).

For r=3 the multiplier -N j0^(-3) is a unit modulo3; for r=2 it is
1 modulo2. Thus the repaired A values are, in an acquired permutation,

    A_h=A_c+2mh, 0<=h<r, 0<A_c<2m.

Every original tag in the class remains a unit: every prime dividing k
already divides m. Every tag has the same colour because c0|m.
No coprimality between r and d was used.

Take the actual base row's public lift J0 and s0=A_c J0 modH, so
s0^2=NA_c modH and s0 is a unit. Acquire

    s(h)=s0+mN s0^(-1)h-(m^2/2)N^2 s0^(-3)h^2 modH.

Squaring cancels the quadratic term. The cubic term is a multiple of
m^3 and the quartic term a multiple of m^4/4, both divisible byH.
Hence s(h)^2=N A_h modH. Reduction modulo k gives

    j_h=s(h)/A_h=J0-m s0 A_c^(-2)h modk.

Its slope after m is a unit modulo r, so it permutes EXACTLY the r
native tags. The actual square root A_h*Jtilde_h agrees with s(h)
modk. For their difference Delta, H divides2s(h)Delta because Delta^2
is a multiple ofH. Since s(h) is an odd unit and gcd(2s(h),H)=2,
Delta is0 orH/2 moduloH. Multiplication by-2 removes this ambiguity,
at every prime valuation including arbitrarily large v2(k) or v3(k).

Center the coefficients of-2s(h) as ell0,ell1,ell2 moduloH. The exact
known carries d_h=(ellhat_h-ell_native,h)/H still satisfy
|d_h|<(r^2+r+10)/2. With B=r^2+r+12, e_h=B+d_h and
L=3H+2+2B, the shifted roots have the exact global representation

    Vhat_h=q^B C0 D0^h E0^(h^2)=q^(e_h)V_h.

The INVERSE Pochhammer arguments therefore have z_h=C D^h E^(h^2),
with every inverse common shift and the mixed barpi^(-2m) in D retained.
All starts, permutations and signed original index labels cost soft k.

For triples B=24 and L=3H+50; for pairs B=18 and L=3H+38. In either
case L<4H on the actual prepared k>16 branch. The earlier extended
unique-minus proof uses only these bounds and the prime-by-prime
valuation argument; it works at arbitrary exponents in k. The original
signed-index saturated consumer has the same <7H^2 margin against
the prepared order product>256H^2. Wrong orientations accept only
verified proper factors and otherwise return bounded failure.

## Constant curvature types, and what pairs do not retain

Since H=m^2 r^2, the centered ell2 is an integer multiple ofm^2. For
inverse arguments set theta=pi^(m^2) and a=-ell2/m^2. Then globally

    theta^(r^2)=q, E=theta^a,
    a=-N^2 s0^(-3)=-J0/A_c mod r^2.

For triples the centered a belongs to {+1,-1,+2,-2,+4,-4}. All
classes use the SAME theta for their prepared label and one of these
six phases. In particular their observable curvature is

    z_0 z_2 / z_1^2 = E^2 = theta^(2a).

This is a genuine global relation for three supplied unit arguments.
All classes of the same a can be grouped in soft k without evaluating
any long product. C and D still vary by class.

For pairs a is+1 or-1 and theta^4=q. But h^2=h for h=0,1, so E can
be absorbed into D. The pair statement therefore imposes NO extra
observable quadratic restriction on an arbitrary supplied pair. Do not
call the two E types a quadratic-cancellation algorithm. Triples are
the preferred constant-size family when curvature is to be exploited.

## Separation, completion and actual cost

DISCARD the old sixteen/polylogarithmic/O(rB0^2) arbitrary delta-fibre
estimates. Added prime powers can create large degenerate square fibres.
Where actual unit separation is needed, exact global deduplication,
product-tree derivative MPE and ONE distinct-pair localization still
give factor-or-separation in soft k, independently of fibre width.
For a full-r coarse reset, retain all r rows and their labels instead;
nonhit aliases do not invalidate the unique-hit proof. Recompute sizes
and degree claims if a later operation deduplicates.

There are J/r constant-size same-colour classes and m=k/r=Theta(k).
The already proved correct-residue completion costs
soft(1+N^(1/4)/m)=soft N^(1/12), so downstream recovery is comfortably
inside the target sixth-rate budget. This does not acquire the residue.
All setup and native family data remain soft k for the WHOLE family.

The actual complete degree-J block evaluator still costs
soft(J+sqrt(JL))=soft k^(3/2). A hypothetical finite native endpoint
engine costing soft(r^omega logL) per class, with all starts and needed
derivatives paid, would now give whole-family soft k because r is a
constant. No such engine is provided. The old big-r auxiliary endpoint
batch saving is only a constant factor in these variants. Generic
Pochhammer values or hypothetical tau initializations are not free.

The concrete completed change is the paid constant-block supplier and
the reproof of its actual phase/coverage contracts. It is not a whole
query advance, a removal of the orientation import, or the full Lean
bit-complexity theorem. No shared/frozen source or numerical campaign
was used to justify it.
