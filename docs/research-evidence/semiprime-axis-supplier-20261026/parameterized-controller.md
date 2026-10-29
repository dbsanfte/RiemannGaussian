# Parameterized axis controllers and a smaller supplied-residue interface

26 October 2026. Primary-paper derivation; scratch only, no examples,
tests, campaign, factoring code, Lean or repository edits.

**Positive result:** restricting Harvey--Hittmeir's already initialized
search to ONE SUPPLIED factor residue gives a soft-k factor-or-failure
consumer for a modulus n of order k^(1/3), not the previous sqrt k
threshold. The proof below uses the actual native large-order beta,
with explicit constants and all starts paid. It does not supply the
residue, and an arbitrary axis collision phase is not a factor tag.

With NO supplied residue, specializing the same paper to public
P in [B,2B] gives the exact optimization

    min_R [R+min{B/R,sqrt(N)/R^(3/2)}]
       =Theta(min{sqrt B,N^(1/5)}),

up to constant/polylogarithmic factors for these constructions.
Thus no fixed-power extension of the soft-k B~k^2 range is obtained
by that parameter choice alone. This is not a lower bound for other
controllers. A supplied narrow factor interval or residue remains
a useful additional input; its acquisition is not treated as free.

## 1. Primary source and prepared input

The used primary source is Harvey--Hittmeir, *A log-log speedup for
exponent one-fifth deterministic integer factorisation*,
[arXiv:2105.11105](https://arxiv.org/pdf/2105.11105), Proposition3.3,
Algorithm4.3, Proposition4.4, with its collision routine Algorithm4.1
and recovery Lemma2.4. Downloaded PDF/text were inspected in
`/tmp/semiprime-axis-supplier-20261026/`; their hashes are retained below.
No balanced-only rank-three theorem is used in Sections2-5.

Use the actual native scalar branch

    N=PQ, P<Q, N<=k^6, k=2*3^e>16, H=k^2,
    beta unit, ord_P(beta),ord_Q(beta)>16H.

Oddness is supplied too but is not needed for the following search's
order bound. No roughness or cross-prime order coprimality is assumed.
The known-residue operation takes a PUBLIC n and candidate sigma
modulo n, with

    k^(1/3)<=n<=sqrt k, gcd(n,N)=1.

Candidate sigma must be a unit modulo n. A correct P residue always
has that property. If it fails, return bounded failure (or a verified
factor if an independent gcd provides one). Wrong candidates may
return only verified factors or failure; never infer primality from
failure of a restricted search.

## 2. Explicit soft-k consumer for one supplied smaller-factor residue

Put

    m0=16k,
    lambda=ceil(4sqrt(N)/(n*m0)^(3/2)),
    kappa=2lambda+1, delta=beta^(n^2) mod N.          (1)

All ceilings can be evaluated by exact integer comparisons/roots;
no floating-point arithmetic or uncharged precision is required.
Since N<=k^6 and n>=k^(1/3),

    lambda<=ceil(k/16), kappa<=k/8+3<k.

For either prime R=P,Q,

    ord_R(delta)=ord_R(beta)/gcd(ord_R(beta),n^2)
                  >=ord_R(beta)/n^2>16k>=kappa.    (2)

Thus the source's global-order precondition and the stronger local
order condition are already paid by the supplied beta. There is NO
additional order finder, smoothness assumption or local inverse.

### Acquire all interval starts and lattice pairs

Run the source centre loop

    sigma0=1,
    sigma0_next=ceil((1+1/m0)*sigma0)

until sigma0>=sqrt N. Keep only the ONE supplied residue sigma
modulo n; do not loop through all units modulo n. There are
O(m0 log N)=soft O(k) centres. For a public bin [B,2B], start at B
and stop at 2B instead; the same argument below applies with only
O(m0) centres. Integer endpoints and clipping are acquired.

At every centre apply Proposition3.3 with modulus n, interval
parameter m0, residue sigma. It returns (a,b)!=(0,0), of O(log N)
bit height, in polynomial(log N) time. For the centre containing P,
IF P=sigma modn, it proves

    |aQ+bP-(aN/sigma0+b*sigma0)|
                      <=4sqrt(N)*sqrt(n)/m0^(3/2),
    aQ+bP = aN/sigma+b*sigma mod(n^2).              (3)

The division in the second line is the acquired inverse of sigma
modulo n^2. It is not division by an unknown factor. The candidate
coefficients and their starts are fully acquired independently of P.

Define exactly as in Algorithm4.3

    tau0=floor((aN/sigma0+b*sigma0)/n^2),
    tau=[aN/sigma+b*sigma]_(n^2),
    j=n^2*(tau0-lambda)+tau,
    v=beta^(aN+b-j) mod N.                         (4)

All rational centres in tau0 have exact integer numerator/denominator
representations. Short signed modular powering and any unit beta
inverse cost polynomial(log N) per centre. The full giant list has
soft O(k) actual values and retained (a,b,j) labels.

Build the kappa actual baby values delta^i, 0<=i<=2lambda. The bound
(3), its n^2 congruence, and the source's floor convention give an
integer i_star in this range with

    aQ+bP=n^2*i_star+j,
    delta^i_star=v mod P.                          (5)

This is exactly the finite interval argument of Algorithm4.3; no
factor-bin or residue values are assumed acquired by the theorem.

### Global and local collisions, including extraneous matches

Sort both lists and process EVERY global match, retaining labels.
The baby values are distinct by (2), so each giant has at most one
global baby match. There can be as many matches as giant entries;
using that conservative bound still costs soft k. We do not require
an unjustified claim that duplicate giants limit the count to kappa.
For each match put u=n^2*i+j and apply the source's exact recovery
Lemma2.4: solve

    b*X^2-u*X+aN=0

with explicit zero-coefficient handling: if b=0, test Q=u/a; if a=0,
test P=u/b. Both zero is excluded by the lattice construction. Verify
every proposed factor by divisibility/gcd. Extraneous matches give verified factors
or are discarded, not unvalidated conclusions.

If the TRUE giant from (5) is globally matched, (2) forces the global
matched i to equal i_star (equality modulo P already suffices).
The polynomial then has the true P as a root and the source lemma
recovers a factor. Thus an extraneous global match cannot silently
remove that true giant. If no global match recovers a factor, remove
all globally matched giant entries. The true giant remains and has
a local P collision with a baby value.

Apply source Algorithm4.1 to the remaining list and delta. Its monic
product tree and geometric MPE have cost soft(number of giants+kappa),
without node-difference inverses. If an evaluation gcd is N, scanning
its giant differences finds a proper gcd: none is globally equal to
that baby after the match removal. Thus the source routine supplies
factor recovery without any generic-annihilator assumption. The
native T_ext is optional additional fallback only after a localized
NONZERO short beta label has actually been established; it is not
needed to rescue the promised true-source global match above.

### Full cost and output contract

All n,m0,centre and lattice parameters meet Proposition3.3's
polynomial-height assumptions. Number of centres, short lattice
constructions, exponentiations, list storage, sort/match processing,
baby construction, polynomial tree, geometric evaluations and final
localization total

    soft O(m0+kappa)=soft O(k).                    (6)

If sigma is the true smaller-factor residue, the attempt is guaranteed
to factor. For a wrong sigma all loops and recovery tests have the same
bound and return a verified factor or failure. This is an actual
initialized consumer with explicit starting data, not a statement that
a residue-conditioned lattice equation alone is enough.

For a known residue of EITHER factor, form also
sigma'=N*sigma^(-1) modn and run the two attempts. A correct unit
residue belongs either to P or Q, and the complementary candidate
then belongs to the other, so one attempt is promised. This costs a
constant factor. No statement about an arbitrary collision's phase
being a correct factor residue is made.

For n>sqrt k the old bounded coarse-residue small-root decoder already
costs soft(1+N^(1/4)/n)<=soft k. Consequently the useful combined
interface accepts an acquired correct factor residue at any public
modulus n>=k^(1/3), with gcd/polynomial-height handling as above. For
an odd-power-of-three supplier one can choose a power within a factor
three of k^(1/3), avoiding factorization of a supplied modulus.

## 3. Fully parameterized restricted-residue cost

More generally take a supplied modulus n and use R=m0. Ignoring
polylogarithmic factors and constant rounding,

    T_known(n,R)=R+sqrt(N)/(nR)^(3/2).              (7)

The mathematical optimum is R=Theta(N^(1/5)/n^(3/5)), with cost
soft(N^(1/5)/n^(3/5)), PROVIDED the order condition is supplied or
paid. Sections1-2 establish it directly in the target native range,
rather than quoting (7) without its guard. The threshold for cost
N^(1/6) is n>=N^(1/18), or n of order k^(1/3).

A palette of S supplied residues, each with the same full factor
interval, gives S*R giant centres sharing one baby alphabet:

    T_palette=S*R+sqrt(N)/(nR)^(3/2),
    R_opt=Theta(N^(1/5)/(S^(2/5)*n^(3/5))),
    optimum soft(N^(1/5)*(S/n)^(3/5)+S).            (8)

The cost to acquire the palette and any order projection is additional.
Taking all residues S=phi(n) restores N^(1/5) up to wheel logarithms.
The +S in (8) pays input acquisition/ceilings when R_opt<1; then taking
R=1 already makes the baby term O(S). No fractional centre count is used.

There is a stronger NATIVE order ledger when n divides k. Put
`delta=beta^(n^2)`. Since n^2 divides H,

    q=delta^(H/n^2),
    ord_R(delta)>=ord_R(q)>16k^2, R=P,Q.

Thus the divisor-modulus consumer permits n ALL THE WAY TO k, rather
than imposing the crude n<=sqrt k bound from Section2. For any public
unit-residue palette of size S with

    n|k, n>=S*k^(1/3),

choose the exact integer interval parameter

    m0=ceil(16k/S).

Then S*m0<=16k+S, n*m0>=16*k^(4/3), and the same baby bound is
kappa<=k/8+3<k. The local order condition is automatic from q, with
no roughness, projected-order screen or factorization of unknown
orders. All acquired candidates, gcd/unit tests, coefficients and
starts cost soft O(k) because S<=n/k^(1/3)<=k^(2/3). In particular
n=k allows an acquired palette of O(k^(2/3)) correct POSSIBLE factor
residues, not merely one exact tag. Constant factors in the size bound
are absorbed by increasing the fixed 16 in m0.

The source collision proof from Section2 applies separately to each
supplied residue and jointly to their shared baby alphabet: only one
candidate needs to be the correct smaller-factor residue. A palette
for either factor may be complemented by N*sigma^(-1) modulo n,
doubling its paid size; candidates with nonunit sigma are discarded
or produce a verified factor before the search. Provenance is a
PROMISE ON THE PALETTE, not an assumption that arbitrary axis aliases
label P. A native row-colour bank satisfying that promise would
already be usable here even without its old clock query, but no such
universally covered small bank is supplied by this report.

Thus the improvement is a genuinely weaker information requirement,
not acquisition of that information. It does not itself supply an axis
phase, remove aliases, or close the all-semiprime goal.

## 4. No-residue PUBLIC P-bin [B,2B]

For comparison, let no residue be supplied and use the source modulus
m. All phi(m) possible residues must be acquired, with the O(m) scan
or an explicitly acquired equivalent list. Restrict centre generation
to [B,2B]. The source giant count is O(phi(m)*m0), losing a logarithm
from the global factor range but no power of B. Its baby count is

    lambda_lat=O(sqrt(N)/(m*m0)^(3/2)).

The absence of B here is NOT a balanced-only assumption. The
Proposition3.3 lattice has determinant N*m*m0*sigma0^2; its second-
order Taylor error cancels sigma0 and gives exactly this bound on
ANY positive public factor bin.

There is an explicit valid axis alternative a=0,b=m at every
residue/centre. It obeys the n^2 congruence (with n replaced by m),
and its interval width in units m^2 is

    lambda_axis=O(B/(m*m0)+1).

This is initialized directly from bP=mP, not an assumed better
nonaxis lattice vector. It reproduces the bounded additive/axis
factorial mechanism. Write R=m*m0. Up to the standard wheel ratio
phi(m)/m and polylogarithms, the paid all-residue search cost is

    m+R+min{B/R,sqrt(N)/R^(3/2)}.                  (9)

All residue and giant starts are counted. One may simply take m=1,
so R is an arbitrary positive interval parameter and no projection
order issue is introduced. For the relevant optima, the native beta
order is much larger than the baby count. Optimizing this PARTICULAR
completed construction gives

    soft(min{sqrt B,N^(1/5)}).                     (10)

Indeed minimizing the two alternative functions separately gives
sqrt B and N^(1/5), and minimizing their pointwise minimum gives
the lesser of those optima. This is an upper-accounting comparison,
not an algorithmic or factoring lower bound.

For N=Theta(k^6), B=Theta(k^(2+gamma)), 0<gamma<1/2,

    (10)=soft k^min(1+gamma/2,6/5).

The switch occurs at gamma=2/5. There is no fixed positive-gamma
interval at the target soft k by this parameter choice. The known
polylogarithmic extension B<=k^2*log^A N is already soft k and is
ordinary prior factorial credit; it is not a new power-range gain.

## 5. A genuinely supplied narrow interval can help, but must be acquired

If instead the factor is promised in a PUBLIC interval of relative
width delta<=1 around B, the same centre step has
O(1+delta*R) actual starts per residue. With no residue and m=1,
the lattice variant therefore has

    T_interval=soft(1+delta*R+sqrt(N)/R^(3/2)),
    optimum soft(1+N^(1/5)*delta^(3/5)).             (11)

Integer clipping adds at most one centre; cap direct enumeration
when intervals contain only a few integers. For N~k^6, a genuinely
SUPPLIED interval of relative width delta<=k^(-1/3) reaches soft k.
The required R is O(k^(4/3)), while its actual giant count is only
O(k), and the native beta guard remains sufficient for the O(k)
baby alphabet. Parameter descriptions still have O(log N) bits.

Covering a dyadic bin by all O(1/delta) such windows does NOT give
this bound for free: the total centre count returns O(R); sharing
baby steps then restores (9)-(10). No native axis or Young-boundary
argument currently acquires one correct narrow interval. This is a
quantified positive extra-input regime, not another declared supplier.

## 6. New rank-three preprint: exact scale check, no balanced import

Also inspected the new primary [Gao--Feng--Hu--Pan,
arXiv:2512.19076](https://arxiv.org/html/2512.19076), Sections4-5.
Although Theorem1.1 is balanced, Algorithm4.3 explicitly takes
c*N^beta<P<=N^beta with 1/3<=beta<=1/2. Its X=N^beta/m corresponds
to B/m on the present public bin. The claimed Lemma4.4/eq(4.3)
second-vector scale is

    ||v2||=O(sqrt(N)*B/m^(3/2)).

Dividing g(P_msb)=iP by P~B removes B again, leaving

    |i|=O(sqrt(N)/m^(3/2)).

Thus even ACCEPTING its second-vector/nontrivial-polynomial lemma,
Proposition4.5 yields the same m+sqrt(N)/m^(3/2) power optimization;
there is no extra B-dependent saving hidden in its balanced abstract.
Its modulus condition m<N^((1-beta)/2)/2 admits the N^(1/5)
optimizer throughout the axis beta range. This packet does not certify
that lemma's full correctness; Sections1-5 above do not depend on it.

Section5 Proposition5.2 states the supplied-residue improvement
sqrt(N)/(m*n)^(3/2) with phi(m) giants, consistent with (7)-(8).
Its printed Theorem5.3 assumes the SAME residue for EVERY prime
factor, stronger than the one supplied-smaller-factor interface proved
here directly from HH. No all-prime promise or unverified CRT formula
from that theorem is imported into the native axis problem. Likewise
Section6's repeated-power divisor model is not the present squarefree
unbalanced semiprime without an additional proven parameter map.

## Final scope

The current methods with only a broad factor bin give (10), not a
new soft-k controller for the full axis regime. The constructive gain
in this pass is the fully paid smaller residue consumer (6)-(8), plus
the exact narrow-interval regime (11). Supplying the correct residue
modulo k^(1/3), or a valid small palette at that scale, is now a sharper
arithmetic target than the old sqrt-k tag target.

An arbitrary axis alias cannot be relabelled P modulo n. Its safe
transport remains the own-label axis-to-kernel bridge, whose AP
consumer is separate. Neither new consumer supplies that residue or
proves the small Young-boundary family covers the leftover axis cases.

## Primary download pins

- URL: https://arxiv.org/pdf/2105.11105
- PDF: `harvey-hittmeir-2105.11105.pdf` in this scratch directory.
- PDF SHA256: `431794fc9aa69b3304cb3df02e4e54f01fbd0125437fa9195295772d2a745d53`.
- Extracted text: `harvey-hittmeir-2105.11105.txt`.
- Text SHA256: `8a273176d64f823bb9a740cb031fa62b8bfb2742ed4cf2e2f1a9ba74f52f2591`.
- Text locations: Proposition3.3 lines226-249; its proof249-313;
  Algorithm4.3 lines350-402; Proposition4.4/proof402-550.

The formulas were read from the primary PDF extraction. The new rank-three
paper was read through its arXiv HTML, with exact source links above;
its nontrivial-vector correctness is not assumed by the new HH consumer.
