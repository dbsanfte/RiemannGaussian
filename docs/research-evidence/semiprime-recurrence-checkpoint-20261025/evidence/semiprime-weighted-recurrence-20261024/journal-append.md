
## Complete phase catalogue and finite recurrence sharing, 2026-10-24

The previous turn made a complete fixed-scale improvement to soft
k^(5/4). This pass does NOT lower that exponent. It acquires a more
structured, complete row family in soft k, removes partial phase masks
from one exact product contraction, and supplies a variable-window
execution interface. The remaining long products are still unpaid at
soft k. The full all-semiprime sixth-rate/Lean goal is unchanged.

### A complete divisor/root catalogue with paid acquisition

The existing single-D0 setup makes k=2c0*3^e have at most three distinct
prime factors, among 2,3 and one ell. If ell>=5 occurs, N mod ell is an
already known nonresidue by reciprocity; Tonelli--Shanks and Hensel lifting
are therefore initialized. The cases ell=2 or 3 are treated explicitly,
with 3 merged into its existing prime-power factor.

The old Gauss length bound implies |ab|<=k/sqrt3. Consequently acquire
ALL signed divisor pairs 0<|ab|<k, plus the only possible shortest axis
vectors (+/-k,0),(0,+/-k). For each signed K=ab acquire every phase

    0<=lambda<H, lambda^2=4KN mod H, H=k^2.

At p^(2e_p)||H, a nonzero unit-root branch with v_p(4K)=2v<2e_p is
one coset modulo p^(2e_p-v), with p^v members. Odd valuations below
2e_p have no roots; valuations >=2e_p give the zero-root coset. Keep
all 2-adic branches. CRT gives at most 16 global cosets per K:

    lambda=lambda0+(H/g_K)t, 0<=t<g_K,
    g_K=prod_(p|k)p^min(floor(v_p(4K)/2),e_p).

This does NOT claim a constant number of roots per K. Write |K|=uv,
where u uses only primes dividing k and v is coprime to them. The count
is at most 32sqrt(u). Summing with divisor multiplicities gives

    sum_(0<|K|<k) tau(|K|)*#roots(K)=O(k log k),

because sum_(u smooth)tau(u)/sqrt(u) is the bounded product
prod_(p|k)(1-p^(-1/2))^(-2), with at most three distinct primes.
The axes contribute exactly 4k phase rows lambda=kt. Sieve, roots,
CRT, all labels and actual V=pi^lambda*barpi^(a+bN) cost soft k.

For each SEPARATE factor bin B<=R<2B, retain a pair only when

    (a B^2)^2+(b N)^2<=2k B^2 N.

This integer filter depends on the pair, so retains COMPLETE root
cosets. It contains every original Gauss witness, and bounds every
retained row by |a|R+|b|N/R<4sqrt(kN). The witness's phase is present
because ell^2-4abN=f'(j)^2-4a f(j)=0 mod H. Additional modular roots
need not correspond to old unit tags; the every-leaf bound makes this
overcover safe. Keep coefficient contents and all signed/axis cases.

Uncentering ell to lambda adds 0 or H. The existing M still covers
the own integer index, since |I|<4sqrt(kN)/H+1<M. Every retained
correct-bin saturated leaf gives

    |aR+bN/R+lambda-Hi|<8sqrt(kN)+4H+4<3H^2,

below ord_R(pi)>256H^2. The integer quadratic decoder therefore
applies to every added row. Wrong bins retain bounded failure, and
the correct bin guarantees success. No QRH orientation is reintroduced.

### Complete phase blocks now contract exactly

For one coset set g=g_K, u=pi^(H/g), V_t=V0*u^t and
Y=q^(-M)/V0. With P_n(X;v)=prod_(i<n)(1-v^i X), u^g=q gives

    prod_(t<g) P_h(Y*u^(-t);q)
       =P_(gh)(Y*u^(-g+1);u).

The exponents g*s-t tile a consecutive interval, so no partial mask
or unknown endpoint remains in THIS contraction. The exact difference
product has the known unit prefactor
(q^M V0)^(gh)*u^(h*g*(g-1)/2). For merged index j, recover
s=floor(j/g), t=g-1-(j mod g), lambda=lambda0+(H/g)t and i=s-M.
These labels preserve the actual integer decoder after norm localization.

There are only polylogarithmically many g types. For C_g retained
cosets, sum_g C_g*g=soft k. Actual block evaluation costs
soft(C_g+sqrt(C_g*g*h)) per type, including every start and residual.
Summing still gives soft(k+sqrt(kh))=soft k^(5/4). The merged length
gh can exceed 16H; monic product/MPE needs no new-base difference
inverses, and the old q screen is NOT transferred to that longer grid.
Localize among groups/cosets and then inside one merged interval;
no broken-coset evaluator is assumed.

Thus the newly acquired object is a complete signed divisor/root
catalogue with safe bin masks and exact full-coset contractions. The
remaining problem is simultaneous long evaluation at the varying
centres V0=pi^lambda0*barpi^(a+bN). Grouping by K and g does not yet
acquire those values cheaply. No output-count lower bound is inferred.

### Charge actual row widths, and set aside the quartic trial

For the original Gauss family, exact extrema of
(a*x+b*N/x+ell)/H on [B,2B] give acquired row windows [s_j,s_j+h_j).
Endpoints and the possible stationary point sqrt(bN/a) suffice;
rational/surd rounding is exact. For S=sum h_j, all products and norm
localization cost soft(J+sqrt S). Choose block size min(hmax,ceil sqrt S),
evaluate every full block, and acquire unequal tails by ascending binary
prefix blocks. The total tail polynomial degree is O(block size), with
soft J actual tail points. This avoids charging J times the largest tail.
The proved current bound is still S=O(k^(5/2)); no smaller uniform
width sum or guaranteed covering subset has been established.

A separate higher-Frobenius trial uses
aR^2+bR+cS+dS^2 and clock k^4. Its four-coefficient Taylor lattice has
EXACT determinant k^6; the derivative map contributes N^3 eta^10.
The exact rational remainder is bounded by seven times its lattice
coordinate bound. Even GRANTING a suitable high-order seed on every
possibly selected local orbit, batched centres cost at best for this
execution soft k^(9/7); separate centres give k^(7/5). Both are worse
than k^(5/4). The grant must cover all centres to decode arbitrary
saturated leaves, not just the private correct centre. No such higher
seed supplier is claimed. This particular construction is set aside;
it is not a lower bound for all extension-field methods.

Sources and exact independent reviews: /tmp/semiprime-weighted-recurrence-20261024/.
The focused literature search supplied no new applicable exact batch
theorem; no duplicate no-result literature report was added. Preserve
all prior prefixes, all 270 frozen entries, HEAD and concurrent work.
No exponent gain, numerical campaign, backend lemma batch, commit or push.
