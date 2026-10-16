# Canonical long query: prescribed sparse probes and endpoint cancellations fail

2026-10-15. This continuation proves actual-family obstructions to
prescribed sparse probes and endpoint-only acquisition, including all
zero-augmentation short signed shift stencils. The full long query remains
unpaid. No improvement in the factoring exponent or new Lean endpoint is
claimed.

## The new arithmetic result

Use the previously retained balanced prime-pair supply P,Q~M^3, of mass
Omega(M^6/log^2 M). Its literal public sixth-width is B=ceil(N^(1/6)).
Allow the first K(N)<=B^.020 candidate primes m>=B, with K_*=O(M^.020)
an envelope for the menu. At each m retain the original positive t=1 seed:

    a_j = N j^(-2) mod m,  1<=j<m,
    ell_j = m b_j-2a_j j,
    delta_j = a_j+ell_j,
    Y_j = gamma^(N+delta_j),  alpha = gamma^(m^2).

Here b_j is the literal full-N lift and gamma is the actual public
factorial-projected unit. On the retained family its local orders are
the fixed primes R_P>P^.677 and R_Q>Q^.677, eventually both >16m^2.
These are proof-side facts, not algorithm inputs.

Before varying N, prescribe an index set I_(m,j) at each m and tag j, of
size at most B_*=O(M^.970). The indices may be arbitrary signed integers
depending on m,j and the fixed scale, but must stay fixed as N varies at
fixed m,j. Then at most O(K_* B_* M^5)=O(M^5.990) original inputs have ANY
nonunit observed residual at ANY allowed modulus or in EITHER field.
After deleting these and the frozen soft O(M^5.994) losses, a majority
supply of size Omega(M^6/log^2 M) has every prescribed observation a unit.
The counterfamily may depend on the prescribed catalogs; there is no
free union over all possible catalogs or arbitrary input-dependent indices.
See [the full sparse-catalog proof](reports/prescribed-tag-catalog-obstruction.md).

For B_* polylogarithmic, these are soft O(m) probes per modulus if their
exponent bit lengths, enumeration and modular powers are also paid. The
count itself grants arbitrary index magnitudes for free and makes no such
bit-cost claim for enormous exponents. Adaptive selection inside a fixed
prescribed catalog is covered; moving the catalog using N is not.

## Endpoint and signed-shift consequence

Set L_m=2m^2+2 and choose 0<=w<=M^.970. Observe every tag at every
integer index in the TWO-SIDED endpoint bands

    [-w,w] union [L_m-w,L_m+w].

After at most O(K_*(w+1)M^5)=O(M^5.990) further input deletions, every
observed residual Y_j-alpha^i is a unit in BOTH hidden fields, at EVERY
allowed modulus. Combining these deletions with the frozen soft
O(M^5.994) losses still leaves Omega(M^6/log^2 M) actual inputs. Yet the
complete canonical rectangle has a forced nonunit residual.

The proof also permits a prescribed public length function between
2m^2+2 and 4m^2, including the native padded seed length; it does not
grant a simultaneous free menu over every possible length function.
See [the complete endpoint proof](reports/endpoint-band-counterfamily.md).

For polylogarithmic w, all these endpoint observations cost soft O(m)
per candidate modulus. Width M^.970 and polynomial-size prime menus are
granted for coverage only; they do not satisfy that acquisition clock.

## Why the count works

Fix P,m, a width-m^2 half-open partner box and a public index i. A local
zero implies

    Q+delta_j-m^2 i = k R_P.

Because -3m^2<=delta_j<=m^2, all possible right sides lie in a length
5m^2 interval; there is at most one k. For each nonzero slope a, reducing
the full source equation modulo m gives

    a j^2-2aP j+aP-P k R_P = 0 mod m,

so at most two tags qualify. At a false tag j!=P mod m, two qualifying
partners with the same a,k,j would satisfy

    (1-P I_j)(Q-Q') = 0 mod m^2,

where I_j is the public inverse of j modulo m. The coefficient is a unit,
so there is at most one partner in the box. This gives O(m(w+1)) bad
partner states per box.

At the own tag, a local zero forces i to equal the exact seed index I.
The balanced supply gives

    c M-O(1) <= I <= sqrt(3/2)m^2+O(m),

which stays outside both endpoint bands for w<=M^.970. Thus there are
no own-tag endpoint hits. The literal prime-menu strip estimate
sum_m(G_m+1)=O(K_*M), together with O(M^3) possible P values, gives the
stated O(K_*(w+1)M^5) total. The proof uses the exact lift throughout,
without assuming local orbit disjointness or prime distribution in short
residue-class intervals.

The stronger per-tag catalog count fixes j,i first. It still has at most
one multiplier k in each partner box, and the same congruence becomes

    a A_j = P k R_P mod m,  A_j=j^2-2Pj+P.

At an ordinary false tag, A_j is nonzero and fixes a, so there is at most
one partner per prescribed index. There are at most two exceptional tags
with A_j=0; each allows at most m slopes and hence O(m) partners per index.
They are false tags because A_(P mod m)=P(1-P) is nonzero on the retained
supply. At the own tag, A_j still fixes a and one Q class modulo m, giving
O(m) partners per index in a width-m^2 box. The total is O(m B_*) per box,
and therefore O(K_* B_* M^5) over the original supply. This general count
needs no endpoint geometry or index-magnitude restriction.

## Consequence for cancellations

For integer weights c_s on shifted length-L intervals, the common interior
has multiplicity sum_s c_s. If this sum is zero and |s|<=w, the remaining
labeled factors lie entirely in the two endpoint bands. On the family
above every such factor is a unit. Therefore ALL these multiplicative
boundary observables are units, simultaneously for arbitrary integer
weights and both hidden fields. Endpoint ratios do not recover the
collisions removed from their interiors.

If the augmentation is nonzero, the long common interior remains. This
does not prove a lower bound for evaluating it implicitly. The obstruction
is for the specified signed-shift/endpoint acquisition route; arbitrary
additive observations, different large shifts and new scalar algorithms
remain outside its scope. See [the exact signed-factor interface](reports/signed-shift-interface.md).

## The arithmetic coverage and leaf recovery were already in Lean

The current native source contains `SemiprimeSeedSumAcquisition`, including
`common_seed_sum_exact`, `long_seed_reader_witness`, and
`long_public_route_seed_batch_succeeds`. The original m-1 seeds already
cover all factor ratios after the quadratic small-factor prefix. No new
hitting theorem is needed for the COMPLETE uncentered seed rectangle.
Smaller centered or endpoint windows have different coverage questions.

On a certified long outcome, D=ord_N(gamma)>16m^4. A globally zero leaf
Y_j=alpha^i gives the public sum S=1-delta_j+m^2 i. Both N+1-S and
phi(N)=N+1-(P+Q) are divisible by D, while |S-(P+Q)|<D. Hence S=P+Q,
and exact integer square root recovers the factors, even at a false tag.
This larger seed range is already covered by the existing native theorem.

A restriction-stable scalar oracle supports a simple controller: compute
the full product and its gcd, then bisect target lists and contiguous index
intervals whenever the gcd is N. A proper gcd ends the search; a final
globally zero leaf uses sum recovery. This needs O(log m) oracle calls,
with no derivatives or residual inversions. It would preserve soft O(m)
acquisition if every restricted query met that cost. It is a conditional
interface, not an implementation of the missing oracle. See
[the source and controller audit](reports/canonical-coverage-and-recovery.md).

## Structured matrices do not yet acquire the query

There is a valid division-free J-by-J matrix

    M_L = G_L(C_H),  G_L(X)=product_(i<L)(X-alpha^i),

whose determinant is the desired norm up to sign. It has displacement
rank at most two, but its first column is exactly G_L modulo H and its
generators contain unknown entries of M_L. The small rank does not
acquire those entries.

The alternative Cauchy equation

    (Y_j-alpha^i) C_(j,i)=1

has NO solution over Z/N on any covered canonical instance: the forced
collision reduces some entry to 0=1 in a hidden field. The 2026
deterministic structured-solver theorem explicitly assumes disjoint point
lists and charges both matrix dimensions. Clearing the denominators
produces generators containing the desired long products themselves.
See [the identities and primary-source audit](reports/structured-query.md),
including [Khichane–Neiger](https://arxiv.org/abs/2603.02425).

## Remaining gate and evidence

The existing general evaluator still costs soft O(J+sqrt(JL)). The desired
balanced bound is soft O(J+sqrt L), at J~m,L~m^2, including target-subset
and interval restrictions for recovery. This turn supplies a rigorous
arithmetic obstruction to one proposed cheaper route, not that bound.

The public long-order certificate is derived by bounded tests and staged
projection; it does not numerically compute the large order. Its source
and gcd counts still need a complete implementation and bit/memory
composition. Kernel descent and the other public branches remain part of
the full goal. See [the routing-cost audit](reports/routing-cost-status.md).

`manifest.json` pins the reports, independent reviews, inherited native
sources, historical evidence and primary PDF. The new endpoint count is
classical and independently reviewed; its analytic supply is inherited
from the frozen audits. No new Lean source, backend certificate, numerical
factorization example or broad build was added. The guaranteed one-sixth
factorization goal remains active and unproved.
