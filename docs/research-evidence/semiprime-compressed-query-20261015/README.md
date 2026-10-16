# Exclusive own rows obstruct a single shared coefficient stream

2026-10-15. A new classical actual-source arithmetic count, independently
reviewed twice, plus three parallel Sol 6.1 investigations. The general
query bound remains soft O(m^(3/2)); no soft O(m) actual-source evaluator
or new Lean endpoint was obtained.

## Two different rows give the two different proper factors

Use the same inherited balanced prime-pair supply N=P Q, P,Q~M^3,
with fixed ratio at most 3/2, exact large local prime orders and the
first-K candidate menu K_*=O(M^.020). After at most

    O(K_* M^5.969)=O(M^5.989)

additional deleted inputs, every candidate m has two exclusive own rows:

    gcd(N,P_L(z_(P mod m);q))=P,
    gcd(N,P_L(z_(Q mod m);q))=Q,

simultaneously for every 2m^2+2<=L<=4m^2. The tags are distinct.
Unite this loss with the frozen losses on the ORIGINAL qualified
supply; Omega(M^6/log^2 M) inputs survive. The factors, tags and orders
are proof-side information, not executable inputs.

Both own hits fit the full interval because balance gives
max(P,Q)<=sqrt(3/2)m^3. The exact seed index
(a_j P+Q+ell_j)/m^2 is an integer, positive eventually, and less than
2m^2+2; the swapped orientation has the same bound.

The new arithmetic step excludes CROSS-field hits at these own tags.
Fix local Q,m and a width-m^2 selector box for the partner P. A cross
hit has

    P+delta_j-m^2 i=k R_Q,  j=P mod m.

All indices i<4m^2 allow O(M^1.969) multipliers k. The own-tag constraint
a_j=Q/j mod m changes the low-digit equation to

    j^2-(2Q+kR_Q)j+Q=0 mod m.

There are at most TWO tags per multiplier. The full-input lift then
fixes at most one partner P modulo m^2 because j!=Q mod m. This removes
the factor m present in the earlier ordinary row-hit incidence count,
giving the new O(K_*M^5.969) INPUT bound. Same-tag inputs have their
separate elementary O(K_*M^5) charge. These are counting bounds, not
algorithm running times.

## Why one common coefficient stream cannot represent every row

Any single forward prefix stream with unit denominators has nested
prime-divisibility supports: once P divides a prefix value, it divides
every later prefix value. Thus such a stream cannot contain BOTH a
P-only value and a Q-only value. Row-specific unit factors do not
change that fact.

The new exclusive rows therefore rule out representing every changing-
target row by a unit factor times one selected value from ONE common
prefix stream. This holds for ANY assignment of nonnegative indices,
including choices using the full N, previous observations, arbitrary
advice or even private factors. The same retained family works for all
such streams and assignments; no union over possible choices is used.

In particular, the Gaussian coefficients of one common top parameter T
have the prefix-ratio form

    c_k(T)=prod_(r<k)(eta^T-eta^r)
            / prod_(r<k)(1-eta^(r+1)).

Whenever the selected denominators are units, they have that same
nested support. A huge common T, chosen input-dependently and powered
succinctly, cannot evade the obstruction. No horizon-inflation or
discrete-log-hardness assumption is used.

Sums, several coefficient values per row, multiple streams, and
polynomial specialization at NONUNIT denominators remain outside this
lookup contract. So do factor-only algorithms and direct norm methods.
The full-tag product on this family is already zero modulo N; returning
that one saturated gcd does not identify either private own tag.
Restricted queries or an equivalent informative payload remain unpaid.
See [the full arithmetic and stream proof](reports/exclusive-own-rows-prefix-obstruction.md).

## Other investigations and exact limits

The cheap selected-coefficient primitive from the previous continuation
remains valid. The special terminating q-Krawtchouk identities inspected
either need an integer q-grid label already supplied or move the
changing target into a changing parameter. Completing all m^2 gamma
sectors changes the query and its cost. These observations are interface
checks, not a universal impossibility theorem for all basic-hypergeometric
transforms. See [the duality audit](reports/duality-audit.md).

Collision sparsity does not make ORDINARY row-value moments sparse.
Their rational generating series has poles at the nonzero rows, so the
retained m-o(m) unit rows force Omega(m) poles and Hankel rank in each
hidden field. A collision-selective projector or syndrome would be
different information; acquiring it cheaply remains open. Recent sparse
GCD papers retain their field, degree and input-access premises. No
general NP-hardness result is transferred to this special source. See
[the sparse-intersection analysis](reports/sparse-intersection-interface.md).

There is a positive block-aggregation special case: if the given block
B(X)=D(X^rho) has bounded-degree D, the scalar aggregate has a soft O(m)
algorithm in the balanced J=T=m regime. The actual block P_b(X;q)
has EVERY coefficient a unit in both fields for b below the local order,
so that direct support-stride compression is unavailable. Its scalar
algorithm supports row and BLOCK-time restrictions; factoring recovery
and restrictions within an original block need separate proofs.

A generic affine-entry determinant for the block aggregate needs
dimension at least JT, by its formal coefficient degree. This does not
give an actual-family circuit lower bound: the q-binomial coefficients
are specialized, and high-degree succinct entries are allowed by other
interfaces. Fresh 2018 and 2026 resultant papers do not supply a paid
compressed aggregate theorem. See [the block analysis](reports/compressed-block-aggregation.md).

## Remaining target and evidence

The new proof is an arithmetic obstruction to a precise proposed
conversion from changing-target rows to one shared unit-denominator
coefficient stream. It is not a lower bound against a fast weighted
combination, several-stream transform, collision-selective syndrome,
or norm-only circuit. Those remain live acquisition routes.

The existing full seed coverage and recovery remain native. Guaranteed
one-sixth factorization still requires a restriction-stable soft O(m)
query, then the complete routing/kernel/controller bit and memory proof
in Lean. New results here are classical; no new Lean, numerical corpus,
broad build, commit or push was added. The manifest preserves final
proof/review hashes, source pins, primary papers and the unchanged older
bundles.
