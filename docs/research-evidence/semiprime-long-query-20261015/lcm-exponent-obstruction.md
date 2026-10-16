# An exact gcd-only LCM compression, and its acquisition obstruction

2026-10-15. Classical argument, independently reviewed; not a Lean theorem.
This concerns one specified exponent-compression route, not arbitrary scalar
queries or a lower bound for factorization.

## The tempting shortcut is arithmetically valid on the prime-order family

Let N=P Q for distinct primes and let gamma be a known unit modulo N.
Suppose its local orders R_P,R_Q are prime, as on the previously retained
hard family. For a finite nonempty list of nonzero integers k_i, put

    K = lcm_i |k_i| > 0.

For p=P or Q, gamma^k_i=1 modulo p exactly when R_p divides k_i. Since
R_p is prime, it divides K exactly when it divides one of the k_i. Therefore

    gcd(N, product_i (gamma^k_i-1)) = gcd(N, gamma^K-1).       (1)

Negative exponents use only the inverse of the known unit gamma. Multiplying
individual residuals by known units does not affect (1). The equality uses
squarefreeness of N and the EXACT LCM. An arbitrary common multiple can add
new local prime-order hits. With composite local orders only the implication
from an old hit to a hit in gamma^K-1 is automatic; for example order 6 is
annihilated by lcm(2,3) although neither individual exponent annihilates it.
Zero exponents make the original product zero modulo N and must be handled
separately; K=0 is not part of the compression contract below.

Thus this is a genuine ANY-preserving gcd reformulation on the prime-order
family. It does not itself guarantee a proper gcd or resolve saturation.

## A uniform elementary bound for primitive arithmetic progressions

Let a,d,n be positive integers, gcd(a,d)=1, and u_i=a+i d for 0<=i<n.
Then

    lcm(u_0,...,u_(n-1)) >= product_i u_i / (n-1)!
                         >= a d^(n-1).                      (2)

Here is a full proof, so no asymptotic theorem with a fixed step is being
silently applied to our growing step d=m^2. Fix a prime r. If r divides d,
none of the u_i is divisible by r. Otherwise choose j maximizing v_r(u_j).
For i different from j, both u_i and u_j are divisible by r^v_r(u_i), hence

    v_r(u_i) <= v_r(u_i-u_j) = v_r(i-j).

Consequently the valuation of product_i u_i divided by its LCM is at most

    sum_(i!=j) v_r(i-j)
      = v_r(j! (n-1-j)!) <= v_r((n-1)!).

This holds for every prime, proving that product/LCM divides (n-1)! and
giving the first inequality in (2). For i>=1, u_i>=i d; multiplying gives
the second inequality. This elementary bound is consistent with the much
sharper arithmetic-progression LCM literature, such as
[Kane–Kominers](https://arxiv.org/abs/1101.0142); no result of that paper is
needed for this proof.

## Application to the actual first-current exponent formula

Use an odd auxiliary prime m not dividing N. The previously derived
first-current identities, for 1<=j<m, are

    a_j = N j^(-2) (mod m),
    ell_j = -2 a_j j (mod m),
    E_j = N+a_j+ell_j-m^2 kappa_j.                            (3)

The integer carry kappa_j may be the centered or pure-current carry; its
value does not affect this argument. These are the original source
identities, not the row-dependently normalized exponents r_j.
With a common known gamma-power origin u=gamma^v and q=gamma^(m^2), the
row factors are known-unit multiples of gamma^k_i-1, where

    k_i = E_j-v-m^2 i,  0<=i<L.

Modulo m, equation (3) gives the exact cancellation

    j^2 k_i = N(j-1)^2-v j^2.                                (4)

The right side is a nonzero polynomial of degree at most two in j: its
linear coefficient is -2N, nonzero modulo the odd prime m. For a common
origin v, at most two tags can have m dividing k_i. For every other tag,
all row exponents are nonzero and coprime to m^2. For the original origin
v=0 there is only the exceptional tag j=1.

Among these L signed exponents, at least n=ceil(L/2) have the same sign.
The positive terms, or the negative terms after reversing and changing
sign, form a consecutive positive arithmetic progression of step m^2.
Its first term is coprime to that step. Applying (2), the LCM of the
absolute values of ALL row exponents satisfies

    log_2 lcm_(i<L) |E_j-v-m^2 i|
      >= 2 (ceil(L/2)-1) log_2 m.                            (5)

In particular a single such long row with L=Theta(m^2) already requires
Omega(m^2 log m) bits in its exact LCM. Taking an LCM over more rows cannot
reduce that size. The established source has Omega(m) long first-current
tags, so deleting at most two exceptions still leaves long rows. Signed
starts only replace v by v+m^2 s and preserve (4). Applying a common unit
normalization to BOTH sides of a residual does not change k_i.

The common-origin assumption is substantive: unrelated row-dependent
exponents v_j can make every tag exceptional. This proof is not applied
to arbitrary such data. Likewise, (4) is not a premise for arbitrary
unit origins with no supplied gamma-power description.

## Precisely what the cost obstruction excludes

Every NONZERO integer multiple of all the k_i has at least the bit length
in (5). Therefore an algorithm constructing that exponent explicitly
cannot have soft O(m) bit time or output space when L=Theta(m^2).

Even a succinct exponent description does not by itself justify a cheap
exact exponentiation. In a formal addition/subtraction chain starting
from exponents 0,1,-1, each multiplication or division of powers can at
most double the largest absolute integer exponent. Producing the exact
formal exponent K thus requires at least ceil(log_2 |K|) such operations.
This is a bound for that formal exponentiation contract. It is NOT a
bound for a circuit which uses other ring operations, exploits a known
annihilating exponent, or produces a smaller exponent merely congruent
to K modulo the actual order. No order oracle is supplied here.

The route therefore has an exact arithmetic identity (1), but its direct
LCM acquisition/exponentiation costs already exceed the target on the
actual long-row source. Sparse order filters, different exponent
descriptions with a proved modular evaluation method, and implicit
resultants remain open.

## Provenance and review

The first-current formulas are retained in the historical
`antipodal-trace-candidate.md` and
`inverse-indexed-normalized-current-candidate.md`, archived in the sibling
`research-checkpoint-20261012` bundle; their SHA256 hashes are respectively
`a67c02ed0746321c59dd18f8484918711e77b114e7e15c8ed6954fae0cbdd54a`
and `af98fbc1bf39a1d2a617d1294a80621377345d3f4e52e01dfa2ea282cd87f17a`.
The journal's 2026-10-08 charged-acquisition discussion records the actual
Theta(m^2) first-current long intervals. We use those source identities
and interval results as historical inputs, without re-auditing their
entire upstream proof closure in this turn.

An independent Sol 6.1 review checked the valuation argument, signed
progression, source congruence, exceptional-tag count and exact scope of
the exponent-chain bound. Its required qualifications (nonzero exponent,
squarefree N, exact LCM for gcd equality, and formal integer exponents)
are incorporated above. See `reviews/lcm-shortcut-independent-review.md`.
