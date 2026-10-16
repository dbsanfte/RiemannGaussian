# A supplied bounded-span carrier cover yields a small-order-multiple certificate

2026-10-16. Conditional deterministic extraction, not acquisition of a cover.
This combines the new triple relation with the separately reviewed
factorial-stripping lemma. Origins and positions here may depend on the
FULL input, unlike the low-digit-plan obstruction.

## Exact input and source promises

Use canonical t=1 first currents, d=m^2, and their literal offsets delta_j.
Their public nodes with integer origins are

    x_j=gamma^(-N-delta_j+d*k_j).

The qualified actual source has N=P*Q<=m^6, P,Q=Theta(m^3), and gamma has
distinct prime orders R_P,R_Q>16m^2 in the two hidden fields. Set
D=R_P*R_Q>16m^4 and S=P+Q-1<D. Then D|phi(N)=N-S.
These are proof-side source promises, not acquired order/factor inputs.

On the g>=2m/3 light first-current tags, the inherited native catalog
theorem bounds labeled delta congruence energy by E. In its polynomial
menu regime one may take E=m^.04*C_m^4*m^(5/2), with C_m polylogarithmic.
It applies at current candidates on the same original majority family.

Suppose a supplied cover assigns each such tag to a progression with
position 0<=r_j<T_i and unit seed/ratio satisfying

    x_j=c_i*rho_i^(r_j).

Write k for the number of nonempty progressions and T=sum_i T_i. Assume

    2*E*k^2*T < g^4.                                            (1)

Few carriers with total nearlinear length satisfy this eventually under
the stated energy bound. All supplied integers have polylogarithmically
many bits. That encoding condition is separate from the origin SPAN:
an enormous common origin cannot be ignored when charging input work.

## Construct the annihilator

Set f_j=-delta_j+d*k_j; the common -N cancels in differences. Within each
carrier use a fixed base tag 0. Equal-position pairs give candidates
f_j-f_0. If another position exists, choose a tag 1 with r_1!=r_0 and form

    K_j=(r_1-r_0)*(f_j-f_0)-(r_j-r_0)*(f_1-f_0).

There are at most 2g candidates. The cover equalities imply gamma^K=1
for every candidate: pair differences eliminate the seed, and cross
powers eliminate the ratio. No discrete logarithm of rho_i is needed.
Thus D divides every candidate K.

At least one candidate is nonzero. If all vanished, f_j would be a
rational-affine function of r_j within each carrier, including repeated
labels. Weighted pair-sum Cauchy--Schwarz and Holder would imply

    E_integer >= g^4/(2*k^2*T).

But integer equality among f sums implies delta congruence modulo d,
so E_integer<=E, contradicting (1). This argument counts source labels,
not just distinct targets. It has no no-wrap or relative-origin premise.
The complete argument is in low-digit-plan.md, where fixed low-digit
metadata is needed only for the subsequent source COUNT, not this step.

Let H=max_j k_j-min_j k_j. The canonical offsets lie in [-3d,d], hence

    |f_j-f_l|<=d*(H+4),
    |K|<=2*d*T*(H+4).                                          (2)

Assume the additional numerical bound

    2*d*T*(H+4)<=16*m^6.                                      (3)

Then the nonzero candidate has 0<|K|<=16m^6<m^2*D. In particular the
unknown integer c=|K|/D is at most m^2. For T~m up to logarithms, (3)
allows origin spans of order m^3 divided by the corresponding logarithms.
It does not cover arbitrary wider origins.

## Recover the factor within the m budget

Compute A=(m^2)! mod |K| by degree-m block factorial and monic
multipoint evaluation over Z/|K|. The separately reviewed extraction
proof shows that this costs soft O(m) bits for log|K|=O(log m) and
requires no invertibility of evaluation-point differences. Since
every prime divisor of D exceeds m^2 while c<=m^2,

    gcd(|K|,A)=c,
    D=|K|/gcd(|K|,A).

Then S=N mod D and P+Q=S+1. An exact integer square root of
(S+1)^2-4N recovers the two factors. No factorization of K, knowledge of
R_P,R_Q, or unknown-field arithmetic is supplied to this algorithm.

Under the polylogarithmic per-integer encodings, generating the O(m)
relations costs soft O(m) bits. Modular powering can verify the cover
or candidate identities at the same scale; final multiplication verifies
the output factors. Untrusted metadata may instead cause failure. The
theorem guarantees success only under its stated source, cover, energy
and size promises.

## What changes and what remains unpaid

A sufficiently compressed, bounded-span cover can serve directly as a
factor certificate: obtaining long-row values from that cover is not
necessary. This is a new sufficient observable, not a constructed cheap
observable. No algorithm here acquires such covers or the nonzero order
multiple. The separate low-digit-plan theorem excludes one way of doing
so, even with much larger numerical origins. Full-input-dependent
metadata, wider certificates and different implicit queries remain open.

These are classical arithmetic proofs. No Lean declaration, all-input
query bound or guaranteed sixth-rate factorizer is claimed.
