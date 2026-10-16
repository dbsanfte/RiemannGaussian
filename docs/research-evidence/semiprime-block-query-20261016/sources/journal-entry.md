## 2026-10-16 — Paid block transforms and one-point channel vectors; common gcd locates collisions

The new [block-query packet](research-evidence/semiprime-block-query-20261016/README.md)
contains a constructive arithmetic win, rather than more successful semiprime
examples. It still does NOT prove the whole-family soft O(m) long query or an
improved factoring exponent. Three gpt-6.1-sol agents investigated in parallel;
the main new block algorithm and collision-locator theorem each passed two
independent final-byte mathematical reviews. These are classical proofs, not
new Lean declarations or a new implemented factoring benchmark.

**An implicit Theta(m^2)-entry coefficient matrix now has paid soft O(m) actions.**
Write F=P_L(t;q)=sum c_k t^k, assuming every 1-q^r for 1<=r<=L is a unit.
For arbitrary public starts a_j and width B with a_j+B-1<=L, define

    C_(j,s)=c_(a_j+s),  0<=s<B.

Both C*v and C^T*w, with arbitrary formal weights and repeated starts, cost
soft O(B+nu+sqrt L), INCLUDING their selected c_(a_j) seeds and preprocessing.
The coefficient recurrence gives a COMMON rational Newton basis

    c_(a+s)=c_a prod_(r<s)(q^L-q^(a+r))/(1-q^(a+r+1)).

A balanced polynomial matrix product converts a weighted sum of those basis
functions to one numerator/denominator pair. Monic multipoint evaluation and
unit batch inversion give the forward action; formal reverse mode gives the
transpose at the same clock. No coefficient or row value is inverted. This
pays the m-by-m block operator without constructing all m^2 entries.

Transposing at regular starts Bn with weights X^n acquires the FULL remainder
F mod(t^B-X) in soft O(B+L/B+sqrt L), for ANY scalar X, including nonunits.
The ragged final block uses selected coefficients only through L; no hidden
order premise through L+B is needed. At B~sqrt L~m the cost is soft O(m),
with the usual log N bit factor and soft O(m) residue storage.

For dyadic B, the mask E_B=D_B(t^B)/D(t) obeys the fraction-free identity

    E_B(t)=prod_(h<log2 B) D_(2^h)(-t^(2^h)).

Nested reduction modulo u^(B/2^h)-X acquires its full binomial remainder in
soft O(J+B); there is NO inverse of D_B(X), even if X is a powered target.
Multiplying the two remainders therefore pays ALL channel values N_r(X) at
ONE arbitrary scalar X in soft O(J+B+L/B+sqrt L). Only point evaluation is
paid; this does not acquire the O(J)-degree channel polynomials themselves.

**The channels have a genuinely collision-selecting common factor.** In either
actual hidden field of odd characteristic, after public node deduplication,

    monic gcd_(r<B) N_r(Y)=prod_(j:F(z_j)=0)(Y-z_j^B),  B>=2 dyadic.

The mask contributes each node's B-1 nontrivial dyadic phases. All F roots
lie in the odd subgroup and are simple, so they supply the missing phase
exactly at a collision. Complete fibers prove both exactness and squarefreeness.
The factor has o(m) degree on the inherited unit-row counterfamily, unlike
the ordinary row moments whose poles survive at the many unit rows.
Acquiring this common gcd cheaply from the new structured vector oracle is
UNPROVED. Its small degree is not sparse coefficients, free syndromes, or
a composite-ring field-gcd algorithm. Fresh black-box/sparse-GCD sources
did not pay that conversion; generic degree-sized point interpolation loses
the desired clock. No structured lower bound is inferred from that fact.

**Both actions of an actual mixed matrix are paid; its diagonal is still missing.**
With y_i=z_i^B, V_y(i,n)=y_i^n and V_z^T(s,j)=z_j^s, set

    S=V_y C V_z^T + the explicit rank-one ragged correction.

Then diag S=(F(z_i))_i, while S*x, S^T*x and S*1 all cost soft O(m) from the
new block operator and ring-safe Vandermonde maps. A supplied polylog-rank
ordinary commutator generator YS-SY=UV^T would recover the diagonal via
off-diagonal rational multipoint sums at that clock. The compatible rank and
generator acquisition are NOT proved. The available q-displacement changes
z to qz and cannot be substituted for this fixed-node commutator. The older
exploratory source note's missing diagonal identification is now resolved;
the generator or another diagonal algorithm remains the real missing step.

Supporting exact investigations classify the one-channel restricted gcd
interface, inverse-reflection digit cancellation with linearly many centers,
binary mask/Fourier pruning, and coarse-point alignment/binomial coverage.
Their scopes leave additive simultaneous-point and factor-only routes open.
All seven predecessor evidence bundles and their exact journal entries remain
byte-unchanged. No new Lean, broad build, example corpus, commit or push is
claimed. The generic query is still soft O(m^(3/2)); restriction-stable whole-
family soft O(m) acquisition and the full Lean sixth-rate composition remain
open. The next positive targets are the structured common gcd or the mixed
diagonal, using the newly paid operators rather than assuming their outputs.


