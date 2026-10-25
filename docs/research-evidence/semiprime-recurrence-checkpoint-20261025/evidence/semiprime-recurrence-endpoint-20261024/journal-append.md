
## Recurrence endpoint: acquired binary masks and scalar elimination tests, 2026-10-24

The positive algorithm in this pass acquires EXACT native index-residue
masks modulo B=2^r using O(log B) dyadic classes per row. Their total
acquisition costs soft m, avoiding the literal m*B residue table. It does
not improve the whole covered-query exponent: the completed evaluation
and localization still cost soft(m+sqrt(mL))=soft m^(3/2).

For the original scalar row, H=m² is odd and the own identity is
H*I=a_j*P+Q+ell_j. Since P is odd, its own index lies in the public image
S_j(B)={H^-1*(a_j*v+N/v+ell_j) mod B : v odd mod B}. The inverse and
all carries here are computed modulo the known power of two. To acquire
the image, partition the odd inputs into balls v=v0+2^t*z. Put
k=v2(a*v0²-N). If k<t, the normalized difference
(f(v0+2^t*z)-f(v0))/2^(t+k), f(v)=a*v+N/v, is a rational map with odd
denominator, reduction z mod 2 and odd derivative. Unique binary lifting
proves its image is one COMPLETE class f(v0) mod 2^min(r,t+k).
If k>=t, split the ball until 2t>=r, when its image is a single residue.
Only critical balls split; at most four solve a*v0²=N mod 2^t at each
level. This proves the O(log B) state and output bound, with initialized
offsets rather than an unacquired next-bit recurrence.

These particular masks have constant density. For even a the image is
exactly one parity class. For odd a, either v0=1 has k<=3, or v0=3 has
k=3; a regular subball supplies a complete output class of modulus at
most 128. Consequently |S_j(B)|>=B/128. This is a property of the tested
filter, not a computational lower bound or a new semiprime counterfamily.
Group acquired classes i=c+D*k by the dyadic modulus D and their two
possible clipped lengths; targets q^-c*Y_j and base q^D give a paid scalar
query with the original bounded leaf decoder. The masks preserve the
own witness. Their product need not equal the unrestricted original
resultant. Coincident shifted roots can help particular instances; no
distinct-target lower bound is inferred from labeled metadata.

The finite-geometric Christoffel test was also completed with lawful
initialization. Its full Hankel determinant equals a unit Vandermonde
square times prod_i F(q^i). The short alternant uses
Y_j^r*P_L(Y_j), so it retains exactly the long grid evaluations. A compact
rational descriptor for the moments costs soft J, but full moments cost
soft(L+J), and its ordinary rank is L minus the hit count. Scalar-only
evaluation without a dense matrix is already paid at softsqrt(JL).
The full-support boundary and rank distinction were previously known;
this completed test supplies no new rate theorem.

The primary-source endpoint audit retains coefficient degree J in the
q-holonomic theorem, yielding softsqrt(JL), and distinguishes explicit
modular-composition inputs from an implicit long recurrence endpoint.
A different fully acquired input for further work is the tensor norm
Norm_(R[X,Y]/(A_s(X),B_t(Y))) F(XY), where A_s has roots q^a,
B_t has roots q^(s*b), and s*t covers the long prefix with s,t~sqrt L.
Its inputs and short tail cost soft(J+sqrt L). The remaining scalar norm
is NOT acquired at that cost: the tensor rank is st, an explicit inner
resultant has degree at most J*s, and arithmetic modulo B_t costs with
rank t. A faster elimination must prove compact-generator closure and
include restrictions and nonunit handling; a determinant identity alone
does not meet that contract.

Reports, primary caches, exact-byte independent reviews and the
preservation validator are in `/tmp/semiprime-recurrence-endpoint-20261024`.
No examples, new backend lemmas, or changed factoring exponent are claimed.
The sixth-rate goal and full bit/Lean composition remain open. All prior
document prefixes, 270 frozen entries and concurrent RH work are retained.
