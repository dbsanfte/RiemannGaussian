# Execute factor-window descent and carry-residue fusion

26 October 2026. Paper-only continuation of the [complete ternary hierarchy](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-direct-contraction-20261026/ternary-fusion.md). Scratch only; no tests, code, Lean or repository changes.

**Outcome.** A fully charged parent-level query on factor-size windows is available, but descending the hierarchy does not improve its initialized cost. True-child stationarity cancels the higher quotient digit in the finite phase. Only g quotient classes, rather than g², are needed for this corrected label-sensitive fusion. The initialized completion below still retains the long clock. No improvement over the existing weighted K^(5/4) query is established.

## 1. Keep the supplied torus, descend only the arithmetic row table

Let original H=K², N<=K^6, P<Q, P,Q>16H. Keep the original prepared pi, barpi, large nonsplit order and roughness; do not rerun a supplier at an invalid smaller N^(1/6) scale. Choose n=K/g with g a power of three. For the coarse HH consumer one may stop with n>=K^(1/3). Define q_n=pi^(n²), so original q=q_n^(g²). All these powers are acquired from the supplied pi.

Acquire both complete monic parent families modulo n, using their centered phases modulo n². Their arithmetic tables, numeric roots and tags cost soft n. Acquiring all logarithmically many hierarchy levels costs soft K in total. At whichever nonsplit prime R is present, choose A if R=P and B if R=Q. In both good cases the parent root's physical exponent is

    T_a=Q+aP+ell_a,  1<=a<n, |ell_a|<=n²/2.

At its own true colour, T_a is divisible by n². Conversely an exact hit forces the true colour modulo n by the same unit-coefficient stationary quadratic argument as the original monic family. This argument uses the supplied original nonsplit order, not an unproved smaller-scale order supplier. All native partial/exceptional triples are retained when constructing the complete parent table.

## 2. Execute a public factor-size-window algorithm

Enumerate dyadic bins P in [L,2L], clipped to the original hard range. There are O(log N) bins. In a correct bin,

    N/(2L)-n²/2 <= T_a <= N/L+2nL+n²/2.

Thus a single conservative integer clock interval covers the true index and has length

    h_n(L)=O(N/(n² L)+L/n+1).                  (1)

The starting integer and interval bounds are public. A shifted clock is paid by replacing each root by its known q_n power times that root. Binary powering has logarithmic exponent length. The original nonsplit order exceeds 256H²; the physical exponent range and these conservative endpoints are O(N/L+nL+n²), which remain O(H²) in the hard range. Consequently the good-component integer-hit/unique-colour decoding is retained after this overcover, with ample order margin. There is no need to assert that every OTHER local component has clock order exceeding this enlarged index interval.

That distinction matters: use the division-free shared geometric-product engine. Do not import a q-factorial formula requiring all 1-q_n^t to be units through h_n(L). For directional first variations use the already licensed constant-rank jet engine and retain its good-component guarantee. Unit constants for normalization and a unique hit at the good field remain necessary; multiple hits elsewhere are handled by the existing validator/leading-slice protocol, not by assuming global uniqueness.

For each level and bin the paid old engine gives

    soft O(n+sqrt(n h_n(L)))
      =soft O(n+sqrt(N/(nL)+L)).               (2)

All input arrays are read/acquired in soft K across levels, and all bins/levels add only logarithmic factors. Fixed-rank first-jet processing does not remove the degree/clock bill in (2).

This is an actual initialized query algorithm, not just a compact parent descriptor. For this algorithm the best level is the largest n, apart from insignificant n and ceiling tradeoffs: the L term is invariant under descent, and N/(nL) increases as n decreases. Even if a tighter public factor interval removes most of the Q-offset variation, the range of coefficients aP contributes length about L/n, whose product with the n parent roots remains of order L. Accordingly the executed bill retains sqrt L.

For N of order K^6 and L=K^(2+gamma), (2) at n=K is

    soft O(K + K^((3-gamma)/2) + K^(1+gamma/2)).

This can improve the uniform monic K^(3/2) fallback in a supplied factor-size regime. Its minimum exponent is 5/4 near gamma=1/2, already the existing weighted-query rate. It is not a new uniform sixth-rate bound. These are costs of the executed engine, not runtime lower bounds for parent queries or scalar fusion.

## 3. Corrected true-child cancellation: only g classes, not g²

At depth g, write the exact acquired hierarchy as

    y_d=p U^d q_n^(c_d), 0<=d<g,               (3)

with actual coefficient a_d=a0+n d and the corresponding public child-colour permutation and phase carries. The true-parent interpretation is U=q_n^u, P=j+n u (or the smaller complementary factor in good B). Literal alignment of ALL child phases separately would use u mod g². That is an unnecessarily strong requirement for a label-sensitive fusion retaining only the true child. The following cancellation corrects that earlier assessment.

Let f(X)=a0 X²+ell0 X+N. Its stationary parent phase gives the acquired integers

    f(j)=n² eta, f'(j)=n kappa.

Consequently, as an exact rational function with denominators units modulo powers of three,

    I0(u)=(a0 u²+kappa u+eta)/(j+n u).         (4)

At the actual factor this is the integer parent clock index. Put P=j+n u and choose d so that a_d P²=N modulo ng=K; this d depends only on u modulo g. Define

    B=2a0 u+kappa-n I0(u)+dP.

Direct calculation gives

    n P B=a_d P²-N.

At the actual u, B is an integer, and therefore g divides B. More generally the same statement holds in the 3-local rational ring, since P is a 3-unit. For any v, exact subtraction of (4) gives

    I0(u+v)+d(u+v)-I0(u)-du
      =v*[B+(a0+nd)v]/(P+nv).                 (5)

Taking v=g t makes the numerator divisible by g² and the denominator remains a unit. Hence

    I0(u+g t)+d(u+g t)+c_d
       = I0(u)+du+c_d mod g².                 (6)

The higher quotient digit cancels for the coefficient d corresponding to the true child. All quantities are rational modulo g² where necessary; there is no division by the nonunit n or g in a modular ring. The integer identity nPB and its known divisibility justify cancellation before reduction.

This is not merely a differential argument. Equation (5) retains the quadratic finite-difference term and proves the cancellation for every integer t. For B, first use the publicly permuted reciprocal parent colour c=[N/j]_n and variable S=N/R. Its stationary polynomial is b0*S²+ell0*S+N, and child coefficients are inverse-square lifts in c. The complementary-factor proof is then exactly (4)–(6); it does not silently identify the original B tag j with S modulo n. A recovered reciprocal tag transports back by N/c modulo n.

## 4. Execute the reduced-class fusion and retain the finite shift

Enumerate v in 0,...,g-1 for each parent, and set P_v=j+n v. The child coefficient d(v) is computed by the actual inverse-square lift modulo K. Its associated child phase ell_d and carry c_d are already supplied. Formula (6) shows that

    I0(v)+d(v)v+c_d = 0 mod g².

Indeed the stronger numerator identity is

    [a_d P_v²+ell_d P_v+N]/(n² P_v)
       =I0(v)+d(v)v+c_d,

and the stationary child numerator is divisible by K². These congruences are automatic for EACH correctly matched child class; they do not select the unknown v. They do eliminate the need to enumerate its next g quotient digits. Exactly n*g=K matched child entries, not K*g, suffice. All their numeric roots, tags and phase starts are acquired in soft K from the existing hierarchy.

For actual P=P_v+K t, write the acquired child stationary polynomial as f_d. Its exact expansion is

    f_d(P_v)=K² eta_d, f_d'(P_v)=K kappa_d,
    i(t)*P=a_d t²+kappa_d t+eta_d.             (7)

Here i(t)=f_d(P)/K²P is the actual child clock index. Thus cancellation of the higher digit modulo g² leaves an unknown INTEGRAL clock position, not a known child clock value or a shorter window. A correct factor-size bin gives a public range for t, but supplying every allowed i(t) or testing those positions collectively is precisely an additional arithmetic query. It is not licensed to divide by an unknown clock period or omit that finite range.

A complete implementation is now explicit: construct the K matched child roots via (3), and apply the existing shared division-free geometric first-jet engine on their original finite clock. This has the original soft(K+sqrt(Kh)) monic cost. Alternatively query the parent windows in §§1–2 and pay (2). No extra residue digits are prerequisites for these lawful implementations. The original assertion that g² guesses were necessary for useful label-sensitive fusion was too strong and is withdrawn.

The [frozen joint q-binomial operator](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-direct-contraction-20261026/qbinomial-joint.md) supplies a potentially useful next interface: all section starts and both final tails are paid. Applying that operator jointly to the K matched entries still needs its same-parent/root diagonal contraction. The cancellation above is a genuine simplification of the support fed to such a contraction, but does not itself evaluate the remaining scalar.

## 5. Updated outcome

The parent-window algorithm is a completed all-semiprime overcover through the good orientation and correct public bin. Its method cost retains sqrt L. The stronger new arithmetic fact is that true-child stationarity reduces phase-class guesses from g² to g. It follows by exact finite differences and works without acquiring the hidden higher quotient digit.

After that reduction the acquired matched table is soft K, and all original finite endpoints can be retained. What remains unpaid is a collective scalar/first-jet evaluation of that table against its unknown integral clock positions. The present completion uses the old monic engine or the factor-window parent engine; neither beats the current weighted K^(5/4) bound. No obstruction to a better matched-table contraction, no bounded rational-block ansatz, and no new factoring exponent is claimed.
