# Scalar q-difference solve before the two-GP tangent norm

26 October 2026. Scratch paper execution. **Outcome:** the actual scalar q-difference equation gives fully initialized first AND last M coefficients of the marked block polynomial in soft(J+M), including M~sqrt(h) inside the sixth-rate budget. This avoids the rank-J series arithmetic of the old Sylvester formal-prefix approach. However its reduction to the unit giant-clock quotient has an explicit live quotient correction; the tested fast formal solve does not acquire the fused norm or row-index pair. The completed safe query remains the older block algorithm. No general complexity obstruction is claimed.

## 1. Exact input, fixed jets and finite tail

Use separated-selector/separated-recurrence.md's actual marked polynomial

F_e(X)=prod_j(X-T_j+e_0+e_1 w_j), w_j=j,
A=B[e_0,e_1]/(e_0²,e_0e_1,e_1²).

It is monic degree J, its constant is a unit because all T_j are units, and its coefficients are acquired in soft J. Let h=bc+r, 0<=r<b, with b=ceil(sqrt(h)), c=floor(h/b). Baby and giant polynomials are

B_b(Z)=prod_(u<b)(Z-q^u), G_c(S)=prod_(v<c)(S-q^(bv)).

Their coefficients and explicit nodes cost soft(b+c). All arithmetic below is over the fixed-rank A; no one algebra operation hides J base coordinates.

The rectangle polynomial and exact norm are

R_b(S)=prod_(u<b)F_e(q^u S),
P_rect(e)=Res_S(G_c(S),R_b(S)).                    (1)

The literal r-node tail is acquired by monic MPE of F_e and multiplication in soft(J+r). For a weak rectangle-pair oracle, first gate each tail constant: a nonunit localizes to an actual row leaf and factors under the licensed original mixed-label consumer; otherwise the tail is globally unit and the unique good hit lies inside the rectangle. Algebraic localization costs soft(J+r); the once-only terminating extractor costs original soft K separately. For EXACT full jets without this gate one needs the rectangle constant in addition to its two derivatives. These interfaces are not interchanged.

The chosen retuned scale has J=O(K^(2/3)), h=O(K²), b,c=O(K); h=Theta(J³) only in a maximal-row regime J=Theta(K^(2/3)). Original K preparation, not N<=(K')^6, supplies the unit/order margins.

## 2. Execute the scalar q-difference formal solve

The exact equation is

F_e(S) R_b(qS)=F_e(q^b S) R_b(S),
R_b(0)=F_e(0)^b.                                 (2)

Put f(S)=F_e(S)/F_e(0), with f(0)=1, and L(S)=log f(S). For n>=1 define

s_n=(1-q^(bn))/(1-q^n)=1+q^n+...+q^((b-1)n).

Then the literal finite product proves

R_b(S)=F_e(0)^b exp(sum_(n>=1) s_n [S^n]L(S) S^n).  (3)

The sum notation is formal; computing modulo S^M uses only n<M. No infinite evaluation at a unit is made. Equation (3) also follows by taking the normalized formal logarithm of (2), whose constant term has already been supplied. It does not take a logarithm of the native scalar F_e(0); that factor is powered explicitly.

Here is an executable prefix algorithm:

1. Acquire F_e(0)^-1 and normalize f, cost soft J.
2. Compute f^-1 modulo S^M by Newton iteration, then integrate f'/f to obtain L modulo S^M.
3. List q^n and (q^b)^n for n<M, batch-invert the certified unit denominators 1-q^n, and multiply the n-th logarithm coefficient by s_n.
4. Exponentiate the zero-constant series by Newton iteration, and multiply by the acquired jet F_e(0)^b.

All four steps together cost soft(J+M) base-ring operations with fixed jet rank. Needed integer denominators are 1,...,M-1. For M=O(sqrt(h))=O(K), prepared primes >16H make all these integers units. Needed q-gap denominators have exponent only n<M; q^(bn) appears solely in a numerator and may be computed by powering the known base q^b. For an actual parity-shortened rooted base, these gap certificates use the doubled original exponents, still O(K)<<16H. No local field or unknown local order is used.

A precise primary source for the standard formal inverse/log/exp Newton operations is Brent–Kung, *Fast Algorithms for Manipulating Formal Power Series*, JACM25(4),1978,581–595, especially §5, p.589 (formal log/exp and their Newton iterations): https://maths-people.anu.edu.au/~brent/pd/rpb045.pdf ; author-hosted full text also https://www.eecs.harvard.edu/~htk/publication/1978-jacm-brent-kung . Its field presentation is not applied blindly: the above identities need only the enumerated unit constants/integers, which are explicitly available here. Formula (3) itself is derived from the native finite product.

This is stronger formal initialization than keeping J-by-M Sylvester cofactor series. It is not a new acquisition of a scalar at a unit point. Our base-ring bit accounting is explicit: base B has fixed rank over Z/N, each base operation has polylog N bit overhead; all exponents have logarithmic bit length.

## 3. Both ends of R_b are paid, still not its quotient value

The degree is exactly n=Jb and its leading coefficient is the known unit

q^(J*b*(b-1)/2),

independent of the row marks. Reverse R_b and apply the same algorithm with inverse base and reciprocal F_e, whose constant is also a unit. Thus M coefficients at BOTH ends are acquired in soft(J+M), provided all integers 1,...,M-1 and actual-base q-gaps through M-1 are certified units. The target M=O(sqrt(h)) in the explicit guarded range certainly satisfies this; no arbitrary precision beyond the characteristic is asserted. At M~c~sqrt(h), these end strips cost soft K, while the middle can still have degree Jb-2M. Nothing in the construction drops that middle or claims a generic lower bound from its size.

A simple symbolic diagnostic rules out ONLY using a formal prefix as the norm input. Let b=c>=2, take F(S)=(1-aS)(1-dS), a=q^-I, 0<=I<b, and use the giant node S=1. The true R_b(1) is zero for every d because its first factor product vanishes. For the truncated prefix R_<b(1), the constant coefficient as a polynomial in d is instead the first product with its degree-b term deleted, evaluated at1. It equals minus that product's nonzero unit leading coefficient. Hence the truncated prefix does NOT identically preserve the collision even in this two-row symbolic family. This is not asserted to be an attained full native catalogue instance, or to exclude an algorithm using both ends/F/native data; it diagnoses the proposed truncation substitution exactly.

## 4. Execute quotient reduction of the q-difference equation

Try instead to solve directly for r(S)=R_b(S) mod G_c(S), degree<c. Write exactly

R_b(S)=r(S)+G_c(S)t(S).

Substituting into (2), before any specialization, gives the exact quotient equation

F_e(S) r(qS)-F_e(q^b S) r(S)
   =-F_e(S)G_c(qS)t(qS) mod G_c(S).                (4)

The right side is not supplied by (2)'s short initial value or the formal coefficients in (3). It is the omitted quotient evaluated on the SHIFTED giant grid.

This boundary is particularly concrete on the actual grid. If b>1, G_c(qS) is a unit modulo G_c: at S=q^(bv), every factor is q^(bv+1)-q^(bu). Its nonzero exponent gap is b(v-u)+1, with absolute value <bc<=h. The original short-gap certificates (with the actual doubled-base interpretation where applicable) therefore certify it globally. Its values/inverse can be acquired by monic MPE and interpolation in soft c. There is no finite endpoint-only zero of this factor. For b=1 the giant set is almost shift-closed and this correction collapses toward a boundary, but then c=h lies above the target input budget.

One may also gate F_0(S) on these c giant nodes in soft(J+c). Those are ORIGINAL clock positions bv. A nonunit localizes to a row and factors; otherwise F_e(S) is a unit in the fixed jet quotient algebra. This is the already credited phase-zero subclock test, not a new complete phase supplier. On continuation the multiplier F_e(S)G_c(qS) in (4) is invertible. Therefore setting its quotient correction to zero would impose t(qS)=0 on the whole shifted giant grid; it is not a consequence of the actual q-difference equation.

This unit-multiplier fact does NOT prove that the actual special quotient t has full rank, lacks cancellations, or requires c independent acquisitions. Its q-factorial structure is still available and could support a new fused solve. It shows exactly which additional data the proposed quotient q-difference algorithm has to compute. The short origin series does not vanish under reduction because S is a unit modulo G_c; its omitted S^M tail is not nilpotent there.

## 5. Completed cost and what differs from previous audits

A complete safe fallback acquires R_b coefficients and evaluates them at all c giant nodes, or changes block length d and acquires R_d. This costs soft(Jd+h/d+J), optimized at soft(J+sqrt(Jh)); it includes the fixed jets, literal tail and good weak-pair consumer. This is the old whole query and is not counted as new progress. On the retuned bank its uniform guarantee is at most soft K^(4/3), so the original K^(5/4) family remains preferable absent a new contraction.

The new executed operation here is the direct scalar LOGARITHMIC q-difference solve (3), supplying both end strips at target cost, and the explicit native unit-grid correction (4). It differs from:

* recurrence-checkpoint/evidence/semiprime-tensor-norm-20261024/sylvester-elimination.md: that executes mixed Schur pivots and formal q-hook initialization, whose fully expanded series state carries an extra rank-J dimension. Here there are no Sylvester pivots, all formal scalar coefficients are explicitly computed, but endpoint evaluation remains unpaid.
* recurrence-checkpoint/evidence/semiprime-rough-block-composition-20261024/block-composition.md: its global block polynomial coefficient completion is the retained fallback, already credited. No new terminal-value rate is assigned to that recurrence.
* direct-contraction/composition-hybrid.md: the shifted-modulus correction is related in spirit and keeps its prior credit. Here (4) specializes the correction to the ACTUAL first-order q-equation and shows G_c(qS) is globally invertible for the GP giant grid, with all unit tests paid. No full-rank or arbitrary-algorithm obstruction is imported.

The precise next sufficient acquisition is now either the two selected tangent norm coefficients of R_b in (1), directly from (2)–(3), or a fused solve of (4) that supplies the relevant quotient correction without the Jb middle coefficient array. All starts and end-strip data are paid; the finite unit-point/tangent norm is the missing operation. No new factoring bound, conditional genericity assumption, unguarded additive decoder or repository edit is claimed.
