# Newton-grid execution of the terminal boundary recurrence

24 October 2026. Scratch research. This tests a geometric Newton basis and a paid coefficient solve of the actual long polynomial. It gives an exact sparse shift identity and an initialized completion, but does not improve the soft k^(3/2) whole query.

## Actual initialized input

Use reciprocal-recurrence.md's paid augmented MAIN instance: m=k, G=2k, Q=q^k, acquired degree-J monic F, J=Theta(k) (augmentation changes only the constant), and

 R(T)=product_(0<=g<G) Q^(gJ) F(Q^(-g)T), D=JG=O(H), H=k².

Both coefficient ends of length k and all degree-J equation generators are actually supplied. The original last two factors per row are separately acquired and retained. The authoritative exact equation is

 F(Q^(-(G-1))T) R(QT)=F(QT) R(T).                 (1)

Equivalently rescale its two generators to A(T)R(QT)=A(Q^G T)R(T). All scalar normalizations are acquired units. The source reciprocal augmentation preserves the original query's prime zero support by a known-unit square and explicit original index reflection. No implicit long polynomial is treated as an acquired coefficient vector here.

The target is R modulo P_k(T)=product_(0<=i<k)(1-q^i T), or its scalar resultant. q^r-1 is actually guarded through C=16H. In the paid rough branch both underlying beta,W local orders are k-rough. Consequently Q^n-1 is a unit for 1<=n<=D<=4H: on every field component, q^n-1 is a unit by the existing guard, and raising q^n to k cannot create identity because its order is k-rough. This argument includes split coordinates; no original beta order is transferred to pi without the actual rough-group proof. Integers <=D are units since P,Q>16H.

## 1. Execute the geometric Newton shift

Let x_i=q^(-i) and N_d(T)=product_(0<=i<d)(T-x_i), N_0=1. Distinct nodes through 2k have unit differences by the existing short q guard. Conversion of an acquired degree-d vector between monomials and this basis can be done by monic product/remainder trees in soft d; when d=D this costs soft D, not soft k.

The key q-Weyl identity is exact:

 N_k(T) N_d(QT)=Q^d N_(d+k)(T).                  (2)

Indeed multiplying each shifted root by Q^-1 appends nodes x_k,...,x_(k+d-1). Thus a Newton expansion R=sum_(d=0)^D r_d N_d gives the sparse shifted expansion

 N_k R(QT)=sum_d Q^d r_d N_(d+k).                (3)

Multiplication by T is also explicit:

 T N_d=N_(d+1)+x_d N_d.                          (4)

Substituting (3) into (1), after multiplying by N_k, is an actual banded Newton equation: multiplication by either degree-J generator is the composition of J such bidiagonal operations, and multiplication by N_k has width k. This is a valid operator representation. Building its full coefficient table by (4) emits O(D(J+k)) entries and is not the requested short solve. Keeping products as factored operators avoids that table but does not acquire their terminal solution.

The desired remainder is precisely sum_(d<k) r_d N_d. Top monomial coefficients are convertible to the top Newton block in soft(D) by the general transform, or by a separate short-end computation if supplied; neither interpretation supplies the bottom Newton block. In particular a bottom MONOMIAL block is not a bottom Newton block: every N_d has nonzero constant term, so high Newton degrees affect low monomial degrees. No change of coordinate is credited as a solved boundary problem.

## 2. Test quotient closure before using a short q-Weyl state

The tempting update S(h)=h(QT) modulo P_k is well-defined on chosen degree-<k representatives, but is not induced by raw scaling on the quotient. Execute its first missing carry on the zero representative P_k:

 P_k(Q x_i)=product_(0<=r<k)(1-q^(k+r-i)), 0<=i<k.

Every exponent lies in [1,2k-1], so every value is a certified unit. Therefore P_k(QT) modulo P_k is itself a unit (its resultant is a product of these units, so the monic extended resultant identity supplies an inverse). It is not zero. If h=P_k u+v, the exact shifted state is

 h(QT) mod P_k = P_k(QT) u(QT) mod P_k + v(QT) mod P_k. (5)

The omitted quotient carry is multiplied by a unit, rather than annihilated. Equation (2) makes the same issue visible as the required N_k multiplier. Thus the tested degree-k quotient state does not close under the raw shift used in (1). This is an explicit failure of this update, not a theorem against other enriched states or scalar contractions.

At actual nodes, (1) instead links R(x_i) to R(Qx_i), outside the chosen k-point window. Repeating advances through G windows. Cross multiplication is always valid, but division by A(x_i) is not generally legal: these generator values can contain original collisions. The supplied reciprocal end relates windows, but supplies no amplitudes at the first window. A global-zero multiplier is not a licence to select an arbitrary amplitude.

## 3. A fully paid fast coefficient completion

There is an actual alternative to the quadratic-width Newton table. Write A(T)=sum_(h=0)^J a_h T^h, with a_0 a unit, R(T)=sum c_n T^n. The rescaled equation gives for n>=1

 a_0(Q^n-1)c_n = sum_(h=1)^min(J,n) a_h (Q^(Gh)-Q^(n-h)) c_(n-h). (6)

Its initial c_0 is the actually supplied constant coefficient. Every denominator on the left is a certified unit by the rough-order argument above. Crucially these denominators depend on n, not on a target value, so this solve is valid even if the terminal resultant vanishes.

Execute divide-and-conquer relaxed convolution: maintain the two known sequences c_r and Q^r c_r; a completed coefficient interval contributes to future right sides through convolutions with a_h Q^(Gh) and a_h, respectively. At each binary recursion level their disjoint interval convolutions have total soft O(D) cost. Solve each next coefficient by (6), batch-inverting the known unit diagonal if desired. This acquires the COMPLETE vector c_0,...,c_D in soft D arithmetic (logarithmic factors suppressed), using O(D) coefficients and O(log N)-bit exponent metadata. All Q powers, a_h Q^(Gh) and diagonal units cost O(D+J) initialization. Thus this is an executed initialized solver, not an invocation of a free approximant basis.

Now reduce monically modulo P_k in soft D and compute its resultant with P_k by guarded polynomial algorithms. A nonunit pivot is routed by the original coefficient classifier; original block/row restriction is rerun for localization rather than interpreting an auxiliary pivot as an original hit. This completed coefficient route costs soft D=soft k². It is slower than the existing labelled blocked completion soft sqrt(JL)=soft k^(3/2), which remains the fallback and preserves the original scalar/quadratic consumer and last-two-factor labels.

The short supplied coefficient ends do save initialization; they do not change the number D of coefficients emitted by (6). This ledger is specific to that solve. A terminal-only convolution circuit avoiding its middle coefficients would be additional work, not something established by the sparse shift (2).

## Outcome

The Newton basis gives the exact sparse q-shift identity (2), and the scalar coefficient recurrence (6) is genuinely solvable with paid unit diagonal and soft D work. The proposed short quotient update fails at the explicitly computed, unit-valued carry (5). No completed algorithm below soft k^(3/2) results. The remaining constructive target is an enriched terminal state or direct scalar contraction that uses the acquired two ends without emitting the D middle coefficients, with original restriction and zero localization intact. No generic recurrence, rank or complexity lower bound is asserted.

## 4. Strengthened test: acquire the true upper Newton boundary cheaply

The generic soft-D transform in Section 1 is unnecessary for the upper block. Here is the actual soft-k conversion, which supersedes that generic option. Let f(w)=w^D R(1/w) modulo w^k and b_D(w)=product_(i<D)(1-x_i w). The first k coefficients of b_D are acquired in soft k from its geometric-root power sums: sum_(i<D)q^(-ri)=(1-q^(-rD))/(1-q^(-r)), 1<=r<k. Only short, already guarded denominators occur; q^D is known. Logarithm/exponential uses only unit integers <k. Thus U=f/b_D modulo w^k is actual data, acquired with constant-one series inversion.

Put z_l=x_(D-1-l), B_r(w)=product_(l<r)(1-z_l w). Reversing the Newton expansion proves

 U(w)=sum_(r<k) r_(D-r) w^r/B_r(w) modulo w^k.

Acquire V(w)=B_(k-1)(w)U(w) modulo w^k. Then

 V(w)=sum_(r<k) r_(D-r) w^r product_(l=r)^(k-2)(1-z_l w).

Reversing this degree-<k identity gives an ordinary length-k Newton basis with the nodes in reversed order. Monic product-tree basis conversion therefore acquires ALL r_D,...,r_(D-k+1) in soft k. No middle coefficient of R or b_D is emitted. This is a genuine additional initialized upper boundary, together with the actual lower monomial block; it is still not the lower Newton block.

### Execute the first bidirectional window transfer

Set v_i=R(x_i). Evaluating (1) at x_(k+r), and using A(T)=F(Q^(-(G-1))T), gives the exact equation

 F(q^(-(kG+r))) v_r = F(q^(-r)) v_(k+r).          (7)

For the FIRST window 0<=r<k, all 2k values of F in (7) are acquired by monic MPE in soft(J+k), with explicitly generated geometric arguments. If F(q^(-r)) is a unit, its inverse gives a diagonal transfer multiplier from v_r to v_(k+r). Otherwise the coefficient classifier factors or returns a global-zero coefficient. In this first window the denominator is an acquired original or reciprocal-image endpoint: a native root y_j maps to original index r, while a reciprocal root a0/y_j, a0=q^(1-L0), maps to original index L0-1-r. Both indices lie in the MAIN interval because 0<=r<k and L0=kG. A global-zero product is localized to its acquired row factors and consumed with this stored root-type map. No numerator is inverted. In particular the first Newton-coefficient update is already visible at r=0:

 F(q^(-kG)) r_0
   =F(1) sum_(d=0)^k r_d N_d(x_k).

Its pivot for r_k is F(1)N_k(x_k). The geometric factor N_k(x_k) is a certified unit; F(1) is a real target product, tested and localized as above (native index 0 or reciprocal-image index L0-1). Hence this is an executed first update, not merely an operator identity. It leaves the k unknown initial values v_0,...,v_(k-1), or equivalently the lower Newton block.

One can continue (7) with r successively increased by k. The naive full transfer acquires O(D) evaluations of F, at denominator arguments q^(-r) and numerator arguments q^(-(kG+r)). These are actual degree-J polynomial MPE outputs costing soft(D+J); generating every multiplier and propagating k chains costs O(D). For later indices outside the original horizon no auxiliary global-zero coefficient is assigned an original leaf decoder: retain cross multiplication there, or use the zero-safe coefficient completion (6). Even on the branch where every denominator is a unit, full transfer emits Theta(D) values, so its clock is soft k², not soft k.

To test the supplied upper boundary rather than discard it, on that all-unit branch interpolate v_0,...,v_D at the D+1 geometric nodes symbolically as linear functions of the k initial amplitudes. The kth-chain transfer expresses each v_i as a known multiplier times ONE initial amplitude. Each upper Newton coefficient is an explicit divided-difference linear functional on these D+1 values; its weights are acquired from geometric product trees in soft D for one functional. Combining the k supplied upper coefficients consequently gives a genuine k-by-k linear system for the initial amplitudes. Its entries require these chain multipliers and weighted sums; writing all entries already costs k². Direct assembly and guarded dense elimination are a paid, generally slower completion, not a short Schur complement with free entries. Nonunit pivots invoke the coefficient classifier and require lawful zero-safe solving, so this dense option is not used as the universal fallback. The universal completion remains (6), followed by the original restriction/localization algorithm.

Thus this strongest tested bidirectional use DOES acquire the true upper Newton boundary and executes the first window transfer in soft k. Its literal all-window transfer and explicit boundary matching still cost at least their emitted Theta(D) and k² arrays, respectively. No assertion is made that another implicit matrix action or terminal-only solver must emit these arrays. Acquiring such an action in soft k, without target inversions or omitted quotient carries, is precisely the remaining problem; it has not been inferred from the cheap boundary conversion.

Final label scope: first-window denominator leaves retain their native/reciprocal root flag and use respectively r or L0-1-r as the original MAIN index. They are not assigned to either acquired tail index L0,L0+1. Later auxiliary pivots outside that scope receive no automatic original-index interpretation.
