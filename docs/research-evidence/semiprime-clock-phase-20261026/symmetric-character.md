# Finite symmetric-character probe

Status: a legal reciprocal native rebuild and two executed finite character/summation tests; no improved query bound. The retained initialized execution is soft O(J+sqrt(Jh)), hence soft K^(5/4). Reciprocal/Cayley folding and paired q-factorials have prior credit; they are not newly acquired scalars here.

## 1. Exact character closure, including its tail

Work modulo z^h over the prepared composite coefficient ring. Put

    B(z)=sum_{m=0}^{h-1} q^{m(m-1)/2}z^m/(q;q)_m,
    H(z)=B(z)/B(-z).

All denominators used here are among the screened unit gaps. The formal q-binomial identity, or its coefficient recurrence, gives

    H(qz)=(1-z)H(z)/(1+z),
    [z^m]H=(-1;q)_m/(q;q)_m.

These are finite truncated identities: no convergence or native root-of-unity assumption is used. With S f(z)=f(qz), L_+=(1+z)S and L_-=(1-z)S, one has H^{-1}L_+H=L_-. For the actual response C^+(z)=B(z)A(z), its parity partner is exactly

    C^-(z)=B(z)A(-z)=H(z)C^+(-z).

Thus a short prefix of H is acquired in soft J, but the requested final coefficient still requires the correlated convolution with C^+. This is a concrete initialized transform, not a second independent short inverse.

The tempting finite-alphabet substitution has the exact correction

    H(z)=prod_{i=0}^{m-1}[(1+q^i z)/(1-q^i z)] H(q^m z) mod z^h.

The remaining H(q^m z) is not 1 at native q. Dropping it loses the finite response. Emitting its h coefficients costs h, already above the target. This test does not exclude another selected-coefficient algorithm.

## 2. Legal physical inverse rebuild and trace clock

Start with the actually selected unique-cover rows y_j, j=1..J, and centered clock q^i, -M<=i<=M. Adjoin the ACTUAL inverse rows y_j^{-1}, retaining the original row's public tag. This is a constant-factor family enlargement; it does not assume the supplied family was inverse closed. Negated integer coefficient/phase labels give the inverse. Centered phase boundary ell=-H/2 cannot occur in the native pure family: for nonaxes v_3(ell)=v_3(a)<e, whereas v_3(H/2)=2e; axis phases have valuation e. Alternatively retain an explicit q-carry. The newer parity family also excludes that boundary by ell=0 mod4 while H/2=2 mod4.

Screen y_j-1 by the actual mixed-label decoder in soft K. A proper gcd factors; a saturated labelled relation is handled by the licensed annihilator decoder. On continuation these are units. Native y_j have odd local order, hence y_j+1 is a unit; consequently y_j-y_j^{-1} is a unit. If a later summation requires interior hits, screen y_j-q^{+M} and y_j-q^{-M} as well using the original labels. These are genuine original leaves, not arbitrary additive annihilators.

At the promised good field, the original unique hit i is now the two distinct physical hits i and -i, with identical parity. Define

    D_c(x)=prod_j(x-y_j)(x-y_j^{-1})=x^J G(x+x^{-1}),
    G(Z)=prod_j[Z-(y_j+y_j^{-1})].

G is acquired in soft J. Its degree is J relative to ORIGINAL J rows, not J/2. The regularized trace source is

    x^J/[D_c(x)+delta x^J]=1/[G(x+x^{-1})+delta].

This numerator/regularizer is essential. A physical double hit gives residue 2(-1)^i in the signed centered sum; after division by unit 2 it gives parity. Once the middle is screened, folding the two physical copies gives exactly the residue of

    sum_{i=1}^M (-1)^i/[G(q^i+q^{-i})+delta].

Each folded denominator has a SIMPLE delta pole; physical multiplicity two is not a double delta pole, nor a statement about the different deformation D_c+delta. The trace nodes are unit-separated since

    (q^i+q^{-i})-(q^k+q^{-k})=(q^i-q^k)(1-q^{-i-k}),

and all required exponents are <=2M in the inherited screened range.

Execution: separate even/odd i, set X=q^{2t}; their trace arguments are X+X^{-1} and qX+q^{-1}X^{-1}. The fraction-free pair transfer has diagonal f_even f_odd and off-diagonal f_odd-f_even, where f=G(trace)+delta. Laurent clearing gives degree O(J), and halves the clock only by a constant. The existing division-free polynomial-matrix block engine therefore costs soft(J+sqrt(JM)). This preserves a valid parity output but gives no exponent improvement. All zero-divisor branches use norm/coordinate tests and actual labelled localization; native collision denominators are never inverted.

## 3. A finite q-Dixon summation, executed on a reciprocal pair

Primary source: Wenchang Chu, “Terminating Almost Poised q-Dixon Sums”, Kyushu J. Math. 77 (2023), 131–140, equation (1), DOI 10.2206/kyushujm.77.131. PDF: https://www.jstage.jst.go.jp/article/kyushujm/77/1/77_131/_pdf/-char/en . Its even terminating formula (epsilon=0,1) is

    3phi2(q^{-2M},b,d; q^{1-2M}/b,q^{1-2M}/d; q,q^{1+epsilon-M}/(bd))
    = q^{M(epsilon-1)} (b,d;q)_M/(q,bd;q)_M * (q,bd;q)_{2M}/(b,d;q)_{2M}.

Set b=q^{-M}/y, d=q^{-M}y. Then bd=q^{-2M}, the lower parameters are qd,qb, and cancellation of the two HALF products gives exactly

    S_epsilon(y)=(-1)^M q^{M(epsilon-1)-M(M+1)/2} (q;q)_{2M}/(y,y^{-1};q)_M.

This follows from (q^{-M};q)_M=(-1)^M q^{-M(M+1)/2}(q;q)_M, so is a finite rational identity with cleared polynomial meaning at poles. The two displayed positive-character responses satisfy S_1=q^M S_0. They therefore do not by themselves produce the negative-character/parity response. More explicitly, take n=2M, T_+=q^M y, T_-=q^M/y, D_T(X)=(X-T_+)(X-T_-). The coefficient of z^n in B(z) sum_{k>=0} (-1)^k zeta^k q^k z^k/[(q;q)_k D_T(q^k)] is B_n/D_T(1) times this 3phi2 with argument zeta q^2. (This follows by B_{n-k}/B_n=(-1)^k q^k(q^{-n};q)_k.) Thus the displayed Dixon evaluations have zeta=q^{M-1+epsilon}. Replacing zeta by its negative, as the parity comparison requires, is not an evaluation supplied by this displayed theorem.

More significantly, even the evaluated response retains the native half-clock paired product (y,y^{-1};q)_M. Applying the formula to each acquired trace root therefore leaves J long paired factors. Meromorphic continuation/first delta jets are legal after the above unit gates, but they do not acquire those factors. Shared baseline cost remains soft(J+sqrt(JM)); separate evaluation of all M factors is worse. The identity is useful exact input to a future paired-factor algorithm, not such an algorithm. No claim about all q-Kummer or very-well-poised summations follows from this specific test.

## 4. Schur-Q/Pfaffian cancellation test

Primary source: Soichi Okada, “Pfaffian Formulas and Schur Q-Function Identities”, arXiv:1706.01029v1 (2017), Adv. Math. 353 (2019), 446–470, Theorems 4.1 and 5.1: https://arxiv.org/html/1706.01029 . Its one-row generating function is prod_i(1+x_i z)/(1-x_i z), and its Q/P Cauchy identity uses the corresponding pairwise product. Schur's Pfaffian kernel was already tested in the Oct23 reciprocal-Bezout report; this is not first credit.

Actual inverse rows become opposite variables under the legal Cayley coordinate v=(y-1)/(y+1), since v(y^{-1})=-v(y). The complete Q-kernel contribution then cancels identically:

    [(1+vz)/(1-vz)] [(1-vz)/(1+vz)]=1.

This cancels the collision divisor as well as the harmless factors. At a collision the cancelled numerator and denominator both vanish; its cleared identity does not retain the desired residue. A symmetry-preserving deformation still gives 1. A noncovariant marked deformation retaining the denominator restores an inverse-product response which has not been acquired. Thus this exact Pfaffian/Q cancellation does not deliver the selector. It is not an obstruction to other insertions or algorithms.

## 5. Exact remaining initialized target

After the legal trace fold the sufficient finite target is a single signed residue over M unit-separated trace-clock nodes, with acquired degree-J G and simple delta regularization. Either a selected negative-character q-Dixon-type evaluation that contracts ALL varying trace roots, or a direct last-coefficient algorithm for H(z)C^+(-z) avoiding the long convolution, would improve the readout. Neither is supplied by the executed identities above. All startup data cost soft K; the first unpaid operation is the correlated long scalar readout, not the trace polynomial or the short character coefficients. No factorization or general algorithm lower bound is asserted.
