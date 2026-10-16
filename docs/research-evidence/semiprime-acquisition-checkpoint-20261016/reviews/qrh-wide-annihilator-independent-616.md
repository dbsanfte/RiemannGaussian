# Independent review of the QRH long-annihilator extension

2026-10-16. Verdict: **PASS, conditional on accepting the pinned QRH Theorem 1.1 and the inherited universal monic separator.** No correctness gap found in the composite Jacobi menu, round-robin coverage, or additive bit-length charge. This review does not audit the QRH theorem's proof or assert a Lean result, nor does it acquire the annihilator.

Reviewed `qrh-wide-annihilator-extension.md` and `primary-source-pins.json`. All four pinned PDF/text byte counts and SHA256 values match. The pinned QRH text explicitly states both the Hecke result and the Dirichlet result in Theorem 1.1; Corollary 1.2 itself concerns prime moduli. The extension correctly derives rather than attributes the composite-character corollary.

## Uniform explicit formula and all residues

Let chi be primitive, nonprincipal and real, of conductor q. Accepting QRH and applying the functional equation places its nontrivial zeros in the **closed** strip 1/8 <= Re rho <= 7/8, including any zeros on the boundary. Thus the denominator in

    S_chi(x) = sum_rho 2*x^rho/[rho*(rho+1)*(rho+2)]

has no small-real-part singularity. The usual effective uniform zero count, with multiplicity, on unit height intervals is O(log(q*(2+|T|))). Summing against a cubic height denominator gives

    |S_chi(x)| <= C*x^(7/8)*log(2q),

with an absolute effective C. This needs no character-dependent constant from the proof of QRH.

For particularly clean bookkeeping, shift the Mellin integral for

    (-L'/L)(s,chi) * 2*x^s/[s*(s+1)*(s+2)]

from Re s>1 to **Re s=-1/2**. Then no negative trivial zero, and neither kernel pole -1 or -2, is crossed. At s=0:

* For odd chi, L(0,chi) is nonzero; the kernel's simple pole contributes -L'/L(0,chi).
* For even chi, L(s,chi) has its simple trivial zero at zero. The resulting double pole contributes a multiple of log x plus the constant term of L'/L at zero.

Both character-dependent constants are O(log(2q)) uniformly and effectively under the reflected strip. One way to see this without assuming a GRH-size L(1,chi) is to use the paired Hadamard product for the completed real L-function: its logarithmic derivative at 0 or 1 is bounded by the convergent paired zero sum, since both endpoints are a fixed distance from every nontrivial zero. Gamma-factor constants and the conductor term add O(log(2q)). The reflection is important here; a bare assertion about arbitrary primitive characters would allow a near-1 zero to make this estimate much larger.

On Re s=-1/2 the functional equation expresses L'/L in terms of its absolutely convergent Euler series at Re(1-s)=3/2, the conductor term, and gamma logarithmic derivatives. It is O(log(2q)+log(2+|Im s|)). The line integral is therefore O(x^(-1/2)*log(2q)). Standard contours avoiding zeros have vanishing horizontal integrals because of the cubic kernel denominator. This proves the report's deliberately looser remainder

    W_chi(x) = -S_chi(x) + O(log(2q)*log(2x)).

For zeta, its pole at s=1 gives x/3 exactly; zeta is nonzero at s=0, and the same shift yields the claimed error. There is no omitted nonprincipal pole at s=1 and no uncontrolled trivial-zero contribution. The alternative initial contour at 15/16 also lies strictly to the right of the accepted zero strip; the later explicit zero-sum proof avoids needing a separate uniform logarithmic-derivative assertion on that right line.

## Composite Jacobi character and the cutoff

For distinct odd P,Q, the two primitive Legendre characters have coprime conductors. Their product is primitive of conductor PQ and nonprincipal, regardless of PQ modulo 4. Thus chi_N is covered by the preceding uniform formula.

If no nonresidue prime occurs up to x, every unramified prime-power contribution to W_zeta and W_chi is identical. The remaining contribution is nonnegative and at most omega(q)*log x <= log(q)*log(x)/log 2. This comparison is valid even when x reaches a prime dividing q: those terms are precisely the included ramified contribution.

At x=C*(log(2q))^16, the zero-sum error divided by x is O(C^(-1/8)/log(2q)); all logarithmic and ramified errors are smaller after increasing one absolute effective C. Consequently a nonresidue prime exists by that cutoff. The report's common exponent 32 is a valid weakening. No dependence on the character or an ineffectively known analytic threshold remains in this implication. The algorithm nevertheless need not know C, because it scans bases and verifies factors algebraically.

The analogous proof under the fixed width delta=10^(-6) has constants depending only on that fixed delta and admits exponent 2/delta. The weaker primitive-roots route is unnecessary once the pinned Dirichlet QRH theorem is accepted. Its norm-pullback discussion does not introduce an extra hypothesis into the stronger route.

## Algebraic coverage and cost

Writing d_P=ord_P(gamma), the oddness assumption and gamma^K=1 imply d_P divides K0 after all twos are stripped from |K|. For each unit a,

    ord_P(a^K0) divides (P-1)/gcd(P-1,K0),

and hence divides (P-1)/d_P. No coprimality between d_P and its index is required. In the correct dyadic bin this order is below 2X/B <= M_X, so the inherited separator cannot return NoHit. Its earliest saturated-leaf guarantee proves exact equality of the two local orders even when only one order was bounded. A base having unequal local 2-primary orders therefore forces a proper factor in that bin.

Odd powering preserves those 2-primary orders. If v2(P-1)=v2(Q-1), a Jacobi-minus-one base separates them. If the valuations differ, a nonresidue at the prime with larger valuation separates them. Both witnesses lie in the common polylogarithmic integer menu. The algorithm need not know which case holds, identify the witness, or recognize either local Legendre symbol. Wrong-bin outputs are harmless.

The maximum cap is O(1+sqrt(N)/B), and therefore a separator costs soft O(1+N^(1/4)/m)=soft O(1+N^(1/12)) when m=Theta(N^(1/6)). There are only O(log N) bins. Each round computes a^K0 once and shares it across all bins. Binary powering charges soft O(L+1) bit work per round; the fixed polylogarithmic number of rounds absorbs this to soft O(L+1), even for arbitrary supplied L-bit K. Reading, absolute value, stripping twos, the optional gamma^K check, gcds, and bin construction fit the same total. Thus

    soft O(L + N^(1/12))

is justified under the stated promises. This does not require K to be a multiple of phi(N), and does not support a Miller-only polylogarithmic remainder: the one-small-local-order separator remains part of the paid algorithm.

No changes to the target report are mathematically required. The fixed shift to -1/2 above is an optional clarification that makes its zero-at-zero and trivial-zero justification explicit.
