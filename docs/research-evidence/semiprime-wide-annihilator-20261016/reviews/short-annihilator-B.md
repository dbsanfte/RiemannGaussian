# Independent review B: short-annihilator extractor and wide-cover bridge

2026-10-16. Verdict: PASS for both supplied exact reports. No mathematical correction requested. This is a classical proof/interface review, not a new Lean certification or acquisition result.

## Exact reviewed bytes
- `short-annihilator-extractor.md`: 10375 bytes; SHA256 `433d10d8c413ad8cbe7ecb09bbafe0794559afa8b2b535e3667b9491950c1131`.
- `wide-cover-certificate.md`: 11079 bytes; SHA256 `063250598bc508dc149b0e64fc1a638bab83a7be059496669322142cbcddc1e1`.
- `small-order-separator.md`: 5679 bytes; SHA256 `5fd92268584613b0ffe9b1c12e076dd3ef93a52d53cb3d76c799b2a747793109`.
- `uniform-preprocessing-audit.md`: 6015 bytes; SHA256 `d656d7284fe923e567070f3192dffb7c9410d7e426a8564ab7225272da01fabf`.

## Standalone extractor

Section 1 correctly states balance and m=Theta(N^(1/6)), the odd local orders and SMALL INDICES, and a supplied nonzero polylog-bit global annihilator. Prime/distinct/coprime local orders are not assumed. Reading and powering by a polylog-bit exponent fits suppressed fixed log powers, even when its numerical multiplier is enormous.

Section 2 faithfully states the composite-safe separator, including its unconditional NoHit implication: all tested b^t-1 are units, so BOTH local orders exceed the tested horizon. Monic division/evaluation requires no unit point differences; repeated nodes are harmless. Earliest saturated leaf returns exact common local order, not an arbitrary multiple. Sections 3 and 5-6 use the promised small indices to exclude NoHit on every powered trial base.

Section 3's b^v=1 proof is especially important: r divides K_0, so K_0*v is a multiple of P-1. This remains valid if r and v have common factors. Odd powering preserves the entire 2-primary order. The Jacobi-minus base therefore forces different field valuations whenever the separator returns equal orders. A nonresidue in the larger-valuation field then forces unequal local orders and a factor. No hidden field identity or Legendre-symbol oracle is used.

Section 4 uses the separately reviewed Lau--Wu cubefree-character theorem with strict exponent slack. Both the Jacobi character modulo distinct odd squarefree N and the prime-field characters meet its stated hypothesis. Balance changes the prime exponent to one half of the modulus exponent, yielding the claimed 5/64 cutoff. Section 5 invokes a separator only ONCE after its character scan; Section 6 invokes one per trial. Thus the claimed exponents and 31/192 arithmetic are correct. The precise m upper-bound qualification is now explicit.

Section 7's computable cutoff and deterministic trial-division fallback make the algorithm total without a known analytic threshold. Uniform sufficiently-large success means fallback is confined to finitely many promised N, so it affects only the asymptotic constant. This does not claim an effective numerical Burgess threshold or validate every invalid input promise. Factor outputs are checked. The separate uniform-preprocessing theorem is an identified dependency; this report does not silently acquire K or transfer original collision coverage to a different base.

## Wide explicit-cover certificate

Sections 1-2 correctly use the ENTIRE light-catalog congruence-energy bound on CURRENT qualified candidates. Trimming large explicit relative origins loses o(m) labels and leaves a witness of at least m/2 labels. Full-input dependence of this witness causes no problem because this is an extraction, not a fixed-plan counting argument. Full covers contain the witness; no useful collision after trimming is asserted.

All-zero equal-position/cross-difference relations force rational-affine values in each assigned carrier. Weighted energy bounds labeled multiplicities and contradicts nearlinear k²T. Therefore a nonzero polylog-bit candidate exists. A cover in just ONE hidden field makes the gcd greater than one: proper gcd factors immediately, saturation supplies a global annihilator to the standalone extractor. Seed/ratio values, discrete logarithms, and an arbitrary common origin are unnecessary. No numerical span or multiplier restriction survives; the total EXPLICIT expanded relative-origin encoding remains essential.

Section 3's summarized prefix/binary-search separator is a compatible soft-cost variant of the independently proved row/tree separator. Sections 3-4 preserve the conditional analytic input and do not claim an acquired cover or new direct-norm clock. Reading the list, inherited witness setup, trimming, candidates, one power/gcd and conditional extraction fit soft O(m).

Section 5's converse is sound on the exact prime-order qualified source: v,w<m and the auxiliary prime m cannot divide v,w or R_P,R_Q, so gcd(m²,phi)=1. The displayed modular inverse makes every reoriginated exponent divisible by phi, producing the global one-point cover with O(m log N) explicit bits. This uses known factors and changes the original search intervals; it does not make a free cover or assert original interval completeness. The two conditional reductions consequently support the stated source-restricted equivalence, not a lower bound or all-input controller theorem.

No correction needed. Both reports keep the acquisition gap and formal-proof gap explicit.
