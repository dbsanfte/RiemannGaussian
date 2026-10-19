# Exterior correction and literal physical transfer

Research checkpoint, 2026-10-19. The unchanged imported correction now has
proved bounds on a larger contour region. The native marked-factor estimate
has also been extended. A separate paper-level application audit identifies
how a quantitative full Gauss-series mean would apply to the actual physical
weights. None of these results bounds the remaining signed theta pairing or
improves the imported strict `Re(s)>7/8` zero-free endpoint.

This follows the [source/cusp checkpoint](arithmetic-operator-cusp-source-frontier.md)
and the [Siegel interpolation review](siegel-interpolation-review.md). The
transfer principle remains the same: retain the actual arithmetic object,
its source, and every fixed or moving support condition.

## The same Euler correction on both exterior contours

[QuasiRHExteriorRegionAudit](../scripts/QuasiRHExteriorRegionAudit.lean)
proves, for the actual local factor and phase norms at most one,

    |unramifiedClosed-1| <= 240 Q^(-149/100)
       on Re x>=3/4, Re w>=19/20, Re z>=33/200;
    |unramifiedClosed-1| <= 240 Q^(-73/50)
       on Re x>=3/4, Re w>=9/10, Re z>=4/25.

Both bounds require `Q>=4`. Native denominator nonvanishing and separate
coordinate analyticity are proved directly on these enlarged regions; an
old theorem with a `7/8` hypothesis is not applied outside its domain.

[QuasiRHExteriorCorrectionAudit](../scripts/QuasiRHExteriorCorrectionAudit.lean)
uses unconditional ideal summability of the second envelope. After excluding
a sufficiently large, fixed finite set of prime ideals, the **same** global
normal product differs from one by at most `1/2`. It is nonzero, with inverse
norm at most two, uniformly in the native finite character and all heights.

The product is separately analytic on the open coordinate half-planes.
The actual `w=19/20` and `z=33/200` contours lie strictly inside them, with
margins `1/20` and `1/200`. Bounds hold at `Re x=3/4`, while the displayed
analyticity theorem in x has open domain `Re x>3/4`.

`exists_exterior_source_exclusions` constructs compatible enlarged
exclusions and retains the original `SourceExclusions` obligations. The
new summable envelope dominates the old `17/10` envelope. The calibration
must then be rebuilt for this new fixed set before the detector scale grows.
An old calibration does not automatically enforce coprimality with newly
excluded primes.

## The marked cancellation survives with an amended rate

[QuasiRHExteriorSlotAudit](../scripts/QuasiRHExteriorSlotAudit.lean)
retains the exact unit-character cancellation and proves

    |regionSlot+1| <= 1440 Q^(-alpha)

for `4/5<=alpha<=7/8`, `Re x>=alpha`, the original exterior w/z bounds,
`Q>=480`, and the actual unit character. Its prime-ideal specialization
retains the angular phase, target character, coprimality condition and
the `Q^(z-1)` factor in the literal marked multiplier.

The weakened exponent is necessary: at the double source coordinate the
local error has leading term `-eta(P) Q^(-x)`. The old `7/8` exponent
cannot simply be carried into a smaller source half-plane. The new rate
still gives a geometric saving for marks of size `Q>=c Z^ellMin`.

The detailed principal-contour audit is **paper-level**. The reciprocal-L
bound already works at every line strictly right of the native zero
supremum, with height degree two. The principal L factors, Gaussian and
window estimates need no new `7/8` restriction. Keeping all their constants,
the normalized principal comparison has errors

    O(Z^(betaStar-11/16-17/48000+nu))
      + O(Z^(betaStar-11/16+e-alpha*ellMin)).

Positive margins are available when `0<nu<17/48000`, `0<e<=1/1000` and
`e<alpha*ellMin`. The two exterior powers themselves are unchanged.
This is a verified application calculation, not a newly compiled full
contour wrapper. The complete nonprincipal, ramified and high-row transport
must also be checked before asserting a source theorem in the enlarged band.

## Applying the full-series mean to the literal physical weights

The relevant analytic input is Proposition 3 of the AI-authored preprint
[Primitive sextic Kubota means and a sharp sixth-power-free large sieve,
paper 10/v2](https://rstation.ai/problems/riemann_hypothesis/papers/10/v2).
It is **not imported into Lean**. The application audit is conditional on
that proposition and its full-vector continuation, growth and sieve inputs.
It does not substitute the paper's primitive-series corollary for the
repository's imprimitive physical series.

The actual calibration character vanishes on numerators not coprime to
the entire current exclusion set. On the surviving support, the previously
checked calibration transfer moves each good-prime factor into a fixed
numerator multiplier `M_C`, with `N M_C<=K_C^4`. The bad-place and ray
profile remains in the fixed 216-component local sixth-power family.
Every physical prime power and the Fourier index `-m` are retained.

Fixed good-prime exclusions can be removed in an explicitly ordered finite
recursion. At each prime it retains the current character, its value at that
prime, the reciprocity twist, numerator exponents `j` and `4-j`, and the
denominator `1-q^(5-6u)`. Those denominators introduce no pole in the physical
contour strip `Re u>=1+eta`. No moving conductor is introduced.

The `B=1` case of Proposition 3, followed by the unique decomposition of
a numerator into a coprime squarefree part and a powerful part, gives the
required unrestricted numerator mean. The powerful-part cost sums as
`sum (Nh)^(-1/2)=O(log Q)`. Thus all numerator valuations remain included.
The precise local-profile and analytic assumptions are recorded in the
checkpoint's independently reviewed application note.

For the actual physical normalization `P=Y^(1/2)*lowRayAmplitude`, the
resulting contour identity is

    P_sigma,Y,v(m)
      = Y^(1/6) W1hat(1/6+iv) rho_hsigma(-m) + E_sigma,Y,v(m),

with conditional mean bound

    sum_(Nm~Q, (m,S)=1) |E_sigma,Y,v(m)|^2
      << Y^(2eta) Q^(1+epsilon) (1+|v|)^6.

The `Y^(2eta)` loss is essential. At the native scales `Y^8<<Q^5`, a
sufficiently small **fixed** eta absorbs it into the desired subpower.
The residue is the full physical sextic residue, not the primitive residue,
an explicit cubic substitute, or an assumed scalar spectral projection.

## What this changes, and the remaining gate

The formal correction and slot results remove concrete inherited analytic
restrictions. The paper application eliminates the need for an unspecified
theorem about an arbitrary fixed section: it identifies a finite reduction
of the actual section to a stated quantitative input, with its original
masks and constants.

Combining that conditional physical mean with the already imported marked,
cube and tuple energy estimates gives the previously calculated continuous
cost `Z^(17/96+O(epsilon))`. It separates from a source
`Z^(beta-11/16)` only when `beta>83/96`. Once the complete source and
exterior accounting is established, this comparison would place its
surviving source in the full signed theta contribution. It does **not**
pay that contribution.

The next substantive gates are the actual analytic import/physical
transfer, complete source and exterior accounting, and an independent bound
on the unchanged theta covariance. A scalar projection or a generic norm
does not provide the last step. No new zero exclusion, independent RH
endpoint inequality, or exhausted Tier-1 family is claimed.

Validation, exact commands, artifact hashes and formal/paper boundaries are
recorded in [the manifest](arithmetic-operator-exterior-physical-transfer-gates.json).
This remains local work: no root registration, broad CI, commit or push.
