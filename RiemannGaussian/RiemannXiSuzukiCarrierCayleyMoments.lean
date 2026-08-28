import RiemannGaussian.RiemannXiSuzukiCarrierCayleyHardy

/-!
# Cayley moments and the Hardy Hankel block

The positive and negative unitary orbits from the Cayley--Hardy split have a
concrete scalar Gram geometry.  This file packages every integer power of the
unit-modulus boundary Cayley coordinate as an `L²(μ)` vector and defines its
moment against the finite xi-energy Nevanlinna measure.

The bilateral orbit Gram matrix is Toeplitz: its `(m,n)` entry is the moment
at `n-m`.  Under the previous positive/negative Hardy indexing, the cross
block is therefore Hankel, with entry indexed by `m+n+1`.  Every moment is
also identified with its literal xi-energy weighted Lebesgue integral.

No decay or summability of these moments is asserted here; that arithmetic
Hankel estimate is the newly exposed frontier.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The integer-power Cayley character on the real boundary. -/
def suzukiXiCarrierCayleyBoundaryZPower (k : ℤ) (x : ℝ) : ℂ :=
  suzukiXiCarrierCayleyBoundaryCoordinate x ^ k

/-- Every boundary Cayley character is Borel measurable. -/
theorem measurable_suzukiXiCarrierCayleyBoundaryZPower (k : ℤ) :
    Measurable (suzukiXiCarrierCayleyBoundaryZPower k) := by
  exact measurable_suzukiXiCarrierCayleyBoundaryCoordinate.pow_const k

/-- Every integer-power Cayley character has pointwise unit norm. -/
@[simp] theorem norm_suzukiXiCarrierCayleyBoundaryZPower
    (k : ℤ) (x : ℝ) :
    ‖suzukiXiCarrierCayleyBoundaryZPower k x‖ = 1 := by
  unfold suzukiXiCarrierCayleyBoundaryZPower
  rw [Complex.norm_zpow,
    norm_suzukiXiCarrierCayleyBoundaryCoordinate, one_zpow]

/-- Every integer-power Cayley character belongs to the finite carrier
`L²` space. -/
theorem memLp_two_suzukiXiCarrierCayleyBoundaryZPower (k : ℤ) :
    MemLp (suzukiXiCarrierCayleyBoundaryZPower k) 2
      suzukiXiCarrierNevanlinnaMeasure := by
  apply (memLp_const (μ := suzukiXiCarrierNevanlinnaMeasure) (1 : ℂ)).congr_norm
  · exact
      (measurable_suzukiXiCarrierCayleyBoundaryZPower k).aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by simp

/-- The bilateral integer-indexed Cayley orbit in the finite carrier Hilbert
space. -/
def suzukiXiCarrierCayleyBilateralOrbit (k : ℤ) :
    Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  (memLp_two_suzukiXiCarrierCayleyBoundaryZPower k).toLp
    (suzukiXiCarrierCayleyBoundaryZPower k)

/-- The packaged bilateral orbit has its literal boundary character almost
everywhere. -/
theorem suzukiXiCarrierCayleyBilateralOrbit_ae (k : ℤ) :
    suzukiXiCarrierCayleyBilateralOrbit k =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        suzukiXiCarrierCayleyBoundaryZPower k :=
  MemLp.coeFn_toLp (memLp_two_suzukiXiCarrierCayleyBoundaryZPower k)

/-- The `k`-th Cayley moment of the canonical xi-energy measure. -/
def suzukiXiCarrierCayleyMoment (k : ℤ) : ℂ :=
  ∫ x : ℝ, suzukiXiCarrierCayleyBoundaryZPower k x
    ∂suzukiXiCarrierNevanlinnaMeasure

/-- Every Cayley character is integrable against the finite carrier measure. -/
theorem integrable_suzukiXiCarrierCayleyBoundaryZPower (k : ℤ) :
    Integrable (suzukiXiCarrierCayleyBoundaryZPower k)
      suzukiXiCarrierNevanlinnaMeasure := by
  rw [← memLp_one_iff_integrable]
  exact (memLp_two_suzukiXiCarrierCayleyBoundaryZPower k).mono_exponent
    (by norm_num)

/-- Each Cayley moment is literally the corresponding xi-energy weighted
Lebesgue integral. -/
theorem suzukiXiCarrierCayleyMoment_eq_xiEnergy_integral (k : ℤ) :
    suzukiXiCarrierCayleyMoment k =
      ∫ x : ℝ, suzukiXiCarrierNevanlinnaWeight x •
        suzukiXiCarrierCayleyBoundaryZPower k x := by
  unfold suzukiXiCarrierCayleyMoment
  exact integral_suzukiXiCarrierNevanlinnaMeasure_eq_smul _

/-- Pointwise multiplication of two Cayley characters, conjugating the first,
subtracts their integer frequencies. -/
theorem star_suzukiXiCarrierCayleyBoundaryZPower_mul
    (m n : ℤ) (x : ℝ) :
    starRingEnd ℂ (suzukiXiCarrierCayleyBoundaryZPower m x) *
        suzukiXiCarrierCayleyBoundaryZPower n x =
      suzukiXiCarrierCayleyBoundaryZPower (n - m) x := by
  let u : ℂ := suzukiXiCarrierCayleyBoundaryCoordinate x
  have hnorm : ‖u‖ = 1 :=
    norm_suzukiXiCarrierCayleyBoundaryCoordinate x
  have hu : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
  change starRingEnd ℂ (u ^ m) * u ^ n = u ^ (n - m)
  rw [map_zpow₀, ← Complex.inv_eq_conj hnorm, inv_zpow, ← zpow_neg,
    ← zpow_add₀ hu]
  congr 1
  ring

/-- The bilateral Cayley-orbit Gram matrix is Toeplitz: an entry depends only
on the frequency difference. -/
theorem inner_suzukiXiCarrierCayleyBilateralOrbit_eq_moment
    (m n : ℤ) :
    inner ℂ (suzukiXiCarrierCayleyBilateralOrbit m)
        (suzukiXiCarrierCayleyBilateralOrbit n) =
      suzukiXiCarrierCayleyMoment (n - m) := by
  rw [L2.inner_def]
  calc
    (∫ x : ℝ,
        inner ℂ (suzukiXiCarrierCayleyBilateralOrbit m x)
          (suzukiXiCarrierCayleyBilateralOrbit n x)
        ∂suzukiXiCarrierNevanlinnaMeasure) =
        ∫ x : ℝ,
          starRingEnd ℂ (suzukiXiCarrierCayleyBoundaryZPower m x) *
            suzukiXiCarrierCayleyBoundaryZPower n x
          ∂suzukiXiCarrierNevanlinnaMeasure := by
      apply integral_congr_ae
      filter_upwards [suzukiXiCarrierCayleyBilateralOrbit_ae m,
        suzukiXiCarrierCayleyBilateralOrbit_ae n] with x hm hn
      rw [hm, hn, RCLike.inner_apply']
    _ = ∫ x : ℝ,
        suzukiXiCarrierCayleyBoundaryZPower (n - m) x
        ∂suzukiXiCarrierNevanlinnaMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦
        star_suzukiXiCarrierCayleyBoundaryZPower_mul m n x
    _ = suzukiXiCarrierCayleyMoment (n - m) := rfl

/-- Negative Cayley moments are complex conjugates of the corresponding
positive moments. -/
theorem suzukiXiCarrierCayleyMoment_neg (k : ℤ) :
    suzukiXiCarrierCayleyMoment (-k) =
      starRingEnd ℂ (suzukiXiCarrierCayleyMoment k) := by
  calc
    suzukiXiCarrierCayleyMoment (-k) =
        inner ℂ (suzukiXiCarrierCayleyBilateralOrbit 0)
          (suzukiXiCarrierCayleyBilateralOrbit (-k)) := by
      simpa using
        (inner_suzukiXiCarrierCayleyBilateralOrbit_eq_moment 0 (-k)).symm
    _ = starRingEnd ℂ
        (inner ℂ (suzukiXiCarrierCayleyBilateralOrbit (-k))
          (suzukiXiCarrierCayleyBilateralOrbit 0)) := by
      rw [inner_conj_symm]
    _ = starRingEnd ℂ (suzukiXiCarrierCayleyMoment k) := by
      rw [inner_suzukiXiCarrierCayleyBilateralOrbit_eq_moment]
      congr 2
      ring

/-- Every Cayley moment is bounded by the total xi-energy measure mass. -/
theorem norm_suzukiXiCarrierCayleyMoment_le_measureMass (k : ℤ) :
    ‖suzukiXiCarrierCayleyMoment k‖ ≤
      suzukiXiCarrierNevanlinnaMeasure.real univ := by
  unfold suzukiXiCarrierCayleyMoment
  simpa using norm_integral_le_of_norm_le_const
    (Eventually.of_forall fun x ↦
      le_of_eq (norm_suzukiXiCarrierCayleyBoundaryZPower k x))

/-- The canonical mass bound gives the uniform numerical estimate `‖M_k‖ ≤
pi` for every integer moment. -/
theorem norm_suzukiXiCarrierCayleyMoment_le_pi (k : ℤ) :
    ‖suzukiXiCarrierCayleyMoment k‖ ≤ Real.pi :=
  (norm_suzukiXiCarrierCayleyMoment_le_measureMass k).trans
    suzukiXiCarrierNevanlinnaMeasure_real_univ_le_pi

/-! ## Identification with the one-sided Hardy orbits -/

/-- The literal inverse boundary coordinate is the multiplicative inverse of
the forward coordinate. -/
theorem suzukiXiCarrierCayleyBoundaryInverseCoordinate_eq_inv (x : ℝ) :
    suzukiXiCarrierCayleyBoundaryInverseCoordinate x =
      (suzukiXiCarrierCayleyBoundaryCoordinate x)⁻¹ :=
  eq_inv_of_mul_eq_one_right
    (suzukiXiCarrierCayleyBoundaryCoordinate_mul_inverse x)

/-- An `n`-fold forward unitary power acts almost everywhere by the `n`-th
boundary Cayley monomial. -/
theorem suzukiXiCarrierCayleyForwardPower_ae
    (n : ℕ) (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyForwardPower n f =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        fun x : ℝ ↦
          suzukiXiCarrierCayleyBoundaryCoordinate x ^ n * f x := by
  induction n generalizing f with
  | zero =>
      simp
  | succ n ih =>
      rw [suzukiXiCarrierCayleyForwardPower_succ]
      filter_upwards [ih (suzukiXiCarrierCayleyUnitary f),
        suzukiXiCarrierCayleyUnitary_ae f] with x hpower hunitary
      rw [hpower, hunitary, pow_succ]
      ring

/-- An `n`-fold inverse-unitary power acts almost everywhere by the `n`-th
inverse boundary monomial. -/
theorem suzukiXiCarrierCayleyBackwardPower_ae
    (n : ℕ) (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyBackwardPower n f =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        fun x : ℝ ↦
          suzukiXiCarrierCayleyBoundaryInverseCoordinate x ^ n * f x := by
  induction n generalizing f with
  | zero =>
      simp
  | succ n ih =>
      rw [suzukiXiCarrierCayleyBackwardPower_succ]
      filter_upwards [ih (suzukiXiCarrierCayleyUnitary.symm f),
        suzukiXiCarrierCayleyUnitary_symm_ae f] with x hpower hunitary
      rw [hpower, hunitary, pow_succ]
      ring

/-- The previous strictly positive Hardy orbit is the corresponding positive
part of the bilateral integer orbit. -/
theorem suzukiXiCarrierCayleyForwardOrbit_eq_bilateralOrbit
    (n : ℕ) :
    suzukiXiCarrierCayleyForwardOrbit n =
      suzukiXiCarrierCayleyBilateralOrbit (n + 1 : ℕ) := by
  apply Lp.ext
  filter_upwards [suzukiXiCarrierCayleyForwardPower_ae (n + 1)
      suzukiXiCarrierNevanlinnaOneLp,
    suzukiXiCarrierNevanlinnaOneLp_ae,
    suzukiXiCarrierCayleyBilateralOrbit_ae (n + 1 : ℕ)]
      with x hpower hone hbilateral
  rw [suzukiXiCarrierCayleyForwardOrbit, hpower, hone, hbilateral]
  unfold suzukiXiCarrierNevanlinnaOneFunction
    suzukiXiCarrierCayleyBoundaryZPower
  simp only [mul_one, zpow_natCast]

/-- The previous nonpositive Hardy orbit is the corresponding negative part
of the bilateral integer orbit. -/
theorem suzukiXiCarrierCayleyBackwardOrbit_eq_bilateralOrbit
    (n : ℕ) :
    suzukiXiCarrierCayleyBackwardOrbit n =
      suzukiXiCarrierCayleyBilateralOrbit (-(n : ℤ)) := by
  apply Lp.ext
  filter_upwards [suzukiXiCarrierCayleyBackwardPower_ae n
      suzukiXiCarrierNevanlinnaOneLp,
    suzukiXiCarrierNevanlinnaOneLp_ae,
    suzukiXiCarrierCayleyBilateralOrbit_ae (-(n : ℤ))]
      with x hpower hone hbilateral
  rw [suzukiXiCarrierCayleyBackwardOrbit, hpower, hone, hbilateral,
    suzukiXiCarrierCayleyBoundaryInverseCoordinate_eq_inv]
  unfold suzukiXiCarrierNevanlinnaOneFunction
    suzukiXiCarrierCayleyBoundaryZPower
  simp only [mul_one, zpow_neg, zpow_natCast, inv_pow]

/-- The Gram matrix within the forward Hardy orbit is Toeplitz. -/
theorem inner_suzukiXiCarrierCayleyForwardOrbit_eq_moment
    (m n : ℕ) :
    inner ℂ (suzukiXiCarrierCayleyForwardOrbit m)
        (suzukiXiCarrierCayleyForwardOrbit n) =
      suzukiXiCarrierCayleyMoment ((n : ℤ) - (m : ℤ)) := by
  rw [suzukiXiCarrierCayleyForwardOrbit_eq_bilateralOrbit,
    suzukiXiCarrierCayleyForwardOrbit_eq_bilateralOrbit,
    inner_suzukiXiCarrierCayleyBilateralOrbit_eq_moment]
  congr 1
  push_cast
  ring

/-- The Gram matrix within the backward Hardy orbit is Toeplitz with the
opposite orientation. -/
theorem inner_suzukiXiCarrierCayleyBackwardOrbit_eq_moment
    (m n : ℕ) :
    inner ℂ (suzukiXiCarrierCayleyBackwardOrbit m)
        (suzukiXiCarrierCayleyBackwardOrbit n) =
      suzukiXiCarrierCayleyMoment ((m : ℤ) - (n : ℤ)) := by
  rw [suzukiXiCarrierCayleyBackwardOrbit_eq_bilateralOrbit,
    suzukiXiCarrierCayleyBackwardOrbit_eq_bilateralOrbit,
    inner_suzukiXiCarrierCayleyBilateralOrbit_eq_moment]
  congr 1
  ring

/-- The cross Gram block between backward and forward Hardy orbits is
Hankel: its entry depends on the sum `m+n+1`. -/
theorem inner_suzukiXiCarrierCayleyBackwardOrbit_forwardOrbit_eq_moment
    (m n : ℕ) :
    inner ℂ (suzukiXiCarrierCayleyBackwardOrbit m)
        (suzukiXiCarrierCayleyForwardOrbit n) =
      suzukiXiCarrierCayleyMoment ((m + n + 1 : ℕ) : ℤ) := by
  rw [suzukiXiCarrierCayleyBackwardOrbit_eq_bilateralOrbit,
    suzukiXiCarrierCayleyForwardOrbit_eq_bilateralOrbit,
    inner_suzukiXiCarrierCayleyBilateralOrbit_eq_moment]
  congr 1
  push_cast
  ring

/-- The reverse cross block is the conjugate Hankel moment. -/
theorem inner_suzukiXiCarrierCayleyForwardOrbit_backwardOrbit_eq_moment
    (m n : ℕ) :
    inner ℂ (suzukiXiCarrierCayleyForwardOrbit m)
        (suzukiXiCarrierCayleyBackwardOrbit n) =
      starRingEnd ℂ
        (suzukiXiCarrierCayleyMoment ((m + n + 1 : ℕ) : ℤ)) := by
  rw [← inner_conj_symm,
    inner_suzukiXiCarrierCayleyBackwardOrbit_forwardOrbit_eq_moment]
  simp [add_comm]

/-! ## Finite Hankel forms -/

/-- The scalar Hankel kernel coupling the backward and forward cyclic Hardy
orbits. -/
def suzukiXiCarrierCayleyHardyHankelKernel (m n : ℕ) : ℂ :=
  suzukiXiCarrierCayleyMoment ((m + n + 1 : ℕ) : ℤ)

/-- A finite synthesis of backward Hardy-orbit vectors. -/
def suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis
    (c : ℕ →₀ ℂ) : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  ∑ m ∈ c.support, c m • suzukiXiCarrierCayleyBackwardOrbit m

/-- A finite synthesis of forward Hardy-orbit vectors. -/
def suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis
    (d : ℕ →₀ ℂ) : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  ∑ n ∈ d.support, d n • suzukiXiCarrierCayleyForwardOrbit n

/-- The finite sesquilinear Hankel form generated by the positive xi-energy
Cayley moments. -/
def suzukiXiCarrierCayleyHardyFiniteHankelForm
    (c d : ℕ →₀ ℂ) : ℂ :=
  ∑ m ∈ c.support, ∑ n ∈ d.support,
    starRingEnd ℂ (c m) *
      (d n * suzukiXiCarrierCayleyHardyHankelKernel m n)

/-- The finite Hankel form is exactly the Hilbert cross pairing of the two
opposite Hardy-orbit syntheses. -/
theorem inner_suzukiXiCarrierCayleyBackwardForwardFiniteSynthesis_eq_hankel
    (c d : ℕ →₀ ℂ) :
    inner ℂ (suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis c)
        (suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis d) =
      suzukiXiCarrierCayleyHardyFiniteHankelForm c d := by
  unfold suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis
    suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis
    suzukiXiCarrierCayleyHardyFiniteHankelForm
    suzukiXiCarrierCayleyHardyHankelKernel
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_suzukiXiCarrierCayleyBackwardOrbit_forwardOrbit_eq_moment]

/-- Reversing the two Hardy syntheses gives the conjugate finite Hankel form. -/
theorem inner_suzukiXiCarrierCayleyForwardBackwardFiniteSynthesis_eq_hankel
    (c d : ℕ →₀ ℂ) :
    inner ℂ (suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis d)
        (suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis c) =
      starRingEnd ℂ
        (suzukiXiCarrierCayleyHardyFiniteHankelForm c d) := by
  rw [← inner_conj_symm,
    inner_suzukiXiCarrierCayleyBackwardForwardFiniteSynthesis_eq_hankel]

/-! ## Positive-definite bilateral moment sequence -/

/-- A finite synthesis of the bilateral integer Cayley orbit. -/
def suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis
    (c : ℤ →₀ ℂ) : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  ∑ m ∈ c.support, c m • suzukiXiCarrierCayleyBilateralOrbit m

/-- The finite Toeplitz quadratic generated by the bilateral xi-energy
Cayley moment sequence. -/
def suzukiXiCarrierCayleyMomentFinsuppQuadratic
    (c : ℤ →₀ ℂ) : ℂ :=
  ∑ m ∈ c.support, ∑ n ∈ c.support,
    starRingEnd ℂ (c m) *
      (c n * suzukiXiCarrierCayleyMoment (n - m))

/-- The moment Toeplitz quadratic is exactly the inner square of its finite
bilateral-orbit synthesis. -/
theorem inner_suzukiXiCarrierCayleyBilateralFiniteSynthesis_eq_momentQuadratic
    (c : ℤ →₀ ℂ) :
    inner ℂ (suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c)
        (suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c) =
      suzukiXiCarrierCayleyMomentFinsuppQuadratic c := by
  unfold suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis
    suzukiXiCarrierCayleyMomentFinsuppQuadratic
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_suzukiXiCarrierCayleyBilateralOrbit_eq_moment]

/-- Every finite moment Toeplitz quadratic is a literal squared `L²(μ)`
norm. -/
theorem suzukiXiCarrierCayleyMomentFinsuppQuadratic_eq_norm_sq
    (c : ℤ →₀ ℂ) :
    suzukiXiCarrierCayleyMomentFinsuppQuadratic c =
      (‖suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c‖ : ℂ) ^ 2 := by
  rw [←
    inner_suzukiXiCarrierCayleyBilateralFiniteSynthesis_eq_momentQuadratic]
  exact inner_self_eq_norm_sq_to_K _

/-- In particular, the xi-energy Cayley moment sequence is positive
definite on every finitely supported integer family. -/
theorem suzukiXiCarrierCayleyMomentFinsuppQuadratic_re_nonneg
    (c : ℤ →₀ ℂ) :
    0 ≤ (suzukiXiCarrierCayleyMomentFinsuppQuadratic c).re := by
  rw [suzukiXiCarrierCayleyMomentFinsuppQuadratic_eq_norm_sq, pow_two]
  simp
  positivity

end

end RiemannGaussian
