import RiemannGaussian.Hybrid.EtaGeometricReflectionCrossLayerTransport

/-!
# Reciprocal-radius Gram control for reflection-summed eta modes

Critical tilting sends an off-line zero and its critical-line reflection to
finite geometric modes with one common unit phase and reciprocal positive
radii.  This module keeps that signed two-colour representation intact.  It
proves the exact cross-correlation, the strict Gram determinant reserve, and
an exact quadratic norm ledger for arbitrary complex coefficients, including
the interference term rather than replacing it by an absolute-value bound.

The abstract reciprocal-mode results are then identified with the literal
critical-shifted eta pair in every upper spectral window.  In particular, an
off-line pair has a strictly positive finite Gram reserve at every length
greater than one, so its two radial colours cannot cancel nontrivially.  This
is local pairwise coercivity; no aggregate certificate or improved zero
proportion is asserted here.
-/

open Complex Matrix Finset
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Two distinct finite geometric vectors of length at least two are linearly
independent. -/
theorem linearIndependent_two_finiteGeometricPhaseVectors
    {M : ℕ} (hM : 1 < M) {z w : ℂ} (hzw : z ≠ w) :
    LinearIndependent ℂ
      ![finiteGeometricPhaseVector M z,
        finiteGeometricPhaseVector M w] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hzero
    have h := congrFun hzero (⟨0, by omega⟩ : Fin M)
    change (1 : ℂ) = 0 at h
    exact one_ne_zero h
  · intro a ha
    have hzero := congrFun ha (⟨0, by omega⟩ : Fin M)
    have hone := congrFun ha (⟨1, hM⟩ : Fin M)
    have haone : a = 1 := by
      simpa [finiteGeometricPhaseVector] using hzero
    apply hzw
    simpa [finiteGeometricPhaseVector, haone] using hone.symm

/-- Strict finite Cauchy--Schwarz for two distinct geometric modes, obtained
from positivity of their two-by-two Gram determinant. -/
theorem finiteGeometricMode_correlation_sq_lt_normSq_mul_normSq
    {M : ℕ} (hM : 1 < M) {z w : ℂ} (hzw : z ≠ w) :
    ‖star (finiteGeometricPhaseVector M w) ⬝ᵥ
        finiteGeometricPhaseVector M z‖ ^ 2 <
      finiteGeometricModeNormSq M z * finiteGeometricModeNormSq M w := by
  let v : Fin 2 → Fin M → ℂ :=
    ![finiteGeometricPhaseVector M z,
      finiteGeometricPhaseVector M w]
  have hli : LinearIndependent ℂ v := by
    exact linearIndependent_two_finiteGeometricPhaseVectors hM hzw
  let e := (WithLp.linearEquiv 2 ℂ (Fin M → ℂ)).symm
  let u : Fin 2 → EuclideanSpace ℂ (Fin M) :=
    fun i ↦ WithLp.toLp 2 (v i)
  have hliEuclidean : LinearIndependent ℂ u := by
    have hmapped := hli.map' e.toLinearMap
      (LinearMap.ker_eq_bot_of_injective e.injective)
    simpa [u, e, Function.comp_def] using hmapped
  have hdet := (Matrix.posDef_gram_of_linearIndependent hliEuclidean).det_pos
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.gram_apply, u, v, Matrix.cons_val_zero,
    Matrix.cons_val_one, EuclideanSpace.inner_toLp_toLp] at hdet
  rw [dotProduct_comm (finiteGeometricPhaseVector M z)
      (star (finiteGeometricPhaseVector M z)),
    dotProduct_comm (finiteGeometricPhaseVector M w)
      (star (finiteGeometricPhaseVector M w)),
    dotProduct_comm (finiteGeometricPhaseVector M w)
      (star (finiteGeometricPhaseVector M z)),
    dotProduct_comm (finiteGeometricPhaseVector M z)
      (star (finiteGeometricPhaseVector M w))] at hdet
  have hselfZ :
      star (finiteGeometricPhaseVector M z) ⬝ᵥ
          finiteGeometricPhaseVector M z =
        (finiteGeometricModeNormSq M z : ℂ) := by
    unfold finiteGeometricModeNormSq dotProduct
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  have hselfW :
      star (finiteGeometricPhaseVector M w) ⬝ᵥ
          finiteGeometricPhaseVector M w =
        (finiteGeometricModeNormSq M w : ℂ) := by
    unfold finiteGeometricModeNormSq dotProduct
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  have hswap :
      star (finiteGeometricPhaseVector M z) ⬝ᵥ
          finiteGeometricPhaseVector M w =
        starRingEnd ℂ
          (star (finiteGeometricPhaseVector M w) ⬝ᵥ
            finiteGeometricPhaseVector M z) := by
    have h := Matrix.star_dotProduct
      (finiteGeometricPhaseVector M w)
      (finiteGeometricPhaseVector M z)
    simpa using (congrArg (starRingEnd ℂ) h).symm
  rw [hselfZ, hselfW, hswap] at hdet
  have hdetReal := (RCLike.pos_iff.mp hdet).1
  have hdetReal' :
      (star (finiteGeometricPhaseVector M w) ⬝ᵥ
          finiteGeometricPhaseVector M z).re *
          (star (finiteGeometricPhaseVector M w) ⬝ᵥ
            finiteGeometricPhaseVector M z).re +
        (star (finiteGeometricPhaseVector M w) ⬝ᵥ
          finiteGeometricPhaseVector M z).im *
          (star (finiteGeometricPhaseVector M w) ⬝ᵥ
            finiteGeometricPhaseVector M z).im <
        finiteGeometricModeNormSq M z * finiteGeometricModeNormSq M w := by
    simpa [Complex.mul_re, Complex.mul_im] using hdetReal
  rw [Complex.sq_norm, Complex.normSq_apply]
  exact hdetReal'

/-- The two finite geometric modes with common unit phase and reciprocal real
radii. -/
def finiteReciprocalRadialPhaseModes
    (M : ℕ) (r : ℝ) (z : ℂ) : Fin 2 → Fin M → ℂ :=
  ![finiteGeometricPhaseVector M ((r : ℂ) * z),
    finiteGeometricPhaseVector M (((r : ℂ)⁻¹) * z)]

/-- Reciprocal positive radial colours with one unit phase have exact
cross-correlation equal to the window length. -/
theorem finiteReciprocalRadialPhaseModes_correlation_eq_card
    (M : ℕ) {r : ℝ} (hr : 0 < r) (z : ℂ) (hz : ‖z‖ = 1) :
    star (finiteReciprocalRadialPhaseModes M r z 1) ⬝ᵥ
        finiteReciprocalRadialPhaseModes M r z 0 = M := by
  change star (finiteGeometricPhaseVector M (((r : ℂ)⁻¹) * z)) ⬝ᵥ
      finiteGeometricPhaseVector M ((r : ℂ) * z) = M
  rw [finiteGeometricPhaseVector_correlation_eq_geomSum]
  have hratio :
      star (((r : ℂ)⁻¹) * z) * ((r : ℂ) * z) = 1 := by
    simp only [map_mul, map_inv₀, RCLike.star_def, conj_ofReal]
    have hzprod : conj z * z = 1 := by
      rw [Complex.conj_mul', hz]
      norm_num
    calc
      ((r : ℂ)⁻¹ * conj z) * ((r : ℂ) * z) =
          ((r : ℂ)⁻¹ * (r : ℂ)) * (conj z * z) := by ring
      _ = 1 := by
        rw [inv_mul_cancel₀ (by exact_mod_cast hr.ne'), hzprod, one_mul]
  rw [hratio]
  simp

/-- A unit phase scaled by a radius greater than one differs from the same
phase scaled by its reciprocal. -/
theorem reciprocalRadialPhaseMode_ne
    {r : ℝ} (hr : 1 < r) (z : ℂ) (hz : ‖z‖ = 1) :
    (r : ℂ) * z ≠ (r : ℂ)⁻¹ * z := by
  intro hone
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hz
    norm_num at hz
  have hrcomplex : (r : ℂ) = (r : ℂ)⁻¹ :=
    mul_right_cancel₀ hz0 hone
  have hrreal : r = r⁻¹ := by
    exact_mod_cast hrcomplex
  have hrinv : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  linarith

/-- Reciprocal-radius geometric vectors of length at least two are distinct
when the forward radius is greater than one. -/
theorem finiteReciprocalRadialPhaseModes_ne
    {M : ℕ} (hM : 1 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) :
    finiteReciprocalRadialPhaseModes M r z 0 ≠
      finiteReciprocalRadialPhaseModes M r z 1 := by
  intro h
  have hone := congrFun h (⟨1, hM⟩ : Fin M)
  apply reciprocalRadialPhaseMode_ne hr z hz
  simpa [finiteReciprocalRadialPhaseModes,
    finiteGeometricPhaseVector] using hone

/-- The square of the exact reciprocal-mode correlation is strictly below
the product of the two squared norms. -/
theorem finiteReciprocalRadialPhaseModes_card_sq_lt_normSq_mul_normSq
    {M : ℕ} (hM : 1 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (M : ℝ) ^ 2 <
      finiteGeometricModeNormSq M ((r : ℂ) * z) *
        finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z) := by
  have hstrict :=
    finiteGeometricMode_correlation_sq_lt_normSq_mul_normSq
      (z := (r : ℂ) * z) (w := ((r : ℂ)⁻¹) * z) hM
      (reciprocalRadialPhaseMode_ne hr z hz)
  have hcorr := finiteReciprocalRadialPhaseModes_correlation_eq_card
    M (zero_lt_one.trans hr) z hz
  change star (finiteGeometricPhaseVector M (((r : ℂ)⁻¹) * z)) ⬝ᵥ
      finiteGeometricPhaseVector M ((r : ℂ) * z) = M at hcorr
  rw [hcorr] at hstrict
  simpa using hstrict

/-- Gram determinant reserve of a reciprocal-radius phase pair. -/
def finiteReciprocalRadialPhaseReserve
    (M : ℕ) (r : ℝ) (z : ℂ) : ℝ :=
  finiteGeometricModeNormSq M ((r : ℂ) * z) *
      finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z) -
    (M : ℝ) ^ 2

/-- The reciprocal-radius Gram reserve is strictly positive beyond length
one whenever the forward radius is greater than one. -/
theorem finiteReciprocalRadialPhaseReserve_pos
    {M : ℕ} (hM : 1 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) :
    0 < finiteReciprocalRadialPhaseReserve M r z := by
  unfold finiteReciprocalRadialPhaseReserve
  exact sub_pos.mpr
    (finiteReciprocalRadialPhaseModes_card_sq_lt_normSq_mul_normSq
      hM hr z hz)

/-- A reciprocal-radius phase pair is linearly independent beyond length one
when its forward radius is greater than one. -/
theorem linearIndependent_finiteReciprocalRadialPhaseModes
    {M : ℕ} (hM : 1 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) :
    LinearIndependent ℂ (finiteReciprocalRadialPhaseModes M r z) := by
  simpa only [finiteReciprocalRadialPhaseModes] using
    linearIndependent_two_finiteGeometricPhaseVectors hM
      (reciprocalRadialPhaseMode_ne hr z hz)

/-- Squared Euclidean norm of a finite complex vector. -/
def finiteComplexVectorNormSq
    {d : Type*} [Fintype d] (v : d → ℂ) : ℝ :=
  ∑ j, ‖v j‖ ^ 2

/-- The Hermitian self-correlation of a finite complex vector is its real
squared Euclidean norm. -/
theorem star_dot_self_eq_finiteComplexVectorNormSq
    {d : Type*} [Fintype d] (v : d → ℂ) :
    star v ⬝ᵥ v = (finiteComplexVectorNormSq v : ℂ) := by
  unfold finiteComplexVectorNormSq dotProduct
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

/-- A signed complex linear combination of the forward and backward
reciprocal-radius phase modes. -/
def finiteReciprocalRadialPhaseCombination
    (M : ℕ) (r : ℝ) (z c d : ℂ) : Fin M → ℂ :=
  c • finiteReciprocalRadialPhaseModes M r z 0 +
    d • finiteReciprocalRadialPhaseModes M r z 1

/-- Exact signed norm ledger for a reciprocal-radius combination.  The final
term retains the real part of the complex coefficient interference. -/
theorem finiteReciprocalRadialPhaseCombination_normSq_eq
    (M : ℕ) {r : ℝ} (hr : 0 < r) (z : ℂ) (hz : ‖z‖ = 1)
    (c d : ℂ) :
    finiteComplexVectorNormSq
        (finiteReciprocalRadialPhaseCombination M r z c d) =
      ‖c‖ ^ 2 * finiteGeometricModeNormSq M ((r : ℂ) * z) +
        ‖d‖ ^ 2 * finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z) +
        2 * M * (star c * d).re := by
  let f := finiteReciprocalRadialPhaseModes M r z 0
  let b := finiteReciprocalRadialPhaseModes M r z 1
  have hcrossBF : star b ⬝ᵥ f = (M : ℂ) := by
    exact finiteReciprocalRadialPhaseModes_correlation_eq_card M hr z hz
  have hcrossFB : star f ⬝ᵥ b = (M : ℂ) := by
    have h := Matrix.star_dotProduct b f
    rw [hcrossBF] at h
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'.symm
  have hselfF : star f ⬝ᵥ f =
      (finiteGeometricModeNormSq M ((r : ℂ) * z) : ℂ) := by
    exact star_dot_self_eq_finiteComplexVectorNormSq f
  have hselfB : star b ⬝ᵥ b =
      (finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z) : ℂ) := by
    exact star_dot_self_eq_finiteComplexVectorNormSq b
  have hdot :
      star (finiteReciprocalRadialPhaseCombination M r z c d) ⬝ᵥ
          finiteReciprocalRadialPhaseCombination M r z c d =
        star c * c * (finiteGeometricModeNormSq M ((r : ℂ) * z) : ℂ) +
          star d * d *
            (finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z) : ℂ) +
          (M : ℂ) * (star c * d + star d * c) := by
    change star (c • f + d • b) ⬝ᵥ (c • f + d • b) = _
    have hstar :
        star (c • f + d • b) =
          star c • star f + star d • star b := by
      ext j
      simp [Pi.star_apply]
    rw [hstar]
    simp only [add_dotProduct, dotProduct_add,
      smul_dotProduct, smul_dotProduct,
      dotProduct_smul, dotProduct_smul,
      dotProduct_smul, dotProduct_smul,
      hselfF, hselfB, hcrossBF, hcrossFB]
    simp only [smul_eq_mul]
    ring
  have hcc : star c * c = (‖c‖ ^ 2 : ℂ) := by
    simpa [Complex.star_def] using Complex.conj_mul' c
  have hdd : star d * d = (‖d‖ ^ 2 : ℂ) := by
    simpa [Complex.star_def] using Complex.conj_mul' d
  have hcd :
      star c * d + star d * c = (2 * (star c * d).re : ℝ) := by
    apply Complex.ext
    · simp [Complex.mul_re]
      ring
    · simp [Complex.mul_im]
      ring
  have hcast :
      (finiteComplexVectorNormSq
          (finiteReciprocalRadialPhaseCombination M r z c d) : ℂ) =
        (‖c‖ ^ 2 * finiteGeometricModeNormSq M ((r : ℂ) * z) +
          ‖d‖ ^ 2 * finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z) +
          2 * M * (star c * d).re : ℝ) := by
    rw [← star_dot_self_eq_finiteComplexVectorNormSq, hdot,
      hcc, hdd, hcd]
    push_cast
    ring
  exact_mod_cast hcast

/-- A reciprocal-radius mode combination vanishes exactly when both complex
coefficients vanish. -/
theorem finiteReciprocalRadialPhaseCombination_eq_zero_iff
    {M : ℕ} (hM : 1 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) (c d : ℂ) :
    finiteReciprocalRadialPhaseCombination M r z c d = 0 ↔
      c = 0 ∧ d = 0 := by
  constructor
  · intro hzero
    have hli := linearIndependent_finiteReciprocalRadialPhaseModes
      hM hr z hz
    have hsum :
        ∑ i : Fin 2, ![c, d] i •
            finiteReciprocalRadialPhaseModes M r z i = 0 := by
      rw [Fin.sum_univ_two]
      exact hzero
    have hcoeff := Fintype.linearIndependent_iff.mp hli ![c, d] hsum
    constructor
    · simpa using hcoeff (0 : Fin 2)
    · simpa using hcoeff (1 : Fin 2)
  · rintro ⟨rfl, rfl⟩
    simp [finiteReciprocalRadialPhaseCombination]

/-- Every nonzero finite complex vector has strictly positive squared
Euclidean norm. -/
theorem finiteComplexVectorNormSq_pos_of_ne_zero
    {d : Type*} [Fintype d] {v : d → ℂ} (hv : v ≠ 0) :
    0 < finiteComplexVectorNormSq v := by
  have hj : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  rcases hj with ⟨j, hj⟩
  unfold finiteComplexVectorNormSq
  apply Finset.sum_pos'
  · intro k _hk
    positivity
  · exact ⟨j, Finset.mem_univ j, sq_pos_of_pos (norm_pos_iff.mpr hj)⟩

/-- Every nontrivial reciprocal-radius mode combination has strictly positive
squared norm. -/
theorem finiteReciprocalRadialPhaseCombination_normSq_pos
    {M : ℕ} (hM : 1 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) {c d : ℂ}
    (hcoeff : c ≠ 0 ∨ d ≠ 0) :
    0 < finiteComplexVectorNormSq
      (finiteReciprocalRadialPhaseCombination M r z c d) := by
  apply finiteComplexVectorNormSq_pos_of_ne_zero
  intro hzero
  have hcd :=
    (finiteReciprocalRadialPhaseCombination_eq_zero_iff
      hM hr z hz c d).mp hzero
  exact hcoeff.elim (fun hc ↦ hc hcd.1) (fun hd ↦ hd hcd.2)

/-- The exact signed quadratic form of a reciprocal-radius pair is positive
for every nonzero coefficient pair. -/
theorem finiteReciprocalRadialPhaseQuadraticForm_pos
    {M : ℕ} (hM : 1 < M) {r : ℝ} (hr : 1 < r)
    (z : ℂ) (hz : ‖z‖ = 1) {c d : ℂ}
    (hcoeff : c ≠ 0 ∨ d ≠ 0) :
    0 <
      ‖c‖ ^ 2 * finiteGeometricModeNormSq M ((r : ℂ) * z) +
        ‖d‖ ^ 2 * finiteGeometricModeNormSq M (((r : ℂ)⁻¹) * z) +
        2 * M * (star c * d).re := by
  rw [← finiteReciprocalRadialPhaseCombination_normSq_eq
    M (zero_lt_one.trans hr) z hz c d]
  exact finiteReciprocalRadialPhaseCombination_normSq_pos
    hM hr z hz hcoeff

/-- A shifted eta mode is its positive norm times its retained normalized
unit phase. -/
theorem etaGeometricShiftedMode_eq_norm_mul_normalized
    {q : ℕ} (hq : 0 < q) (σ : ℝ) (s : ℂ) :
    etaGeometricShiftedMode q σ s =
      (‖etaGeometricShiftedMode q σ s‖ : ℂ) *
        etaGeometricNormalizedMode q s := by
  calc
    etaGeometricShiftedMode q σ s =
        (((q : ℝ) ^ (σ - s.re) : ℝ) : ℂ) *
          etaGeometricNormalizedMode q s :=
      etaGeometricShiftedMode_eq_real_rpow_mul_normalized hq σ s
    _ = _ := by rw [norm_etaGeometricShiftedMode hq]

/-- The abstract reciprocal-radius phase pair is exactly the literal pair of
critical-shifted eta modes at a zero and its reflection. -/
theorem finiteReciprocalRadialPhaseModes_eq_criticalShiftedPair
    {q : ℕ} (hq : 0 < q) (rho : NontrivialZetaZero) (M : ℕ) :
    finiteReciprocalRadialPhaseModes M
        ‖etaGeometricShiftedMode q (1 / 2) rho.val‖
        (etaGeometricNormalizedMode q rho.val) =
      ![finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q (1 / 2) rho.val),
        finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q (1 / 2)
            (NontrivialZetaZero.conjugatePartner rho).val)] := by
  have hpartnerNorm :
      ‖etaGeometricShiftedMode q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho).val‖ =
        ‖etaGeometricShiftedMode q (1 / 2) rho.val‖⁻¹ :=
    eq_inv_of_mul_eq_one_right
      (norm_etaGeometricCriticalShiftedMode_mul_partner hq rho)
  have hforward :=
    etaGeometricShiftedMode_eq_norm_mul_normalized
      hq (1 / 2) rho.val
  have hpartner :
      etaGeometricShiftedMode q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho).val =
        ((‖etaGeometricShiftedMode q (1 / 2) rho.val‖⁻¹ : ℝ) : ℂ) *
          etaGeometricNormalizedMode q rho.val := by
    calc
      etaGeometricShiftedMode q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho).val =
        (‖etaGeometricShiftedMode q (1 / 2)
            (NontrivialZetaZero.conjugatePartner rho).val‖ : ℂ) *
          etaGeometricNormalizedMode q
            (NontrivialZetaZero.conjugatePartner rho).val :=
        etaGeometricShiftedMode_eq_norm_mul_normalized
          hq (1 / 2) _
      _ = _ := by
        rw [hpartnerNorm,
          etaGeometricNormalizedMode_conjugatePartner hq]
  have hinvCast :
      (‖etaGeometricShiftedMode q (1 / 2) rho.val‖ : ℂ)⁻¹ =
        ((‖etaGeometricShiftedMode q (1 / 2) rho.val‖⁻¹ : ℝ) : ℂ) := by
    norm_cast
  funext i
  fin_cases i
  · change finiteGeometricPhaseVector M
        ((‖etaGeometricShiftedMode q (1 / 2) rho.val‖ : ℂ) *
          etaGeometricNormalizedMode q rho.val) =
        finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q (1 / 2) rho.val)
    exact congrArg (finiteGeometricPhaseVector M) hforward.symm
  · change finiteGeometricPhaseVector M
        ((‖etaGeometricShiftedMode q (1 / 2) rho.val‖ : ℂ)⁻¹ *
          etaGeometricNormalizedMode q rho.val) =
        finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q (1 / 2)
            (NontrivialZetaZero.conjugatePartner rho).val)
    rw [hinvCast]
    exact congrArg (finiteGeometricPhaseVector M) hpartner.symm

/-- Every literal off-line critical-shifted eta pair has cross-correlation
exactly equal to the finite window length. -/
theorem spectralUpperZetaZeroWindow_criticalShiftedPair_correlation_eq_card
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T)) (M : ℕ) :
    star (finiteGeometricPhaseVector M
        (etaGeometricShiftedMode q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho.1).val)) ⬝ᵥ
      finiteGeometricPhaseVector M
        (etaGeometricShiftedMode q (1 / 2) rho.1.val) = M := by
  have hcorr := finiteReciprocalRadialPhaseModes_correlation_eq_card
    M (zero_lt_one.trans
      (spectralUpperZetaZeroWindow_criticalShiftedMode_radii hq rho).1)
    (etaGeometricNormalizedMode q rho.1.val)
    (norm_etaGeometricNormalizedMode hq.le rho.1.val)
  have hpair :=
    finiteReciprocalRadialPhaseModes_eq_criticalShiftedPair
      hq.le rho.1 M
  have hzero := congrFun hpair (0 : Fin 2)
  have hone := congrFun hpair (1 : Fin 2)
  rw [hzero, hone] at hcorr
  exact hcorr

/-- Every literal off-line critical-shifted eta pair has strictly positive
finite Gram determinant reserve at every length greater than one. -/
theorem spectralUpperZetaZeroWindow_criticalShiftedPair_gramReserve_pos
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) :
    0 <
      finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q (1 / 2) rho.1.val) *
        finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q (1 / 2)
            (NontrivialZetaZero.conjugatePartner rho.1).val) -
        (M : ℝ) ^ 2 := by
  apply sub_pos.mpr
  have hradii :=
    spectralUpperZetaZeroWindow_criticalShiftedMode_radii hq rho
  have hne :
      etaGeometricShiftedMode q (1 / 2) rho.1.val ≠
        etaGeometricShiftedMode q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho.1).val := by
    intro heq
    have hnorm := congrArg norm heq
    linarith
  have hstrict :=
    finiteGeometricMode_correlation_sq_lt_normSq_mul_normSq
      hM hne
  rw [spectralUpperZetaZeroWindow_criticalShiftedPair_correlation_eq_card
    hq rho M] at hstrict
  simpa using hstrict

end

end RiemannGaussian
