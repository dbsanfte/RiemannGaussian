import RiemannGaussian.Hybrid.EtaGeometricReflectionEvenFramePotential

/-!
# Pairwise decorrelation reserve for the reflection-even eta frame

This module separates the literal eta frame potential into its diagonal
self-mass and distinct-pair correlations. For each ordered distinct pair it
retains the weighted Gram-determinant reserve
`weight_a * weight_b * (norm_a² * norm_b² - correlation_ab²)`.

Lean proves every such term nonnegative directly from complex
Cauchy--Schwarz, and proves the exact conservation law
`mass² = potential + reserve`. Consequently the checked `13/18` and
finite-window `18/18` moment premises are equivalent to explicit lower bounds
on this colour-resolved decorrelation reserve. Those lower bounds remain open
eta-arithmetic estimates; this module does not prove an improved zero
proportion.
-/

open Complex Matrix Finset Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Squared Euclidean norm of one literal reflection-even eta atom. -/
def pairedEtaReflectionEvenFrameAtomNormSq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    (a : PairedEtaReflectionEvenFrameIndex T) : ℝ :=
  ∑ j, ‖pairedEtaReflectionEvenFrameVector cutoff T a j‖ ^ 2

/-- Multiplicity-weighted squared norm of one eta frame atom. -/
def pairedEtaReflectionEvenFrameAtomMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    (a : PairedEtaReflectionEvenFrameIndex T) : ℝ :=
  pairedEtaReflectionEvenFrameWeight T a *
    pairedEtaReflectionEvenFrameAtomNormSq cutoff T a

/-- A frame atom's real self-correlation is exactly its squared norm. -/
theorem pairedEtaReflectionEvenFrameCorrelation_self_re
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    (a : PairedEtaReflectionEvenFrameIndex T) :
    (star (pairedEtaReflectionEvenFrameVector cutoff T a) ⬝ᵥ
        pairedEtaReflectionEvenFrameVector cutoff T a).re =
      pairedEtaReflectionEvenFrameAtomNormSq cutoff T a := by
  unfold pairedEtaReflectionEvenFrameAtomNormSq dotProduct
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

/-- Sum of the squared weighted masses of all individual eta atoms. -/
def pairedEtaReflectionEvenFrameDiagonalMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ a : PairedEtaReflectionEvenFrameIndex T,
    pairedEtaReflectionEvenFrameAtomMass cutoff T a ^ 2

/-- The frame potential restricted to ordered pairs of distinct atoms. -/
def pairedEtaReflectionEvenFrameOffDiagonalPotential
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ a : PairedEtaReflectionEvenFrameIndex T,
    ∑ b ∈ (Finset.univ : Finset
        (PairedEtaReflectionEvenFrameIndex T)).erase a,
      pairedEtaReflectionEvenFrameWeight T a *
        pairedEtaReflectionEvenFrameWeight T b *
          (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
              pairedEtaReflectionEvenFrameVector cutoff T a).re ^ 2

/-- The colour-resolved sum of pairwise Gram-determinant deficits over
ordered distinct eta atoms. -/
def pairedEtaReflectionEvenFrameDecorrelationReserve
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ a : PairedEtaReflectionEvenFrameIndex T,
    ∑ b ∈ (Finset.univ : Finset
        (PairedEtaReflectionEvenFrameIndex T)).erase a,
      pairedEtaReflectionEvenFrameWeight T a *
        pairedEtaReflectionEvenFrameWeight T b *
          (pairedEtaReflectionEvenFrameAtomNormSq cutoff T a *
              pairedEtaReflectionEvenFrameAtomNormSq cutoff T b -
            (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
              pairedEtaReflectionEvenFrameVector cutoff T a).re ^ 2)

/-- The full frame potential is its diagonal mass plus its distinct-pair
potential. -/
theorem pairedEtaReflectionEvenFramePotential_eq_diagonal_add_offDiagonal
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaReflectionEvenFramePotential cutoff T =
      pairedEtaReflectionEvenFrameDiagonalMass cutoff T +
        pairedEtaReflectionEvenFrameOffDiagonalPotential cutoff T := by
  rw [pairedEtaReflectionEvenFramePotential_eq_sum_weight_mul_re_sq]
  unfold pairedEtaReflectionEvenFrameDiagonalMass
    pairedEtaReflectionEvenFrameOffDiagonalPotential
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  let f : PairedEtaReflectionEvenFrameIndex T → ℝ := fun b ↦
    pairedEtaReflectionEvenFrameWeight T a *
      pairedEtaReflectionEvenFrameWeight T b *
        (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
          pairedEtaReflectionEvenFrameVector cutoff T a).re ^ 2
  calc
    ∑ b, pairedEtaReflectionEvenFrameWeight T a *
        pairedEtaReflectionEvenFrameWeight T b *
          (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
            pairedEtaReflectionEvenFrameVector cutoff T a).re ^ 2 =
        f a + ∑ b ∈ (Finset.univ : Finset
          (PairedEtaReflectionEvenFrameIndex T)).erase a, f b := by
      exact (Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)).symm
    _ = pairedEtaReflectionEvenFrameAtomMass cutoff T a ^ 2 +
        ∑ b ∈ (Finset.univ : Finset
          (PairedEtaReflectionEvenFrameIndex T)).erase a,
          pairedEtaReflectionEvenFrameWeight T a *
            pairedEtaReflectionEvenFrameWeight T b *
              (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
                pairedEtaReflectionEvenFrameVector cutoff T a).re ^ 2 := by
      unfold f pairedEtaReflectionEvenFrameAtomMass
      rw [pairedEtaReflectionEvenFrameCorrelation_self_re]
      ring

/-- Squared real eta correlation is bounded by the product of atom norm
squares. This is complex Euclidean Cauchy--Schwarz, with reality supplied by
the checked reflection-even structure. -/
theorem pairedEtaReflectionEvenFrameCorrelation_sq_le_normSq_mul_normSq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    (a b : PairedEtaReflectionEvenFrameIndex T) :
    (dotProduct (star (pairedEtaReflectionEvenFrameVector cutoff T b))
        (pairedEtaReflectionEvenFrameVector cutoff T a)).re ^ 2 ≤
      pairedEtaReflectionEvenFrameAtomNormSq cutoff T a *
        pairedEtaReflectionEvenFrameAtomNormSq cutoff T b := by
  let va := pairedEtaReflectionEvenFrameVector cutoff T a
  let vb := pairedEtaReflectionEvenFrameVector cutoff T b
  let z := dotProduct (star vb) va
  have hva : star va = va :=
    star_pairedEtaReflectionEvenFrameVector cutoff T a
  have hvb : star vb = vb :=
    star_pairedEtaReflectionEvenFrameVector cutoff T b
  have hz : ((z.re : ℝ) : ℂ) = z :=
    Complex.conj_eq_iff_re.mp
      (pairedEtaReflectionEvenFrameCorrelation_star_eq cutoff T a b)
  have h := inner_mul_inner_self_le (𝕜 := ℂ)
    (WithLp.toLp 2 vb : EuclideanSpace ℂ (d × Fin 2))
    (WithLp.toLp 2 va : EuclideanSpace ℂ (d × Fin 2))
  simp only [EuclideanSpace.inner_toLp_toLp] at h
  change
    ‖dotProduct va (star vb)‖ * ‖dotProduct vb (star va)‖ ≤
      (dotProduct vb (star vb)).re * (dotProduct va (star va)).re at h
  rw [hva, hvb] at h
  change z.re ^ 2 ≤ _
  calc
    z.re ^ 2 = ‖z‖ * ‖z‖ := by
      rw [← hz]
      simp [Real.norm_eq_abs]
      ring
    _ = ‖dotProduct va vb‖ * ‖dotProduct vb va‖ := by
      unfold z
      rw [hvb, dotProduct_comm]
    _ ≤ (dotProduct vb vb).re * (dotProduct va va).re := h
    _ = pairedEtaReflectionEvenFrameAtomNormSq cutoff T a *
        pairedEtaReflectionEvenFrameAtomNormSq cutoff T b := by
      have ha : (dotProduct va va).re =
          pairedEtaReflectionEvenFrameAtomNormSq cutoff T a := by
        calc
          _ = (dotProduct (star va) va).re := by rw [hva]
          _ = _ := by
            unfold va
            exact pairedEtaReflectionEvenFrameCorrelation_self_re cutoff T a
      have hb : (dotProduct vb vb).re =
          pairedEtaReflectionEvenFrameAtomNormSq cutoff T b := by
        calc
          _ = (dotProduct (star vb) vb).re := by rw [hvb]
          _ = _ := by
            unfold vb
            exact pairedEtaReflectionEvenFrameCorrelation_self_re cutoff T b
      rw [ha, hb]
      ring

/-- The frame trace mass is the sum of the individual weighted atom masses. -/
theorem pairedEtaReflectionEvenFrameTraceMass_eq_sum_atomMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaReflectionEvenFrameTraceMass cutoff T =
      ∑ a : PairedEtaReflectionEvenFrameIndex T,
        pairedEtaReflectionEvenFrameAtomMass cutoff T a := by
  rfl

/-- Sum of weighted norm products over all ordered distinct atom pairs. -/
def pairedEtaReflectionEvenFrameOffDiagonalNormProduct
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ a : PairedEtaReflectionEvenFrameIndex T,
    ∑ b ∈ (Finset.univ : Finset
        (PairedEtaReflectionEvenFrameIndex T)).erase a,
      pairedEtaReflectionEvenFrameAtomMass cutoff T a *
        pairedEtaReflectionEvenFrameAtomMass cutoff T b

/-- The square of total frame mass splits into diagonal mass and the ordered
distinct-pair norm product. -/
theorem pairedEtaReflectionEvenFrameTraceMass_sq_eq_diagonal_add_offDiagonalNormProduct
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaReflectionEvenFrameTraceMass cutoff T ^ 2 =
      pairedEtaReflectionEvenFrameDiagonalMass cutoff T +
        pairedEtaReflectionEvenFrameOffDiagonalNormProduct cutoff T := by
  rw [pairedEtaReflectionEvenFrameTraceMass_eq_sum_atomMass]
  unfold pairedEtaReflectionEvenFrameDiagonalMass
    pairedEtaReflectionEvenFrameOffDiagonalNormProduct
  rw [pow_two, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  let f : PairedEtaReflectionEvenFrameIndex T → ℝ := fun b ↦
    pairedEtaReflectionEvenFrameAtomMass cutoff T a *
      pairedEtaReflectionEvenFrameAtomMass cutoff T b
  calc
    ∑ b, pairedEtaReflectionEvenFrameAtomMass cutoff T a *
        pairedEtaReflectionEvenFrameAtomMass cutoff T b =
      f a + ∑ b ∈ (Finset.univ : Finset
        (PairedEtaReflectionEvenFrameIndex T)).erase a, f b := by
        exact (Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)).symm
    _ = pairedEtaReflectionEvenFrameAtomMass cutoff T a ^ 2 +
        ∑ b ∈ (Finset.univ : Finset
          (PairedEtaReflectionEvenFrameIndex T)).erase a,
          pairedEtaReflectionEvenFrameAtomMass cutoff T a *
            pairedEtaReflectionEvenFrameAtomMass cutoff T b := by
      unfold f
      ring

/-- The distinct-pair norm product is exactly correlation potential plus
decorrelation reserve. -/
theorem pairedEtaReflectionEvenFrameOffDiagonalNormProduct_eq_potential_add_reserve
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaReflectionEvenFrameOffDiagonalNormProduct cutoff T =
      pairedEtaReflectionEvenFrameOffDiagonalPotential cutoff T +
        pairedEtaReflectionEvenFrameDecorrelationReserve cutoff T := by
  unfold pairedEtaReflectionEvenFrameOffDiagonalNormProduct
    pairedEtaReflectionEvenFrameOffDiagonalPotential
    pairedEtaReflectionEvenFrameDecorrelationReserve
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  unfold pairedEtaReflectionEvenFrameAtomMass
  ring

/-- Exact frame conservation law: total mass squared equals frame potential
plus the colour-resolved decorrelation reserve. -/
theorem pairedEtaReflectionEvenFrameTraceMass_sq_eq_potential_add_reserve
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaReflectionEvenFrameTraceMass cutoff T ^ 2 =
      pairedEtaReflectionEvenFramePotential cutoff T +
        pairedEtaReflectionEvenFrameDecorrelationReserve cutoff T := by
  rw [pairedEtaReflectionEvenFrameTraceMass_sq_eq_diagonal_add_offDiagonalNormProduct,
    pairedEtaReflectionEvenFramePotential_eq_diagonal_add_offDiagonal,
    pairedEtaReflectionEvenFrameOffDiagonalNormProduct_eq_potential_add_reserve]
  ring

/-- Every individual weighted pairwise decorrelation term is nonnegative. -/
theorem pairedEtaReflectionEvenFrameDecorrelationPairTerm_nonneg
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    (a b : PairedEtaReflectionEvenFrameIndex T) :
    0 ≤ pairedEtaReflectionEvenFrameWeight T a *
        pairedEtaReflectionEvenFrameWeight T b *
          (pairedEtaReflectionEvenFrameAtomNormSq cutoff T a *
              pairedEtaReflectionEvenFrameAtomNormSq cutoff T b -
            (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
              pairedEtaReflectionEvenFrameVector cutoff T a).re ^ 2) := by
  exact mul_nonneg
    (mul_nonneg (pairedEtaReflectionEvenFrameWeight_pos T a).le
      (pairedEtaReflectionEvenFrameWeight_pos T b).le)
    (sub_nonneg.mpr
      (pairedEtaReflectionEvenFrameCorrelation_sq_le_normSq_mul_normSq
        cutoff T a b))

/-- The complete distinct-pair decorrelation reserve is nonnegative. -/
theorem pairedEtaReflectionEvenFrameDecorrelationReserve_nonneg
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    0 ≤ pairedEtaReflectionEvenFrameDecorrelationReserve cutoff T := by
  unfold pairedEtaReflectionEvenFrameDecorrelationReserve
  exact Finset.sum_nonneg fun a _ha ↦
    Finset.sum_nonneg fun b _hb ↦
      pairedEtaReflectionEvenFrameDecorrelationPairTerm_nonneg cutoff T a b

/-- The strict `13/18` frame-moment premise is exactly the corresponding
lower bound on pairwise decorrelation reserve. -/
theorem pairedEtaReflectionEvenFrame_thirteenEighteenMoment_iff_reserve
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) (N : ℕ) :
    ((31 : ℝ) * N * pairedEtaReflectionEvenFramePotential cutoff T <
        36 * pairedEtaReflectionEvenFrameTraceMass cutoff T ^ 2) ↔
      (((31 : ℝ) * N - 36) *
          pairedEtaReflectionEvenFramePotential cutoff T <
        36 * pairedEtaReflectionEvenFrameDecorrelationReserve cutoff T) := by
  rw [pairedEtaReflectionEvenFrameTraceMass_sq_eq_potential_add_reserve]
  constructor <;> intro h <;> nlinarith

/-- The finite-window `18/18` frame-moment ceiling is exactly the endpoint
lower bound on pairwise decorrelation reserve. -/
theorem pairedEtaReflectionEvenFrame_endpointMoment_iff_reserve
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) (N : ℕ) :
    ((N : ℝ) * pairedEtaReflectionEvenFramePotential cutoff T ≤
        pairedEtaReflectionEvenFrameTraceMass cutoff T ^ 2) ↔
      (((N : ℝ) - 1) * pairedEtaReflectionEvenFramePotential cutoff T ≤
        pairedEtaReflectionEvenFrameDecorrelationReserve cutoff T) := by
  rw [pairedEtaReflectionEvenFrameTraceMass_sq_eq_potential_add_reserve]
  constructor <;> intro h <;> nlinarith

/-- The explicit strict decorrelation-reserve inequality is sufficient to
beat the `13/18` critical-zero proportion. -/
theorem pairedEtaGeometricReflectionEven_thirteen_eighteen_of_decorrelationReserve
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (hreserve :
      ((31 : ℝ) * (spectralZetaZeroWindow T).card - 36) *
          pairedEtaReflectionEvenFramePotential
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T <
        36 * pairedEtaReflectionEvenFrameDecorrelationReserve
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T) :
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card := by
  apply pairedEtaGeometricReflectionEven_thirteen_eighteen_of_framePotential
    q hT n hwindow hK
  exact
    (pairedEtaReflectionEvenFrame_thirteenEighteenMoment_iff_reserve
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j)
      T (spectralZetaZeroWindow T).card).2 hreserve

/-- The endpoint decorrelation-reserve inequality is sufficient for every
zero in the represented finite window to be critical. -/
theorem pairedEtaGeometricReflectionEven_allCritical_of_decorrelationReserve
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (hreserve :
      (((spectralZetaZeroWindow T).card : ℝ) - 1) *
          pairedEtaReflectionEvenFramePotential
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T ≤
        pairedEtaReflectionEvenFrameDecorrelationReserve
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T) :
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card := by
  apply pairedEtaGeometricReflectionEven_allCritical_of_framePotentialCeiling
    q hT n hwindow hK
  exact
    (pairedEtaReflectionEvenFrame_endpointMoment_iff_reserve
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j)
      T (spectralZetaZeroWindow T).card).2 hreserve

/-- The two open pairwise decorrelation premises paired with their checked
`13/18` and finite-window `18/18` consequences. -/
def PairedEtaGeometricReflectionEvenDecorrelationReserveTargets
    (q : ℕ) (T : ℝ) (n : ℕ) : Prop :=
  ((((31 : ℝ) * (spectralZetaZeroWindow T).card - 36) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T <
      36 * pairedEtaReflectionEvenFrameDecorrelationReserve
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T) →
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card) ∧
  (((((spectralZetaZeroWindow T).card : ℝ) - 1) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T ≤
      pairedEtaReflectionEvenFrameDecorrelationReserve
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T) →
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card)

/-- The decorrelation-reserve targets are exactly equivalent to the preceding
frame-potential targets; opening the gap loses no information and proves no
new arithmetic estimate. -/
theorem pairedEtaGeometricReflectionEvenDecorrelationReserveTargets_iff_framePotentialTargets
    (q : ℕ) (T : ℝ) (n : ℕ) :
    PairedEtaGeometricReflectionEvenDecorrelationReserveTargets q T n ↔
      PairedEtaGeometricReflectionEvenFramePotentialTargets q T n := by
  let cutoff : Fin (spectralZetaZeroWindow T).card → ℕ := fun j ↦
    pairedEtaGeometricHyperbolicCutoff q n j
  have hthirteen :=
    pairedEtaReflectionEvenFrame_thirteenEighteenMoment_iff_reserve
      cutoff T (spectralZetaZeroWindow T).card
  have hendpoint :=
    pairedEtaReflectionEvenFrame_endpointMoment_iff_reserve
      cutoff T (spectralZetaZeroWindow T).card
  unfold PairedEtaGeometricReflectionEvenDecorrelationReserveTargets
    PairedEtaGeometricReflectionEvenFramePotentialTargets
  change
    ((_ → _) ∧ (_ → _)) ↔ ((_ → _) ∧ (_ → _))
  constructor
  · rintro ⟨hthirteenReserve, hendpointReserve⟩
    exact
      ⟨fun hmoment ↦ hthirteenReserve (hthirteen.mp hmoment),
        fun hmoment ↦ hendpointReserve (hendpoint.mp hmoment)⟩
  · rintro ⟨hthirteenMoment, hendpointMoment⟩
    exact
      ⟨fun hreserve ↦ hthirteenMoment (hthirteen.mpr hreserve),
        fun hreserve ↦ hendpointMoment (hendpoint.mpr hreserve)⟩

/-- Both reserve implications hold whenever the actual eta features are
separated; this theorem does not assert either open reserve premise. -/
theorem pairedEtaGeometricReflectionEvenDecorrelationReserveCertificateInterface
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    PairedEtaGeometricReflectionEvenDecorrelationReserveTargets q T n := by
  exact
    ⟨pairedEtaGeometricReflectionEven_thirteen_eighteen_of_decorrelationReserve
      q hT n hwindow hK,
    pairedEtaGeometricReflectionEven_allCritical_of_decorrelationReserve
      q hT n hwindow hK⟩

/-- For every nonempty finite window, one odd prime base makes the complete
decorrelation-reserve interface valid at all sufficiently late blocks. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenDecorrelationReserveCertificateInterface
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        PairedEtaGeometricReflectionEvenDecorrelationReserveTargets q T n := by
  obtain ⟨q, hqPrime, hqOdd, hq, htargets⟩ :=
    exists_prime_eventually_pairedEtaGeometricReflectionEvenFramePotentialCertificateInterface
      hT hwindow
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [htargets] with n hn
  exact
    (pairedEtaGeometricReflectionEvenDecorrelationReserveTargets_iff_framePotentialTargets
      q T n).2 hn

end

end RiemannGaussian
