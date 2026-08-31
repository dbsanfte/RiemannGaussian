import RiemannGaussian.Hybrid.EtaGeometricReflectionEvenDecorrelationReserve

/-!
# Strict decorrelation from separated geometric eta features

This module feeds the project's unconditional late-block eta feature
separation into the pairwise decorrelation reserve. A square-root-weighted
frame synthesis matrix realizes the reflection-even coordinate carrier as an
exact Gram factor. The carrier's checked rank then proves that all literal
critical and upper-off-line-real frame atoms are linearly independent.

Every distinct pair therefore has a positive two-vector Gram determinant.
After transporting that determinant through the proved reality of the frame,
Lean obtains strict Cauchy--Schwarz for each pair and strict positivity of its
weighted decorrelation term. At a separated block the complete reserve is
positive exactly when the frame contains at least two atoms; one odd prime
base makes this characterization valid eventually.

This is an unconditional eta-arithmetic separation result. It supplies a
strict reserve but no quantitative lower bound relative to the frame
potential, so it does not yet establish the open `13/18` premise.
-/

open Complex Matrix Finset Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Positive square-root scale attached to a reflection-even frame weight. -/
def pairedEtaReflectionEvenFrameSqrtWeight (T : ℝ)
    (a : PairedEtaReflectionEvenFrameIndex T) : ℂ :=
  (Real.sqrt (pairedEtaReflectionEvenFrameWeight T a) : ℂ)

/-- Every reflection-even square-root frame weight is nonzero. -/
theorem pairedEtaReflectionEvenFrameSqrtWeight_ne_zero
    (T : ℝ) (a : PairedEtaReflectionEvenFrameIndex T) :
    pairedEtaReflectionEvenFrameSqrtWeight T a ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact Real.sqrt_ne_zero'.mpr
    (pairedEtaReflectionEvenFrameWeight_pos T a)

/-- Squaring the real frame scale recovers the original positive weight. -/
theorem pairedEtaReflectionEvenFrameSqrtWeight_sq
    (T : ℝ) (a : PairedEtaReflectionEvenFrameIndex T) :
    pairedEtaReflectionEvenFrameSqrtWeight T a *
        pairedEtaReflectionEvenFrameSqrtWeight T a =
      (pairedEtaReflectionEvenFrameWeight T a : ℂ) := by
  unfold pairedEtaReflectionEvenFrameSqrtWeight
  norm_cast
  exact Real.mul_self_sqrt
    (pairedEtaReflectionEvenFrameWeight_pos T a).le

/-- Column synthesis matrix of the square-root-weighted reflection-even eta
frame. -/
def pairedEtaReflectionEvenFrameSynthesisMatrix
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    Matrix (d × Fin 2) (PairedEtaReflectionEvenFrameIndex T) ℂ :=
  fun j a ↦ pairedEtaReflectionEvenFrameSqrtWeight T a *
    pairedEtaReflectionEvenFrameVector cutoff T a j

/-- The weighted frame synthesis Gram is exactly the sum of its literal
rank-one eta atom blocks. -/
theorem pairedEtaReflectionEvenFrameSynthesisMatrix_self_mul_conjTranspose
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaReflectionEvenFrameSynthesisMatrix cutoff T *
        (pairedEtaReflectionEvenFrameSynthesisMatrix cutoff T)ᴴ =
      ∑ a : PairedEtaReflectionEvenFrameIndex T,
        (pairedEtaReflectionEvenFrameWeight T a : ℂ) •
          Matrix.vecMulVec
            (pairedEtaReflectionEvenFrameVector cutoff T a)
            (pairedEtaReflectionEvenFrameVector cutoff T a) := by
  ext i j
  simp only [Matrix.mul_apply, pairedEtaReflectionEvenFrameSynthesisMatrix,
    Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [star_mul]
  have hstar : star (pairedEtaReflectionEvenFrameSqrtWeight T a) =
      pairedEtaReflectionEvenFrameSqrtWeight T a := by
    simp [pairedEtaReflectionEvenFrameSqrtWeight, RCLike.star_def,
      Complex.conj_ofReal]
  have hvstar :
      star (pairedEtaReflectionEvenFrameVector cutoff T a j) =
        pairedEtaReflectionEvenFrameVector cutoff T a j := by
    exact congrFun
      (star_pairedEtaReflectionEvenFrameVector cutoff T a) j
  rw [hstar]
  calc
    _ = (pairedEtaReflectionEvenFrameSqrtWeight T a *
          pairedEtaReflectionEvenFrameSqrtWeight T a) *
        (pairedEtaReflectionEvenFrameVector cutoff T a i *
          star (pairedEtaReflectionEvenFrameVector cutoff T a j)) := by ring
    _ = _ := by
      rw [pairedEtaReflectionEvenFrameSqrtWeight_sq, hvstar]

/-- The geometric reflection-even coordinate carrier is exactly the weighted
literal frame synthesis Gram. -/
theorem pairedEtaGeometricReflectionEvenCoordinateCarrier_eq_frameSynthesis
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n =
      pairedEtaReflectionEvenFrameSynthesisMatrix
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T *
        (pairedEtaReflectionEvenFrameSynthesisMatrix
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T)ᴴ := by
  rw [pairedEtaGeometricReflectionEvenCoordinateCarrier_eq_onLine_add_offLineReal,
    pairedEtaReflectionEvenFrameSynthesisMatrix_self_mul_conjTranspose,
    sum_pairedEtaReflectionEvenFrame_eq_onLine_add_offLineReal]

/-- At a separated block the weighted frame synthesis has one rank direction
for every reflection-even atom. -/
theorem pairedEtaGeometricReflectionEvenFrameSynthesisMatrix_rank
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaReflectionEvenFrameSynthesisMatrix
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j) T).rank =
      Fintype.card (PairedEtaReflectionEvenFrameIndex T) := by
  let W := pairedEtaReflectionEvenFrameSynthesisMatrix
    (fun j : Fin (spectralZetaZeroWindow T).card ↦
      pairedEtaGeometricHyperbolicCutoff q n j) T
  have hrank := pairedEtaGeometricReflectionEvenCoordinateCarrier_rank
    q hT n hK
  rw [pairedEtaGeometricReflectionEvenCoordinateCarrier_eq_frameSynthesis,
    Matrix.rank_self_mul_conjTranspose] at hrank
  change W.rank = _
  change W.rank = _ at hrank
  exact hrank.trans (card_pairedEtaReflectionEvenFrameIndex T).symm

/-- Full synthesis rank makes the square-root-weighted frame columns linearly
independent. -/
theorem linearIndependent_cols_pairedEtaGeometricReflectionEvenFrameSynthesisMatrix
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameSynthesisMatrix
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T).col := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (PairedEtaReflectionEvenFrameIndex T) =
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (pairedEtaReflectionEvenFrameSynthesisMatrix
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T).col))
  rw [← Matrix.rank_eq_finrank_span_cols]
  exact
    (pairedEtaGeometricReflectionEvenFrameSynthesisMatrix_rank
      q hT n hK).symm

/-- Removing the nonzero square-root weights leaves the literal
reflection-even eta frame vectors linearly independent. -/
theorem linearIndependent_pairedEtaGeometricReflectionEvenFrameVector
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T) := by
  let cutoff : Fin (spectralZetaZeroWindow T).card → ℕ := fun j ↦
    pairedEtaGeometricHyperbolicCutoff q n j
  let v := pairedEtaReflectionEvenFrameVector cutoff T
  let w : PairedEtaReflectionEvenFrameIndex T → ℂˣ := fun a ↦
    Units.mk0 (pairedEtaReflectionEvenFrameSqrtWeight T a)
      (pairedEtaReflectionEvenFrameSqrtWeight_ne_zero T a)
  have hscaled :=
    linearIndependent_cols_pairedEtaGeometricReflectionEvenFrameSynthesisMatrix
      q hT n hK
  have hcols :
      (pairedEtaReflectionEvenFrameSynthesisMatrix cutoff T).col =
        w • v := by
    funext a j
    rfl
  change LinearIndependent ℂ v
  rw [hcols] at hscaled
  exact (LinearIndependent.units_smul_iff v w).mp hscaled

/-- Distinct separated geometric eta frame atoms satisfy strict
Cauchy--Schwarz. The proof is positivity of their two-vector complex Gram
determinant, transported back to the real correlation formula. -/
theorem pairedEtaGeometricReflectionEvenFrameCorrelation_sq_lt_normSq_mul_normSq
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    {a b : PairedEtaReflectionEvenFrameIndex T} (hab : a ≠ b) :
    (star (pairedEtaReflectionEvenFrameVector
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T b) ⬝ᵥ
        pairedEtaReflectionEvenFrameVector
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T a).re ^ 2 <
      pairedEtaReflectionEvenFrameAtomNormSq
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T a *
        pairedEtaReflectionEvenFrameAtomNormSq
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T b := by
  let cutoff : Fin (spectralZetaZeroWindow T).card → ℕ := fun j ↦
    pairedEtaGeometricHyperbolicCutoff q n j
  let v := pairedEtaReflectionEvenFrameVector cutoff T
  have hli : LinearIndependent ℂ v :=
    linearIndependent_pairedEtaGeometricReflectionEvenFrameVector
      q hT n hK
  let pair : Fin 2 → PairedEtaReflectionEvenFrameIndex T := ![a, b]
  have hpair : LinearIndependent ℂ (v ∘ pair) :=
    hli.comp pair (injective_pair_iff_ne.mpr hab)
  let e := (WithLp.linearEquiv 2 ℂ
    (Fin (spectralZetaZeroWindow T).card × Fin 2 → ℂ)).symm
  let u : Fin 2 → EuclideanSpace ℂ
      (Fin (spectralZetaZeroWindow T).card × Fin 2) :=
    fun i ↦ WithLp.toLp 2 (v (pair i))
  have hpairEuclidean : LinearIndependent ℂ u := by
    have hmapped := hpair.map' e.toLinearMap
      (LinearMap.ker_eq_bot_of_injective e.injective)
    simpa [u, e, Function.comp_def] using hmapped
  have hdet :=
    (Matrix.posDef_gram_of_linearIndependent hpairEuclidean).det_pos
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.gram_apply, u, pair, Matrix.cons_val_zero,
    Matrix.cons_val_one, EuclideanSpace.inner_toLp_toLp] at hdet
  have hva : star (v a) = v a :=
    star_pairedEtaReflectionEvenFrameVector cutoff T a
  have hvb : star (v b) = v b :=
    star_pairedEtaReflectionEvenFrameVector cutoff T b
  rw [hva, hvb, dotProduct_comm (v a) (v b)] at hdet
  let z := dotProduct (v b) (v a)
  have hz : ((z.re : ℝ) : ℂ) = z := by
    unfold z
    apply Complex.conj_eq_iff_re.mp
    have hcorr :=
      pairedEtaReflectionEvenFrameCorrelation_star_eq cutoff T a b
    change starRingEnd ℂ (dotProduct (star (v b)) (v a)) =
      dotProduct (star (v b)) (v a) at hcorr
    rw [hvb] at hcorr
    exact hcorr
  have hza :
      ((pairedEtaReflectionEvenFrameAtomNormSq cutoff T a : ℝ) : ℂ) =
        dotProduct (v a) (v a) := by
    calc
      _ = (((star (v a) ⬝ᵥ v a).re : ℝ) : ℂ) := by
        rw [pairedEtaReflectionEvenFrameCorrelation_self_re cutoff T a]
      _ = star (v a) ⬝ᵥ v a :=
        Complex.conj_eq_iff_re.mp
          (pairedEtaReflectionEvenFrameCorrelation_star_eq cutoff T a a)
      _ = _ := by rw [hva]
  have hzb :
      ((pairedEtaReflectionEvenFrameAtomNormSq cutoff T b : ℝ) : ℂ) =
        dotProduct (v b) (v b) := by
    calc
      _ = (((star (v b) ⬝ᵥ v b).re : ℝ) : ℂ) := by
        rw [pairedEtaReflectionEvenFrameCorrelation_self_re cutoff T b]
      _ = star (v b) ⬝ᵥ v b :=
        Complex.conj_eq_iff_re.mp
          (pairedEtaReflectionEvenFrameCorrelation_star_eq cutoff T b b)
      _ = _ := by rw [hvb]
  change 0 < dotProduct (v a) (v a) * dotProduct (v b) (v b) - z * z at hdet
  rw [← hza, ← hzb, ← hz] at hdet
  have hdetReal :
      0 < pairedEtaReflectionEvenFrameAtomNormSq cutoff T a *
          pairedEtaReflectionEvenFrameAtomNormSq cutoff T b - z.re * z.re := by
    simpa using (RCLike.pos_iff.mp hdet).1
  change (dotProduct (star (v b)) (v a)).re ^ 2 <
    pairedEtaReflectionEvenFrameAtomNormSq cutoff T a *
      pairedEtaReflectionEvenFrameAtomNormSq cutoff T b
  rw [hvb]
  change z.re ^ 2 < _
  nlinarith

/-- Every ordered distinct pair contributes a strictly positive weighted
decorrelation term at a separated geometric block. -/
theorem pairedEtaGeometricReflectionEvenFrameDecorrelationPairTerm_pos
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    {a b : PairedEtaReflectionEvenFrameIndex T} (hab : a ≠ b) :
    0 < pairedEtaReflectionEvenFrameWeight T a *
        pairedEtaReflectionEvenFrameWeight T b *
          (pairedEtaReflectionEvenFrameAtomNormSq
                (fun j : Fin (spectralZetaZeroWindow T).card ↦
                  pairedEtaGeometricHyperbolicCutoff q n j) T a *
              pairedEtaReflectionEvenFrameAtomNormSq
                (fun j : Fin (spectralZetaZeroWindow T).card ↦
                  pairedEtaGeometricHyperbolicCutoff q n j) T b -
            (star (pairedEtaReflectionEvenFrameVector
                  (fun j : Fin (spectralZetaZeroWindow T).card ↦
                    pairedEtaGeometricHyperbolicCutoff q n j) T b) ⬝ᵥ
              pairedEtaReflectionEvenFrameVector
                (fun j : Fin (spectralZetaZeroWindow T).card ↦
                  pairedEtaGeometricHyperbolicCutoff q n j) T a).re ^ 2) := by
  exact mul_pos
    (mul_pos (pairedEtaReflectionEvenFrameWeight_pos T a)
      (pairedEtaReflectionEvenFrameWeight_pos T b))
    (sub_pos.mpr
      (pairedEtaGeometricReflectionEvenFrameCorrelation_sq_lt_normSq_mul_normSq
        q hT n hK hab))

/-- One distinct atom pair forces the complete decorrelation reserve to be
strictly positive. -/
theorem pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos_of_pair
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    {a b : PairedEtaReflectionEvenFrameIndex T} (hab : a ≠ b) :
    0 < pairedEtaReflectionEvenFrameDecorrelationReserve
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j) T := by
  unfold pairedEtaReflectionEvenFrameDecorrelationReserve
  apply Finset.sum_pos'
  · intro x _hx
    exact Finset.sum_nonneg fun y _hy ↦
      pairedEtaReflectionEvenFrameDecorrelationPairTerm_nonneg
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T x y
  · refine ⟨a, Finset.mem_univ a, ?_⟩
    apply Finset.sum_pos'
    · intro x _hx
      exact pairedEtaReflectionEvenFrameDecorrelationPairTerm_nonneg
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T a x
    · refine ⟨b, ?_, ?_⟩
      · exact Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
      · exact
          pairedEtaGeometricReflectionEvenFrameDecorrelationPairTerm_pos
            q hT n hK hab

/-- A separated frame with at least two atoms has strictly positive total
decorrelation reserve. -/
theorem pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (hcard : 1 < Fintype.card (PairedEtaReflectionEvenFrameIndex T)) :
    0 < pairedEtaReflectionEvenFrameDecorrelationReserve
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j) T := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hcard
  exact pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos_of_pair
    q hT n hK hab

/-- Any frame with at most one atom has zero distinct-pair reserve. -/
theorem pairedEtaReflectionEvenFrameDecorrelationReserve_eq_zero_of_card_le_one
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    (hcard : Fintype.card (PairedEtaReflectionEvenFrameIndex T) ≤ 1) :
    pairedEtaReflectionEvenFrameDecorrelationReserve cutoff T = 0 := by
  unfold pairedEtaReflectionEvenFrameDecorrelationReserve
  apply Finset.sum_eq_zero
  intro a _ha
  apply Finset.sum_eq_zero
  intro b hb
  exfalso
  exact (Finset.mem_erase.mp hb).1
    ((Fintype.card_le_one_iff.mp hcard) b a)

/-- At a separated block the total reserve is positive exactly when the
reflection-even eta frame contains at least two atoms. -/
theorem pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos_iff
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    0 < pairedEtaReflectionEvenFrameDecorrelationReserve
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T ↔
      1 < Fintype.card (PairedEtaReflectionEvenFrameIndex T) := by
  constructor
  · intro hreserve
    by_contra hcard
    have hcardLe :
        Fintype.card (PairedEtaReflectionEvenFrameIndex T) ≤ 1 :=
      Nat.not_lt.mp hcard
    rw [pairedEtaReflectionEvenFrameDecorrelationReserve_eq_zero_of_card_le_one
      (fun j : Fin (spectralZetaZeroWindow T).card ↦
        pairedEtaGeometricHyperbolicCutoff q n j) T hcardLe] at hreserve
    exact lt_irrefl 0 hreserve
  · exact pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos
      q hT n hK

/-- At a separated block, strict improvement over the rank-one frame-potential
identity occurs exactly when at least two reflection-even atoms are present. -/
theorem pairedEtaGeometricReflectionEvenFramePotential_lt_traceMass_sq_iff
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaReflectionEvenFramePotential
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T <
        pairedEtaReflectionEvenFrameTraceMass
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T ^ 2 ↔
      1 < Fintype.card (PairedEtaReflectionEvenFrameIndex T) := by
  let cutoff : Fin (spectralZetaZeroWindow T).card → ℕ := fun j ↦
    pairedEtaGeometricHyperbolicCutoff q n j
  have hreserve :=
    pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos_iff
      q hT n hK
  rw [pairedEtaReflectionEvenFrameTraceMass_sq_eq_potential_add_reserve]
  change
    pairedEtaReflectionEvenFramePotential cutoff T <
        pairedEtaReflectionEvenFramePotential cutoff T +
          pairedEtaReflectionEvenFrameDecorrelationReserve cutoff T ↔ _
  rw [lt_add_iff_pos_right]
  exact hreserve

/-- For every nonnegative window height, one odd prime base makes the exact
reserve-positivity characterization valid at all sufficiently late blocks. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos_iff
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        (0 < pairedEtaReflectionEvenFrameDecorrelationReserve
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T ↔
          1 < Fintype.card (PairedEtaReflectionEvenFrameIndex T)) := by
  obtain ⟨q, hqPrime, hqOdd, hq, hpos⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hpos] with n hn
  exact pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos_iff
    q hT n hn.1

/-- If the reflection-even window has at least two atoms, one odd prime base
makes its literal eta decorrelation reserve strictly positive at every
sufficiently late block. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos
    {T : ℝ} (hT : 0 ≤ T)
    (hcard : 1 < Fintype.card (PairedEtaReflectionEvenFrameIndex T)) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        0 < pairedEtaReflectionEvenFrameDecorrelationReserve
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T := by
  obtain ⟨q, hqPrime, hqOdd, hq, hpos⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hpos] with n hn
  exact pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_pos
    q hT n hn.1 hcard

end

end RiemannGaussian
