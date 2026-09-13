/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovShiftedMoment
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The two-Hölder reduction with complete frequency multiplicities

The finite exponential sum is converted to an explicit even moment over
its full tuple-frequency support. All complex alignment weights and all
integer frequency coordinates remain available. This is the reduction in
Ford (2002), Lemma 5.1, equation (5.3); estimating the resulting moment and
the homogeneous Vinogradov counts is still required for a power saving.
-/

namespace RiemannGaussian.VinogradovMomentReduction
noncomputable section
open UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open scoped BigOperators ComplexConjugate

/-- All frequency values attained by the finite family. -/
def frequencySupport {ι G : Type*} [Fintype ι] (v : ι → G) : Finset G := by
  classical
  exact Finset.univ.image v

/-- The literal number of indices attaining a frequency. -/
def frequencyMultiplicity {ι G : Type*} [Fintype ι] (v : ι → G) (c : G) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => v i = c)).card

/-- Grouping by exact frequency retains its full multiplicity and works
over any semiring, including natural counts and complex phases. -/
theorem sum_frequencyMultiplicity {ι G R : Type*} [Fintype ι] [Semiring R]
    (v : ι → G) (F : G → R) :
    (∑ c ∈ frequencySupport v, (frequencyMultiplicity v c : R) * F c) = ∑ i, F (v i) := by
  classical
  calc
    _ = ∑ c ∈ frequencySupport v, ∑ i ∈ Finset.univ.filter (fun i => v i = c), F (v i) := by
      apply Finset.sum_congr rfl
      intro c hc
      have he : (∑ i ∈ Finset.univ.filter (fun i => v i = c), F (v i)) =
          ∑ _i ∈ Finset.univ.filter (fun i => v i = c), F c := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      rw [he]
      simp [frequencyMultiplicity]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem v hi) _

/-- The full frequency multiplicity has exactly the original total mass. -/
theorem frequencyMultiplicity_mass {ι G : Type*} [Fintype ι] (v : ι → G) :
    (∑ c ∈ frequencySupport v, frequencyMultiplicity v c) = Fintype.card ι := by
  simpa using sum_frequencyMultiplicity v (fun _ => (1 : ℕ))

/-- Squared frequency multiplicity is exactly the homogeneous collision
count, with no loss from taking a support envelope. -/
theorem frequencyMultiplicity_energy {d ι : Type*} [Fintype d] [Fintype ι]
    (v : ι → d → ℤ) :
    (∑ c ∈ frequencySupport v, frequencyMultiplicity v c ^ 2) = differenceCount v 0 := by
  classical
  have he := sum_frequencyMultiplicity v (frequencyMultiplicity v)
  simp only [Nat.cast_id, ← sq] at he
  rw [he, differenceCount, Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [frequencyMultiplicity, Finset.card_filter, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eq_comm]

/-- Natural-power weighted Hölder, with the complete nonnegative weight
mass and no real-exponent convention at zero. -/
theorem weighted_power_bound {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hf : ∀ i ∈ S, 0 ≤ f i) {p : ℕ} (hp : 1 ≤ p) :
    (∑ i ∈ S, w i * f i) ^ p ≤
      (∑ i ∈ S, w i) ^ (p - 1) * ∑ i ∈ S, w i * f i ^ p := by
  have hW : 0 ≤ ∑ i ∈ S, w i := Finset.sum_nonneg hw
  by_cases hzero : ∑ i ∈ S, w i = 0
  · have hz : ∀ i ∈ S, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hzero
    have he : (∑ i ∈ S, w i * f i) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hz i hi, zero_mul])
    rw [he, zero_pow (by omega)]
    exact mul_nonneg (pow_nonneg hW _) (Finset.sum_nonneg (fun i hi => by
      exact mul_nonneg (hw i hi) (pow_nonneg (hf i hi) _)))
  have hpos := lt_of_le_of_ne hW (Ne.symm hzero)
  have hn : (∑ i ∈ S, w i / (∑ j ∈ S, w j)) = 1 := by
    rw [← Finset.sum_div, div_self hzero]
  have h := Real.pow_arith_mean_le_arith_mean_pow S
    (fun i => w i / (∑ j ∈ S, w j)) f
    (fun i hi => div_nonneg (hw i hi) hW) hn hf p
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, div_pow] at h
  have h' := (div_le_div_iff₀ (pow_pos hpos p) hpos).mp h
  have he : (∑ i ∈ S, w i) ^ p = (∑ i ∈ S, w i) * (∑ i ∈ S, w i) ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp]
  rw [he] at h'
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  nlinarith only [h']

/-- The complex weighted sum pays the natural-power Hölder budget, with
norms introduced only after the original sum has been formed. -/
theorem norm_weighted_power_bound {ι : Type*} (S : Finset ι) (w : ι → ℝ) (F : ι → ℂ)
    (hw : ∀ i ∈ S, 0 ≤ w i) {p : ℕ} (hp : 1 ≤ p) :
    ‖∑ i ∈ S, (w i : ℂ) * F i‖ ^ p ≤
      (∑ i ∈ S, w i) ^ (p - 1) * ∑ i ∈ S, w i * ‖F i‖ ^ p := by
  have hn : ‖∑ i ∈ S, (w i : ℂ) * F i‖ ≤ ∑ i ∈ S, w i * ‖F i‖ := by
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn p).trans
    (weighted_power_bound S w (fun i => ‖F i‖) hw (fun _ _ => norm_nonneg _) hp)

/-- The second Hölder step retains both the frequency mass and its exact
square energy, followed by the complete even moment of the remaining sum. -/
theorem norm_weighted_even_bound {ι : Type*} (S : Finset ι) (w : ι → ℝ) (F : ι → ℂ)
    (hw : ∀ i ∈ S, 0 ≤ w i) {s : ℕ} (hs : 1 ≤ s) :
    ‖∑ i ∈ S, (w i : ℂ) * F i‖ ^ (2 * s) ≤
      (∑ i ∈ S, w i) ^ (2 * s - 2) * (∑ i ∈ S, w i ^ 2) *
        ∑ i ∈ S, ‖F i‖ ^ (2 * s) := by
  have h := norm_weighted_power_bound S w F hw hs
  have hsq := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) s) h 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S w (fun i => ‖F i‖ ^ s)
  have he : 2 * s - 2 = (s - 1) * 2 := by omega
  simp only [mul_pow, ← pow_mul] at hsq
  simp only [← pow_mul] at hc
  rw [Nat.mul_comm s 2] at hsq hc
  apply hsq.trans
  rw [he, mul_assoc]
  exact mul_le_mul_of_nonneg_left hc (pow_nonneg (Finset.sum_nonneg hw) _)

/-- Exact alignment of a complex value with the positive real axis. At
zero the alignment is zero, which remains an admissible bounded weight. -/
def phaseAlign (z : ℂ) : ℂ := (‖z‖ : ℂ) / z

/-- Every alignment weight has norm at most one, including at zero. -/
theorem norm_phaseAlign (z : ℂ) : ‖phaseAlign z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phaseAlign, hz]
  · simp [phaseAlign, norm_ne_zero_iff.mpr hz]

/-- Alignment preserves the entire magnitude exactly before any estimate. -/
theorem phaseAlign_mul (z : ℂ) : phaseAlign z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [phaseAlign, hz]
  · exact div_mul_cancel₀ _ hz

/-- The first Hölder step retains the complex alignment of every powered
inner sum, with all cardinality exponents explicit. -/
theorem norm_sum_power_le_aligned {ι : Type*} [Fintype ι] (F : ι → ℂ)
    {r : ℕ} (hr : 1 ≤ r) :
    ‖∑ i, F i‖ ^ r ≤ (Fintype.card ι : ℝ) ^ (r - 1) *
      ‖∑ i, phaseAlign (F i ^ r) * F i ^ r‖ := by
  have h := norm_weighted_power_bound Finset.univ (fun _ : ι => 1) F (by simp) hr
  simp only [Complex.ofReal_one, one_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at h
  have he : ‖∑ i, phaseAlign (F i ^ r) * F i ^ r‖ = ∑ i, ‖F i‖ ^ r := by
    simp only [phaseAlign_mul, norm_pow, ← Complex.ofReal_sum, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun _ _ => by positivity))
  rwa [he]

/-- The powered Fourier sum has its exact full frequency multiplicity. -/
theorem fourier_power_by_multiplicity {d ι : Type*} [Fintype d] [Fintype ι]
    (r : ℕ) (v : ι → d → ℤ) (θ : UnitAddTorus d) :
    (∑ i, mFourier (v i) θ) ^ r =
      ∑ c ∈ frequencySupport (tupleFrequency r v),
        (frequencyMultiplicity (tupleFrequency r v) c : ℂ) * mFourier c θ := by
  rw [sum_frequencyMultiplicity]
  exact power_expansion v r θ

/-- Arbitrary outer weights and all tuple frequencies survive the exact
exchange of the powered inner sum with the frequency multiplicity. -/
theorem weighted_power_sum {d ι κ : Type*} [Fintype d] [Fintype ι] [Fintype κ]
    (r : ℕ) (v : ι → d → ℤ) (θ : κ → UnitAddTorus d) (w : κ → ℂ) :
    (∑ b, w b * (∑ a, mFourier (v a) (θ b)) ^ r) =
      ∑ c ∈ frequencySupport (tupleFrequency r v),
        (frequencyMultiplicity (tupleFrequency r v) c : ℂ) *
          ∑ b, w b * mFourier c (θ b) := by
  simp_rw [fourier_power_by_multiplicity, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- The complete even moment over the actual tuple-frequency support,
with every complex alignment weight and sampling phase retained. -/
def dualMoment {d ι κ : Type*} [Fintype d] [Fintype ι] [Fintype κ]
    (r s : ℕ) (v : ι → d → ℤ) (θ : κ → UnitAddTorus d) (w : κ → ℂ) : ℝ :=
  ∑ c ∈ frequencySupport (tupleFrequency r v), ‖∑ b, w b * mFourier c (θ b)‖ ^ (2 * s)

/-- The actual alignment weight is determined by the original powered
inner sum. Its dependence on the sampling phases remains explicit. -/
def alignmentWeights {d ι κ : Type*} [Fintype d] [Fintype ι]
    (r : ℕ) (v : ι → d → ℤ) (θ : κ → UnitAddTorus d) (b : κ) : ℂ :=
  phaseAlign ((∑ a, mFourier (v a) (θ b)) ^ r)

/-- The explicit phase-dependent alignment weights are bounded at every
sample, including samples where the original inner sum vanishes. -/
theorem norm_alignmentWeights {d ι κ : Type*} [Fintype d] [Fintype ι]
    (r : ℕ) (v : ι → d → ℤ) (θ : κ → UnitAddTorus d) (b : κ) :
    ‖alignmentWeights r v θ b‖ ≤ 1 := norm_phaseAlign _

/-- The two-Hölder reduction keeps the literal homogeneous moment and the
complete dual moment with the actual phase-dependent alignment weights.
It holds for every finite frequency family and torus sampling family. -/
theorem two_holder_bound {d ι κ : Type*} [Fintype d] [Fintype ι] [Fintype κ]
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (v : ι → d → ℤ) (θ : κ → UnitAddTorus d) :
    ‖∑ b, ∑ a, mFourier (v a) (θ b)‖ ^ (2 * r * s) ≤
      (Fintype.card κ : ℝ) ^ ((r - 1) * (2 * s)) *
      (Fintype.card ι : ℝ) ^ (r * (2 * s - 2)) *
      moment r v * dualMoment r s v θ (alignmentWeights r v θ) := by
  classical
  let F : κ → ℂ := fun b => ∑ a, mFourier (v a) (θ b)
  let w : κ → ℂ := alignmentWeights r v θ
  have hfirst := norm_sum_power_le_aligned F hr
  have hpow := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) r) hfirst (2 * s)
  change ‖∑ b, F b‖ ^ r ≤ (Fintype.card κ : ℝ) ^ (r - 1) *
    ‖∑ b, w b * F b ^ r‖ at hfirst
  change (‖∑ b, F b‖ ^ r) ^ (2 * s) ≤
    ((Fintype.card κ : ℝ) ^ (r - 1) * ‖∑ b, w b * F b ^ r‖) ^ (2 * s) at hpow
  simp only [F, weighted_power_sum, mul_pow, ← pow_mul] at hpow
  have hmass : (∑ c ∈ frequencySupport (tupleFrequency r v),
      (frequencyMultiplicity (tupleFrequency r v) c : ℝ)) = (Fintype.card ι : ℝ) ^ r := by
    rw [← Nat.cast_sum, frequencyMultiplicity_mass, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_pow]
  have henergy : (∑ c ∈ frequencySupport (tupleFrequency r v),
      (frequencyMultiplicity (tupleFrequency r v) c : ℝ) ^ 2) = moment r v := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (frequencyMultiplicity_energy (tupleFrequency r v))
    simpa only [Nat.cast_sum, Nat.cast_pow, tupleFrequency_count_zero,
      ← moment_eq_collisionCount] using h
  have hsecond := norm_weighted_even_bound (frequencySupport (tupleFrequency r v))
    (fun c => (frequencyMultiplicity (tupleFrequency r v) c : ℝ))
    (fun c => ∑ b, w b * mFourier c (θ b)) (fun _ _ => Nat.cast_nonneg _) hs
  simp only [Complex.ofReal_natCast, hmass, henergy, ← pow_mul] at hsecond
  have h := hpow.trans (mul_le_mul_of_nonneg_left hsecond (by positivity))
  rw [show 2 * r * s = r * (2 * s) by ring]
  simpa only [dualMoment, mul_assoc] using h

/-- The bounded-weight form follows from the explicit alignment theorem.
The stronger theorem keeps the formula needed for later phase correlations. -/
theorem exists_two_holder {d ι κ : Type*} [Fintype d] [Fintype ι] [Fintype κ]
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (v : ι → d → ℤ) (θ : κ → UnitAddTorus d) :
    ∃ w : κ → ℂ, (∀ b, ‖w b‖ ≤ 1) ∧
      ‖∑ b, ∑ a, mFourier (v a) (θ b)‖ ^ (2 * r * s) ≤
        (Fintype.card κ : ℝ) ^ ((r - 1) * (2 * s)) *
        (Fintype.card ι : ℝ) ^ (r * (2 * s - 2)) *
        moment r v * dualMoment r s v θ w :=
  ⟨alignmentWeights r v θ, norm_alignmentWeights r v θ, two_holder_bound hr hs v θ⟩

end
end RiemannGaussian.VinogradovMomentReduction
