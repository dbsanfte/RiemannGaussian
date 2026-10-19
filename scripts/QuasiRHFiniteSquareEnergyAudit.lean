/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.CubicSieve.Sharp
import OAI.NumberTheory.DirichletL.CubicSieve.Gcd
import OAI.NumberTheory.DirichletL.CubicSieve.B2Growth
import OAI.NumberTheory.DirichletL.Detector.LowColumnBounds
import OAI.NumberTheory.DirichletL.Detector.GramIdealSummation
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
Quantitative finite divisor assembly with the literal native cubic kernel.
The sieve energy is proved from the imported arithmetic theorem, not assumed.
The separate Gauss bridge to the original finite amplitude is not asserted.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.FiniteSquareEnergy
open OAI OAI.SevenEighths OAI.CompletedGauss
open OAI.SevenEighths.CubicSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "SupportedIdeal" => {I : Id // CanonicalQuadraticSieve.Supported I}

/-- A literal cubic divisor block, retaining both coprimality masks. The
coefficient is fixed across quotient rows; the extra mask is row-only. -/
def divisorBlock (N : ℝ) (d : SupportedIdeal) (b : idealRange N → ℂ)
    (r : Id → ℂ) (a : Id) : ℂ :=
  if d.val ∣ a ∧ IsCoprime d.val (CanonicalQuadraticSieve.idealQuotient d.val a) then
    r (CanonicalQuadraticSieve.idealQuotient d.val a) *
      ∑ j : idealRange N, star (idealKernel j.val (CanonicalQuadraticSieve.idealQuotient d.val a)) *
        (if IsCoprime d.val j.val then b j else 0)
  else 0

/-- The actual divisor incidence vanishes off divisibility. -/
theorem divisorBlock_zero (N : ℝ) (d : SupportedIdeal) (b : idealRange N → ℂ)
    (r : Id → ℂ) (a : Id) (h : ¬d.val ∣ a) : divisorBlock N d b r a = 0 := by
  simp [divisorBlock, h]

/-- Native conjugate cubic energy on any injective squarefree ideal family. -/
theorem conjugate_family_energy {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (rows : m → Id) (cols : n → Id)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (b : n → ℂ) :
    (∑ i, ‖∑ j, star (idealKernel (cols j) (rows i)) * b j‖^2) ≤
      sieveNorm M N * ∑ j, ‖b j‖^2 := by
  have h := energy_le_squaredNorm (fun i j => idealKernel (cols j) (rows i)) (fun j => star (b j))
  have hn := family_squared_norm_le rows cols hr hc M N hrows hcols
  have he (i : m) : ‖∑ j, star (idealKernel (cols j) (rows i)) * b j‖ =
      ‖∑ j, idealKernel (cols j) (rows i) * star (b j)‖ := by
    conv_lhs => rw [← norm_star]
    simp only [star_sum, star_mul, star_star, mul_comm]
  simp only [he, norm_star] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_right hn (by positivity))

/-- Actual quotient rows inject into the native range A/Nd. No supplied row
energy or unexplained quotient multiplicity is used. -/
theorem divisorBlock_energy (A N : ℝ) (d : SupportedIdeal) (b : idealRange N → ℂ)
    (r : Id → ℂ) (hr : ∀ I, ‖r I‖ ≤ 1) :
    (∑ a ∈ idealRange A, ‖divisorBlock N d b r a‖^2) ≤
      sieveNorm (A / ProbeGramCommon.gramIdealNorm d) N * ∑ j, ‖b j‖^2 := by
  let S := (idealRange A).filter (fun a => d.val ∣ a ∧
    IsCoprime d.val (CanonicalQuadraticSieve.idealQuotient d.val a))
  let rows : S → Id := fun a => CanonicalQuadraticSieve.idealQuotient d.val a.val
  let coef : idealRange N → ℂ := fun j => if IsCoprime d.val j.val then b j else 0
  have hdiv (a : S) : d.val ∣ a.val := (Finset.mem_filter.mp a.property).2.1
  have hi : Function.Injective rows := by
    intro a a' he
    apply Subtype.ext
    exact CanonicalQuadraticSieve.idealQuotient_injective_on d.val (hdiv a) (hdiv a') he
  have hrows : ∀ a : S, Admissible (rows a) ∧
      (Ideal.absNorm (rows a) : ℝ) ≤ A / ProbeGramCommon.gramIdealNorm d := by
    intro a
    have ha := mem_idealRange.mp (Finset.mem_filter.mp a.property).1
    exact ⟨cubic_admissible_quotient ha.1 (hdiv a),
      CanonicalQuadraticSieve.idealQuotient_norm_le d.property.1 (hdiv a) A ha.2⟩
  have he := conjugate_family_energy rows (fun j : idealRange N => j.val) hi
    Subtype.val_injective _ N hrows (fun j => mem_idealRange.mp j.property) coef
  have hmass : (∑ j, ‖coef j‖^2) ≤ ∑ j, ‖b j‖^2 := by
    apply Finset.sum_le_sum
    intro j _
    dsimp [coef]
    split_ifs <;> simp
  have hn : 0 ≤ sieveNorm (A / ProbeGramCommon.gramIdealNorm d) N := squaredNorm_nonneg _
  calc
    _ = ∑ a ∈ S, ‖r (CanonicalQuadraticSieve.idealQuotient d.val a) *
        ∑ j : idealRange N, star (idealKernel j.val (CanonicalQuadraticSieve.idealQuotient d.val a)) * coef j‖^2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [divisorBlock, coef]
      split_ifs <;> simp
    _ = ∑ a : S, ‖r (rows a) * ∑ j : idealRange N, star (idealKernel j.val (rows a)) * coef j‖^2 := by
      dsimp only [rows]
      exact (Finset.sum_coe_sort S (fun a : Id => ‖r (CanonicalQuadraticSieve.idealQuotient d.val a) * ∑ j : idealRange N, star (idealKernel j.val (CanonicalQuadraticSieve.idealQuotient d.val a)) * coef j‖^2)).symm
    _ ≤ ∑ a : S, ‖∑ j : idealRange N, star (idealKernel j.val (rows a)) * coef j‖^2 := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_of_le_one_left (norm_nonneg _) (hr _)) 2
    _ ≤ sieveNorm (A / ProbeGramCommon.gramIdealNorm d) N * ∑ j, ‖coef j‖^2 := he
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hn

/-- The literal supported-ideal divisor fiber is bounded by the imported
actual ideal divisor count. -/
theorem divisor_fiber_card (D : Finset SupportedIdeal) (a : Id) (ha : a ≠ 0) :
    ((D.filter (fun d => d.val ∣ a)).card : ℝ) ≤
      (IdealMobiusDivisorSum.idealDivisors a).card := by
  have hi : Function.Injective (fun d : SupportedIdeal => d.val) := Subtype.val_injective
  have hs : (D.filter (fun d => d.val ∣ a)).image (fun d => d.val) ⊆
      IdealMobiusDivisorSum.idealDivisors a := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    exact (IdealMobiusDivisorSum.mem_idealDivisors ha).mpr (Finset.mem_filter.mp hs).2
  have hh := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hi] at hh
  exact_mod_cast hh

/-- Divisor Cauchy pays the actual incoming multiplicity before exchanging
finite rows and divisor blocks. It assumes no arithmetic energy estimate. -/
theorem divisor_assembly_cauchy (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 1 ≤ A → ∀ (D : Finset SupportedIdeal)
      (H : SupportedIdeal → Id → ℂ),
      (∀ d ∈ D, ∀ a ∈ idealRange A, ¬d.val ∣ a → H d a = 0) →
      (∑ a ∈ idealRange A, ‖∑ d ∈ D, H d a‖^2) ≤
        C * A^η * ∑ d ∈ D, ∑ a ∈ idealRange A, ‖H d a‖^2 := by
  obtain ⟨C, hC, hb⟩ := IdealDivisorBound.ideal_divisor_small_power η hη
  refine ⟨C, hC, ?_⟩
  intro A hA D H hzero
  have hp (a : Id) (ha : a ∈ idealRange A) :
      ‖∑ d ∈ D, H d a‖^2 ≤ C * A^η * ∑ d ∈ D, ‖H d a‖^2 := by
    have ha' := mem_idealRange.mp ha
    have ha0 := primaryGenerator_ne_zero_ideal a ha'.1.2
    let F := D.filter (fun d => d.val ∣ a)
    have hcard : (F.card : ℝ) ≤ C * A^η := by
      exact (divisor_fiber_card D a ha0).trans ((hb a ha0).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ha'.2 hη.le) hC.le))
    have he : (∑ d ∈ D, H d a) = ∑ d ∈ F, H d a := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hn
      exact hzero d hd a ha (by simpa only [F, Finset.mem_filter, hd, true_and] using hn)
    rw [he]
    calc
      _ ≤ (∑ d ∈ F, ‖H d a‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (F.card : ℝ) * ∑ d ∈ F, ‖H d a‖^2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (C*A^η) * ∑ d ∈ F, ‖H d a‖^2 := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ a ∈ idealRange A, C*A^η * ∑ d ∈ D, ‖H d a‖^2 := Finset.sum_le_sum hp
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

/-- Pointwise column norms and the ACTUAL finite ideal count pay the entire
column mass. No row-energy assumption is hidden in this bound. -/
theorem column_mass_bound (Y D B : ℝ) (hY : 0 < Y) (hD : 0 < D)
    (hN : 1 ≤ Y / D^3) (b : idealRange (Y/D^3) → ℂ)
    (hb : ∀ j, ‖b j‖ ≤ B*D/Y) :
    (∑ j, ‖b j‖^2) ≤ (128*B^2)/(Y*D) := by
  have hc := DescentFiberCost.finite_ideal_count_real (idealRange (Y/D^3))
    (Y/D^3) hN
    (fun I hI => primaryGenerator_ne_zero_ideal I (mem_idealRange.mp hI).1.2)
    (fun I hI => (mem_idealRange.mp hI).2)
  calc
    _ ≤ ∑ _j : idealRange (Y/D^3), (B*D/Y)^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
    _ = ((idealRange (Y/D^3)).card : ℝ)*(B*D/Y)^2 := by simp
    _ ≤ (128*(Y/D^3))*(B*D/Y)^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by field_simp

/-- Uniform decay of the literal rectangular shape in the divisor norm. -/
theorem divisor_shape (A Y D ε : ℝ) (hA : 0 < A) (hY : 0 < Y)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) :
    ((A/D)*(Y/D^3))^ε * (A/D+Y/D^3+((A/D)*(Y/D^3))^(2/3 : ℝ)) /
      (Y*D) ≤ (A*Y)^ε * ((A+Y+(A*Y)^(2/3 : ℝ))/Y) * D^(-2 : ℝ) := by
  have hD0 : 0 < D := by linarith
  have hD3 : D ≤ D^3 := by nlinarith [sq_nonneg (D-1)]
  have hD4 : 1 ≤ D^4 := one_le_pow₀ hD
  have he : (A/D)*(Y/D^3)=A*Y/D^4 := by field_simp
  have hp : ((A/D)*(Y/D^3))^ε ≤ (A*Y)^ε := by
    apply Real.rpow_le_rpow (by positivity) _ hε
    rw [he]
    exact div_le_self (by positivity) hD4
  have h8 : D ≤ D^(8/3 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one D]
    exact Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
  have hcross : ((A/D)*(Y/D^3))^(2/3 : ℝ) ≤ (A*Y)^(2/3 : ℝ)/D := by
    rw [he, Real.div_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast_mul hD0.le]
    norm_num
    exact div_le_div_of_nonneg_left (by positivity) hD0 h8
  have hs : A/D+Y/D^3+((A/D)*(Y/D^3))^(2/3 : ℝ) ≤
      (A+Y+(A*Y)^(2/3 : ℝ))/D := by
    have hy : Y/D^3 ≤ Y/D := div_le_div_of_nonneg_left hY.le hD0 hD3
    rw [add_div, add_div]
    linarith
  calc
    _ ≤ (A*Y)^ε * ((A+Y+(A*Y)^(2/3 : ℝ))/D) / (Y*D) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hp hs (by positivity) (by positivity)
    _ = _ := by
      rw [Real.rpow_neg hD0.le, Real.rpow_two]
      field_simp

/-- Fully paid finite cubic divisor assembly. Only explicit coefficient MASS
is supplied; every block energy, incoming divisor cost, and divisor sum is proved
from actual imported arithmetic. Both literal coprimality masks are retained. -/
theorem assembled_energy (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ A Y B : ℝ, 1 ≤ A → 1 ≤ Y → 0 ≤ B →
      ∀ (D : Finset SupportedIdeal)
        (b : (d : SupportedIdeal) → idealRange (Y / ProbeGramCommon.gramIdealNorm d ^ 3) → ℂ)
        (r : SupportedIdeal → Id → ℂ),
        (∀ d ∈ D, 1 ≤ A / ProbeGramCommon.gramIdealNorm d ∧
          1 ≤ Y / ProbeGramCommon.gramIdealNorm d ^ 3) →
        (∀ d ∈ D, ∀ I, ‖r d I‖ ≤ 1) →
        (∀ d ∈ D, (∑ j, ‖b d j‖^2) ≤ B / (Y*ProbeGramCommon.gramIdealNorm d)) →
        (∑ a ∈ idealRange A, ‖∑ d ∈ D,
          divisorBlock (Y / ProbeGramCommon.gramIdealNorm d ^ 3) d (b d) (r d) a‖^2) ≤
          C * A^η * (A*Y)^ε * ((A+Y+(A*Y)^(2/3 : ℝ))/Y) * B := by
  obtain ⟨K, hK, hsieve⟩ := sieveNorm_sharp ε hε
  obtain ⟨L, hL, hcauchy⟩ := divisor_assembly_cauchy η hη
  obtain ⟨S, hS, hsum⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-2) (by norm_num)
  refine ⟨L*K*S, by positivity, ?_⟩
  intro A Y B hA hY hB D b r hscale hr hmass
  have hA0 : 0 < A := by linarith
  have hY0 : 0 < Y := by linarith
  have he (d : SupportedIdeal) (hd : d ∈ D) :
      (∑ a ∈ idealRange A,
        ‖divisorBlock (Y / ProbeGramCommon.gramIdealNorm d ^ 3) d (b d) (r d) a‖^2) ≤
        (K*B*(A*Y)^ε*((A+Y+(A*Y)^(2/3 : ℝ))/Y)) *
          ProbeGramCommon.gramIdealNorm d ^ (-2 : ℝ) := by
    let t := ProbeGramCommon.gramIdealNorm d
    have ht : 0 < t := ProbeGramCommon.gramIdealNorm_pos d
    have hn : 0 ≤ sieveNorm (A/t) (Y/t^3) := squaredNorm_nonneg _
    have hcost : 0 ≤ K*((A/t)*(Y/t^3))^ε*(A/t+Y/t^3+((A/t)*(Y/t^3))^(2/3 : ℝ)) := by positivity
    calc
      _ ≤ sieveNorm (A/t) (Y/t^3) * ∑ j, ‖b d j‖^2 :=
        divisorBlock_energy A _ d (b d) (r d) (hr d hd)
      _ ≤ sieveNorm (A/t) (Y/t^3) * (B/(Y*t)) :=
        mul_le_mul_of_nonneg_left (hmass d hd) hn
      _ ≤ (K*((A/t)*(Y/t^3))^ε*(A/t+Y/t^3+((A/t)*(Y/t^3))^(2/3 : ℝ))) * (B/(Y*t)) :=
        mul_le_mul_of_nonneg_right (hsieve _ _ (hscale d hd).1 (hscale d hd).2) (by positivity)
      _ = (K*B) * (((A/t)*(Y/t^3))^ε*(A/t+Y/t^3+((A/t)*(Y/t^3))^(2/3 : ℝ))/(Y*t)) := by ring
      _ ≤ (K*B) * ((A*Y)^ε*((A+Y+(A*Y)^(2/3 : ℝ))/Y)*t^(-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (divisor_shape A Y t ε hA0 hY0 (ProbeGramCommon.gramIdealNorm_one_le d) hε.le) (by positivity)
      _ = _ := by ring
  have hc := hcauchy A hA D
    (fun d => divisorBlock (Y / ProbeGramCommon.gramIdealNorm d ^ 3) d (b d) (r d))
    (fun d _ a _ h => divisorBlock_zero _ d _ _ a h)
  calc
    _ ≤ L*A^η * ∑ d ∈ D, ∑ a ∈ idealRange A,
        ‖divisorBlock (Y / ProbeGramCommon.gramIdealNorm d ^ 3) d (b d) (r d) a‖^2 := hc
    _ ≤ L*A^η * ∑ d ∈ D,
        (K*B*(A*Y)^ε*((A+Y+(A*Y)^(2/3 : ℝ))/Y)) *
          ProbeGramCommon.gramIdealNorm d ^ (-2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum he) (by positivity)
    _ = L*A^η * ((K*B*(A*Y)^ε*((A+Y+(A*Y)^(2/3 : ℝ))/Y)) *
          ∑ d ∈ D, ProbeGramCommon.gramIdealNorm d ^ (-2 : ℝ)) := by simp only [Finset.mul_sum]
    _ ≤ L*A^η * ((K*B*(A*Y)^ε*((A+Y+(A*Y)^(2/3 : ℝ))/Y)) * S) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hsum D) (by positivity)) (by positivity)
    _ = _ := by ring

/-- Pointwise column costs alone suffice for the assembled bound. In the
native amplitude the multiplier Nd times lowGaussColumn has exactly this cost. -/
theorem assembled_pointwise_energy (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ A Y B : ℝ, 1 ≤ A → 1 ≤ Y →
      ∀ (D : Finset SupportedIdeal)
        (b : (d : SupportedIdeal) → idealRange (Y / ProbeGramCommon.gramIdealNorm d ^ 3) → ℂ)
        (r : SupportedIdeal → Id → ℂ),
        (∀ d ∈ D, 1 ≤ A / ProbeGramCommon.gramIdealNorm d ∧
          1 ≤ Y / ProbeGramCommon.gramIdealNorm d ^ 3) →
        (∀ d ∈ D, ∀ I, ‖r d I‖ ≤ 1) →
        (∀ d ∈ D, ∀ j, ‖b d j‖ ≤ B*ProbeGramCommon.gramIdealNorm d/Y) →
        (∑ a ∈ idealRange A, ‖∑ d ∈ D,
          divisorBlock (Y / ProbeGramCommon.gramIdealNorm d ^ 3) d (b d) (r d) a‖^2) ≤
          C * A^η * (A*Y)^ε * ((A+Y+(A*Y)^(2/3 : ℝ))/Y) * B^2 := by
  obtain ⟨C, hC, hb⟩ := assembled_energy ε η hε hη
  refine ⟨128*C, by positivity, ?_⟩
  intro A Y B hA hY D b r hscale hr hcoef
  have hh := hb A Y (128*B^2) hA hY (by positivity) D b r hscale hr
    (fun d hd => column_mass_bound Y _ B (by linarith)
      (ProbeGramCommon.gramIdealNorm_pos d) (hscale d hd).2 (b d) (hcoef d hd))
  convert hh using 1; ring

/-- Literal scaled native low-column coefficient. Unsupported products are
zero, so the native exclusions are not replaced by a free coefficient vector. -/
def nativeColumn (C : ProbePhysical.CalibrationData) (W : ℝ → ℂ) (Y : ℝ)
    (σ : RayFourExpansion.RayRing) (v : ℝ) (d : SupportedIdeal) (N : ℝ)
    (phase : idealRange N → ℂ) (j : idealRange N) : ℂ :=
  if hs : CanonicalQuadraticSieve.Supported (j.val*d.val^3) then
    (ProbeGramCommon.gramIdealNorm d : ℂ) * phase j *
      ProbePhysical.lowGaussColumn C W Y σ v ⟨j.val*d.val^3, hs⟩
  else 0

/-- The actual imported lowGaussColumn norm pays the coefficient hypothesis
of the finite assembly, including its calibration and ray factors. -/
theorem nativeColumn_norm (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (W : ℝ → ℂ) (a z B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hW : Function.support W ⊆ Set.Icc a z) (hWB : ∀ x, ‖W x‖ ≤ B)
    (Y : ℝ) (hY : 0 < Y) (σ : RayFourExpansion.RayRing) (v : ℝ)
    (d : SupportedIdeal) (N : ℝ) (phase : idealRange N → ℂ)
    (hphase : ∀ j, ‖phase j‖ ≤ 1) (j : idealRange N) :
    ‖nativeColumn (ProbePhysical.calibrationForSet S hS) W Y σ v d N phase j‖ ≤
      (B*a^(-(1/2 : ℝ)))*ProbeGramCommon.gramIdealNorm d/Y := by
  have hd0 := ProbeGramCommon.gramIdealNorm_pos d
  unfold nativeColumn
  split_ifs with hs
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ProbeGramCommon.gramIdealNorm_pos d)]
    have hcol := ProbePhysical.lowGaussColumn_norm_bound S hS W a z B ha hB
      hW hWB Y hY σ v ⟨j.val*d.val^3, hs⟩
    calc
      _ ≤ ProbeGramCommon.gramIdealNorm d * 1 * (B*a^(-(1/2 : ℝ))/Y) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hphase j) hd0.le) hcol
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

/-- Original finite low-ray square energy, conditional ONLY on the displayed
exact Gauss divisor bridge and elementary support/phase hypotheses. Z is the
physical norm cutoff, independently of the normalization scale Y. All column
norms and all cubic block energies are paid here from imported native theorems. -/
theorem actual_energy_of_gauss_bridge (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
      (W : ℝ → ℂ) (a z B : ℝ), 0 < a → 0 ≤ B →
      Function.support W ⊆ Set.Icc a z → (∀ x, ‖W x‖ ≤ B) →
      ∀ A Y Z : ℝ, 1 ≤ A → 1 ≤ Y → 1 ≤ Z →
      ∀ (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ : O)
        (D : Finset SupportedIdeal)
        (phase : (d : SupportedIdeal) → idealRange (Z / ProbeGramCommon.gramIdealNorm d ^ 3) → ℂ)
        (r : SupportedIdeal → Id → ℂ),
      (∀ d ∈ D, 1 ≤ A / ProbeGramCommon.gramIdealNorm d ∧
        1 ≤ Z / ProbeGramCommon.gramIdealNorm d ^ 3) →
      (∀ d ∈ D, ∀ I, ‖r d I‖ ≤ 1) →
      (∀ d ∈ D, ∀ j, ‖phase d j‖ ≤ 1) →
      (∀ I ∈ idealRange A,
        ProbePhysical.lowRayAmplitude (ProbePhysical.calibrationForSet S hS) W Y σ
          (ζ * primaryGenerator I ^ 2) v =
        ∑ d ∈ D, divisorBlock (Z / ProbeGramCommon.gramIdealNorm d ^ 3) d
          (nativeColumn (ProbePhysical.calibrationForSet S hS) W Y σ v d _ (phase d)) (r d) I) →
      (∑ I ∈ idealRange A,
        ‖ProbePhysical.lowRayAmplitude (ProbePhysical.calibrationForSet S hS) W Y σ
          (ζ * primaryGenerator I ^ 2) v‖^2) ≤
        C * A^η * (A*Z)^ε * ((A+Z+(A*Z)^(2/3 : ℝ))/Z) *
          (B*a^(-(1/2 : ℝ))*Z/Y)^2 := by
  obtain ⟨C, hC, hb⟩ := assembled_pointwise_energy ε η hε hη
  refine ⟨C, hC, ?_⟩
  intro S hS W a z B ha hB hW hWB A Y Z hA hY hZ σ v ζ D phase r hscale hr hphase hbridge
  have he := hb A Z (B*a^(-(1/2 : ℝ))*Z/Y) hA hZ D
    (fun d => nativeColumn (ProbePhysical.calibrationForSet S hS) W Y σ v d _ (phase d))
    r hscale hr
    (fun d hd j => by
      have ht := nativeColumn_norm S hS W a z B ha hB hW hWB Y
        (by linarith) σ v d _ (phase d) (hphase d hd) j
      apply ht.trans_eq
      field_simp)
  have hh : (∑ I ∈ idealRange A,
      ‖ProbePhysical.lowRayAmplitude (ProbePhysical.calibrationForSet S hS) W Y σ
        (ζ * primaryGenerator I ^ 2) v‖^2) =
      ∑ I ∈ idealRange A, ‖∑ d ∈ D, divisorBlock (Z / ProbeGramCommon.gramIdealNorm d ^ 3) d
        (nativeColumn (ProbePhysical.calibrationForSet S hS) W Y σ v d _ (phase d)) (r d) I‖^2 := by
    apply Finset.sum_congr rfl
    intro I hI
    rw [hbridge I hI]
  rw [hh]
  exact he

/-- Actual full-element cubic sieve input for arbitrary roots, including
nonunit zeros. This is an arithmetic input, not the missing imprimitive Gauss bridge. -/
theorem full_element_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      ∀ (b : idealRange N → ℂ) (r : elementRange M → ℂ),
        (∀ x, ‖r x‖ ≤ 1) →
        (∑ x : elementRange M,
          ‖r x * ∑ j : idealRange N, star (cubicRow j.val x.val) * b j‖^2) ≤
          C*(M*N)^ε*(M^(1/3 : ℝ)*N+M^(4/3 : ℝ))*∑ j, ‖b j‖^2 := by
  obtain ⟨C, hC, hb⟩ := HasCubicExponent.full_element_bound
    hasCubicExponent_four_thirds (by norm_num) ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN b r hr
  have he := energy_le_squaredNorm (elementMatrix M N) (fun j => star (b j))
  have hh (x : elementRange M) : ‖∑ j : idealRange N, star (cubicRow j.val x.val) * b j‖ =
      ‖∑ j : idealRange N, cubicRow j.val x.val * star (b j)‖ := by
    conv_lhs => rw [← norm_star]
    simp only [star_sum, star_mul, star_star, mul_comm]
  calc
    _ ≤ ∑ x : elementRange M, ‖∑ j : idealRange N, star (cubicRow j.val x.val) * b j‖^2 := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_of_le_one_left (norm_nonneg _) (hr x)) 2
    _ = ∑ x : elementRange M, ‖∑ j : idealRange N, cubicRow j.val x.val * star (b j)‖^2 := by
      simp only [hh]
    _ ≤ elementSieveNorm M N * ∑ j, ‖b j‖^2 := by
      simpa only [elementSieveNorm, elementMatrix, norm_star] using he
    _ ≤ _ := mul_le_mul_of_nonneg_right (hb M N hM hN) (by positivity)

/-- Exact native exponents for the full-element arithmetic input. No source or
complete physical amplitude bridge is encoded by this rate ledger. -/
theorem full_element_native_rates (d : ℝ) :
    (5/6-2*d)/12 = (5/72-d/6 : ℝ) ∧
      (5/6-2*d)/3-(23/48-d)/2 = (11/288-d/6 : ℝ) ∧
      (5/72-d/6)-(11/288-d/6) = (1/32 : ℝ) := by
  constructor
  · ring
  constructor <;> ring

end OpenAIReview.FiniteSquareEnergy
#lint+ in OpenAIReview.FiniteSquareEnergy

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    details := details.push (Json.mkObj [("declaration", toJson n.toString),
      ("isTheorem", toJson ci.isTheorem), ("axioms", toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty native cubic mean audit."
  logInfo m!"Finite square energy audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-finite-square-energy"
  IO.FS.writeFile ".lake/arithmetic-operator-finite-square-energy/axioms.json"
    (Json.mkObj [("scope", toJson "actual cubic divisor assembly and literal lowGaussColumn cost; original square amplitude conditional on explicit Gauss bridge; full-element arithmetic input, no rho or source claim"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
