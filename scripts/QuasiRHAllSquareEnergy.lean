/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHFiniteSquareEnergyAudit

/-!
Finite all-root element divisor assembly for the actual cubic matrix.
The original amplitude specialization keeps its literal Gauss bridge explicit.
The row factor is exactly cubic(e,u) times coprimality with d; no coprimality
with the full divisor T or its principal sixth-power part is imposed.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.AllSquareEnergy
open OAI OAI.SevenEighths OAI.CompletedGauss
open OAI.SevenEighths.CubicSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "SupportedIdeal" => {I : Id // CanonicalQuadraticSieve.Supported I}

/-- Literal element quotient by the fixed primary generator of T. -/
def elementQuotient (T : SupportedIdeal) (x : O) : O :=
  if h : primaryGenerator T.val ∣ x then h.choose else 0

/-- Ideal divisibility is exactly divisibility by the native primary generator. -/
theorem divisor_iff (T : SupportedIdeal) (x : O) :
    T.val ∣ Ideal.span {x} ↔ primaryGenerator T.val ∣ x := by
  have he := (primaryGenerator_spec T.val
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero T.val T.property)).1
  calc
    _ ↔ Ideal.span {primaryGenerator T.val} ∣ Ideal.span {x} := by rw [he]
    _ ↔ _ := Ideal.span_singleton_dvd_span_singleton_iff_dvd

/-- The quotient reconstructs the original element at every actual divisor. -/
theorem elementQuotient_mul (T : SupportedIdeal) (x : O) (h : T.val ∣ Ideal.span {x}) :
    primaryGenerator T.val * elementQuotient T x = x := by
  have hd := (divisor_iff T x).mp h
  simp only [elementQuotient, dite_eq_left hd]
  exact hd.choose_spec.symm

/-- Actual element quotient rows inject, without a unit-associate multiplicity. -/
theorem elementQuotient_injective (T : SupportedIdeal) :
    Set.InjOn (elementQuotient T) {x | T.val ∣ Ideal.span {x}} := by
  intro x hx y hy he
  calc
    x = primaryGenerator T.val * elementQuotient T x := (elementQuotient_mul T x hx).symm
    _ = primaryGenerator T.val * elementQuotient T y := by rw [he]
    _ = y := elementQuotient_mul T y hy

/-- All root elements, including nonsquarefree and nonunit roots, map to the
exact smaller native element range A/NT. -/
theorem elementQuotient_mem (A : ℝ) (T : SupportedIdeal) (x : O)
    (hx : x ∈ elementRange A) (h : T.val ∣ Ideal.span {x}) :
    elementQuotient T x ∈ elementRange (A / ProbeGramCommon.gramIdealNorm T) := by
  have hx' := (mem_elementRange A x).mp hx
  have ht := ProbeGramCommon.gramIdealNorm_pos T
  apply (mem_elementRange _ _).mpr
  constructor
  · intro hz
    have he := elementQuotient_mul T x h
    rw [hz, mul_zero] at he
    exact hx'.1 he.symm
  · have he : Ideal.span {x} = T.val * Ideal.span {elementQuotient T x} := by
      rw [← (primaryGenerator_spec T.val
        (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero T.val T.property)).1,
        Ideal.span_singleton_mul_span_singleton, elementQuotient_mul T x h]
    have hn : (Ideal.absNorm (Ideal.span {x}) : ℝ) =
        ProbeGramCommon.gramIdealNorm T * (Ideal.absNorm (Ideal.span {elementQuotient T x}) : ℝ) := by
      rw [he, map_mul, Nat.cast_mul]
      rfl
    apply (le_div_iff₀ ht).mpr
    rw [mul_comm, ← hn]
    exact hx'.2

/-- Exact surviving row factor. Principal-only primes of T receive NO extra
coprimality mask. Both cubic and coprimality zeros remain literal. -/
def squareRow (d e : Id) (u : O) : ℂ :=
  cubicRow e u * if IsCoprime d (Ideal.span {u}) then 1 else 0

/-- The literal cubic row character is a contraction on arbitrary root elements. -/
theorem cubicRow_norm (e : Id) (u : O) : ‖cubicRow e u‖ ≤ 1 := by
  unfold OAI.SevenEighths.CubicSieve.cubicRow
  rw [← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm u e) 2).trans_eq (by norm_num)

/-- The exact e/d row factor decreases energy even at nonunit roots. -/
theorem squareRow_norm (d e : Id) (u : O) : ‖squareRow d e u‖ ≤ 1 := by
  unfold squareRow
  split_ifs
  · simpa only [mul_one] using cubicRow_norm e u
  · simp

/-- Fixed-T cubic block with the exact e/d row and b/(de) column masks. -/
def squareBlock (N : ℝ) (T : SupportedIdeal) (d e : Id)
    (b : idealRange N → ℂ) (x : O) : ℂ :=
  if T.val ∣ Ideal.span {x} then
    squareRow d e (elementQuotient T x) *
      ∑ j : idealRange N, star (cubicRow j.val (elementQuotient T x)) *
        (if IsCoprime j.val (d*e) then b j else 0)
  else 0

/-- A fixed-T block vanishes off actual ideal divisibility. -/
theorem squareBlock_zero (N : ℝ) (T : SupportedIdeal) (d e : Id)
    (b : idealRange N → ℂ) (x : O) (h : ¬T.val ∣ Ideal.span {x}) :
    squareBlock N T d e b x = 0 := by simp [squareBlock, h]

/-- Actual full-element arithmetic bounds every fixed-T block; no block energy
is assumed and the coefficient vector stays common across all quotient roots. -/
theorem squareBlock_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ A N : ℝ, ∀ (T : SupportedIdeal),
      1 ≤ A / ProbeGramCommon.gramIdealNorm T → 1 ≤ N →
      ∀ (d e : Id) (b : idealRange N → ℂ),
      (∑ x ∈ elementRange A, ‖squareBlock N T d e b x‖^2) ≤
        C*((A/ProbeGramCommon.gramIdealNorm T)*N)^ε *
          ((A/ProbeGramCommon.gramIdealNorm T)^(1/3 : ℝ)*N+
            (A/ProbeGramCommon.gramIdealNorm T)^(4/3 : ℝ)) * ∑ j, ‖b j‖^2 := by
  obtain ⟨C, hC, hb⟩ := FiniteSquareEnergy.full_element_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro A N T hA hN d e b
  let F := (elementRange A).filter (fun x => T.val ∣ Ideal.span {x})
  let coef : idealRange N → ℂ := fun j => if IsCoprime j.val (d*e) then b j else 0
  let E : O → ℝ := fun u => ‖squareRow d e u *
    ∑ j : idealRange N, star (cubicRow j.val u) * coef j‖^2
  have hmap : F.image (elementQuotient T) ⊆ elementRange (A/ProbeGramCommon.gramIdealNorm T) := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    have hh := Finset.mem_filter.mp hx
    exact elementQuotient_mem A T x hh.1 hh.2
  have hi : Set.InjOn (elementQuotient T) (↑F : Set O) := by
    intro x hx y hy he
    exact elementQuotient_injective T (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2 he
  have ht := Finset.sum_le_sum_of_injOn (elementQuotient T) hi hmap
    (f := fun x => E (elementQuotient T x)) (g := E)
    (by intro x _; rfl) (by intro u _ _; exact sq_nonneg _)
  have hm : (∑ j, ‖coef j‖^2) ≤ ∑ j, ‖b j‖^2 := by
    apply Finset.sum_le_sum
    intro j _
    dsimp [coef]
    split_ifs <;> simp
  have he := hb (A/ProbeGramCommon.gramIdealNorm T) N hA hN coef
    (fun u => squareRow d e u.val) (fun u => squareRow_norm d e u.val)
  calc
    _ = ∑ x ∈ F, E (elementQuotient T x) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      dsimp [squareBlock, E, coef]
      split_ifs <;> simp
    _ ≤ ∑ u ∈ elementRange (A/ProbeGramCommon.gramIdealNorm T), E u := ht
    _ = ∑ u : elementRange (A/ProbeGramCommon.gramIdealNorm T), E u.val :=
      (Finset.sum_coe_sort _ E).symm
    _ ≤ C*((A/ProbeGramCommon.gramIdealNorm T)*N)^ε *
        ((A/ProbeGramCommon.gramIdealNorm T)^(1/3 : ℝ)*N+
          (A/ProbeGramCommon.gramIdealNorm T)^(4/3 : ℝ)) * ∑ j, ‖coef j‖^2 := he
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

/-- Divisor Cauchy for ALL nonzero element roots. The incoming count is the
actual ideal divisor count of span{x}, without an assumed fiber estimate. -/
theorem element_divisor_cauchy (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 1 ≤ A → ∀ (D : Finset SupportedIdeal)
      (H : SupportedIdeal → O → ℂ),
      (∀ T ∈ D, ∀ x ∈ elementRange A, ¬T.val ∣ Ideal.span {x} → H T x = 0) →
      (∑ x ∈ elementRange A, ‖∑ T ∈ D, H T x‖^2) ≤
        C*A^η * ∑ T ∈ D, ∑ x ∈ elementRange A, ‖H T x‖^2 := by
  obtain ⟨C, hC, hb⟩ := IdealDivisorBound.ideal_divisor_small_power η hη
  refine ⟨C, hC, ?_⟩
  intro A hA D H hzero
  have hp (x : O) (hx : x ∈ elementRange A) :
      ‖∑ T ∈ D, H T x‖^2 ≤ C*A^η * ∑ T ∈ D, ‖H T x‖^2 := by
    have hx' := (mem_elementRange A x).mp hx
    have hx0 : Ideal.span {x} ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hx'.1
    let F := D.filter (fun T => T.val ∣ Ideal.span {x})
    have hcard : (F.card : ℝ) ≤ C*A^η :=
      (FiniteSquareEnergy.divisor_fiber_card D _ hx0).trans ((hb _ hx0).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hx'.2 hη.le) hC.le))
    have he : (∑ T ∈ D, H T x) = ∑ T ∈ F, H T x := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro T hT hn
      exact hzero T hT x hx (by simpa only [F, Finset.mem_filter, hT, true_and] using hn)
    rw [he]
    calc
      _ ≤ (∑ T ∈ F, ‖H T x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (F.card : ℝ)*∑ T ∈ F, ‖H T x‖^2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (C*A^η)*∑ T ∈ F, ‖H T x‖^2 := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ x ∈ elementRange A, C*A^η * ∑ T ∈ D, ‖H T x‖^2 := Finset.sum_le_sum hp
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

/-- The actual finite ideal count pays a fixed-T column vector at the enlarged
native range Z/t², keeping its pointwise t/Y normalization exactly. -/
theorem column_mass (Z Y t B : ℝ) (hY : 0 < Y) (ht : 0 < t)
    (hN : 1 ≤ Z/t^2) (b : idealRange (Z/t^2) → ℂ)
    (hb : ∀ j, ‖b j‖ ≤ B*t/Y) :
    (∑ j, ‖b j‖^2) ≤ 128*B^2*Z/Y^2 := by
  have hc := DescentFiberCost.finite_ideal_count_real (idealRange (Z/t^2))
    (Z/t^2) hN
    (fun I hI => primaryGenerator_ne_zero_ideal I (mem_idealRange.mp hI).1.2)
    (fun I hI => (mem_idealRange.mp hI).2)
  calc
    _ ≤ ∑ _j : idealRange (Z/t^2), (B*t/Y)^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
    _ = ((idealRange (Z/t^2)).card : ℝ)*(B*t/Y)^2 := by simp
    _ ≤ (128*(Z/t^2))*(B*t/Y)^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by field_simp

/-- Exact all-root block cost after the genuine full-element cubic operator.
The physical cutoff Z and original normalization Y remain independent. -/
theorem block_shape (A Z Y t ε : ℝ) (hA : 0 < A) (hZ : 0 < Z)
    (hY : 0 < Y) (ht : 1 ≤ t) (hε : 0 ≤ ε) :
    ((A/t)*(Z/t^2))^ε * ((A/t)^(1/3 : ℝ)*(Z/t^2)+(A/t)^(4/3 : ℝ)) * (Z/Y^2) ≤
      (A*Z)^ε*(Z/Y)^2 *
        (A^(1/3 : ℝ)*t^(-(7/3 : ℝ))+(A^(4/3 : ℝ)/Z)*t^(-(4/3 : ℝ))) := by
  have ht0 : 0 < t := by linarith
  have he : (A/t)*(Z/t^2)=A*Z/t^3 := by field_simp
  have hp : ((A/t)*(Z/t^2))^ε ≤ (A*Z)^ε := by
    apply Real.rpow_le_rpow (by positivity) _ hε
    rw [he]
    exact div_le_self (by positivity) (one_le_pow₀ ht)
  have h7 : t^(7/3 : ℝ)=t^(1/3 : ℝ)*t^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
    norm_num
  calc
    _ ≤ (A*Z)^ε * ((A/t)^(1/3 : ℝ)*(Z/t^2)+(A/t)^(4/3 : ℝ)) * (Z/Y^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
    _ = _ := by
      rw [Real.div_rpow hA.le ht0.le, Real.div_rpow hA.le ht0.le,
        Real.rpow_neg ht0.le, Real.rpow_neg ht0.le, h7]
      field_simp

/-- All fixed-T blocks assemble using the actual element-divisor count and
T^(-7/3),T^(-4/3) convergent native ideal sums. No block energy is assumed. -/
theorem assembled_energy (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ A Z Y B : ℝ, 1 ≤ A → 1 ≤ Z → 0 < Y → 0 ≤ B →
      ∀ (D : Finset SupportedIdeal) (d e : SupportedIdeal → Id)
        (b : (T : SupportedIdeal) → idealRange (Z / ProbeGramCommon.gramIdealNorm T ^ 2) → ℂ),
        (∀ T ∈ D, 1 ≤ A/ProbeGramCommon.gramIdealNorm T ∧
          1 ≤ Z/ProbeGramCommon.gramIdealNorm T^2) →
        (∀ T ∈ D, (∑ j, ‖b T j‖^2) ≤ B*Z/Y^2) →
        (∑ x ∈ elementRange A, ‖∑ T ∈ D,
          squareBlock (Z / ProbeGramCommon.gramIdealNorm T ^ 2) T (d T) (e T) (b T) x‖^2) ≤
          C*B*A^η*(A*Z)^ε*(Z/Y)^2*(A^(1/3 : ℝ)+A^(4/3 : ℝ)/Z) := by
  obtain ⟨K, hK, hb⟩ := squareBlock_energy ε hε
  obtain ⟨L, hL, hcauchy⟩ := element_divisor_cauchy η hη
  obtain ⟨S7, hS7, hsum7⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(7/3 : ℝ)) (by norm_num)
  obtain ⟨S4, hS4, hsum4⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(4/3 : ℝ)) (by norm_num)
  refine ⟨L*K*(S7+S4), by positivity, ?_⟩
  intro A Z Y B hA hZ hY hB D d e b hscale hmass
  have hA0 : 0 < A := by linarith
  have hZ0 : 0 < Z := by linarith
  have hblock (T : SupportedIdeal) (hT : T ∈ D) :
      (∑ x ∈ elementRange A,
        ‖squareBlock (Z / ProbeGramCommon.gramIdealNorm T ^ 2) T (d T) (e T) (b T) x‖^2) ≤
        (K*B*(A*Z)^ε*(Z/Y)^2) *
          (A^(1/3 : ℝ)*ProbeGramCommon.gramIdealNorm T^(-(7/3 : ℝ))+
            (A^(4/3 : ℝ)/Z)*ProbeGramCommon.gramIdealNorm T^(-(4/3 : ℝ))) := by
    let t := ProbeGramCommon.gramIdealNorm T
    have ht : 0 < t := ProbeGramCommon.gramIdealNorm_pos T
    have he := hb A (Z/t^2) T (hscale T hT).1 (hscale T hT).2 (d T) (e T) (b T)
    calc
      _ ≤ (K*((A/t)*(Z/t^2))^ε*((A/t)^(1/3 : ℝ)*(Z/t^2)+(A/t)^(4/3 : ℝ))) * ∑ j, ‖b T j‖^2 := he
      _ ≤ (K*((A/t)*(Z/t^2))^ε*((A/t)^(1/3 : ℝ)*(Z/t^2)+(A/t)^(4/3 : ℝ))) * (B*Z/Y^2) :=
        mul_le_mul_of_nonneg_left (hmass T hT) (by positivity)
      _ = (K*B) * (((A/t)*(Z/t^2))^ε*((A/t)^(1/3 : ℝ)*(Z/t^2)+(A/t)^(4/3 : ℝ))*(Z/Y^2)) := by ring
      _ ≤ (K*B) * ((A*Z)^ε*(Z/Y)^2 *
          (A^(1/3 : ℝ)*t^(-(7/3 : ℝ))+(A^(4/3 : ℝ)/Z)*t^(-(4/3 : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (block_shape A Z Y t ε hA0 hZ0 hY (ProbeGramCommon.gramIdealNorm_one_le T) hε.le) (by positivity)
      _ = _ := by ring
  have hsum : (∑ T ∈ D,
      (A^(1/3 : ℝ)*ProbeGramCommon.gramIdealNorm T^(-(7/3 : ℝ))+
        (A^(4/3 : ℝ)/Z)*ProbeGramCommon.gramIdealNorm T^(-(4/3 : ℝ)))) ≤
      (S7+S4)*(A^(1/3 : ℝ)+A^(4/3 : ℝ)/Z) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hs7 := mul_le_mul_of_nonneg_left (hsum7 D) (show 0 ≤ A^(1/3 : ℝ) by positivity)
    have hs4 := mul_le_mul_of_nonneg_left (hsum4 D) (show 0 ≤ A^(4/3 : ℝ)/Z by positivity)
    nlinarith [mul_nonneg hS4.le (show 0 ≤ A^(1/3 : ℝ) by positivity),
      mul_nonneg hS7.le (show 0 ≤ A^(4/3 : ℝ)/Z by positivity)]
  have hc := hcauchy A hA D
    (fun T => squareBlock (Z / ProbeGramCommon.gramIdealNorm T ^ 2) T (d T) (e T) (b T))
    (fun T _ x _ h => squareBlock_zero _ T _ _ _ x h)
  calc
    _ ≤ L*A^η * ∑ T ∈ D, ∑ x ∈ elementRange A,
        ‖squareBlock (Z / ProbeGramCommon.gramIdealNorm T ^ 2) T (d T) (e T) (b T) x‖^2 := hc
    _ ≤ L*A^η * ∑ T ∈ D, (K*B*(A*Z)^ε*(Z/Y)^2) *
        (A^(1/3 : ℝ)*ProbeGramCommon.gramIdealNorm T^(-(7/3 : ℝ))+
          (A^(4/3 : ℝ)/Z)*ProbeGramCommon.gramIdealNorm T^(-(4/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hblock) (by positivity)
    _ = L*A^η * ((K*B*(A*Z)^ε*(Z/Y)^2) * ∑ T ∈ D,
        (A^(1/3 : ℝ)*ProbeGramCommon.gramIdealNorm T^(-(7/3 : ℝ))+
          (A^(4/3 : ℝ)/Z)*ProbeGramCommon.gramIdealNorm T^(-(4/3 : ℝ)))) := by
      simp only [Finset.mul_sum]
    _ ≤ L*A^η * ((K*B*(A*Z)^ε*(Z/Y)^2) * ((S7+S4)*(A^(1/3 : ℝ)+A^(4/3 : ℝ)/Z))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)
    _ = _ := by ring

/-- Pointwise native column costs suffice; coefficient mass is proved using
the actual ideal count, not supplied as an energy premise. -/
theorem assembled_pointwise_energy (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ A Z Y B : ℝ, 1 ≤ A → 1 ≤ Z → 0 < Y →
      ∀ (D : Finset SupportedIdeal) (d e : SupportedIdeal → Id)
        (b : (T : SupportedIdeal) → idealRange (Z / ProbeGramCommon.gramIdealNorm T ^ 2) → ℂ),
        (∀ T ∈ D, 1 ≤ A/ProbeGramCommon.gramIdealNorm T ∧
          1 ≤ Z/ProbeGramCommon.gramIdealNorm T^2) →
        (∀ T ∈ D, ∀ j, ‖b T j‖ ≤ B*ProbeGramCommon.gramIdealNorm T/Y) →
        (∑ x ∈ elementRange A, ‖∑ T ∈ D,
          squareBlock (Z / ProbeGramCommon.gramIdealNorm T ^ 2) T (d T) (e T) (b T) x‖^2) ≤
          C*B^2*A^η*(A*Z)^ε*(Z/Y)^2*(A^(1/3 : ℝ)+A^(4/3 : ℝ)/Z) := by
  obtain ⟨C, hC, hb⟩ := assembled_energy ε η hε hη
  refine ⟨128*C, by positivity, ?_⟩
  intro A Z Y B hA hZ hY D d e b hscale hcoef
  have he := hb A Z Y (128*B^2) hA hZ hY (by positivity) D d e b hscale
    (fun T hT => column_mass Z Y _ B hY (ProbeGramCommon.gramIdealNorm_pos T)
      (hscale T hT).2 (b T) (hcoef T hT))
  convert he using 1; ring

/-- The actual canonical footprint T²*d*e is at least T² in norm. This
uses actual nonzero ideals, not a free height assumption. -/
theorem footprint_norm (T : SupportedIdeal) (d e : Id) (hd : d ≠ 0) (he : e ≠ 0) :
    ProbeGramCommon.gramIdealNorm T ^ 2 ≤ (Ideal.absNorm (T.val^2*d*e) : ℝ) := by
  have hd1 : (1 : ℝ) ≤ Ideal.absNorm d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hd)
  have he1 : (1 : ℝ) ≤ Ideal.absNorm e := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr he)
  have hm : (1 : ℝ) ≤ (Ideal.absNorm d : ℝ)*(Ideal.absNorm e : ℝ) :=
    one_le_mul_of_one_le_of_one_le hd1 he1
  rw [map_mul, map_mul, map_pow, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  change ProbeGramCommon.gramIdealNorm T^2 ≤
    ProbeGramCommon.gramIdealNorm T^2*(Ideal.absNorm d : ℝ)*(Ideal.absNorm e : ℝ)
  nlinarith [mul_nonneg (sq_nonneg (ProbeGramCommon.gramIdealNorm T)) (sub_nonneg.mpr hm)]

/-- Every actual squarefree physical column in a footprint V≥T² lies in the
enlarged native cubic range Z/(NT)². Coefficients and all masks are unchanged. -/
theorem enlarged_column_range (Z : ℝ) (T : SupportedIdeal) (V j : Id)
    (hj : Admissible j)
    (hV : ProbeGramCommon.gramIdealNorm T^2 ≤ (Ideal.absNorm V : ℝ))
    (hphys : (Ideal.absNorm (j*V) : ℝ) ≤ Z) :
    j ∈ idealRange (Z / ProbeGramCommon.gramIdealNorm T^2) := by
  have ht := ProbeGramCommon.gramIdealNorm_pos T
  apply mem_idealRange.mpr
  refine ⟨hj, (le_div_iff₀ (sq_pos_of_pos ht)).mpr ?_⟩
  have hp : (Ideal.absNorm (j*V) : ℝ) = (Ideal.absNorm j : ℝ)*(Ideal.absNorm V : ℝ) := by
    rw [map_mul, Nat.cast_mul]
  have hh := mul_le_mul_of_nonneg_left hV (show 0 ≤ (Ideal.absNorm j : ℝ) by positivity)
  linarith

/-- Literal common column: the original low column times its actual normalized
Gauss value at the fixed square baseline. No freely assigned phase is used. -/
def actualColumn (C : ProbePhysical.CalibrationData) (W : ℝ → ℂ) (Y : ℝ)
    (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ : O) (T : SupportedIdeal)
    (V : Id) (N : ℝ) (j : idealRange N) : ℂ :=
  if hs : CanonicalQuadraticSieve.Supported (j.val*V) then
    ProbePhysical.lowGaussColumn C W Y σ v ⟨j.val*V, hs⟩ *
      CenteredMomentGaussEnergy.gaussRow (primaryGenerator (j.val*V))
        ((CanonicalQuadraticSieve.supported_span_primaryGenerator_iff (j.val*V)).mpr hs)
        (-ζ * primaryGenerator T.val ^ 2)
  else 0

/-- The imported original column norm and an EXPLICIT ACTUAL baseline Gauss
bound pay the common vector. The Gauss norm hypothesis is not a phase model. -/
theorem actualColumn_norm (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (W : ℝ → ℂ) (a z B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hW : Function.support W ⊆ Set.Icc a z) (hWB : ∀ x, ‖W x‖ ≤ B)
    (Y : ℝ) (hY : 0 < Y) (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ : O)
    (T : SupportedIdeal) (V : Id) (N : ℝ) (j : idealRange N)
    (hbase : ∀ hs : CanonicalQuadraticSieve.Supported (j.val*V),
      ‖CenteredMomentGaussEnergy.gaussRow (primaryGenerator (j.val*V))
        ((CanonicalQuadraticSieve.supported_span_primaryGenerator_iff (j.val*V)).mpr hs)
        (-ζ * primaryGenerator T.val ^ 2)‖ ≤ ProbeGramCommon.gramIdealNorm T) :
    ‖actualColumn (ProbePhysical.calibrationForSet S hS) W Y σ v ζ T V N j‖ ≤
      (B*a^(-(1/2 : ℝ)))*ProbeGramCommon.gramIdealNorm T/Y := by
  have ht := ProbeGramCommon.gramIdealNorm_pos T
  unfold actualColumn
  split_ifs with hs
  · rw [norm_mul]
    have hcol := ProbePhysical.lowGaussColumn_norm_bound S hS W a z B ha hB
      hW hWB Y hY σ v ⟨j.val*V, hs⟩
    calc
      _ ≤ (B*a^(-(1/2 : ℝ))/Y)*ProbeGramCommon.gramIdealNorm T :=
        mul_le_mul hcol (hbase hs) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

/-- Original all-square finite amplitude payment, with both remaining ACTUAL
Gauss obligations displayed: baseline norm and exact canonical finite bridge.
No supplied energy, arbitrary Gauss phase, residue or source premise is used. -/
theorem actual_energy_of_gauss_bridge (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
      (W : ℝ → ℂ) (a z B : ℝ), 0 < a → 0 ≤ B →
      Function.support W ⊆ Set.Icc a z → (∀ x, ‖W x‖ ≤ B) →
      ∀ A Z Y : ℝ, 1 ≤ A → 1 ≤ Z → 0 < Y →
      ∀ (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ : O)
        (D : Finset SupportedIdeal) (d e V : SupportedIdeal → Id),
      (∀ T ∈ D, 1 ≤ A/ProbeGramCommon.gramIdealNorm T ∧
        1 ≤ Z/ProbeGramCommon.gramIdealNorm T^2) →
      (∀ T ∈ D, ∀ j : idealRange (Z / ProbeGramCommon.gramIdealNorm T ^ 2),
        ∀ hs : CanonicalQuadraticSieve.Supported (j.val*V T),
        ‖CenteredMomentGaussEnergy.gaussRow (primaryGenerator (j.val*V T))
          ((CanonicalQuadraticSieve.supported_span_primaryGenerator_iff (j.val*V T)).mpr hs)
          (-ζ * primaryGenerator T.val ^ 2)‖ ≤ ProbeGramCommon.gramIdealNorm T) →
      (∀ x ∈ elementRange A,
        ProbePhysical.lowRayAmplitude (ProbePhysical.calibrationForSet S hS) W Y σ (ζ*x^2) v =
          ∑ T ∈ D, squareBlock (Z / ProbeGramCommon.gramIdealNorm T ^ 2) T (d T) (e T)
            (actualColumn (ProbePhysical.calibrationForSet S hS) W Y σ v ζ T (V T) _) x) →
      (∑ x ∈ elementRange A,
        ‖ProbePhysical.lowRayAmplitude (ProbePhysical.calibrationForSet S hS) W Y σ (ζ*x^2) v‖^2) ≤
        C*(B*a^(-(1/2 : ℝ)))^2*A^η*(A*Z)^ε*(Z/Y)^2*(A^(1/3 : ℝ)+A^(4/3 : ℝ)/Z) := by
  obtain ⟨C, hC, hb⟩ := assembled_pointwise_energy ε η hε hη
  refine ⟨C, hC, ?_⟩
  intro S hS W a z B ha hB hW hWB A Z Y hA hZ hY σ v ζ D d e V hscale hbase hbridge
  have he := hb A Z Y (B*a^(-(1/2 : ℝ))) hA hZ hY D d e
    (fun T => actualColumn (ProbePhysical.calibrationForSet S hS) W Y σ v ζ T (V T) _) hscale
    (fun T hT j => actualColumn_norm S hS W a z B ha hB hW hWB Y hY σ v ζ T (V T) _ j (hbase T hT j))
  have hh : (∑ x ∈ elementRange A,
      ‖ProbePhysical.lowRayAmplitude (ProbePhysical.calibrationForSet S hS) W Y σ (ζ*x^2) v‖^2) =
      ∑ x ∈ elementRange A, ‖∑ T ∈ D,
        squareBlock (Z / ProbeGramCommon.gramIdealNorm T ^ 2) T (d T) (e T)
          (actualColumn (ProbePhysical.calibrationForSet S hS) W Y σ v ζ T (V T) _) x‖^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hbridge x hx]
  rw [hh]
  exact he

end OpenAIReview.AllSquareEnergy
#lint+ in OpenAIReview.AllSquareEnergy

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
  logInfo m!"All-square energy audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-all-square-energy"
  IO.FS.writeFile ".lake/arithmetic-operator-all-square-energy/axioms.json"
    (Json.mkObj [("scope", toJson "all-root actual cubic divisor assembly; literal original amplitude conditional on exact Gauss bridge and actual baseline norm; no rho, free phase or source premise"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
