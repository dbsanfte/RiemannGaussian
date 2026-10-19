/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHAllSquarePartition
import scripts.QuasiRHAllSquareGaussBridge
import scripts.QuasiRHAllSquareEnergy
import scripts.QuasiRHSquareGaussIdealNorm

/-!
Actual ideal-level join of the literal canonical partition and independently
proved finite-prime Gauss formulas. No source or energy premise is introduced.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.AllSquareAmplitudeBridge
open OAI OAI.SevenEighths OAI.CompletedGauss
open OAI.SevenEighths.CubicSieve
open OAI.SevenEighths.ProbePhysical
open OAI.CanonicalQuadraticSieve
open OAI.SevenEighths.CenteredMomentUnequal
open OpenAIReview.AllSquarePartition
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- A nonzero ACTUAL global Gauss sum at a square satisfies the literal ideal
valuation constraints. No prime-support or phase law is assumed. -/
theorem nonzero_square_support (I : Id) (hI : Supported I) (x ζ : O)
    (hx : x ≠ 0) (hζ : IsUnit ζ)
    (hG : sexticGauss (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI) (ζ*x^2) ≠ 0) :
    SquareSupport I (Ideal.span {x}) := by
  let p : PrimeOf I → O := primeElement I
  let k : PrimeOf I → ℕ := fun P => val I P.val
  have hG' : sexticGauss (∏ P : PrimeOf I, p P ^ k P)
      (supportedElement_ne_zero _ (AllSquareGaussBridge.supported_finset_product Finset.univ _
        (fun P => supported_power (p P) (primeElement_supported hI P) (k P)))) (ζ*x^2) ≠ 0 := by
    simpa only [p, k, ← primaryGenerator_family hI.1] using hG
  have hs := AllSquareGaussBridge.nonzero_square_prime_product_support Finset.univ p
    (primeElement_prime hI) (primeElement_supported hI) (primeElement_coprime hI) k x ζ hx hζ hG'
  apply squareSupport_of_family
  intro P
  have hp := hs P (Finset.mem_univ P)
  dsimp only [p, k] at hp
  rw [← val_span_primeElement hI P hx] at hp
  by_cases hd : val I P.val % 6 = 0
  · rw [ite_eq_left hd]
    simpa only [ite_eq_left (Nat.dvd_of_mod_eq_zero hd)] using hp
  · rw [ite_eq_right hd]
    have hn : ¬6 ∣ val I P.val := fun h => hd (Nat.mod_eq_zero_of_dvd h)
    simpa only [ite_eq_right hn] using hp

/-- Actual nonzero square support supplies ALL canonical allowed classes and
actual root-divisor incidence. -/
theorem nonzero_square_canonical (I : Id) (hI : Supported I) (x ζ : O)
    (hx : x ≠ 0) (hζ : IsUnit ζ)
    (hG : sexticGauss (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI) (ζ*x^2) ≠ 0) :
    Allowed I ∧ rootPart I ∣ Ideal.span {x} := by
  have hs := nonzero_square_support I hI x ζ hx hζ hG
  exact ⟨allowed_of_squareSupport hs,
    rootPart_dvd_of_squareSupport (Ideal.span_singleton_eq_bot.not.mpr hx) hs⟩

/-- The literal element coprimality character equals the exact ideal row mask,
with the same primary generator and no associate phase. -/
theorem native_mask (I : Id) (hI : Supported I) (u : O) :
    CanonicalRowCompletion.coprimalityMask u (primaryGenerator I) =
      if IsCoprime I (Ideal.span {u}) then 1 else 0 := by
  have he := (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1
  conv_rhs => rw [← he, Ideal.isCoprime_span_singleton_iff]
  change (if IsCoprime u (primaryGenerator I) then (1:ℂ) else 0) =
    if IsCoprime (primaryGenerator I) u then 1 else 0
  rw [isCoprime_comm]

/-- Full literal IDEAL transport, with all principal nonunit branches retained.
Every unit/CRT phase remains in the ACTUAL baseline Gauss sum. -/
theorem ideal_transport (I : Id) (hI : Supported I) (ha : Allowed I) (w u : O) :
    sexticGauss (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)
      (primaryGenerator (rootPart I)^2*w*u^2) =
    sexticGauss (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)
      (primaryGenerator (rootPart I)^2*w) *
        star (CubicSieve.cubicRow (b6 I) u) *
          AllSquareEnergy.squareRow (d6 I) (e6 I) u := by
  let p : PrimeOf I → O := primeElement I
  let h : PrimeOf I → ℕ := fun P => val I P.val / 6
  let r : PrimeOf I → ℕ := fun P => val I P.val % 6
  have hr (P : PrimeOf I) : r P=0 ∨ r P=1 ∨ r P=3 ∨ r P=5 := ha P.val
  have hc : (∏ P : PrimeOf I, p P ^ (6*h P+r P)) = primaryGenerator I := by
    rw [primaryGenerator_family hI.1]
    apply Finset.prod_congr rfl
    intro P _
    dsimp [p, h, r]
    congr 1
    omega
  have ht : (∏ P : PrimeOf I, p P ^ (3*h P+r P/2)) = primaryGenerator (rootPart I) := by
    rw [primaryGenerator_rootPart_family]
    apply Finset.prod_congr rfl
    intro P _
    dsimp [p, h, r]
    congr 1
    have hh := ha P.val
    split_ifs <;> omega
  have hb : (∏ P : PrimeOf I, if r P=1 then p P else 1) = primaryGenerator (b6 I) := by
    rw [b6, primaryGenerator_block_family]
    apply Finset.prod_congr rfl
    intro P _
    dsimp [p, r]
    split_ifs <;> simp
  have hd : (∏ P : PrimeOf I, if r P=3 then p P else 1) = primaryGenerator (d6 I) := by
    rw [d6, primaryGenerator_block_family]
    apply Finset.prod_congr rfl
    intro P _
    dsimp [p, r]
    split_ifs <;> simp
  have he : (∏ P : PrimeOf I, if r P=5 then p P else 1) = primaryGenerator (e6 I) := by
    rw [e6, primaryGenerator_block_family]
    apply Finset.prod_congr rfl
    intro P _
    dsimp [p, r]
    split_ifs <;> simp
  have hg := AllSquareGaussBridge.all_square_cubic_transport Finset.univ p
    (primeElement_prime hI) (primeElement_supported hI) (primeElement_coprime hI) h r hr w u
  simp only [hc, ht, hb, hd, he] at hg
  rw [(primaryGenerator_spec (b6 I) (supported_primaryGenerator_ne_zero _ (b6_supported hI))).1,
    (primaryGenerator_spec (e6 I) (supported_primaryGenerator_ne_zero _ (e6_supported hI))).1,
    native_mask _ (d6_supported hI)] at hg
  unfold AllSquareEnergy.squareRow
  exact hg.trans (by ring)

/-- Normalization preserves the exact all-nonunit ideal transport; the same
native sqrt(NI) is retained on both sides. -/
theorem normalized_ideal_transport (I : Id) (hI : Supported I) (ha : Allowed I) (w u : O) :
    CenteredMomentGaussEnergy.gaussRow (primaryGenerator I)
      ((supported_span_primaryGenerator_iff I).mpr hI) (primaryGenerator (rootPart I)^2*w*u^2) =
    CenteredMomentGaussEnergy.gaussRow (primaryGenerator I)
      ((supported_span_primaryGenerator_iff I).mpr hI) (primaryGenerator (rootPart I)^2*w) *
        star (CubicSieve.cubicRow (b6 I) u) * AllSquareEnergy.squareRow (d6 I) (e6 I) u := by
  unfold CenteredMomentGaussEnergy.gaussRow
  rw [ideal_transport I hI ha w u]
  ring

/-- Actual normalized Gauss support implies allowed physical classes and the
canonical root divisor, for every nonzero element root and unit sector. -/
theorem normalized_nonzero_square_canonical (I : Id) (hI : Supported I) (x ζ : O)
    (hx : x ≠ 0) (hζ : IsUnit ζ)
    (hG : CenteredMomentGaussEnergy.gaussRow (primaryGenerator I)
      ((supported_span_primaryGenerator_iff I).mpr hI) (ζ*x^2) ≠ 0) :
    Allowed I ∧ rootPart I ∣ Ideal.span {x} := by
  apply nonzero_square_canonical I hI x ζ hx hζ
  intro hz
  apply hG
  unfold CenteredMomentGaussEnergy.gaussRow
  rw [hz, zero_div]

/-- TOTAL actual normalized Gauss formula, including zero outside canonical
square support. No source coefficient, unit phase or nonunit mask is reset. -/
theorem normalized_square_formula (I : Id) (hI : Supported I) (x ζ : O)
    (hx : x ≠ 0) (hζ : IsUnit ζ) :
    CenteredMomentGaussEnergy.gaussRow (primaryGenerator I)
      ((supported_span_primaryGenerator_iff I).mpr hI) (ζ*x^2) =
    if Allowed I ∧ rootPart I ∣ Ideal.span {x} then
      CenteredMomentGaussEnergy.gaussRow (primaryGenerator I)
        ((supported_span_primaryGenerator_iff I).mpr hI) (ζ*primaryGenerator (rootPart I)^2) *
        star (CubicSieve.cubicRow (b6 I)
          (AllSquareEnergy.elementQuotient ⟨rootPart I, rootPart_supported hI⟩ x)) *
        AllSquareEnergy.squareRow (d6 I) (e6 I)
          (AllSquareEnergy.elementQuotient ⟨rootPart I, rootPart_supported hI⟩ x)
    else 0 := by
  by_cases hs : Allowed I ∧ rootPart I ∣ Ideal.span {x}
  · rw [ite_eq_left hs]
    let T : {J : Id // Supported J} := ⟨rootPart I, rootPart_supported hI⟩
    let u := AllSquareEnergy.elementQuotient T x
    have hu := AllSquareEnergy.elementQuotient_mul T x hs.2
    have harg : primaryGenerator (rootPart I)^2*ζ*u^2=ζ*x^2 := by
      calc
        _ = ζ*(primaryGenerator (rootPart I)*u)^2 := by ring
        _ = _ := by rw [hu]
    have he := normalized_ideal_transport I hI hs.1 ζ u
    rw [harg, show primaryGenerator (rootPart I)^2*ζ=ζ*primaryGenerator (rootPart I)^2 by ring] at he
    exact he
  · rw [ite_eq_right hs]
    by_contra hn
    exact hs (normalized_nonzero_square_canonical I hI x ζ hx hζ hn)

local notation "SupportedIdeal" => {I : Id // Supported I}

/-- The actual canonical root index of a literal supported physical ideal. -/
def rootIndex (s : SupportedIdeal) : SupportedIdeal :=
  ⟨rootPart s.val, rootPart_supported s.property⟩

/-- Literal allowed physical columns in one canonical root fiber. -/
def physicalFiber (F : Finset SupportedIdeal) (T : SupportedIdeal) : Finset SupportedIdeal :=
  F.filter (fun s => Allowed s.val ∧ rootIndex s = T)

/-- Concrete finite zero extension of a common column vector. -/
def finitePush {α β : Type*} (F : Finset α) (f : α → β) (c : α → ℂ) (j : β) : ℂ :=
  ∑ i ∈ F, if f i = j then c i else 0

/-- An injective physical-column map cannot increase a pointwise coefficient bound. -/
theorem finitePush_norm {α β : Type*} (F : Finset α) (f : α → β) (c : α → ℂ)
    (hf : Set.InjOn f (↑F : Set α)) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i ∈ F, ‖c i‖ ≤ B) (j : β) : ‖finitePush F f c j‖ ≤ B := by
  by_cases he : ∃ i ∈ F, f i = j
  · obtain ⟨i, hi, hij⟩ := he
    have hs : finitePush F f c j = c i := by
      unfold finitePush
      rw [Finset.sum_eq_single i]
      · simp only [hij, ite_true]
      · intro k hk hki
        have hn : f k ≠ j := by
          intro hkj
          exact hki (hf hk hi (hkj.trans hij.symm))
        simp only [hn, ite_false]
      · intro hn
        exact (hn hi).elim
    rw [hs]
    exact hc i hi
  · have hs : finitePush F f c j = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact ite_eq_right (fun h => he ⟨i, hi, h⟩)
    rw [hs, norm_zero]
    exact hB

/-- Exact finite embedding into the native cubic range; all common coefficients
are preserved before any norm or estimate. -/
theorem finitePush_sum {α β : Type*} (F : Finset α) (J : Finset β)
    (f : α → β) (c : α → ℂ) (g : β → ℂ) (hf : ∀ i ∈ F, f i ∈ J) :
    (∑ j ∈ J, g j * finitePush F f c j) = ∑ i ∈ F, g (f i) * c i := by
  simp_rw [finitePush, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (f i)]
  · simp
  · intro j _ hn
    simp only [Ne.symm hn, ite_false, mul_zero]
  · intro hn
    exact (hn (hf i hi)).elim

/-- Actual b6 columns inject in each fixed allowed physical T fiber. -/
theorem fiber_column_injective (F : Finset SupportedIdeal) (T : SupportedIdeal) :
    Set.InjOn (fun s : SupportedIdeal => b6 s.val) (↑(physicalFiber F T) : Set SupportedIdeal) := by
  intro s hs t ht he
  have hs' := (Finset.mem_filter.mp hs).2
  have ht' := (Finset.mem_filter.mp ht).2
  apply Subtype.ext
  apply partition_injective s.property.1 t.property.1 hs'.1 ht'.1 _ he
  exact congrArg Subtype.val (hs'.2.trans ht'.2.symm)

/-- Every physical b6 column has the exact separate column coprimality mask. -/
theorem fiber_column_coprime (F : Finset SupportedIdeal) (T s : SupportedIdeal)
    (hs : s ∈ physicalFiber F T) : IsCoprime (b6 s.val) (d3 T.val*e3 T.val) := by
  have ht := congrArg Subtype.val (Finset.mem_filter.mp hs).2.2
  change rootPart s.val = T.val at ht
  rw [← ht, d3_rootPart, e3_rootPart]
  exact (b6_coprime_d6 s.val).mul_right (b6_coprime_e6 s.val)

/-- The enlarged native range contains EVERY actual column in the fiber. -/
theorem fiber_column_range (F : Finset SupportedIdeal) (Z : ℝ)
    (hF : ∀ s ∈ F, (Ideal.absNorm s.val : ℝ) ≤ Z) (T s : SupportedIdeal)
    (hs : s ∈ physicalFiber F T) :
    b6 s.val ∈ CubicSieve.idealRange (Z/ProbeGramCommon.gramIdealNorm T^2) := by
  have hs' := Finset.mem_filter.mp hs
  have ht := congrArg Subtype.val hs'.2.2
  change rootPart s.val = T.val at ht
  have he := physical_eq_canonical s.property.1 hs'.2.1
  rw [ht] at he
  have hp : b6 s.val * (T.val^2*d3 T.val*e3 T.val) = s.val := by
    calc
      _ = T.val^2*d3 T.val*e3 T.val*b6 s.val := by ring
      _ = _ := he.symm
  exact AllSquareEnergy.enlarged_column_range Z T _ _
    ⟨b6_squarefree s.val, supported_primaryGenerator_ne_zero _ (b6_supported s.property)⟩
    (AllSquareEnergy.footprint_norm T _ _ (d3_ne_zero _) (e3_ne_zero _))
    (by rw [hp]; exact hF s hs'.1)

/-- The literal coefficient of an actual physical column at the fixed square
baseline; no freely assigned complex phase is introduced. -/
def physicalCoefficient (C : CalibrationData) (W : ℝ → ℂ) (Y : ℝ)
    (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ : O) (T s : SupportedIdeal) : ℂ :=
  lowGaussColumn C W Y σ v s * CenteredMomentGaussEnergy.gaussRow (primaryGenerator s.val)
    ((supported_span_primaryGenerator_iff s.val).mpr s.property) (-ζ*primaryGenerator T.val^2)

/-- The actual baseline norm for EVERY physical column in a canonical fiber
is proved by the new any-divisor native norm theorem. Unit sectors are explicit. -/
theorem physicalCoefficient_norm (F : Finset SupportedIdeal) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (W : ℝ → ℂ) (a z B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hW : Function.support W ⊆ Set.Icc a z)
    (hWB : ∀ x, ‖W x‖ ≤ B) (Y : ℝ) (hY : 0 < Y)
    (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ : O) (hζ : IsUnit ζ)
    (T s : SupportedIdeal) (hs : s ∈ physicalFiber F T) :
    ‖physicalCoefficient (calibrationForSet S hS) W Y σ v ζ T s‖ ≤
      (B*a^(-(1/2 : ℝ)))*ProbeGramCommon.gramIdealNorm T/Y := by
  have ht := congrArg Subtype.val (Finset.mem_filter.mp hs).2.2
  change rootPart s.val = T.val at ht
  have hd : T.val ∣ s.val := ht ▸ rootPart_dvd s.property.1
  have hg := SquareGaussIdealNorm.gaussRow_divisor_square_norm s.property hd ζ hζ
  have hc := lowGaussColumn_norm_bound S hS W a z B ha hB hW hWB Y hY σ v s
  unfold physicalCoefficient
  rw [norm_mul]
  calc
    _ ≤ (B*a^(-(1/2 : ℝ))/Y)*ProbeGramCommon.gramIdealNorm T :=
      mul_le_mul hc hg (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Actual prescribed physical columns embedded into the native cubic range. -/
def pushedCoefficient (F : Finset SupportedIdeal) (C : CalibrationData) (W : ℝ → ℂ)
    (Y : ℝ) (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ : O) (T : SupportedIdeal) (j : Id) : ℂ :=
  finitePush (physicalFiber F T) (fun s => b6 s.val) (physicalCoefficient C W Y σ v ζ T) j

/-- The literal common vector inherits the original coefficient cost with no
fiber multiplicity, by actual b6 injectivity. -/
theorem pushedCoefficient_norm (F : Finset SupportedIdeal) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (W : ℝ → ℂ) (a z B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hW : Function.support W ⊆ Set.Icc a z)
    (hWB : ∀ x, ‖W x‖ ≤ B) (Y : ℝ) (hY : 0 < Y)
    (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ : O) (hζ : IsUnit ζ)
    (T : SupportedIdeal) (j : Id) :
    ‖pushedCoefficient F (calibrationForSet S hS) W Y σ v ζ T j‖ ≤
      (B*a^(-(1/2 : ℝ)))*ProbeGramCommon.gramIdealNorm T/Y := by
  have ht := ProbeGramCommon.gramIdealNorm_pos T
  exact finitePush_norm _ _ _ (fiber_column_injective F T) _ (by positivity)
    (fun s hs => physicalCoefficient_norm F S hS W a z B ha hB hW hWB Y hY σ v ζ hζ T s hs) j

/-- Exact native cubic embedding of an entire actual physical fiber, including
the original column mask; no coefficient is dropped before the sum. -/
theorem pushed_cubic_sum (F : Finset SupportedIdeal) (Z : ℝ)
    (hF : ∀ s ∈ F, (Ideal.absNorm s.val : ℝ) ≤ Z)
    (C : CalibrationData) (W : ℝ → ℂ) (Y : ℝ) (σ : RayFourExpansion.RayRing)
    (v : ℝ) (ζ : O) (T : SupportedIdeal) (u : O) :
    (∑ j : CubicSieve.idealRange (Z/ProbeGramCommon.gramIdealNorm T^2),
      star (CubicSieve.cubicRow j.val u) *
        (if IsCoprime j.val (d3 T.val*e3 T.val) then
          pushedCoefficient F C W Y σ v ζ T j.val else 0)) =
      ∑ s ∈ physicalFiber F T, star (CubicSieve.cubicRow (b6 s.val) u) *
        physicalCoefficient C W Y σ v ζ T s := by
  have he := finitePush_sum (physicalFiber F T)
    (CubicSieve.idealRange (Z/ProbeGramCommon.gramIdealNorm T^2))
    (fun s => b6 s.val) (physicalCoefficient C W Y σ v ζ T)
    (fun j => if IsCoprime j (d3 T.val*e3 T.val) then star (CubicSieve.cubicRow j u) else 0)
    (fun s hs => fiber_column_range F Z hF T s hs)
  have hm (j : Id) : star (CubicSieve.cubicRow j u) *
      (if IsCoprime j (d3 T.val*e3 T.val) then pushedCoefficient F C W Y σ v ζ T j else 0) =
      (if IsCoprime j (d3 T.val*e3 T.val) then star (CubicSieve.cubicRow j u) else 0) *
        pushedCoefficient F C W Y σ v ζ T j := by
    split_ifs <;> simp
  simp_rw [hm]
  rw [Finset.sum_coe_sort (CubicSieve.idealRange (Z/ProbeGramCommon.gramIdealNorm T^2))
    (fun j : Id => (if IsCoprime j (d3 T.val*e3 T.val) then star (CubicSieve.cubicRow j u) else 0) *
      pushedCoefficient F C W Y σ v ζ T j)]
  change (∑ j ∈ CubicSieve.idealRange (Z/ProbeGramCommon.gramIdealNorm T^2),
    (if IsCoprime j (d3 T.val*e3 T.val) then star (CubicSieve.cubicRow j u) else 0) *
      finitePush (physicalFiber F T) (fun s => b6 s.val) (physicalCoefficient C W Y σ v ζ T) j) = _
  rw [he]
  apply Finset.sum_congr rfl
  intro s hs
  rw [ite_eq_left (fiber_column_coprime F T s hs)]

/-- Exact pointwise physical-column transport on its actual fixed-T fiber.
Every generator and the negative unit numerator agree literally. -/
theorem fiber_transport (F : Finset SupportedIdeal) (C : CalibrationData) (W : ℝ → ℂ)
    (Y : ℝ) (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ x : O)
    (T s : SupportedIdeal) (hs : s ∈ physicalFiber F T) (hdiv : T.val ∣ Ideal.span {x}) :
    lowGaussColumn C W Y σ v s * CenteredMomentGaussEnergy.gaussRow (primaryGenerator s.val)
      ((supported_span_primaryGenerator_iff s.val).mpr s.property) ((-ζ)*x^2) =
    AllSquareEnergy.squareRow (d3 T.val) (e3 T.val) (AllSquareEnergy.elementQuotient T x) *
      star (CubicSieve.cubicRow (b6 s.val) (AllSquareEnergy.elementQuotient T x)) *
        physicalCoefficient C W Y σ v ζ T s := by
  have hs' := (Finset.mem_filter.mp hs).2
  have ht := congrArg Subtype.val hs'.2
  change rootPart s.val = T.val at ht
  let u := AllSquareEnergy.elementQuotient T x
  have hu := AllSquareEnergy.elementQuotient_mul T x hdiv
  have hg := normalized_ideal_transport s.val s.property hs'.1 (-ζ) u
  rw [ht] at hg
  have harg : primaryGenerator T.val^2*(-ζ)*u^2=(-ζ)*x^2 := by
    calc
      _ = (-ζ)*(primaryGenerator T.val*u)^2 := by ring
      _ = _ := by rw [hu]
  rw [harg, show primaryGenerator T.val^2*(-ζ)=(-ζ)*primaryGenerator T.val^2 by ring] at hg
  have hd : d6 s.val = d3 T.val := by rw [← ht, d3_rootPart]
  have he : e6 s.val = e3 T.val := by rw [← ht, e3_rootPart]
  rw [hd, he] at hg
  rw [hg]
  unfold physicalCoefficient
  ring


/-- Literal summand of the original finite physical amplitude at a square. -/
def squareColumn (C : CalibrationData) (W : ℝ → ℂ) (Y : ℝ)
    (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ x : O) (s : SupportedIdeal) : ℂ :=
  lowGaussColumn C W Y σ v s * CenteredMomentGaussEnergy.gaussRow (primaryGenerator s.val)
    ((supported_span_primaryGenerator_iff s.val).mpr s.property) ((-ζ)*x^2)

/-- Any nonzero original column has its actual canonical divisor support. -/
theorem squareColumn_nonzero (C : CalibrationData) (W : ℝ → ℂ) (Y : ℝ)
    (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ x : O) (s : SupportedIdeal)
    (hx : x ≠ 0) (hζ : IsUnit ζ) (hs : squareColumn C W Y σ v ζ x s ≠ 0) :
    Allowed s.val ∧ (rootIndex s).val ∣ Ideal.span {x} := by
  apply normalized_nonzero_square_canonical s.val s.property x (-ζ) hx hζ.neg
  intro hz
  exact hs (by simp only [squareColumn, hz, mul_zero])

/-- Exact physical square norm forces the canonical divisor into the physical
cutoff, independently of the normalization Y. -/
theorem rootIndex_square_norm (s : SupportedIdeal) (ha : Allowed s.val) :
    ProbeGramCommon.gramIdealNorm (rootIndex s)^2 ≤ (Ideal.absNorm s.val : ℝ) := by
  have he := physical_eq_canonical s.property.1 ha
  have hd : (rootPart s.val)^2 ∣ s.val := by
    refine ⟨d3 (rootPart s.val)*e3 (rootPart s.val)*b6 s.val, ?_⟩
    calc
      _ = rootPart s.val^2*d3 (rootPart s.val)*e3 (rootPart s.val)*b6 s.val := he
      _ = _ := by ring
  have hn : Ideal.absNorm ((rootPart s.val)^2) ≤ Ideal.absNorm s.val :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1))
      (map_dvd Ideal.absNorm hd)
  rw [map_pow] at hn
  change (Ideal.absNorm (rootPart s.val) : ℝ)^2 ≤ _
  exact_mod_cast hn

/-- The actual finite canonical divisors that can occur for these independent
root and physical cutoffs. -/
def rootIndices (A Z : ℝ) (F : Finset SupportedIdeal) : Finset SupportedIdeal :=
  (F.image rootIndex).filter (fun T => ProbeGramCommon.gramIdealNorm T ≤ A ∧
    ProbeGramCommon.gramIdealNorm T^2 ≤ Z)

/-- Every retained index has precisely the scales required by the native
cubic/divisor theorem. -/
theorem rootIndices_scales (A Z : ℝ) (F : Finset SupportedIdeal) (T : SupportedIdeal)
    (hT : T ∈ rootIndices A Z F) :
    1 ≤ A/ProbeGramCommon.gramIdealNorm T ∧
      1 ≤ Z/ProbeGramCommon.gramIdealNorm T^2 := by
  have ht := ProbeGramCommon.gramIdealNorm_pos T
  have hh := (Finset.mem_filter.mp hT).2
  exact ⟨(le_div_iff₀ ht).mpr (by simpa only [one_mul] using hh.1),
    (le_div_iff₀ (sq_pos_of_pos ht)).mpr (by simpa only [one_mul] using hh.2)⟩

/-- Original nonzero columns lie in the actual finite root-index set. -/
theorem rootIndex_mem (A Z : ℝ) (F : Finset SupportedIdeal)
    (hF : ∀ s ∈ F, (Ideal.absNorm s.val : ℝ) ≤ Z) (x : O) (hx : x ∈ elementRange A)
    (s : SupportedIdeal) (hs : s ∈ F) (ha : Allowed s.val)
    (hd : (rootIndex s).val ∣ Ideal.span {x}) : rootIndex s ∈ rootIndices A Z F := by
  have hx' := (mem_elementRange A x).mp hx
  have hn : Ideal.absNorm (rootIndex s).val ≤ Ideal.absNorm (Ideal.span {x}) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hx'.1))) (map_dvd Ideal.absNorm hd)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_, (rootIndex_square_norm s ha).trans (hF s hs)⟩
  have hn' : (Ideal.absNorm (rootIndex s).val : ℝ) ≤
      (Ideal.absNorm (Ideal.span {x}) : ℝ) := by exact_mod_cast hn
  exact hn'.trans hx'.2

/-- Whole-fiber exact transport to one native cubic block. The zero extension
contains only original physical columns; no inverse enlarged-column identity
is needed, including at the dangerous noncanonical j/e overlaps. -/
theorem fiber_squareBlock (F : Finset SupportedIdeal) (Z : ℝ)
    (hF : ∀ s ∈ F, (Ideal.absNorm s.val : ℝ) ≤ Z)
    (C : CalibrationData) (W : ℝ → ℂ) (Y : ℝ) (σ : RayFourExpansion.RayRing)
    (v : ℝ) (ζ x : O) (hx : x ≠ 0) (hζ : IsUnit ζ) (T : SupportedIdeal) :
    (∑ s ∈ F.filter (fun s => rootIndex s = T), squareColumn C W Y σ v ζ x s) =
      AllSquareEnergy.squareBlock (Z/ProbeGramCommon.gramIdealNorm T^2) T (d3 T.val) (e3 T.val)
        (fun j => pushedCoefficient F C W Y σ v ζ T j.val) x := by
  by_cases hd : T.val ∣ Ideal.span {x}
  · have hsub : physicalFiber F T ⊆ F.filter (fun s => rootIndex s = T) := by
      intro s hs
      have hh := Finset.mem_filter.mp hs
      exact Finset.mem_filter.mpr ⟨hh.1, hh.2.2⟩
    have hr : (∑ s ∈ F.filter (fun s => rootIndex s = T), squareColumn C W Y σ v ζ x s) =
        ∑ s ∈ physicalFiber F T, squareColumn C W Y σ v ζ x s := by
      symm
      apply Finset.sum_subset hsub
      intro s hs hn
      by_contra hz
      have ha := (squareColumn_nonzero C W Y σ v ζ x s hx hζ hz).1
      exact hn (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, ha, (Finset.mem_filter.mp hs).2⟩)
    rw [hr]
    unfold AllSquareEnergy.squareBlock
    rw [ite_eq_left hd, pushed_cubic_sum F Z hF C W Y σ v ζ T]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact (fiber_transport F C W Y σ v ζ x T s hs hd).trans (by ring)
  · rw [AllSquareEnergy.squareBlock_zero _ T _ _ _ x hd]
    apply Finset.sum_eq_zero
    intro s hs
    by_contra hz
    have hh := (squareColumn_nonzero C W Y σ v ζ x s hx hζ hz).2
    have ht := congrArg Subtype.val (Finset.mem_filter.mp hs).2
    exact hd (ht ▸ hh)

/-- Exact regrouping of the complete original finite physical sum; every
column is retained before transport and all zero exclusions are proved. -/
theorem finite_square_decomposition (A Z : ℝ) (F : Finset SupportedIdeal)
    (hF : ∀ s ∈ F, (Ideal.absNorm s.val : ℝ) ≤ Z)
    (C : CalibrationData) (W : ℝ → ℂ) (Y : ℝ) (σ : RayFourExpansion.RayRing)
    (v : ℝ) (ζ x : O) (hx : x ∈ elementRange A) (hζ : IsUnit ζ) :
    (∑ s ∈ F, squareColumn C W Y σ v ζ x s) =
      ∑ T ∈ rootIndices A Z F,
        AllSquareEnergy.squareBlock (Z/ProbeGramCommon.gramIdealNorm T^2) T (d3 T.val) (e3 T.val)
          (fun j => pushedCoefficient F C W Y σ v ζ T j.val) x := by
  let D := rootIndices A Z F
  have hr : (∑ s ∈ F, squareColumn C W Y σ v ζ x s) =
      ∑ s ∈ F.filter (fun s => rootIndex s ∈ D), squareColumn C W Y σ v ζ x s := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hn
    by_contra hz
    have hh := squareColumn_nonzero C W Y σ v ζ x s (mem_elementRange A x |>.mp hx).1 hζ hz
    have hm := rootIndex_mem A Z F hF x hx s hs hh.1 hh.2
    exact hn (Finset.mem_filter.mpr ⟨hs, hm⟩)
  rw [hr, ← Finset.sum_fiberwise_eq_sum_filter F D rootIndex (squareColumn C W Y σ v ζ x)]
  apply Finset.sum_congr rfl
  intro T _
  exact fiber_squareBlock F Z hF C W Y σ v ζ x (mem_elementRange A x |>.mp hx).1 hζ T


/-- The actual compact physical columns obey the independently chosen upper
cutoff Z whenever the profile upper endpoint satisfies zY≤Z. -/
theorem lowGaussColumns_cutoff (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (a z Z Y : ℝ) (hY : 0 < Y) (hW : Function.support W ⊆ Set.Icc a z)
    (hcut : z*Y ≤ Z) :
    ∀ s ∈ lowGaussColumns W hWc Y hY, (Ideal.absNorm s.val : ℝ) ≤ Z := by
  intro s hs
  have hw := (hW ((lowGaussColumns_mem W hWc Y hY s).mp hs)).2
  exact ((div_le_iff₀ hY).mp hw).trans hcut

/-- Exact decomposition of the ORIGINAL lowRayAmplitude at every square in
the root range. All physical columns, heights, rays and calibration phases
are retained before the actual cubic sieve is applied. -/
theorem lowRayAmplitude_square_decomposition (C : CalibrationData) (W : ℝ → ℂ)
    (hWc : HasCompactSupport W) (a z A Z Y : ℝ) (hY : 0 < Y)
    (hW : Function.support W ⊆ Set.Icc a z) (hcut : z*Y ≤ Z)
    (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ x : O) (hζ : IsUnit ζ)
    (hx : x ∈ elementRange A) :
    lowRayAmplitude C W Y σ (ζ*x^2) v =
      ∑ T ∈ rootIndices A Z (lowGaussColumns W hWc Y hY),
        AllSquareEnergy.squareBlock (Z/ProbeGramCommon.gramIdealNorm T^2) T (d3 T.val) (e3 T.val)
          (fun j => pushedCoefficient (lowGaussColumns W hWc Y hY) C W Y σ v ζ T j.val) x := by
  rw [lowRayAmplitude_source_columns C W hWc Y hY σ v (ζ*x^2)]
  unfold CenteredMomentGaussEnergy.gaussPolynomial
  have harg : -(ζ*x^2)=(-ζ)*x^2 := by ring
  rw [harg]
  exact finite_square_decomposition A Z (lowGaussColumns W hWc Y hY)
    (lowGaussColumns_cutoff W hWc a z Z Y hY hW hcut) C W Y σ v ζ x hx hζ

/-- Unconditional actual all-square physical energy. The only hypotheses
are the original profile/support and scales, plus the actual unit sector.
No Gauss bridge, phase, baseline norm or energy premise is assumed. Uniformity
includes the calibration set, ray and archimedean height. Z remains independent
of the normalization Y, so the literal profile cost (Z/Y)² is displayed. -/
theorem lowRayAmplitude_all_square_energy (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
      (W : ℝ → ℂ) (_hWc : HasCompactSupport W) (a z B : ℝ),
      0 < a → 0 ≤ B → Function.support W ⊆ Set.Icc a z → (∀ t, ‖W t‖ ≤ B) →
      ∀ A Z Y : ℝ, 1 ≤ A → 1 ≤ Z → 0 < Y → z*Y ≤ Z →
      ∀ (σ : RayFourExpansion.RayRing) (v : ℝ) (ζ : O), IsUnit ζ →
      (∑ x ∈ elementRange A, ‖lowRayAmplitude (calibrationForSet S hS) W Y σ (ζ*x^2) v‖^2) ≤
        K*(B*a^(-(1/2 : ℝ)))^2*A^η*(A*Z)^ε*(Z/Y)^2*(A^(1/3 : ℝ)+A^(4/3 : ℝ)/Z) := by
  obtain ⟨K, hK, hb⟩ := AllSquareEnergy.assembled_pointwise_energy ε η hε hη
  refine ⟨K, hK, ?_⟩
  intro S hS W hWc a z B ha hB hW hWB A Z Y hA hZ hY hcut σ v ζ hζ
  let F := lowGaussColumns W hWc Y hY
  let D := rootIndices A Z F
  have he := hb A Z Y (B*a^(-(1/2 : ℝ))) hA hZ hY D
    (fun T => d3 T.val) (fun T => e3 T.val)
    (fun T j => pushedCoefficient F (calibrationForSet S hS) W Y σ v ζ T j.val)
    (fun T hT => rootIndices_scales A Z F T hT)
    (fun T _ j => pushedCoefficient_norm F S hS W a z B ha hB hW hWB Y hY σ v ζ hζ T j.val)
  have hh : (∑ x ∈ elementRange A,
      ‖lowRayAmplitude (calibrationForSet S hS) W Y σ (ζ*x^2) v‖^2) =
      ∑ x ∈ elementRange A, ‖∑ T ∈ D,
        AllSquareEnergy.squareBlock (Z/ProbeGramCommon.gramIdealNorm T^2) T (d3 T.val) (e3 T.val)
          (fun j => pushedCoefficient F (calibrationForSet S hS) W Y σ v ζ T j.val) x‖^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [lowRayAmplitude_square_decomposition (calibrationForSet S hS) W hWc a z A Z Y hY hW hcut σ v ζ x hζ hx]
  rw [hh]
  exact he

end OpenAIReview.AllSquareAmplitudeBridge
#lint+ in OpenAIReview.AllSquareAmplitudeBridge

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
  unless declarations > 0 do throwError "Empty actual all-square amplitude audit."
  logInfo m!"Actual all-square amplitude audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-all-square-bridge-integration"
  IO.FS.writeFile ".lake/arithmetic-operator-all-square-bridge-integration/axioms.json"
    (Json.mkObj [("scope", toJson "unconditional original lowRayAmplitude all-square energy from actual native Gauss support and transport, canonical ideal fibers, ANY-divisor baseline norm, actual cubic sieve and ideal divisor bounds; unit sectors explicit; no source allocation"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
