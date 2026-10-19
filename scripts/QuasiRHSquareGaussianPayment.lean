/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHSquareNativePayment
import OAI.NumberTheory.DirichletL.Detector.LowGaussianSum
import OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer

/-!
Original central Gaussian square tuples, with actual sector integrability and
an exact square/complement dyad ledger. The remote family is kept whole and
no numerator subset is assigned the original source.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical ContDiff BigOperators SchwartzMap
open MeasureTheory
namespace OpenAIReview.SquareGaussianPayment
open OAI OAI.SevenEighths OAI.CompletedGauss
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.CubicSieve
open RayFourExpansion CanonicalQuadraticSieve SquareSectorTransfer ProbeCompleted FourierBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Literal original Mellin-normalized numerator restriction. The only new
notation is the fixed predicate; all windows and the companion remain native. -/
def normalizedSectorIntegral (P : O → Prop) (C : CalibrationData) (W0 W1 : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (B : RayRing → O → ℂ) : ℂ :=
  ((Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
    ∫v : ℝ, physicalSector ((lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
      (lowPhysicalScale_pos C X Y hX hY)).filter P) C W0 W1 a b X Y B v

/-- The square specialization is exactly the already proved native integral. -/
theorem normalizedSectorIntegral_square (C : CalibrationData) (W0 W1 : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (B : RayRing → O → ℂ) :
    normalizedSectorIntegral SquareNumerator C W0 W1 a b ha hb X Y hX hY B =
      SquareNativePayment.normalizedSquareIntegral C W0 W1 a b ha hb X Y hX hY B := rfl

/-- Exact finite physical-row representation of a restricted original Mellin
integral. The restriction stays on the literal numerator r.2. -/
theorem normalizedSectorIntegral_rows (P : O → Prop) (C : CalibrationData)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing → O → ℂ) :
    normalizedSectorIntegral P C W0 W1 (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) X Y hX hY B =
      ∑'r : PhysicalRowIndex, physicalRowWeight C W0 W1 X Y r*
        (if P r.2 then B (physicalIdealRay r.1) r.2 else 0) := by
  unfold normalizedSectorIntegral
  have he : physicalSector ((lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
      (lowPhysicalScale_pos C X Y hX hY)).filter P) C W0 W1 (a0*a1) (max 1 (b0*b1)) X Y B =
      lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y
        (fun σ m=>if P m then B σ m else 0) := by
    funext v
    exact SquareSectorIntegral.sector_eq_separated P _ _ _ _ C W0 W1 X Y hX hY B v
  rw [he]
  exact (physicalRowWeight_low_separated C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s
    X Y hX hY (fun σ m=>if P m then B σ m else 0)).symm

/-- Exact original selected-row Gaussian integrability. All finite selected
weights, cubes, correction coefficients and norm-twist phases remain native. -/
theorem selected_gaussian_integrable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (slots : Fin K → Finset O) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (Yp : Fin K → ℝ) (U : ℝ) (hU : 0<U)
    (σ : RayRing) (m : O) (b : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ=>lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) U t σ m*b t) := by
  unfold lowSelectedInverseRow
  simp_rw [Finset.sum_mul]
  apply integrable_finsetSum
  intro k _
  have hg := gaussian_selected_completed_integrable (fun i : SelectedSlot J=>W i.val)
    (fun i : SelectedSlot J=>elementNorm (k i).val/Yp i.val) b S (lowSelectedIdeal slots J k)
    (physicalRayRowMonoid η (calibrationForSet S hS) σ m) U hU
  have he (t : ℝ) := (lowMarkedInverseRow_eq η S hS hbad (lowSelectedIdeal slots J k) U t hU σ m).symm
  simp_rw [he]
  convert hg.const_mul (star (HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(k i).val))) using 1
  funext t
  dsimp [lowSelectedWeight]
  ring

/-- Genuine outer-height integrability of every actual numerator restriction.
Finite physical support is used BEFORE the Gaussian integral; no measurability
or cancellation is inferred just from an energy bound. -/
theorem sector_selected_integrable (P : O → Prop) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀Q∈S,Q.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) {K : ℕ} (slots : Fin K → Finset O) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (Yp : Fin K → ℝ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (U : ℝ) (hU : 0<U) (b : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ=>normalizedSectorIntegral P (calibrationForSet S hS) W0 W1
      (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) X Y hX hY
      (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
        η S hS (lowSelectedIdeal slots J) U t)*b t) := by
  let C := calibrationForSet S hS
  have hW0c : HasCompactSupport W0 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  let hf := physicalRowWeight_finite_support C W0 W1 hW0c hW1c X Y hX hY
  let R := hf.toFinset
  have hz (r : PhysicalRowIndex) (hr : r∉R) : physicalRowWeight C W0 W1 X Y r=0 := by
    simpa only [R,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hr
  have he (t : ℝ) : normalizedSectorIntegral P C W0 W1
      (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) X Y hX hY
      (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
        η S hS (lowSelectedIdeal slots J) U t) =
      ∑r∈R,physicalRowWeight C W0 W1 X Y r*(if P r.2 then
        lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
          η S hS (lowSelectedIdeal slots J) U t (physicalIdealRay r.1) r.2 else 0) := by
    rw [normalizedSectorIntegral_rows P C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s]
    exact tsum_eq_sum (fun r hr=>by rw [hz r hr,zero_mul])
  change Integrable (fun t : ℝ=>normalizedSectorIntegral P C W0 W1
    (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) X Y hX hY
    (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
      η S hS (lowSelectedIdeal slots J) U t)*b t)
  simp_rw [he,Finset.sum_mul]
  apply integrable_finsetSum
  intro r _
  by_cases hp : P r.2
  · simp only [ite_eq_left hp]
    convert (selected_gaussian_integrable η S hS hbad slots J W Yp U hU (physicalIdealRay r.1) r.2 b).const_mul
      (physicalRowWeight C W0 W1 X Y r) using 1
    funext t
    ring
  · simp only [ite_eq_right hp,mul_zero,zero_mul]
    exact integrable_zero ℝ ℂ volume

/-- Literal joined original unselected tuples with a fixed numerator mask. -/
def joinedSector (P : O → Prop) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀Q∈S,Q.IsMaximal) (W0 W1 : ℝ → ℂ) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    {K : ℕ} (slots : Fin K → Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (Yp : Fin K → ℝ)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (U t : ℝ) : ℂ :=
  ∑p : LowUnselectedTuple slots J, lowUnselectedWeight slots J W Yp p*
    normalizedSectorIntegral P (calibrationForSet S hS) W0 W1 a b ha hb
      (X/elementNorm (∏i : J,(p i).val)) (Y/elementNorm (∏i : J,(p i).val))
      (div_pos hX (lowUnselectedProduct_norm_pos slots hslots J p))
      (div_pos hY (lowUnselectedProduct_norm_pos slots hslots J p))
      (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
        η S hS (lowSelectedIdeal slots J) U t)

/-- Literal Gaussian integral of the original joined sector. -/
def gaussianSectorDyad (P : O → Prop) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀Q∈S,Q.IsMaximal) (W0 W1 : ℝ → ℂ) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    {K : ℕ} (slots : Fin K → Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (Yp : Fin K → ℝ)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (U R : ℝ)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) : ℂ :=
  ∫t : ℝ,joinedSector P η S hS W0 W1 a b ha hb slots hslots J W Yp X Y hX hY U t*
    gaussianJointDensity V hV (U/R) t

/-- Actual joined sector Gaussian integrability, with no energy premise. -/
theorem joinedSector_integrable (P : O → Prop) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀Q∈S,Q.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) {K : ℕ} (slots : Fin K → Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (Yp : Fin K → ℝ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (U : ℝ) (hU : 0<U) (b : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ=>joinedSector P η S hS W0 W1 (a0*a1) (max 1 (b0*b1))
      (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      slots hslots J W Yp X Y hX hY U t*b t) := by
  unfold joinedSector
  simp_rw [Finset.sum_mul]
  apply integrable_finsetSum
  intro p _
  convert (sector_selected_integrable P η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s
    slots J W Yp (X/elementNorm (∏i : J,(p i).val)) (Y/elementNorm (∏i : J,(p i).val))
    (div_pos hX (lowUnselectedProduct_norm_pos slots hslots J p))
    (div_pos hY (lowUnselectedProduct_norm_pos slots hslots J p)) U hU b).const_mul
    (lowUnselectedWeight slots J W Yp p) using 1
  funext t
  ring


/-- Genuine inner-integral ledger after the original Mellin normalization.
Integrability of both sectors is supplied by the imported actual sector theorem. -/
theorem normalizedSectorIntegral_ledger (C : CalibrationData) (W0 W1 : ℝ → ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing → O → ℂ) :
    ((Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
      (∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y B v) =
      normalizedSectorIntegral SquareNumerator C W0 W1 (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) X Y hX hY B +
      normalizedSectorIntegral (fun m=>¬SquareNumerator m) C W0 W1 (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) X Y hX hY B := by
  have hi := SquareSectorIntegral.integral_sector_ledger (a0*a1) (max 1 (b0*b1))
    (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) C W0 W1 a0 b0 ha0
    hW0 hW0s (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1) X Y hX hY B
  dsimp only at hi
  have hh := congrArg (fun z : ℂ=>(Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*z) hi
  dsimp only [normalizedSectorIntegral,squareRows] at hh ⊢
  rw [mul_add] at hh
  convert hh using 1
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v=>by
    congr 1
    ext m
    simp)

/-- Exact pointwise split of the ORIGINAL finite compensated tuple polynomial.
All selected phases and the same companion remain in both terms. -/
theorem joinedSector_ledger (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀Q∈S,Q.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) {K : ℕ} (slots : Fin K → Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (Yp : Fin K → ℝ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (U t : ℝ) (hU : 0<U) :
    (∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
      compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y U t*
        selectedSlotFactor W Yp (fun i=>(p i).val) J t) =
      joinedSector SquareNumerator η S hS W0 W1 (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) slots hslots J W Yp X Y hX hY U t +
      joinedSector (fun m=>¬SquareNumerator m) η S hS W0 W1 (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) slots hslots J W Yp X Y hX hY U t := by
  rw [compensation_tuple_low_polynomial η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s
    slots hslots J W Yp X Y U t hX hY hU]
  unfold joinedSector
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hl := lowUnselectedProduct_norm_pos slots hslots J p
  have he := normalizedSectorIntegral_ledger (calibrationForSet S hS) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 hW0s _ _ (div_pos hX hl) (div_pos hY hl)
    (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) U t)
  linear_combination lowUnselectedWeight slots J W Yp p*he

/-- Exact ORIGINAL Gaussian dyad ledger. Both outer-height sector integrals
are proved integrable before integral_add is invoked. -/
theorem gaussianSectorDyad_ledger (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀Q∈S,Q.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) {K : ℕ} (slots : Fin K → Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (Yp : Fin K → ℝ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (U R : ℝ) (hU : 0<U) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) :
    lowCommonDyad η (calibrationForSet S hS) W0 W1 slots W Yp J X Y U R V hV =
      gaussianSectorDyad SquareNumerator η S hS W0 W1 (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) slots hslots J W Yp X Y hX hY U R V hV +
      gaussianSectorDyad (fun m=>¬SquareNumerator m) η S hS W0 W1 (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) slots hslots J W Yp X Y hX hY U R V hV := by
  unfold lowCommonDyad gaussianSectorDyad
  rw [←integral_add
    (joinedSector_integrable SquareNumerator η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s
      slots hslots J W Yp X Y hX hY U hU (gaussianJointDensity V hV (U/R)))
    (joinedSector_integrable (fun m=>¬SquareNumerator m) η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s
      slots hslots J W Yp X Y hX hY U hU (gaussianJointDensity V hV (U/R)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>by
    dsimp only
    rw [joinedSector_ledger η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s slots hslots J W Yp X Y hX hY U t hU]
    ring)


/-- Actual central square Gaussian dyad payment. Genuine integrability is
used in the comparison; the original companion and every sector mask remain. -/
theorem central_square_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(hZ0 : 0<Z)(T : Fin K→Finset PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(U : ℝ),0<U→
      Z^(1+lowSelectedLength ell J-ε/2)≤U→U≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖gaussianSectorDyad SquareNumerator η S hS W0 W1 (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        (fun i=>canonicalSlotSupport (T i)) (fun i=>canonicalSlotSupport_nonzero _ (hT i))
        J W (fun i=>Z^(ell i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ))
        (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) U
        (Z^(1+lowSelectedLength ell J)) V hV‖ ≤
        C*Z^(5/72+255*ε:ℝ)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) := by
  obtain ⟨degree,C,hC,he⟩ := SquareNativePayment.native_square_joined η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hM hW0 hW1 hW0s hWM
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZ0 T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  let slots := fun i=>canonicalSlotSupport (T i)
  have hslots : ∀i x,x∈slots i→x≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun t : ℝ=>joinedSector SquareNumerator η S hS W0 W1
    (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) slots hslots J W (fun i=>Z^(ell i))
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) U t*
      gaussianJointDensity V hV (U/R) t
  have hf : Integrable f := joinedSector_integrable SquareNumerator η S hS hbad W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 hW0s slots hslots J W (fun i=>Z^(ell i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ))
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) U hU (gaussianJointDensity V hV (U/R))
  have hb (t : ℝ) : ‖joinedSector SquareNumerator η S hS W0 W1
      (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) slots hslots J W (fun i=>Z^(ell i))
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) U t‖ ≤
      (C*Z^(5/72+255*ε:ℝ))*(1+‖t‖)^degree := by
    simpa only [joinedSector,normalizedSectorIntegral_square,mul_assoc,mul_left_comm,mul_comm] using
      hZ.2 hZ0 T hT hout hdis hnorm J U hU hlo hhi W hW t
  have hi := (JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV (U/R)) degree).const_mul
    (C*Z^(5/72+255*ε:ℝ))
  have hm (t : ℝ) : ‖f t‖ ≤ (C*Z^(5/72+255*ε:ℝ))*
      ((1+‖t‖)^degree*‖gaussianJointDensity V hV (U/R) t‖) := by
    dsimp only [f]
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _)
  change ‖∫t : ℝ,f t‖ ≤ _
  calc
    _ ≤ ∫t : ℝ,‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫t : ℝ,(C*Z^(5/72+255*ε:ℝ))*((1+‖t‖)^degree*‖gaussianJointDensity V hV (U/R) t‖) :=
      integral_mono hf.norm hi hm
    _ = _ := by rw [integral_const_mul];rfl

/-- Original central Gaussian square sum with an independent Gaussian loss.
Both absolute summability and the complex-series norm are proved for the
literal masked original dyads; the whole remote family is not subdivided. -/
theorem central_square_gaussian_payment (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε εG : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) (hεG : 0<εG)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hWM : ∀x,‖W1 x‖≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(hZ0 : 0<Z)(T : Fin K→Finset PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
        gaussianSectorDyad SquareNumerator η S hS W0 W1 (a0*a1) (max 1 (b0*b1))
          (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (fun i=>canonicalSlotSupport (T i)) (fun i=>canonicalSlotSupport_nonzero _ (hT i))
          J W (fun i=>Z^(ell i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ))
          (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) ((2:ℝ)^j)
          (Z^(1+lowSelectedLength ell J)) V hV
      Summable f ∧ Summable (fun j=>‖f j‖) ∧
        (∑'j : ℕ,‖f j‖)≤C*Z^(5/72+255*ε+2*εG:ℝ) ∧
        ‖∑'j : ℕ,f j‖≤C*Z^(5/72+255*ε+2*εG:ℝ) := by
  obtain ⟨degree,C,hC,he⟩ := central_square_gaussian_dyad η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hM hW0 hW1 hW0s hWM
  obtain ⟨Cm,hCm,hm⟩ := gaussianJointMoment_summed V hV degree εG hεG
  refine ⟨C*Cm,mul_pos hC hCm,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZ0 T hT hout hdis hnorm J W hW
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then (0:ℂ) else
    gaussianSectorDyad SquareNumerator η S hS W0 W1 (a0*a1) (max 1 (b0*b1))
      (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (fun i=>canonicalSlotSupport (T i)) (fun i=>canonicalSlotSupport_nonzero _ (hT i))
      J W (fun i=>Z^(ell i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ))
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) ((2:ℝ)^j) R V hV
  obtain ⟨hsm,hmb⟩ := hm R (by dsimp [R];positivity)
  have hb (j : ℕ) : ‖f j‖ ≤ (C*Z^(5/72+255*ε:ℝ))*
      (((2:ℝ)^j)^εG*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := by
    dsimp only [f]
    split_ifs with hj
    · rw [norm_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo,hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength ell J) ε ((2:ℝ)^j) hZ0 hj
      apply (hZ.2 hZ0 T hT hout hdis hnorm J ((2:ℝ)^j) (by positivity) hlo hhi W hW V hV).trans
      have hp : 1≤((2:ℝ)^j)^εG := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hεG.le
      exact mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp) (by positivity)
  have hsn := Summable.of_nonneg_of_le (fun j=>norm_nonneg (f j)) hb (hsm.mul_left (C*Z^(5/72+255*ε:ℝ)))
  have hbound : (∑'j : ℕ,‖f j‖) ≤ (C*Cm)*Z^(5/72+255*ε+2*εG:ℝ) := by
    calc
      _ ≤ ∑'j : ℕ,(C*Z^(5/72+255*ε:ℝ))*(((2:ℝ)^j)^εG*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) :=
        hsn.tsum_le_tsum hb (hsm.mul_left _)
      _ = (C*Z^(5/72+255*ε:ℝ))*(∑'j : ℕ,((2:ℝ)^j)^εG*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := tsum_mul_left
      _ ≤ (C*Z^(5/72+255*ε:ℝ))*(Cm*R^εG) := mul_le_mul_of_nonneg_left hmb (by positivity)
      _ ≤ _ := by
        dsimp only [R]
        rw [←Real.rpow_mul hZ0.le]
        calc
          _=(C*Cm)*(Z^(5/72+255*ε:ℝ)*Z^((1+lowSelectedLength ell J)*εG)) := by ring
          _≤_ := by
            rw [←Real.rpow_add hZ0]
            apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
            have hh := lowLength_bounds ell hell hsum J
            exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith)
  exact ⟨hsn.of_norm,hsn,hbound,(norm_tsum_le_tsum_norm hsn).trans hbound⟩

end OpenAIReview.SquareGaussianPayment
#lint+ in OpenAIReview.SquareGaussianPayment

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
  unless declarations > 0 do throwError "Empty square Gaussian payment audit."
  logInfo m!"Square Gaussian payment audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-square-gaussian-payment"
  IO.FS.writeFile ".lake/arithmetic-operator-square-gaussian-payment/axioms.json"
    (Json.mkObj [("scope", toJson "actual central Gaussian square sum5/72+255epsilon+2epsilonG with absolute summability, genuine inner/outer sector integrability and exact original dyad ledger; remoteAll unsplit; source normalizer not newly formalized; no subset source"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
