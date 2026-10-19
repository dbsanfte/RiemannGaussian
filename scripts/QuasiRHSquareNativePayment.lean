/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHSquareSectorIntegral
import scripts.QuasiRHUnselectedWeightedMassAudit
import OAI.NumberTheory.DirichletL.Detector.LowCentralTuple

/-!
Actual Mellin-normalized central square tuples, using the original selected
inverse row, the native normalized companion theorem, and the actual tuple
mass. No source is assigned to a numerator sector. The whole remote family
and the whole original Probe minus F_all ledger remain separate.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical ContDiff BigOperators
open MeasureTheory
namespace OpenAIReview.SquareNativePayment
open OAI OAI.SevenEighths OAI.CompletedGauss
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.CubicSieve
open RayFourExpansion CanonicalQuadraticSieve SquareSectorTransfer
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Exact positive monomial identity used only to apply the native bound at
the original compensated scales. -/
theorem source_monomial (c Z L r s : ℝ) (hc : 0≤c) (hZ : 0<Z) (hL : 0<L) :
    (c*Z^r/L)^s = c^s*Z^(r*s)*L^(-s) := by
  rw [Real.div_rpow (by positivity) hL.le, Real.mul_rpow hc (by positivity),
    ←Real.rpow_mul hZ.le, Real.rpow_neg hL.le]
  ring

/-- The exact square root range at the literal original physical scale. -/
theorem source_root_range (c Z L : ℝ) (hc : 0<c) (hZ : 0<Z) (hL : 0<L) :
    Real.sqrt (c*Z^(5/6:ℝ)/L^2) = Real.sqrt c*Z^(5/12:ℝ)/L := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul hc.le, Real.sqrt_sq hL.le]
  simp only [Real.sqrt_eq_rpow]
  rw [←Real.rpow_mul hZ.le]
  norm_num

/-- Literal profile energy at the original scales retains the favorable
L^(-1/6) after taking its square root. The small energy loss is bounded by
Z^epsilon; the exact intermediate coefficient is 21epsilon/32. -/
theorem source_square_factor (ε : ℝ) (hε : 0<ε) (c k B : ℝ)
    (hc : 0<c) (hk : 1≤k) :
    ∃ C : ℝ, 0<C ∧ ∀ Z L : ℝ, 1≤Z → 1≤L →
      let A := c*Z^(5/12:ℝ)/L
      let Y := Z^(23/48:ℝ)/L
      Real.sqrt (B^2*A^ε*(A*(k*Y))^ε*((k*Y)/Y)^2*
        (A^(1/3:ℝ)+A^(4/3:ℝ)/(k*Y))) ≤
        C*Z^(5/72+ε:ℝ)*L^(-(1/6:ℝ)) := by
  let C0 := B^2*c^ε*(c*k)^ε*k^2*(c^(1/3:ℝ)+c^(4/3:ℝ)/k)
  refine ⟨Real.sqrt C0+1, by positivity, ?_⟩
  intro Z L hZ hL
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hk0 : 0<k := lt_of_lt_of_le zero_lt_one hk
  dsimp only
  have hA : (c*Z^(5/12:ℝ)/L)^ε ≤ c^ε*Z^((5/12:ℝ)*ε) := by
    calc
      _ ≤ (c*Z^(5/12:ℝ))^ε := Real.rpow_le_rpow (by positivity)
        (div_le_self (by positivity) hL) hε.le
      _ = _ := by rw [Real.mul_rpow hc.le (by positivity), ←Real.rpow_mul hz.le]
  have hAP : ((c*Z^(5/12:ℝ)/L)*(k*(Z^(23/48:ℝ)/L)))^ε ≤
      (c*k)^ε*Z^((43/48:ℝ)*ε) := by
    have he : (c*Z^(5/12:ℝ)/L)*(k*(Z^(23/48:ℝ)/L)) = (c*k)*Z^(43/48:ℝ)/L^2 := by
      have hp : Z^(5/12:ℝ)*Z^(23/48:ℝ)=Z^(43/48:ℝ) := by rw [←Real.rpow_add hz];norm_num
      rw [←hp]
      ring
    rw [he]
    calc
      _ ≤ ((c*k)*Z^(43/48:ℝ))^ε := Real.rpow_le_rpow (by positivity)
        (div_le_self (by positivity) (one_le_pow₀ hL)) hε.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), ←Real.rpow_mul hz.le]
  have hratio : (k*(Z^(23/48:ℝ)/L))/(Z^(23/48:ℝ)/L)=k := by field_simp
  have ha := source_monomial c Z L (5/12) (1/3) hc.le hz hl
  norm_num at ha
  have hb : (c*Z^(5/12:ℝ)/L)^(4/3:ℝ)/(k*(Z^(23/48:ℝ)/L)) =
      (c^(4/3:ℝ)/k)*Z^(11/144:ℝ)*L^(-(1/3:ℝ)) := by
    rw [source_monomial c Z L (5/12) (4/3) hc.le hz hl]
    have hz1 : Z^((5/12:ℝ)*(4/3))/Z^(23/48:ℝ) = Z^(11/144:ℝ) := by
      rw [←Real.rpow_sub hz];norm_num
    have hl1 : L^(-(4/3:ℝ))*L=L^(-(1/3:ℝ)) := by
      calc
        _ = L^(-(4/3:ℝ))*L^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hl];norm_num
    calc
      _ = (c^(4/3:ℝ)/k)*(Z^((5/12:ℝ)*(4/3))/Z^(23/48:ℝ))*(L^(-(4/3:ℝ))*L) := by field_simp
      _ = _ := by rw [hz1,hl1]
  have hbase : (c*Z^(5/12:ℝ)/L)^(1/3:ℝ) +
      (c*Z^(5/12:ℝ)/L)^(4/3:ℝ)/(k*(Z^(23/48:ℝ)/L)) ≤
      (c^(1/3:ℝ)+c^(4/3:ℝ)/k)*Z^(5/36:ℝ)*L^(-(1/3:ℝ)) := by
    rw [ha,hb]
    have hp := Real.rpow_le_rpow_of_exponent_le hZ (show (11/144:ℝ)≤5/36 by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
      (show 0≤c^(4/3:ℝ)/k by positivity)) (show 0≤L^(-(1/3:ℝ)) by positivity)]
  have hF : B^2*(c*Z^(5/12:ℝ)/L)^ε*
      ((c*Z^(5/12:ℝ)/L)*(k*(Z^(23/48:ℝ)/L)))^ε*
      ((k*(Z^(23/48:ℝ)/L))/(Z^(23/48:ℝ)/L))^2*
      ((c*Z^(5/12:ℝ)/L)^(1/3:ℝ)+(c*Z^(5/12:ℝ)/L)^(4/3:ℝ)/(k*(Z^(23/48:ℝ)/L))) ≤
      C0*Z^(5/36+(21/16)*ε:ℝ)*L^(-(1/3:ℝ)) := by
    rw [hratio]
    calc
      _ ≤ B^2*(c^ε*Z^((5/12:ℝ)*ε))*((c*k)^ε*Z^((43/48:ℝ)*ε))*k^2*
          ((c^(1/3:ℝ)+c^(4/3:ℝ)/k)*Z^(5/36:ℝ)*L^(-(1/3:ℝ))) := by gcongr
      _ = _ := by
        have hp : Z^((5/12:ℝ)*ε)*Z^((43/48:ℝ)*ε)*Z^(5/36:ℝ)=Z^(5/36+(21/16)*ε:ℝ) := by
          rw [←Real.rpow_add hz, ←Real.rpow_add hz]
          congr 1
          ring
        dsimp [C0]
        calc
          _ = B^2*c^ε*(c*k)^ε*k^2*(c^(1/3:ℝ)+c^(4/3:ℝ)/k)*
            (Z^((5/12:ℝ)*ε)*Z^((43/48:ℝ)*ε)*Z^(5/36:ℝ))*L^(-(1/3:ℝ)) := by ring
          _ = _ := by rw [hp]
  apply (Real.sqrt_le_sqrt hF).trans
  rw [Real.sqrt_mul (show 0≤C0*Z^(5/36+(21/16)*ε:ℝ) by dsimp [C0];positivity),
    Real.sqrt_mul (show 0≤C0 by dsimp [C0];positivity)]
  simp only [Real.sqrt_eq_rpow]
  rw [←Real.rpow_mul hz.le, ←Real.rpow_mul hl.le]
  have hp : Z^((5/36+(21/16)*ε)*(1/2):ℝ) ≤ Z^(5/72+ε:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  convert mul_le_mul_of_nonneg_right
    (mul_le_mul (show C0^(1/2:ℝ) ≤ C0^(1/2:ℝ)+1 by linarith) hp (by positivity) (by positivity))
    (show 0≤L^(-(1/6:ℝ)) by positivity) using 1
  norm_num


/-- Actual original square integral at the native compensated scales. This
intermediate estimate keeps the full companion mass visible; the next theorem
pays it with the imported actual normalized inverse-row bound. -/
theorem actual_square_source_scale (ε : ℝ) (hε : 0<ε)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW0s : ContDiff ℝ ∞ W0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1) (hB1 : 0≤B1) (hWB1 : ∀t, ‖W1 t‖≤B1)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (a b : ℝ) (ha : 0<a) (hb : 1≤b) :
    ∃ C : ℝ, 0<C ∧ ∀ Z L : ℝ, 1≤Z → 1≤L →
      ∀ (hX : 1≤Z^(17/48:ℝ)/L) (hY : 1≤Z^(23/48:ℝ)/L) (B : RayRing → O → ℂ),
      let Ccal := calibrationForSet S hS
      let X := Z^(17/48:ℝ)/L
      let Y := Z^(23/48:ℝ)/L
      let Q := lowPhysicalScale Ccal X Y
      let hXp := lt_of_lt_of_le zero_lt_one hX
      let hYp := lt_of_lt_of_le zero_lt_one hY
      let hbp := lt_of_lt_of_le zero_lt_one hb
      ‖∫v : ℝ, physicalSector (squareRows a b ha hbp Q (lowPhysicalScale_pos Ccal X Y hXp hYp))
          Ccal W0 W1 a b X Y B v‖ ≤
        C*Z^(5/72+ε:ℝ)*L^(-(1/6:ℝ))*lowInverseMass Ccal a b ha hbp X Y hXp hYp B := by
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  obtain ⟨D,hD,hi⟩ := SquareSectorIntegral.actual_square_integral_bound ε ε hε hε
    W0 a0 b0 ha0 hW0 hW0s
  let Ccal := calibrationForSet S hS
  let q := elementNorm Ccal.generator
  let k := max 1 b1
  let c := Real.sqrt (2*b*q)
  have hq : 0<q := calibration_elementNorm_pos Ccal
  have hb0 : 0<b := lt_of_lt_of_le zero_lt_one hb
  have hc : 0<c := by dsimp [c];positivity
  obtain ⟨Cf,hCf,hf⟩ := source_square_factor ε hε c k (B1*a1^(-(1/2:ℝ))) hc (le_max_left _ _)
  refine ⟨D*Cf, by positivity, ?_⟩
  intro Z L hZ hL hX hY B
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  let X := Z^(17/48:ℝ)/L
  let Y := Z^(23/48:ℝ)/L
  have hx : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hP : 1≤k*Y := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hY
  have hcut : b1*Y≤k*Y := mul_le_mul_of_nonneg_right (le_max_right _ _) hy.le
  have hQpos := lowPhysicalScale_pos Ccal X Y hx hy
  have hA : 1≤Real.sqrt (2*b*lowPhysicalScale Ccal X Y) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    norm_num only [one_pow]
    exact one_le_mul_of_one_le_of_one_le (by linarith)
      (lowPhysicalScale_ge_one Ccal X Y hX hY)
  have hroot : Real.sqrt (2*b*lowPhysicalScale Ccal X Y) = c*Z^(5/12:ℝ)/L := by
    dsimp only [X,Y]
    rw [lowPhysicalScale_source Ccal Z L hz]
    have he : 2*b*(elementNorm Ccal.generator*Z^(5/6:ℝ)/L^2) =
        (2*b*q)*Z^(5/6:ℝ)/L^2 := by dsimp [q];ring
    rw [he,source_root_range _ Z L (by positivity) hz hl]
  have he := hi S hS W1 hW1c a1 b1 B1 ha1 hB1 hW1 hWB1 a b ha hb0 X Y (k*Y) hx hy hP hcut hA B
  dsimp only at he ⊢
  rw [hroot] at he
  have hf0 := hf Z L hZ hL
  dsimp only at hf0
  have hm := lowInverseMass_nonneg Ccal a b ha hb0 X Y hx hy B
  calc
    _ ≤ D*Real.sqrt ((B1*a1^(-(1/2:ℝ)))^2*(c*Z^(5/12:ℝ)/L)^ε*
      ((c*Z^(5/12:ℝ)/L)*(k*Y))^ε*((k*Y)/Y)^2*
      ((c*Z^(5/12:ℝ)/L)^(1/3:ℝ)+(c*Z^(5/12:ℝ)/L)^(4/3:ℝ)/(k*Y))) *
        lowInverseMass Ccal a b ha hb0 X Y hx hy B := he
    _ ≤ D*(Cf*Z^(5/72+ε:ℝ)*L^(-(1/6:ℝ)))*lowInverseMass Ccal a b ha hb0 X Y hx hy B := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf0 hD.le) hm
    _ = _ := by ring

/-- The literal original tuple ranges eventually exceed one uniformly over
all actual unselected products. No physical cutoff or norm is assumed free. -/
theorem eventually_compensated_ranges (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1≤Z ∧ ∀ L : ℝ, 1≤L → L≤B*Z^(1/6:ℝ) →
      1≤Z^(17/48:ℝ)/L ∧ 1≤Z^(23/48:ℝ)/L := by
  have he := (tendsto_rpow_atTop (show 0<(3/16:ℝ) by norm_num)).eventually (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),he] with Z hZ hB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  refine ⟨hZ, ?_⟩
  intro L hL hLB
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLX : L≤Z^(17/48:ℝ) := calc
    L≤B*Z^(1/6:ℝ) := hLB
    _≤Z^(3/16:ℝ)*Z^(1/6:ℝ) := mul_le_mul_of_nonneg_right hB (by positivity)
    _=Z^(17/48:ℝ) := by rw [←Real.rpow_add hz];norm_num
  exact ⟨(le_div_iff₀ hl).mpr (by simpa using hLX),
    (le_div_iff₀ hl).mpr (by simpa using (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ (show (17/48:ℝ)≤23/48 by norm_num))))⟩


/-- Literal original square restriction with its ORIGINAL Mellin normalizer.
This is only an abbreviation of existing native functions, not a new source
carrier or a modified companion row. -/
def normalizedSquareIntegral (C : CalibrationData) (W0 W1 : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (B : RayRing → O → ℂ) : ℂ :=
  ((Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
    ∫v : ℝ, physicalSector (squareRows a b ha hb (lowPhysicalScale C X Y)
      (lowPhysicalScale_pos C X Y hX hY)) C W0 W1 a b X Y B v

/-- Native central single-tuple payment, with the actual selected inverse
row, all selected marks and cubes, and the ORIGINAL moving spectral window.
The full companion energy and Mellin normalization are discharged. -/
theorem native_square_tuple (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J),
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      let L := elementNorm (∏i : J,(p i).val)
      ∀(hX0 : 0<Z^(17/48:ℝ)/L)(hY0 : 0<Z^(23/48:ℝ)/L),
      ‖normalizedSquareIntegral (calibrationForSet S hS) W0 W1
        (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) hX0 hY0
        (lowSelectedInverseRow Finset.univ
          (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
          η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t)‖ ≤
        C*(1+‖t‖)^degree*Z^(5/72+255*ε:ℝ)*L^(-(1/6:ℝ)) := by
  obtain ⟨Cp,hCp,hphysical⟩ := actual_square_source_scale ε hε W0 W1 a0 b0 a1 b1 M ha0 ha1
    hW0 hW0s hW1 hM hWM S hS (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1) (le_max_left _ _)
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized η S hS hbad ell hell hsum
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1
  refine ⟨degree,Cp*Ci,by positivity,?_⟩
  filter_upwards [hinverse,eventually_compensated_ranges ((max 1 b)^K)] with Z hInv hRange
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
  dsimp only
  intro hX0 hY0
  let slots := fun i=>canonicalSlotSupport (T i)
  let L := elementNorm (∏i : J,(p i).val)
  let Ccal := calibrationForSet S hS
  let Q := lowPhysicalScale Ccal (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η slots J W (fun i=>Z^(ell i)) t) η S hS (lowSelectedIdeal slots J) X t
  have hz : 0<Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hLge : 1≤L := lowUnselectedProduct_norm_ge_one slots hslots J p
  have hnormE : ∀i n,n∈slots i→elementNorm n≤max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hLhi := lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z (le_max_left _ _) hInv.1.le slots hnormE J p
  have hr := hRange.2 L hLge hLhi
  have hp := hphysical Z L hInv.1.le hLge hr.1 hr.2 row
  have hi := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t hX0 hY0
  have hQ : 0<Q := lowPhysicalScale_pos Ccal _ _ hX0 hY0
  unfold normalizedSquareIntegral
  rw [norm_mul,low_mellin_normalizer_norm _ hQ]
  have hN : 0≤(Real.sqrt Q)⁻¹/(2*Real.pi) := by positivity
  calc
    _ ≤ ((Real.sqrt Q)⁻¹/(2*Real.pi)) *
      (Cp*Z^(5/72+ε:ℝ)*L^(-(1/6:ℝ))*lowInverseMass Ccal _ _ _ _ _ _ hX0 hY0 row) :=
      mul_le_mul_of_nonneg_left hp hN
    _ = (Cp*Z^(5/72+ε:ℝ)*L^(-(1/6:ℝ))) *
      ((Real.sqrt Q)⁻¹/(2*Real.pi)*lowInverseMass Ccal _ _ _ _ _ _ hX0 hY0 row) := by ring
    _ ≤ (Cp*Z^(5/72+ε:ℝ)*L^(-(1/6:ℝ)))*(Ci*(1+‖t‖)^degree*Z^(507*ε/2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (Cp*Ci)*(1+‖t‖)^degree*(Z^(5/72+ε:ℝ)*Z^(507*ε/2))*L^(-(1/6:ℝ)) := by ring
    _ ≤ _ := by
      rw [←Real.rpow_add hz]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hInv.1.le (by linarith)) (by positivity)) (by positivity)


/-- The actual joined central square family is paid after summing the literal
unselected tuples. The selected inverse row is unchanged and theta=-1/6 is
paid by the existing actual supported-ideal tuple mass. This is a bound on
the original central square summands, not a source identification. -/
theorem native_square_joined (η : HeckeFamily.Character) (S : Finset Id)
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
    ∀(J : Finset (Fin K))(X : ℝ),0<X→
      Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      let slots := fun i=>canonicalSlotSupport (T i)
      let hslots := fun i=>canonicalSlotSupport_nonzero _ (hT i)
      let row := lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η slots J W (fun i=>Z^(ell i)) t) η S hS (lowSelectedIdeal slots J) X t
      ‖∑p : LowUnselectedTuple slots J,
        lowUnselectedWeight slots J W (fun i=>Z^(ell i)) p *
          normalizedSquareIntegral (calibrationForSet S hS) W0 W1
            (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
            (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
            (Z^(17/48:ℝ)/elementNorm (∏i : J,(p i).val))
            (Z^(23/48:ℝ)/elementNorm (∏i : J,(p i).val))
            (div_pos (Real.rpow_pos_of_pos hZ0 _) (lowUnselectedProduct_norm_pos slots hslots J p))
            (div_pos (Real.rpow_pos_of_pos hZ0 _) (lowUnselectedProduct_norm_pos slots hslots J p)) row‖ ≤
        C*(1+‖t‖)^degree*Z^(5/72+255*ε:ℝ) := by
  obtain ⟨degree,Ct,hCt,htuple⟩ := native_square_tuple η S hS hbad ell hell hsum a b ε ha hε hε1
    W0 W1 a0 b0 a1 b1 M ha0 ha1 hM hW0 hW1 hW0s hWM
  obtain ⟨Cm,hCm,hmass⟩ := UnselectedWeightedMass.lowUnselectedWeightedMass_bound K 1 (-(1/6:ℝ))
    (by norm_num) (by norm_num)
  refine ⟨degree,Ct*Cm,by positivity,?_⟩
  filter_upwards [htuple] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZ0 T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  dsimp only
  let slots := fun i=>canonicalSlotSupport (T i)
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η slots J W (fun i=>Z^(ell i)) t) η S hS (lowSelectedIdeal slots J) X t
  let I (p : LowUnselectedTuple slots J) := normalizedSquareIntegral (calibrationForSet S hS) W0 W1
    (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (Z^(17/48:ℝ)/elementNorm (∏i : J,(p i).val)) (Z^(23/48:ℝ)/elementNorm (∏i : J,(p i).val))
    (div_pos (Real.rpow_pos_of_pos hZ0 _) (lowUnselectedProduct_norm_pos slots hslots J p))
    (div_pos (Real.rpow_pos_of_pos hZ0 _) (lowUnselectedProduct_norm_pos slots hslots J p)) row
  have hp (p : LowUnselectedTuple slots J) : ‖I p‖ ≤
      Ct*(1+‖t‖)^degree*Z^(5/72+255*ε:ℝ)*elementNorm (∏i : J,(p i).val)^(-(1/6:ℝ)) :=
    hZ.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t _ _
  change ‖∑p : LowUnselectedTuple slots J, lowUnselectedWeight slots J W (fun i=>Z^(ell i)) p*I p‖ ≤ _
  calc
    _ ≤ ∑p : LowUnselectedTuple slots J, ‖lowUnselectedWeight slots J W (fun i=>Z^(ell i)) p*I p‖ := norm_sum_le _ _
    _ = ∑p : LowUnselectedTuple slots J, ‖lowUnselectedWeight slots J W (fun i=>Z^(ell i)) p‖*‖I p‖ := by
      simp_rw [norm_mul]
    _ ≤ ∑p : LowUnselectedTuple slots J, ‖lowUnselectedWeight slots J W (fun i=>Z^(ell i)) p‖*
        (Ct*(1+‖t‖)^degree*Z^(5/72+255*ε:ℝ)*elementNorm (∏i : J,(p i).val)^(-(1/6:ℝ))) :=
      Finset.sum_le_sum (fun p _=>mul_le_mul_of_nonneg_left (hp p) (norm_nonneg _))
    _ = (Ct*(1+‖t‖)^degree*Z^(5/72+255*ε:ℝ))*
        ∑p : LowUnselectedTuple slots J, ‖lowUnselectedWeight slots J W (fun i=>Z^(ell i)) p‖*
          elementNorm (∏i : J,(p i).val)^(-(1/6:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (Ct*(1+‖t‖)^degree*Z^(5/72+255*ε:ℝ))*Cm :=
      mul_le_mul_of_nonneg_left (hmass T hT J W (fun i=>Z^(ell i)) hW) (by positivity)
    _ = _ := by ring

end OpenAIReview.SquareNativePayment
#lint+ in OpenAIReview.SquareNativePayment

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
  unless declarations > 0 do throwError "Empty native square payment audit."
  logInfo m!"Native square payment audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-square-native-payment"
  IO.FS.writeFile ".lake/arithmetic-operator-square-native-payment/axioms.json"
    (Json.mkObj [("scope", toJson "actual central-window Mellin-normalized square integral and joined native tuple payment at5/72+255epsilon; actual selected inverse row and theta=-1/6 tuple mass; no whole Gaussian/source normalization or source allocation"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
