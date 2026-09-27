/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMarkedPrimeCompletion

/-!
# The joint logarithmic-derivative bridge at the marked rectangle

The proper-prime-power difference is paid inside the full ordered cofactor
and paired Fourier integral. The high marked order supplies the saving;
the least prime, every middle order and both frequencies remain correlated.
This does not bound the resulting signed main response.
-/

namespace RiemannGaussian.ZetaRieszMarkedLogDerivative
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError ZetaRieszOrderedEulerBound
open ZetaRieszMainFrequency ZetaRieszMarkedSeparation ZetaRieszRoughEulerTransfer
open ZetaRieszMarkedPrimeCompletion ZetaExposedPrimeMoments

/-- No order-zero mark occurs in the literal rectangle. This does not
delete any order from the middle or least-prime slots. -/
theorem marked_order_pos {N j h : ℕ}
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) : 0 < j := by
  have hb := (Finset.mem_filter.mp hh).2
  omega

/-- The complete von Mangoldt difference, divided by its marked order.
The unused order-zero value retains the original prime difference. -/
def logDifference : ℕ → ℂ → ℝ → ℂ
  | 0, s, xi => completeDifference 0 s xi
  | k+1, s, xi => (zetaPrimeLogMoment k s-zetaPrimeLogMoment k (s+Complex.I*xi))/(k+1)

/-- The actual proper-prime-power difference, with both frequencies. -/
def properDifference : ℕ → ℂ → ℝ → ℂ
  | 0, _, _ => 0
  | k+1, s, xi =>
    (zetaProperPrimePowerMoment k s-zetaProperPrimePowerMoment k (s+Complex.I*xi))/(k+1)

theorem logDifference_split (j : ℕ) {s : ℂ} (hs : 1 < s.re) (xi : ℝ) :
    logDifference j s xi = completeDifference j s xi+properDifference j s xi := by
  cases j with
  | zero => simp [logDifference,properDifference]
  | succ k =>
    have ht : 1 < (s+Complex.I*xi).re := by simpa using hs
    rw [logDifference,properDifference,completeDifference,
      ordinaryPrimeMoment_succ hs,ordinaryPrimeMoment_succ ht,
      zetaPrimeLogMoment_eq_prime_add_proper k hs,
      zetaPrimeLogMoment_eq_prime_add_proper k ht]
    push_cast
    ring

/-- This is an equality of convergent prime-power series, including
the vanishing Fourier difference at the origin. -/
theorem properDifference_series (k : ℕ) {s : ℂ} (hs : 1/2 < s.re) (xi : ℝ) :
    properDifference (k+1) s xi =
      (∑' p : ℕ, (zetaProperPrimePowerCoefficient p : ℂ)*
        PowerSeries.coeff k (leg s xi p))/(k+1) := by
  have ht : 1/2 < (s+Complex.I*xi).re := by simpa using hs
  rw [properDifference,zetaProperPrimePowerMoment,zetaProperPrimePowerMoment,
    ← (summable_zetaProperPrimePowerMoment k hs).tsum_sub
      (summable_zetaProperPrimePowerMoment k ht)]
  congr 1
  apply tsum_congr
  intro p
  rw [coeff_leg_difference,mul_sub]

/-- A larger radius is available to every proper-prime-power leg. -/
theorem properDifference_bound (k : ℕ) (y xi : ℝ)
    (f : ℕ → ℝ) (_hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p)
    (hw : Summable (fun p => zetaProperPrimePowerCoefficient p*
      zetaPrimeExpWeight (3/4) p*f p)) :
    ‖properDifference (k+1) (3/2+Complex.I*y) xi‖ ≤
      (3/4 : ℝ)⁻¹^k*(∑' p, zetaProperPrimePowerCoefficient p*
        zetaPrimeExpWeight (3/4) p*f p) := by
  have hc (p : ℕ) :
      ‖(zetaProperPrimePowerCoefficient p : ℂ)*
        PowerSeries.coeff k (leg (3/2+Complex.I*y) xi p)‖ ≤
      (3/4 : ℝ)⁻¹^k*(zetaProperPrimePowerCoefficient p*
        zetaPrimeExpWeight (3/4) p*f p) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (zetaProperPrimePowerCoefficient_nonneg p)]
    have h := (norm_leg_le p k (3/2+Complex.I*y) xi (by norm_num : (0 : ℝ) < 3/4)).trans
      (mul_le_mul_of_nonneg_right (hphase p) (by unfold zetaPrimeExpWeight; positivity))
    have h := mul_le_mul_of_nonneg_left h (zetaProperPrimePowerCoefficient_nonneg p)
    simpa only [show (3/2+Complex.I*(y : ℂ)).re-(3/4 : ℝ) = 3/4 by norm_num,
      mul_assoc,mul_comm,mul_left_comm] using h
  have hsum := (hw.mul_left ((3/4 : ℝ)⁻¹^k)).of_norm_bounded hc
  rw [properDifference_series k (by norm_num) xi,norm_div]
  have hk : 1 ≤ ‖((k : ℂ)+1)‖ := by
    norm_cast
    omega
  apply (div_le_self (norm_nonneg _) hk).trans
  exact (norm_tsum_le_tsum_norm hsum.norm).trans
    ((hsum.norm.tsum_le_tsum hc (hw.mul_left ((3/4 : ℝ)⁻¹^k))).trans_eq tsum_mul_left)

/-- The exact high-order window converts the larger proper-power
radius to an exponential saving at the common cofactor radius. -/
theorem proper_radius_saving {N k h : ℕ}
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N (k+1)) :
    (3/4 : ℝ)⁻¹^k ≤ Real.exp (-(N : ℝ)/10)*safeRadius⁻¹^(k+1) := by
  have hb := (Finset.mem_filter.mp hh).2
  have hj : 21*(N : ℝ) ≤ 40*((k : ℝ)+1) := by exact_mod_cast hb.2.1
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3/2)
  norm_num only [inv_div,one_div] at hlog
  have hp : (2/3 : ℝ)^(k+1) ≤ Real.exp (-(N : ℝ)/10) := by
    rw [show (2/3 : ℝ) = (3/2 : ℝ)⁻¹ by norm_num,inv_pow,
      ← Real.exp_log (by positivity : (0 : ℝ) < (3/2)^ (k+1)),Real.log_pow,
      ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ (k : ℝ)+1 by positivity)]
  have hR : (3/4 : ℝ)⁻¹ ≤ (2/3)*safeRadius⁻¹ := by norm_num [safeRadius]
  calc
    _ ≤ (3/4 : ℝ)⁻¹^(k+1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ (3/4)⁻¹) k]
    _ ≤ ((2/3)*safeRadius⁻¹)^(k+1) :=
      pow_le_pow_left₀ (by norm_num) hR _
    _ = (2/3 : ℝ)^(k+1)*safeRadius⁻¹^(k+1) := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity [safeRadius_pos])

/-- The proper-power saving is available uniformly on the exact box. -/
theorem proper_marked_bound (N j h : ℕ)
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) (y xi : ℝ)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p)
    (hw : Summable (fun p => zetaProperPrimePowerCoefficient p*
      zetaPrimeExpWeight (3/4) p*f p)) :
    ‖properDifference j (3/2+Complex.I*y) xi‖ ≤
      (Real.exp (-(N : ℝ)/10)*safeRadius⁻¹^j)*
        ∑' p, zetaProperPrimePowerCoefficient p*zetaPrimeExpWeight (3/4) p*f p := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (marked_order_pos hh))
  exact (properDifference_bound k y xi f hf hphase hw).trans
    (mul_le_mul_of_nonneg_right (proper_radius_saving hh)
      (tsum_nonneg (fun p => mul_nonneg (mul_nonneg
        (zetaProperPrimePowerCoefficient_nonneg p) (Real.exp_pos _).le) (hf p))))

/-- A single finite rectangle costs at most its quadratic cardinality. -/
theorem rectangle_sum_bound (N : ℕ) (F : ℕ → ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ∈ Finset.range (N+2), ∀ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
      ‖F j h‖ ≤ B) :
    ‖∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j, F j h‖ ≤
      ((N : ℝ)+2)^2*B := by
  have hc (j : ℕ) : ((ZetaRieszSkewAllocation.rectangleOrders N j).card : ℝ) ≤ (N : ℝ)+2 := by
    have h := Finset.card_le_card
      (show ZetaRieszSkewAllocation.rectangleOrders N j ⊆ Finset.range (N+1-j+1) from
        Finset.filter_subset _ _)
    rw [Finset.card_range] at h
    exact_mod_cast (show (ZetaRieszSkewAllocation.rectangleOrders N j).card ≤ N+2 by omega)
  calc
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j, ‖F j h‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ _h ∈ ZetaRieszSkewAllocation.rectangleOrders N j, B :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun h hh => hb j hj h hh))
    _ ≤ ∑ _j ∈ Finset.range (N+2), ((N : ℝ)+2)*B := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (hc j) hB
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; push_cast; ring

/-- The proper-power error is still multiplied by the literal ordered
cofactor, with the same correlated total order. -/
def properSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    properDifference j s xi*cofactor A N j h s xi

/-- The main symbol with a complete logarithmic-derivative marked leg. -/
def logSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    logDifference j s xi*cofactor A N j h s xi

theorem logSymbol_split (A : Finset ℕ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) (xi : ℝ) :
    logSymbol A N s xi = completedSymbol A N s xi+properSymbol A N s xi := by
  simp only [logSymbol,logDifference_split _ hs,add_mul,Finset.sum_add_distrib,
    completedSymbol,properSymbol]

/-- The entire coupled symbol is estimated; there is no norm or limit
claim for a separately masked prime leg. -/
theorem properSymbol_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p)
    (hw : Summable (fun p => zetaPrimeExpWeight (3/2-safeRadius) p*f p))
    (hpw : Summable (fun p => zetaProperPrimePowerCoefficient p*zetaPrimeExpWeight (3/4) p*f p))
    {V : ℝ} (hV : (∑' p, zetaPrimeExpWeight (3/2-safeRadius) p*f p) ≤ V)
    (hPV : (∑' p, zetaProperPrimePowerCoefficient p*zetaPrimeExpWeight (3/4) p*f p) ≤ V) :
    ‖properSymbol A N (3/2+Complex.I*y) xi‖ ≤
      mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*V^2 := by
  have hR := safeRadius_pos
  have hv0 : 0 ≤ V := (tsum_nonneg (fun p => mul_nonneg (Real.exp_pos _).le (hf p))).trans hV
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*f r) ≤ V :=
    (hw.sum_le_tsum A (fun p _ => mul_nonneg (Real.exp_pos _).le (hf p))).trans hV
  let B := Real.exp (4*mass (3/2-safeRadius))/safeRadius^(N+1)*
    Real.exp (-(N : ℝ)/10)*V^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ha (j : ℕ) (hj : j ∈ Finset.range (N+2)) (h : ℕ)
      (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) :
      ‖properDifference j (3/2+Complex.I*y) xi*cofactor A N j h (3/2+Complex.I*y) xi‖ ≤ B := by
    have he : j+(N+1-j) = N+1 := by have := Finset.mem_range.mp hj; omega
    have hm := (proper_marked_bound N j h hh y xi f hf hphase hpw).trans
      (mul_le_mul_of_nonneg_left hPV (by positivity))
    have hc := cofactor_bound A h16 N j h hh
      (show 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius by norm_num [safeRadius]) xi f hf hphase
    simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at hc
    have hc := hc.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    rw [norm_mul]
    apply (mul_le_mul hm hc (norm_nonneg _) (by positivity)).trans_eq
    dsimp [B]
    simp only [div_eq_mul_inv,← inv_pow]
    calc
      _ = Real.exp (4*mass (3/2-safeRadius))*
        (safeRadius⁻¹^j*safeRadius⁻¹^(N+1-j))*Real.exp (-(N : ℝ)/10)*V^2 := by ring
      _ = _ := by rw [← pow_add,he]; simp only [div_eq_mul_inv]
  exact (rectangle_sum_bound N _ hB ha).trans_eq (by dsimp [B,mainBudget]; ring)

/-- The extra logarithm needed at the Fourier origin is summable. -/
theorem proper_log_weight_bound (p : ℕ) :
    zetaProperPrimePowerCoefficient p*zetaPrimeExpWeight (3/4) p*Real.log p ≤
      8*(zetaProperPrimePowerCoefficient p*zetaPrimeExpWeight (5/8) p) := by
  have h := norm_zetaPrimeLogKernel_le 1 (3/4 : ℂ) p (by norm_num : (0 : ℝ) < 1/8)
  norm_num only [norm_zetaPrimeLogKernel,pow_one,Nat.factorial_one,Nat.cast_one,
    div_one,Complex.ofReal_re,inv_div,one_div,div_one] at h
  norm_num at h
  have h := mul_le_mul_of_nonneg_left h (zetaProperPrimePowerCoefficient_nonneg p)
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

theorem summable_proper_log_weight :
    Summable (fun p => zetaProperPrimePowerCoefficient p*zetaPrimeExpWeight (3/4) p*Real.log p) :=
  ((summable_zetaProperPrimePowerExpMass (by norm_num : (1/2 : ℝ) < 5/8)).mul_left 8).of_nonneg_of_le
    (fun p => mul_nonneg (mul_nonneg
      (zetaProperPrimePowerCoefficient_nonneg p) (Real.exp_pos _).le)
      (Real.log_natCast_nonneg p)) proper_log_weight_bound

theorem tsum_proper_log_weight_le :
    (∑' p, zetaProperPrimePowerCoefficient p*zetaPrimeExpWeight (3/4) p*Real.log p) ≤
      8*zetaProperPrimePowerExpMass (5/8) := by
  exact (summable_proper_log_weight.tsum_le_tsum proper_log_weight_bound
    ((summable_zetaProperPrimePowerExpMass (by norm_num : (1/2 : ℝ) < 5/8)).mul_left 8)).trans_eq
      (by rw [tsum_mul_left]; rfl)

/-- Shared envelopes for the ordinary least leg and proper-power mark. -/
def jointMass : ℝ := mass (3/2-safeRadius)+zetaProperPrimePowerExpMass (3/4)
/-- The matching logarithmic envelope preserves both Fourier zeros. -/
def jointLogMass : ℝ := logMass (3/2-safeRadius)+8*zetaProperPrimePowerExpMass (5/8)

theorem jointMass_nonneg : 0 ≤ jointMass :=
  add_nonneg (mass_nonneg _) (zetaProperPrimePowerExpMass_nonneg _)

theorem jointLogMass_nonneg : 0 ≤ jointLogMass :=
  add_nonneg (logMass_nonneg (by norm_num [safeRadius]))
    (mul_nonneg (by norm_num) (zetaProperPrimePowerExpMass_nonneg _))

theorem properSymbol_large (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ) :
    ‖properSymbol A N (3/2+Complex.I*y) xi‖ ≤
      4*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*jointMass^2 := by
  have hs : 1 < (3/2 : ℝ)-safeRadius := by norm_num [safeRadius]
  have h := properSymbol_bound A h16 N y xi (fun _ => 2) (fun _ => by norm_num)
    (fun p => phase_le_two p xi) ((summable_zetaPrimeExpWeight hs).mul_right 2)
    ((summable_zetaProperPrimePowerExpMass (by norm_num : (1/2 : ℝ) < 3/4)).mul_right 2)
    (V := jointMass*2)
    (by rw [tsum_mul_right]; unfold jointMass mass; nlinarith [zetaProperPrimePowerExpMass_nonneg (3/4)])
    (by rw [tsum_mul_right]; unfold jointMass zetaProperPrimePowerExpMass; nlinarith [mass_nonneg (3/2-safeRadius)])
  convert h using 1
  ring

theorem properSymbol_small (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ) :
    ‖properSymbol A N (3/2+Complex.I*y) xi‖ ≤
      mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*jointLogMass^2*xi^2 := by
  have hs : 1 < (3/2 : ℝ)-safeRadius := by norm_num [safeRadius]
  have hw : Summable (fun p : ℕ => zetaPrimeExpWeight (3/2-safeRadius) p*(|xi| *Real.log p)) := by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using (summable_log_weight hs).mul_left |xi|
  have hpw : Summable (fun p : ℕ => zetaProperPrimePowerCoefficient p*
      zetaPrimeExpWeight (3/4) p*(|xi| *Real.log p)) := by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using summable_proper_log_weight.mul_left |xi|
  have hV : (∑' p : ℕ, zetaPrimeExpWeight (3/2-safeRadius) p*(|xi| *Real.log p)) ≤
      |xi| *jointLogMass := by
    simp_rw [show ∀ p : ℕ, zetaPrimeExpWeight (3/2-safeRadius) p*(|xi| *Real.log p) =
      |xi| *(Real.log p*zetaPrimeExpWeight (3/2-safeRadius) p) from fun p => by ring]
    rw [tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg xi)
    exact (tsum_log_weight_le hs).trans (le_add_of_nonneg_right
      (by positivity [zetaProperPrimePowerExpMass_nonneg (5/8)]))
  have hPV : (∑' p : ℕ, zetaProperPrimePowerCoefficient p*zetaPrimeExpWeight (3/4) p*
      (|xi| *Real.log p)) ≤ |xi| *jointLogMass := by
    simp_rw [show ∀ p : ℕ, zetaProperPrimePowerCoefficient p*zetaPrimeExpWeight (3/4) p*
      (|xi| *Real.log p) = |xi| *(zetaProperPrimePowerCoefficient p*
        zetaPrimeExpWeight (3/4) p*Real.log p) from fun p => by ring]
    rw [tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg xi)
    exact tsum_proper_log_weight_le.trans (le_add_of_nonneg_left (logMass_nonneg hs))
  have h := properSymbol_bound A h16 N y xi (fun p => |xi| *Real.log p)
    (fun p => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg p))
    (fun p => phase_le_log p xi) hw hpw hV hPV
  simpa only [mul_pow,sq_abs,mul_assoc,mul_comm,mul_left_comm] using h

/-- Both original Fourier signs of the coupled proper-power error. -/
def properPair (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*properSymbol A N s xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*properSymbol A N s (-xi)

theorem properPair_profile (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L xi : ℝ) :
    ‖properPair A N (3/2+Complex.I*y) L xi/(xi : ℂ)^2‖ ≤
      (mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
        (2*jointLogMass^2+8*jointMass^2))*(1+xi^2)⁻¹ := by
  have hB := mainBudget_nonneg N (3/2-safeRadius) safeRadius_pos
  have hl : ‖properPair A N (3/2+Complex.I*y) L xi‖ ≤
      8*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*jointMass^2 := by
    unfold properPair
    apply (norm_add_le _ _).trans
    simpa only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul] using
      (add_le_add (properSymbol_large A h16 N y xi)
        (properSymbol_large A h16 N y (-xi))).trans_eq (by ring)
  have hn : ‖properPair A N (3/2+Complex.I*y) L xi‖ ≤
      (2*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*jointLogMass^2)*xi^2 := by
    unfold properPair
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
    have h := add_le_add (properSymbol_small A h16 N y xi)
      (properSymbol_small A h16 N y (-xi))
    simpa only [neg_sq,two_mul,add_mul,mul_assoc] using h
  exact (norm_div_square_profile (by positivity) (by positivity) hn hl).trans_eq (by ring)

theorem measurable_properDifference (j : ℕ) (s : ℂ) :
    Measurable (fun xi : ℝ => properDifference j s xi) := by
  cases j with
  | zero => exact measurable_const
  | succ k =>
    have hm : Measurable (fun xi : ℝ => zetaProperPrimePowerMoment k (s+Complex.I*xi)) := by
      apply Measurable.tsum
      intro p
      unfold zetaPrimeLogKernel zetaPrimeFeature
      fun_prop
    exact (measurable_const.sub hm).div_const _

theorem measurable_properPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    Measurable (fun xi : ℝ => properPair A N (3/2+Complex.I*y) L xi/(xi : ℂ)^2) := by
  have hm : Measurable (fun xi : ℝ => properSymbol A N (3/2+Complex.I*y) xi) := by
    apply Finset.measurable_fun_sum
    intro j _hj
    apply Finset.measurable_fun_sum
    intro h _hh
    exact (measurable_properDifference j _).mul
      (measurable_cofactor A h16 N j h (by norm_num [safeRadius]))
  have hn := hm.comp measurable_neg
  unfold properPair
  fun_prop

theorem integrable_properPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    IntegrableOn (fun xi : ℝ => properPair A N (3/2+Complex.I*y) L xi/(xi : ℂ)^2) (Ioi 0) := by
  apply ((integrable_inv_one_add_sq.integrableOn).const_mul
    (mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
      (2*jointLogMass^2+8*jointMass^2))).mono'
  · exact (measurable_properPair A h16 N y L).aestronglyMeasurable
  · exact Eventually.of_forall (properPair_profile A h16 N y L)

/-- The bound pays the whole frequency integral, including its origin
and unbounded end. -/
theorem norm_integral_properPair_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    ‖∫ xi : ℝ in Ioi 0, properPair A N (3/2+Complex.I*y) L xi/(xi : ℂ)^2‖ ≤
      (mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
        (2*jointLogMass^2+8*jointMass^2))*(Real.pi/2) := by
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    ((integrable_inv_one_add_sq.integrableOn).const_mul
    (mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
      (2*jointLogMass^2+8*jointMass^2)))
    (Eventually.of_forall (properPair_profile A h16 N y L))
  simpa only [integral_const_mul,integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero] using h

/-- The integrated proper-power error with the original Riesz prefactor. -/
def properResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, properPair A N s L xi/(xi : ℂ)^2

/-- Both frequencies of the main logarithmic-derivative symbol. -/
def logPair (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*logSymbol A N s xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*logSymbol A N s (-xi)

/-- The coupled main integral after the paid proper-power replacement. -/
def logResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, logPair A N s L xi/(xi : ℂ)^2

theorem logPair_split (A : Finset ℕ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) (L xi : ℝ) :
    logPair A N s L xi = completedPair A N s L xi+properPair A N s L xi := by
  simp only [logPair,logSymbol_split A N hs,completedPair,properPair]
  ring

theorem logResponse_split (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p) (y L : ℝ) :
    logResponse A N (3/2+Complex.I*y) L =
      completedResponse A N (3/2+Complex.I*y) L+properResponse A N (3/2+Complex.I*y) L := by
  have hs : 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius := by norm_num [safeRadius]
  have hi : IntegrableOn (fun xi : ℝ => completedPair A N (3/2+Complex.I*y) L xi/(xi : ℂ)^2)
      (Ioi 0) := by
    simp_rw [completedPair_split A hA N (by norm_num : 1 < (3/2+Complex.I*(y : ℂ)).re),add_div]
    exact (integrable_separatedPair A hA h16 N hhead safeRadius_pos hs L).add
      (integrable_completionPair A h16 N hgap hs L)
  unfold logResponse completedResponse properResponse
  simp_rw [logPair_split A N (by norm_num : 1 < (3/2+Complex.I*(y : ℂ)).re),add_div]
  rw [integral_add hi (integrable_properPair A h16 N y L),mul_add]

theorem norm_properResponse_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y : ℝ) {L : ℝ} (hL : 1 ≤ L) :
    ‖properResponse A N (3/2+Complex.I*y) L‖ ≤
      ((N : ℝ)+1)*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
        (2*jointLogMass^2+8*jointMass^2)*(Real.pi/2) := by
  have hL0 : 0 < L := by linarith
  have hden : 1 ≤ 2*Real.pi*L := by nlinarith [Real.pi_gt_three]
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) hden
  unfold properResponse
  rw [norm_mul]
  exact (mul_le_mul hpref (norm_integral_properPair_le A h16 N y L)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- The proper-power error has its own stronger checked rate. -/
def properRate : ℝ := ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius*Real.exp (-(1 : ℝ)/10)

theorem properRate_bounds : 0 ≤ properRate ∧ properRate < 91/100 := by
  have he : Real.exp (-(1 : ℝ)/10) ≤ 10/11 := by
    rw [show -(1 : ℝ)/10 = -(1/10) by ring,Real.exp_neg]
    have ht := Real.add_one_le_exp (1/10)
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  constructor
  · unfold properRate ZetaRieszWideOwnerAudit.radiusCeiling safeRadius
    positivity
  · have h := mul_le_mul_of_nonneg_left he
      (show 0 ≤ ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius by
        norm_num [ZetaRieszWideOwnerAudit.radiusCeiling,safeRadius])
    exact h.trans_lt (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling,safeRadius])

theorem norm_scaled_properResponse_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y : ℝ) {u U L : ℝ} (hu : 0 ≤ u) (hU : u ≤ U) (hL : 1 ≤ L) :
    ‖(u : ℂ)^(N+1)*properResponse A N (3/2+Complex.I*y) L‖ ≤
      ((Real.pi/2)*Real.exp (4*mass (3/2-safeRadius))*
        (2*jointLogMass^2+8*jointMass^2)*(U/safeRadius))*
          ((N : ℝ)+2)^3*(U/safeRadius*Real.exp (-(1 : ℝ)/10))^N := by
  have hU0 := hu.trans hU
  have hR := safeRadius_pos
  have hB := mainBudget_nonneg N (3/2-safeRadius) hR
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  apply (mul_le_mul (pow_le_pow_left₀ hu hU (N+1))
    (norm_properResponse_le A h16 N y hL) (norm_nonneg _) (pow_nonneg hU0 _)).trans
  calc
    _ ≤ U^(N+1)*(((N : ℝ)+2)*mainBudget N (3/2-safeRadius) safeRadius*
        Real.exp (-(N : ℝ)/10)*(2*jointLogMass^2+8*jointMass^2)*(Real.pi/2)) := by
      gcongr
      linarith
    _ = _ := by
      have hexp : Real.exp (-(N : ℝ)/10) = Real.exp (-(1 : ℝ)/10)^N := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      unfold mainBudget
      rw [hexp,mul_pow,div_pow,pow_succ U,pow_succ safeRadius]
      field_simp

/-- Uniform decay of the whole coupled proper-power response. There
is no zero hypothesis and no prime-cutoff or fixed-height condition. -/
theorem tendsto_properResponse (A : ℕ → Finset ℕ)
    (h16 : ∀ N p, p ∈ A N → 16 ≤ p) (height length : ℕ → ℝ) (hL : ∀ N, 1 ≤ length N)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*properResponse (A N) N
      (3/2+Complex.I*height N) (length N)) atTop (nhds 0) := by
  have hr := properRate_bounds
  have hr1 : properRate < 1 := lt_trans hr.2 (by norm_num)
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 hr.1 hr1
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr.1 hr1
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr.1 hr1
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3 hr.1 hr1
  have ht : Tendsto (fun N : ℕ => ((N : ℝ)+2)^3*properRate^N) atTop (nhds 0) := by
    convert ((ht3.add (ht2.const_mul 6)).add (ht1.const_mul 12)).add (ht0.const_mul 8) using 1
    · ext N; simp only [pow_zero,pow_one]; ring
    · norm_num
  let C : ℝ := (Real.pi/2)*Real.exp (4*mass (3/2-safeRadius))*
    (2*jointLogMass^2+8*jointMass^2)*(ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius)
  apply squeeze_zero_norm (a := fun N : ℕ => C*(((N : ℝ)+2)^3*properRate^N))
  · intro N
    simpa only [properRate,mul_assoc,C] using
      norm_scaled_properResponse_le (A N) (h16 N) N (height N) hu hU (hL N)
  · simpa only [mul_zero] using ht.const_mul C

/-- The logarithmic-derivative interface of the same signed packet. -/
def logMain (u y : ℝ) (N : ℕ) : ℂ :=
  logResponse (roughPrimes u N) N (3/2+Complex.I*y) (SquarefreeVaughanLogSource.length u N)

theorem tendsto_log_sub_completed {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (height : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*
      (logMain u (height N) N-completedMain u (height N) N)) atTop (nhds 0) := by
  apply (tendsto_properResponse (roughPrimes u) (fun _ _ hp => rough_sixteen hp) height
    (SquarefreeVaughanLogSource.length u) (ZetaRieszHeadOrders.one_le_length u) hu.le hU).congr'
  filter_upwards [eventually_rough_support hu hU] with N hgap
  rw [logMain,completedMain,logResponse_split (roughPrimes u N)
    (fun _ hp => rough_prime hp) (fun _ hp => rough_sixteen hp) N
    (fun _ hp => rough_head hp) hgap]
  ring

/-- The new logarithmic-derivative response is source-equivalent to
the UNCHANGED signed target. Its joint main bound is still open. -/
theorem tendsto_log_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (logMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have h := ((tendsto_log_sub_completed (by linarith : 0 < u) hU (fun _ => y)).comp
      ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add
    (tendsto_completed_sub_current hu hU y)
  simp only [zero_add] at h
  convert h using 1
  ext j
  simp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszMarkedLogDerivative
