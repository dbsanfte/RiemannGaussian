/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFivePrimeCells
import RiemannGaussian.ZetaRieszFourAngularDomain

/-!
# Opposite-phase ceilings for the unchanged signed prime cells

Calibrating at height pi/t observes the same finite cell near phase minus
one. A lower bound there controls the negative coefficient mass and yields
an upper bound at an arbitrary original height with positive cosine.
No prime weight, allocation or physical mask changes. The complement is
kept signed; these component ceilings do not establish the whole-core 3/2
ceiling needed by the multiplicity-robust endgame.
-/

namespace RiemannGaussian.ZetaRieszOppositePhase
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation
open ZetaRieszAllowancePrimeBoxes
open ZetaRieszCoupledWindow ZetaRieszMacroPrimeWindows ZetaRieszFivePrimeCells
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget

/-- The original cosine on a literal total-log window has a common
lower bound, with its full ordinate and every integer still present. -/
theorem cos_window_lower {n : ℕ} {t h y : ℝ}
    (hlo : t ≤ Real.log n) (hhi : Real.log n ≤ t+h) :
    Real.cos (y*t)-|y| * h ≤ Real.cos (y*Real.log n) := by
  have he : |y*Real.log n-y*t| ≤ |y| * h := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg y)
  have hc := abs_le.mp ((Real.abs_cos_sub_cos_le (y*Real.log n) (y*t)).trans he)
  linarith only [hc.1]

/-- The matching upper observation bound retains the same total-log window. -/
theorem cos_window_upper {n : ℕ} {t h y : ℝ}
    (hlo : t ≤ Real.log n) (hhi : Real.log n ≤ t+h) :
    Real.cos (y*Real.log n) ≤ Real.cos (y*t)+|y| * h := by
  have he : |y*Real.log n-y*t| ≤ |y| * h := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg y)
  have hc := abs_le.mp ((Real.abs_cos_sub_cos_le (y*Real.log n) (y*t)).trans he)
  linarith only [hc.2]

/-- For a nonpositive-coefficient population, a signed lower bound at
ANY calibration height gives a ceiling at a positive original phase.
This uses the same weighted sum; no norm envelope or carrier completion
is introduced. -/
theorem ceiling_of_calibrated_floor (S A : Finset ℕ) (N : ℕ) (L t h y z C : ℝ)
    (hsign : ∀ n ∈ S, (SquarefreeVaughanLogSource.coefficient L n).re ≤ 0)
    (hlog : ∀ n ∈ S, t ≤ Real.log n ∧ Real.log n ≤ t+h)
    (hphase : 0 ≤ Real.cos (y*t)-|y| * h)
    (hfloor : C ≤ (∑ n ∈ S,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*z) n).re) :
    (∑ n ∈ S,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
      -(Real.cos (y*t)-|y| * h)*C := by
  let d := Real.cos (y*t)-|y| * h
  have hd : 0 ≤ d := hphase
  have hpoint (n : ℕ) (hn : n ∈ S) :
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
      -d*(residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*z) n).re := by
    have hobs := cos_window_lower (y := y) (hlog n hn).1 (hlog n hn).2
    have hcal := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (z*Real.log n)) hd
    have he : -d*Real.cos (z*Real.log n) ≤ Real.cos (y*Real.log n) := by
      dsimp only [d] at hcal ⊢
      linarith only [hcal,hobs]
    have hcoef := mul_nonpos_of_nonneg_of_nonpos (weight_nonneg A N n) (hsign n hn)
    have hm := mul_le_mul_of_nonpos_left he hcoef
    rw [re_residual_atom,re_residual_atom]
    nlinarith only [hm]
  have hs := Finset.sum_le_sum hpoint
  simp only [← Complex.re_sum,← Finset.mul_sum] at hs
  exact hs.trans (mul_le_mul_of_nonpos_left hfloor (neg_nonpos.mpr hd))

/-- At calibration height pi/t the entire short window has phase near
minus one. Its loss is at most 1/10000, with no growing-order error. -/
theorem calibration_phase {t h : ℝ} (ht : 1 ≤ t) (hh : 0 ≤ h) (hhu : h ≤ 1/100000) :
    Real.cos ((Real.pi/t)*t) = -1 ∧ |Real.pi/t| * h ≤ 1/10000 := by
  have ht0 : 0 < t := by linarith
  refine ⟨by rw [div_mul_cancel₀ _ ht0.ne',Real.cos_pi],?_⟩
  rw [abs_of_pos (div_pos Real.pi_pos ht0),div_mul_eq_mul_div]
  apply (div_le_self (mul_nonneg Real.pi_pos.le hh) ht).trans
  nlinarith [Real.pi_lt_four]

/-- The calibration mask retains EVERY positive-coefficient four-prime
label in the interval. It imposes no restriction on the original height. -/
theorem mem_calibrated_population_iff (S : Finset ℕ) (L a : ℝ) {t h : ℝ}
    (ht : 1 ≤ t) (hh : 0 ≤ h) (hhu : h ≤ 1/100000) (n : ℕ) :
    n ∈ adversePopulation S L t h (Real.pi/t) a ↔
      n ∈ S ∧ Squarefree n ∧ n.primeFactors.card = 4 ∧
      (∀ p ∈ n.primeFactors, a < Real.log p) ∧
      t < Real.log n ∧ Real.log n ≤ t+h ∧
      0 < (SquarefreeVaughanLogSource.coefficient L n).re := by
  simp only [adversePopulation,Finset.mem_filter]
  constructor
  · rintro ⟨hn,hs,hc,hp,hlo,hhi,hpos,_⟩
    exact ⟨hn,hs,hc,hp,hlo,hhi,hpos⟩
  · rintro ⟨hn,hs,hc,hp,hlo,hhi,hpos⟩
    refine ⟨hn,hs,hc,hp,hlo,hhi,hpos,?_⟩
    have hcal := calibration_phase ht hh hhu
    have hw := cos_window_upper (y := Real.pi/t) hlo.le hhi
    rw [hcal.1] at hw
    linarith only [hw,hcal.2]

/-- A calibration floor controls the same positive-coefficient population
from above at the original height. The constant is a relative local cost,
never a polynomial error multiplied by the whole source envelope. -/
theorem positive_ceiling_of_calibrated_floor (S A : Finset ℕ) (N : ℕ)
    (L t h y C : ℝ) (ht : 1 ≤ t) (hh : 0 ≤ h) (hhu : h ≤ 1/100000)
    (hsign : ∀ n ∈ S, 0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re)
    (hlog : ∀ n ∈ S, t ≤ Real.log n ∧ Real.log n ≤ t+h)
    (hfloor : -C ≤ (∑ n ∈ S,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*(Real.pi/t : ℝ)) n).re) :
    (∑ n ∈ S,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
      (10000/9999 : ℝ)*(max 0 (Real.cos (y*t))+|y| * h)*C := by
  let d := max 0 (Real.cos (y*t))+|y| * h
  let mass := ∑ n ∈ S, weight A N n*(SquarefreeVaughanLogSource.coefficient L n).re
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hcal := calibration_phase ht hh hhu
  have hc := Finset.sum_le_sum (s := S) (fun n hn =>
    mul_le_mul_of_nonneg_left
      (show Real.cos ((Real.pi/t)*Real.log n) ≤ -(9999/10000 : ℝ) by
        have hw := cos_window_upper (y := Real.pi/t) (hlog n hn).1 (hlog n hn).2
        rw [hcal.1] at hw
        linarith only [hw,hcal.2])
      (mul_nonneg (weight_nonneg A N n) (hsign n hn)))
  have hy := Finset.sum_le_sum (s := S) (fun n hn =>
    mul_le_mul_of_nonneg_left
      ((cos_window_upper (y := y) (hlog n hn).1 (hlog n hn).2).trans
        (add_le_add (le_max_right 0 (Real.cos (y*t))) (le_refl (|y| * h))))
      (mul_nonneg (weight_nonneg A N n) (hsign n hn)))
  have hmass : (9999/10000 : ℝ)*mass ≤ C := by
    simp only [← mul_assoc,Complex.re_sum,re_residual_atom,← Finset.sum_mul] at hfloor hc
    dsimp only [mass]
    linarith only [hfloor,hc]
  have htarget := mul_le_mul_of_nonneg_left hmass hd
  rw [Complex.re_sum]
  simp only [re_residual_atom,← mul_assoc]
  simp only [← Finset.sum_mul] at hy
  dsimp only [mass,d] at htarget
  nlinarith only [hy,htarget]

/-- The original complete five-prime cell supplies an independent
negative credit for the UPPER bound on a positive-cosine window. Only
1/1000 of the existing cell constant is spent on calibration. -/
theorem eventually_five_cell_upper {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (lo H : Fin 4 → ℝ) (A : Finset ℕ) (L t y : ℝ),
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∀ i j, i < j → lo i+H i ≤ lo j) → 0 < L → 1 ≤ t →
      α*N ≤ t-(∑ i, (lo i+H i)) →
      lo 3+H 3 ≤ t-(∑ i, (lo i+H i)) → t-(∑ i, lo i)+h ≤ (9/16 : ℝ)*t →
      t-lo 3-lo 2+h ≤ L → L ≤ t-(lo 1+H 1)-(lo 0+H 0) →
      0 ≤ Real.cos (y*t)-|y| * h →
      let M := (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image (fun p => (∏ i, p i : ℕ))
      (∑ n ∈ M.biUnion (fun m => (logPrimes (t-Real.log m) h).image (fun p => m*p)),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
      -(996/1000 : ℝ)*(t/L)*boxCap L t h lo (fun i => lo i+H i)*
        (Real.cos (y*t)-|y| * h)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
        (h/(t-∑ i, lo i))*(∏ i, H i/(lo i+H i)) := by
  filter_upwards [eventually_five_cell_lower hh hhu hα hβ,eventually_ge_atTop (1 : ℕ)]
    with N hN horderN lo H A L t y hlo hH horder hL ht hmin hqp hmax hsat htriple hphase
  dsimp only
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast horderN
  have hlo0 (i : Fin 4) : 0 < lo i := by nlinarith [hlo i]
  have hH0 (i : Fin 4) : 0 < H i := by nlinarith [hH i]
  have hsum : (∑ i, lo i) ≤ ∑ i, (lo i+H i) :=
    Finset.sum_le_sum (fun i _ => le_add_of_nonneg_right (hH0 i).le)
  have hv : 0 < t-∑ i, lo i := by nlinarith
  have ht0 : 0 < t := by linarith
  have hcap := boxCap_nonneg L t h (hi := fun i => lo i+H i) (hlo0 0).le
  have hcal := calibration_phase ht hh.le hhu
  have hlow := hN lo H A L t (Real.pi/t) hlo hH horder hL hmin hqp hmax hsat htriple
    (by rw [hcal.1]; linarith [hcal.2])
  dsimp only at hlow
  rw [hcal.1] at hlow
  let B := (t/L)*boxCap L t h lo (fun i => lo i+H i)*
    (Real.exp (-(t+h)/2)*t^N/N.factorial)*(h/(t-∑ i, lo i))*(∏ i, H i/(lo i+H i))
  have hprod : 0 ≤ ∏ i, H i/(lo i+H i) :=
    Finset.prod_nonneg (fun i _ => div_nonneg (hH0 i).le (by linarith [hlo0 i,hH0 i]))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfactor : (996/1000 : ℝ) ≤ (997/1000)*(1-|Real.pi/t| * h) := by linarith [hcal.2]
  have hpaid := mul_le_mul_of_nonneg_right hfactor hB
  have hfloor : (996/1000 : ℝ)*B ≤ (∑ n ∈
      ((Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image
        (fun p => (∏ i, p i : ℕ))).biUnion (fun m =>
          (logPrimes (t-Real.log m) h).image (fun p => m*p)),
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*(Real.pi/t : ℝ)) n).re := by
    apply hpaid.trans
    convert hlow using 1 <;> first | rfl | (simp only [B]; ring)
  have hupper := ceiling_of_calibrated_floor _ A N L t h y (Real.pi/t) _
    (fun n hn => cell_products_coefficient_nonpos ht0.le hL horder hqp hsat htriple hn)
    (by
      intro n hn
      obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
      have hm0 : (∏ i, v i : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ =>
        (logPrimes_bounds (Fintype.mem_piFinset.mp hv i)).1.ne_zero)
      have hb := product_log_bounds hm0 hp
      exact ⟨hb.2.1.le,hb.2.2⟩) hphase hfloor
  dsimp only [B] at hupper
  convert hupper using 1
  ring

/-- The five-prime ceiling is spent inside the original core, keeping
every unselected term in a single signed complement. This is a component
upper estimate, not the missing whole-carrier ceiling. -/
theorem eventually_five_cell_core_ceiling {u h α β : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ j : ℕ in atTop, ∀ (lo H : Fin 4 → ℝ) (t y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let M := (Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image (fun p => (∏ i, p i : ℕ))
      let D := M.biUnion (fun m => (logPrimes (t-Real.log m) h).image (fun p => m*p))
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∀ i j, i < j → lo i+H i ≤ lo j) →
      α*N ≤ t-(∑ i, (lo i+H i)) →
      lo 3+H 3 ≤ t-(∑ i, (lo i+H i)) → t-(∑ i, lo i)+h ≤ (9/16 : ℝ)*t →
      t-lo 3-lo 2+h ≤ L → L ≤ t-(lo 1+H 1)-(lo 0+H 0) →
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      0 ≤ Real.cos (y*t)-|y| * h →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ ZetaRieszParityPacket.coreBand u N K\D,
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      (996/1000 : ℝ)*(t/L)*boxCap L t h lo (fun i => lo i+H i)*
        (Real.cos (y*t)-|y| * h)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
        (h/(t-∑ i, lo i))*(∏ i, H i/(lo i+H i)) := by
  have hroom : u < Real.exp (-(5/8 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 5/8) hroom
  filter_upwards [eventually_ge_atTop 32,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlength,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_five_cell_upper hh hhu hα hβ)] with j hj hL hN hbound lo H t y
  dsimp only
  intro hlo hH horder hmin hqp hmax hsat htriple htlo hthi hphase
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hDS := cell_products_subset_core j hj hu hU (by linarith)
    horder hqp hmax htlo hthi
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hDS)
  rw [Complex.add_re] at he
  have ht : 1 ≤ t := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hc := hbound lo H A L t y hlo hH horder
    (SquarefreeVaughanLogSource.length_pos u N) ht hmin hqp hmax hsat htriple hphase
  change (∑ n ∈ ZetaRieszParityPacket.coreBand u N
    (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j), f n).re ≤ _
  dsimp only [f] at he
  linarith only [he,hc]

/-- The complete clipped positive-coefficient four-prime population has
an upper bound with the same angular integral and a calibration loss below
0.1 percent. The original cosine is unrestricted and all other labels
remain in the signed complement. -/
theorem eventually_four_core_ceiling {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ (t y : ℝ) (lo : ℚ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (17/25 : ℝ) ≤ lo → (lo : ℝ) ≤ L/t →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
        (∑ n ∈ S\Q, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (10000/9999 : ℝ)*(1+|Real.pi/t| * h)*
        (((1003/1000 : ℝ)*
          ((∫ x in ZetaRieszCapacityCover.region (ZetaRieszFourAngularDomain.outerBox lo),
            ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000+1/78000000)+1/100000)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (Real.cos (y*t))+|y| * h)*h)) := by
  filter_upwards [ZetaRieszFourAngularDomain.eventually_core_capacity_floor hu hU hh hhu hδ hδu,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN t y lo
  dsimp only
  intro htlo hthi hlo hlam
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
  let f := fun (y : ℝ) (n : ℕ) =>
    residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let D := (1003/1000 : ℝ)*
    ((∫ x in ZetaRieszCapacityCover.region (ZetaRieszFourAngularDomain.outerBox lo),
      ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000+1/78000000)+1/100000
  let C := D*((Real.exp (-t/2)*(t+h)^N/N.factorial)*(1+|Real.pi/t| * h)*h)
  have ht : 1 ≤ t := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hcal := calibration_phase ht hh.le hhu
  have hQS : Q ⊆ S := by
    intro n hn
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  have hez := congrArg Complex.re (Finset.sum_sdiff (f := f (Real.pi/t : ℝ)) hQS)
  have hey := congrArg Complex.re (Finset.sum_sdiff (f := f y) hQS)
  simp only [Complex.add_re] at hez hey
  have hf := hJ t (Real.pi/t) lo htlo hthi hlo hlam
  rw [hcal.1] at hf
  simp only [neg_neg,max_eq_right zero_le_one] at hf
  have hfloor : -C ≤ (∑ n ∈ Q, f (Real.pi/t : ℝ) n).re := by
    change (∑ n ∈ S\Q, f (Real.pi/t : ℝ) n).re-C ≤
      (∑ n ∈ S, f (Real.pi/t : ℝ) n).re at hf
    linarith only [hf,hez]
  have hupper := positive_ceiling_of_calibrated_floor Q A N L t h y C ht hh.le hhu
    (fun n hn => (Finset.mem_filter.mp hn).2.2.2.2.2.2.1.le)
    (fun n hn => ⟨(Finset.mem_filter.mp hn).2.2.2.2.1.le,
      (Finset.mem_filter.mp hn).2.2.2.2.2.1⟩) hfloor
  change (∑ n ∈ S, f y n).re ≤ _
  have hsum := hey.symm.le.trans (add_le_add (le_refl (∑ n ∈ S\Q, f y n).re) hupper)
  convert hsum using 1 <;> first | rfl | (dsimp only [D,C]; ring)

/-- The complete positive-mass calibration costs less than one tenth of
one percent, uniformly on every admissible logarithmic cell. -/
theorem calibration_cost_le {t h : ℝ} (ht : 1 ≤ t) (hh : 0 ≤ h) (hhu : h ≤ 1/100000) :
    (10000/9999 : ℝ)*(1+|Real.pi/t| * h) ≤ 1001/1000 := by
  have hc := (calibration_phase ht hh hhu).2
  linarith only [hc]

end
end RiemannGaussian.ZetaRieszOppositePhase
