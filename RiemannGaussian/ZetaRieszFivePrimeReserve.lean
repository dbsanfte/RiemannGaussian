/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourPrimeReserve

/-!
# Exact five-prime adverse-phase debit in the joint floor

Reflect the five-prime response, delete its largest prime when the
positive coefficient can survive, and apply the exact four-prime clipped
balance. This evaluates the entire positive coefficient, including the
saturated and zero chambers. The actual phase and signed complement remain.
-/

namespace RiemannGaussian.ZetaRieszFivePrimeReserve
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszReflectedLinear ZetaRieszPrimeEndpoint
open ZetaRieszFourPrimeFloor ZetaRieszFourPrimeReserve

/-- The exact candidate positive-part allowance uses every cofactor prime
excess beyond the largest-prime deletion cutoff. -/
def positiveAllowance (L : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n then (Real.log n/L)*max 0
    (2*Real.log (largestPrime n)+Real.log n-3*L-
      ∑ p ∈ n.primeFactors.erase (largestPrime n),
        max 0 (Real.log p-(L-Real.log (largestPrime n)))) else 0

/-- Nonnegative allowance, also zero on nonsquarefree labels. -/
theorem positiveAllowance_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 ≤ positiveAllowance L n := by
  unfold positiveAllowance
  split_ifs
  · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (le_max_left _ _)
  · rfl

/-- The positive five-prime coefficient is evaluated exactly, not merely
bounded by its two largest-prime gaps. Every cutoff boundary is included. -/
theorem positiveAllowance_eq {n : ℕ} (hc : n.primeFactors.card = 5)
    {L : ℝ} (hL : 0 < L) (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) :
    positiveAllowance L n = max 0 (SquarefreeVaughanLogSource.coefficient L n).re := by
  by_cases hs : Squarefree n
  · let P := largestPrime n
    let F := 2*Real.log P+Real.log n-3*L-
      ∑ p ∈ n.primeFactors.erase P, max 0 (Real.log p-(L-Real.log P))
    have hsum0 : 0 ≤ ∑ p ∈ n.primeFactors.erase P,
        max 0 (Real.log p-(L-Real.log P)) := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
    have hnp : ¬n.Prime := by intro hp; rw [hp.primeFactors,Finset.card_singleton] at hc; omega
    have hn1 : n ≠ 1 := by intro hn; simp [hn] at hc
    have hscale : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL.le
    change (if Squarefree n then (Real.log n/L)*max 0 F else 0) = _
    rw [if_pos hs]
    by_cases hgate : 2*Real.log P+Real.log n ≤ 3*L
    · have hnonpos := ZetaRieszFivePrimeFloor.coefficient_five_nonpos hc hL hLlo hLhi (Or.inl hgate)
      have hF : F ≤ 0 := by dsimp [F]; linarith
      rw [max_eq_left hF,mul_zero,max_eq_left hnonpos]
    have hP : P ∈ n.primeFactors := by
      have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
      dsimp [P]
      rw [largestPrime,dif_pos hne]
      exact Finset.max'_mem _ _
    let a := ∏ p ∈ n.primeFactors.erase P, p
    have hpa (p : ℕ) (hp : p ∈ n.primeFactors.erase P) : p.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have hfa : a.primeFactors = n.primeFactors.erase P := Nat.primeFactors_prod hpa
    have hac : a.primeFactors.card = 4 := by rw [hfa,Finset.card_erase_of_mem hP,hc]
    have he : n = P*a := by
      rw [← Nat.prod_primeFactors_of_squarefree hs]
      exact (Finset.mul_prod_erase _ _ hP).symm
    have hsp : Squarefree (P*a) := he ▸ hs
    have hp := Nat.prime_of_mem_primeFactors hP
    have hpn : ¬P ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
    have hlog : Real.log n = Real.log P+Real.log a := by
      rw [he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
        (by exact_mod_cast hsp.of_mul_right.ne_zero)]
    let D := Real.log n-L
    have hD : 0 ≤ D := by dsimp [D]; linarith [Real.log_natCast_nonneg n]
    have hlarge : D ≤ Real.log P := by dsimp [D]; linarith
    have hr := VaughanLogAverage.riesz_reflection L hs hn1 hnp
    rw [moebius_eq_primeCount hs,hc] at hr
    norm_num at hr
    have hR : -VaughanLogAverage.riesz L n = VaughanLogAverage.riesz D a := by
      calc
        _ = VaughanLogAverage.riesz D n := hr.symm
        _ = VaughanLogAverage.riesz D a-VaughanLogAverage.riesz (D-Real.log P) a := by
          simpa only [← he] using riesz_prime_mul D hp hpn
        _ = _ := by rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos
          (by linarith : D-Real.log P ≤ 0),sub_zero]
    have hcR : (SquarefreeVaughanLogSource.coefficient L n).re =
        (Real.log n/L)*VaughanLogAverage.riesz D a := by
      simp only [SquarefreeVaughanLogSource.coefficient,if_pos (show Squarefree n ∧ ¬n.Prime from ⟨hs,hnp⟩),
        Complex.ofReal_re]
      rw [show -Real.log n*VaughanLogAverage.riesz L n/L =
        (Real.log n/L)*(-VaughanLogAverage.riesz L n) by ring,hR]
    have hpos : max 0 (VaughanLogAverage.riesz D a) = max 0 F := by
      by_cases hsat : L ≤ Real.log P
      · have ha1 : a ≠ 1 := by intro ha; simp [ha] at hac
        have hap : ¬a.Prime := by intro ha; rw [ha.primeFactors,Finset.card_singleton] at hac; omega
        rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hsp.of_mul_right ha1 hap
          (by dsimp [D]; linarith),max_self]
        have hsum : (∑ p ∈ n.primeFactors.erase P, max 0 (Real.log p-(L-Real.log P))) =
            Real.log a-4*(L-Real.log P) := by
          rw [← hfa]
          have hterm (p : ℕ) (_hp : p ∈ a.primeFactors) :
              max 0 (Real.log p-(L-Real.log P)) = Real.log p-(L-Real.log P) :=
            max_eq_right (by linarith [Real.log_natCast_nonneg p])
          rw [Finset.sum_congr rfl hterm,Finset.sum_sub_distrib,
            ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hsp.of_mul_right,
            Finset.sum_const,nsmul_eq_mul,hac]
          norm_num
        have hF : F = L-Real.log P := by dsimp [F]; rw [hsum]; linarith
        rw [hF,max_eq_left (sub_nonpos.mpr hsat)]
      · have hQ := largestPrime_mem_of_four hac
        have hmax (p : ℕ) (hp' : p ∈ a.primeFactors) :
            Real.log p ≤ Real.log (largestPrime a) := by
          have hne : a.primeFactors.Nonempty := ⟨p,hp'⟩
          have hle : p ≤ largestPrime a := by
            rw [largestPrime,dif_pos hne]
            exact Finset.le_max' _ _ hp'
          exact Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp').pos)
            (by exact_mod_cast hle)
        have hh := (riesz_four_clipped_sum hsp.of_mul_right hac hQ hmax
          (L := D) (by dsimp [D]; linarith) (by dsimp [D]; linarith)).2
        rw [clipped_sum_eq_excess hsp.of_mul_right D] at hh
        have hcut : Real.log a-D = L-Real.log P := by dsimp [D]; linarith
        have hbase : 3*D-2*Real.log a = 2*Real.log P+Real.log n-3*L := by dsimp [D]; linarith
        simpa only [hcut,hbase,hfa,F] using hh
    rw [hcR,show max 0 ((Real.log n/L)*VaughanLogAverage.riesz D a) =
      (Real.log n/L)*max 0 (VaughanLogAverage.riesz D a) by
        rw [mul_max_of_nonneg _ _ hscale,mul_zero],hpos]
  · simp [positiveAllowance,SquarefreeVaughanLogSource.coefficient,hs]

/-- The exact debit never exceeds the existing simultaneous largest-gap
and least-prime bound. -/
theorem positiveAllowance_le_clipped {n : ℕ} (hc : n.primeFactors.card = 5)
    {L : ℝ} (hL : 0 < L) (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) :
    positiveAllowance L n ≤ (Real.log n/L)*min (3*Real.log n.minFac)
      (max 0 (min (2*Real.log (largestPrime n)+Real.log n-3*L)
        (Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n-2*L))) := by
  rw [positiveAllowance_eq hc hL hLlo hLhi]
  apply max_le
  · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
      (le_min (mul_nonneg (by norm_num) (Real.log_natCast_nonneg n.minFac)) (le_max_left _ _))
  · exact ZetaRieszFivePrimeFloor.actual_five_upper_clipped hc hL hLlo hLhi

open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation

/-- On the adverse cosine side, the five-prime floor has no coefficient
slack left: the exact debit and the full positive observation reconstruct
the original atom, with its allocation and factorial weight unchanged. -/
theorem re_five_atom_eq_keep_positive (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hc : n.primeFactors.card = 5) {L : ℝ} (hL : 0 < L)
    (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) (y : ℝ)
    (hcos : Real.cos (y*Real.log n) ≤ 0) :
    (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re =
      max (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re 0-
        weight A N n*positiveAllowance L n*(-Real.cos (y*Real.log n)) := by
  rw [positiveAllowance_eq hc hL hLlo hLhi]
  have he (c : ℝ) : max (c*Real.cos (y*Real.log n)) 0-
      max 0 c*(-Real.cos (y*Real.log n)) = c*Real.cos (y*Real.log n) := by
    by_cases hc' : 0 ≤ c
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc' hcos),max_eq_right hc']
      ring
    · rw [max_eq_left (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hc') hcos),
        max_eq_left (le_of_not_ge hc')]
      ring
  have hm := congrArg (fun z => weight A N n*z) (he (SquarefreeVaughanLogSource.coefficient L n).re)
  rw [mul_sub,mul_max_of_nonneg _ _ (weight_nonneg A N n),mul_zero] at hm
  simpa only [re_residual_atom,mul_assoc] using hm.symm

/-- The new five-prime observed lower bound dominates the old clipped
bound pointwise, before any population sum or source normalization. -/
theorem five_floor_improves_clipped (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hc : n.primeFactors.card = 5) {L : ℝ} (hL : 0 < L)
    (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) (y : ℝ)
    (hcos : Real.cos (y*Real.log n) ≤ 0) (credit : ℝ) :
    credit-weight A N n*(Real.log n/L)*
      min (3*Real.log n.minFac)
      (max 0 (min (2*Real.log (largestPrime n)+Real.log n-3*L)
        (Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n-2*L)))*
      (-Real.cos (y*Real.log n)) ≤
    credit-weight A N n*positiveAllowance L n*(-Real.cos (y*Real.log n)) := by
  apply sub_le_sub_left
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (positiveAllowance_le_clipped hc hL hLlo hLhi) (weight_nonneg A N n))
    (neg_nonneg.mpr hcos)
  simpa only [mul_assoc] using h

/-- Both count classes are handled in the same original finite sum. The
sharpened four-prime debit and exact five-prime debit retain every
other signed term; there is no separate complement estimate. -/
theorem re_sum_ge_four_five_credit (S A : Finset ℕ) (N : ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hwindow : ∀ n ∈ S, n.primeFactors.card = 4 ∨ n.primeFactors.card = 5 →
      L ≤ Real.log n ∧ 2*Real.log n ≤ 3*L ∧ 4*L ≤ 3*Real.log n) :
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ S, if n.primeFactors.card = 4 then
      max (f n).re 0-weight A N n*fourDebit L y n
      else if n.primeFactors.card = 5 ∧ Real.cos (y*Real.log n) ≤ 0 then
        max (f n).re 0-weight A N n*positiveAllowance L n*(-Real.cos (y*Real.log n))
      else (f n).re) ≤ (∑ n ∈ S, f n).re := by
  dsimp only
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro n hn
  split_ifs with hfour hfive
  · have hw := hwindow n hn (Or.inl hfour)
    exact ZetaRieszFourPrimeReserve.re_four_atom_ge_keep_positive A N hfour hL hw.1 hw.2.1 y
  · have hw := hwindow n hn (Or.inr hfive.1)
    exact (re_five_atom_eq_keep_positive A N hfive.1 hL hw.2.1 hw.2.2 y hfive.2).symm.le
  · exact le_rfl

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint

/-- The original core discharges the geometric premises eventually. The
whole signed complement stays inside this one lower comparison. Its
aggregate numerical floor remains open. -/
theorem eventually_re_core_ge_four_five_credit {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ),
      let L := SquarefreeVaughanLogSource.length u N
      let A := intermediatePrimes u N
      let S := coreBand u N K
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*(∑ n ∈ S, if n.primeFactors.card = 4 then
        max (f n).re 0-weight A N n*fourDebit L y n
        else if n.primeFactors.card = 5 ∧ Real.cos (y*Real.log n) ≤ 0 then
          max (f n).re 0-weight A N n*positiveAllowance L n*(-Real.cos (y*Real.log n))
        else (f n).re) ≤ ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  filter_upwards [hL,eventually_ge_atTop (2 : ℕ)] with N hlow hN K y
  have hupp : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  have hwindow (n : ℕ) (hn : n ∈ coreBand u N K)
      (_hc : n.primeFactors.card = 4 ∨ n.primeFactors.card = 5) :
      SquarefreeVaughanLogSource.length u N ≤ Real.log n ∧
        2*Real.log n ≤ 3*SquarefreeVaughanLogSource.length u N ∧
          4*SquarefreeVaughanLogSource.length u N ≤ 3*Real.log n := by
    have hw := (Finset.mem_filter.mp hn).2
    constructor
    · nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
    constructor <;> nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
  have hb := re_sum_ge_four_five_credit (coreBand u N K) (intermediatePrimes u N) N
    (SquarefreeVaughanLogSource.length_pos u N) y hwindow
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  simpa only [coreResponse,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using hm

open ZetaRieszRadialCompensation

/-- Combine the paid balanced triple band and its unspent supply with the
exact-five/refined-four comparison on their untouched complement. Supply
labels are excluded before applying the debit, so no positive credit is
spent twice. This is one joint floor with only the already paid edge error. -/
theorem eventually_compensated_core_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let L := SquarefreeVaughanLogSource.length u N
        let A := intermediatePrimes u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let X := ∑ n ∈ radialTriples S N η, f n
        let Y := ∑ n ∈ radialSupply N h v, f n
        let W := S\(radialTriples S N η ∪ radialSupply N h v ∪ balancedTriples S N η)
        let B := ∑ n ∈ W, if n.primeFactors.card = 4 then
          max (f n).re 0-weight A N n*fourDebit L y n
          else if n.primeFactors.card = 5 ∧ Real.cos (y*Real.log n) ≤ 0 then
            max (f n).re 0-weight A N n*positiveAllowance L n*(-Real.cos (y*Real.log n))
          else (f n).re
        0 < Y.re ∧
          u^(N+1)*(B+max X.re 0+Y.re/2)-r^N*C ≤
            ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,r,C,hη,hηu,hh,hhu,hr,hr1,hC,hfloor⟩ := eventually_core_balanced_floor hu hU hy
  refine ⟨η,h,r,C,hη,hηu,hh,hhu,hr,hr1,hC,?_⟩
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually hL,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2 : ℕ))] with j hj hlow hN
  obtain ⟨v,hv,hY,hfloor⟩ := hj
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let W := S\(radialTriples S N η ∪ radialSupply N h v ∪ balancedTriples S N η)
  have hupp : L ≤ (7/5 : ℝ)*N := by
    have hl := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    dsimp [L,N]
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]
  have hwindow (n : ℕ) (hn : n ∈ W)
      (_hc : n.primeFactors.card = 4 ∨ n.primeFactors.card = 5) :
      L ≤ Real.log n ∧ 2*Real.log n ≤ 3*L ∧ 4*L ≤ 3*Real.log n := by
    have hnS : n ∈ S := (Finset.mem_sdiff.mp hn).1
    have hw := (Finset.mem_filter.mp hnS).2
    change 2*(137/200 : ℝ)*N ≤ L at hlow
    constructor
    · nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
    constructor <;> nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
  have hb := re_sum_ge_four_five_credit W A N (SquarefreeVaughanLogSource.length_pos u N) y hwindow
  refine ⟨v,hv,hY,?_⟩
  apply le_trans _ hfloor
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  exact add_le_add (add_le_add hb le_rfl) le_rfl

end
end RiemannGaussian.ZetaRieszFivePrimeReserve
