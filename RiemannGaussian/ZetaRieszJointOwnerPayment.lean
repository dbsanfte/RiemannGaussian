/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointDominantFloor
import RiemannGaussian.ZetaRieszJointPositiveFiveBounds

/-!
# Paying the large-owner remainder from the existing joint reserve

The original unallocated mass decays on owner shares `119/200..13/20`.
The rate is sufficient relative to the central reserve, although it need
not beat the independent source envelope. All prime counts and the exact
signed complement are retained.
-/

namespace RiemannGaussian.ZetaRieszJointOwnerPayment
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszDominantAllocation
open ZetaRieszParityPacket ZetaRieszAnnulusJoint ZetaRieszPrimeCountFrequency ZetaRieszMaskSupport

private theorem upper_log_rate :
    Real.log (40081/40000 : ℝ)-(13/32 : ℝ)*Real.log (201/200 : ℝ) ≤ -(1/400000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/401)
    (by norm_num : (1/401 : ℝ) < 1) 1
  norm_num [Finset.sum_range_succ] at hlo
  have hhi : Real.log (40081/40000 : ℝ) ≤ 2023/1000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2023/1000000) 3
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- The exact original allocation with a smaller upper-tail tilt. -/
theorem missing_allocation_cutoff_bound (N : ℕ) (hN : 320 ≤ N) {x : ℝ}
    (hx : 0 ≤ x) (hxhi : x ≤ 81 / 200) :
    1 - (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x) ≤
      (40081 / 40000 : ℝ) * Real.exp (-(N : ℝ) / 400000) +
      Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) *
        ((5 / 6 : ℝ) * x + (1 - x)) ^ (N + 1) := by
  have hx1 : x ≤ 1 := by linarith
  have ht : 0 ≤ Real.log (201 / 200 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have h := missed_mass_bound N hN hx hx1
    (Real.exp_pos (-(13 / 32 : ℝ) * N * Real.log (201 / 200 : ℝ))).le
    (Real.exp_pos (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ))).le
    (by norm_num : (0 : ℝ) ≤ 201 / 200) (by norm_num : (0 : ℝ) ≤ 5 / 6) ?_ ?_
  · apply h.trans
    apply add_le_add _ le_rfl
    have hb : ((201 / 200 : ℝ) * x + (1 - x)) ^ (N + 1) ≤ (40081 / 40000 : ℝ) ^ (N + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp (-(13 / 32 : ℝ) * N * Real.log (201 / 200 : ℝ)) *
        (40081 / 40000 : ℝ) ^ (N + 1) = (40081 / 40000 : ℝ) *
          Real.exp ((N : ℝ) * (Real.log (40081 / 40000 : ℝ) -
            (13 / 32 : ℝ) * Real.log (201 / 200 : ℝ))) := by
      rw [pow_succ]
      have hp : (40081 / 40000 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log (40081 / 40000 : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [hp, show (N : ℝ) * (Real.log (40081 / 40000 : ℝ) -
        (13 / 32 : ℝ) * Real.log (201 / 200 : ℝ)) =
          -(13 / 32 : ℝ) * N * Real.log (201 / 200 : ℝ) +
            (N : ℝ) * Real.log (40081 / 40000 : ℝ) by ring, Real.exp_add]
      ring
    calc
      _ ≤ Real.exp (-(13 / 32 : ℝ) * N * Real.log (201 / 200 : ℝ)) * (40081 / 40000 : ℝ) ^ (N + 1) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := he
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left upper_log_rate (Nat.cast_nonneg (α := ℝ) N)]))
          (by norm_num)
  · intro k hk hcut
    have hc : (13 / 32 : ℝ) * N ≤ k := by
      have hn : 13 * N < 32 * k := by omega
      have hnR : (13 : ℝ) * N < 32 * k := by exact_mod_cast hn
      linarith
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 201 / 200),
      ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    simp only [Real.log_exp]
    nlinarith [mul_le_mul_of_nonneg_right hc ht]
  · intro k hk hcut
    have hkN : k ≤ N + 1 := by have := Finset.mem_range.mp hk; omega
    have hc : (k : ℝ) ≤ (N : ℝ) / 5 + 1 := by
      have hn : 5 * k ≤ N + 5 := by omega
      have hnR : (5 : ℝ) * k ≤ N + 5 := by exact_mod_cast hn
      linarith
    have he : (5 / 6 : ℝ) = Real.exp (-Real.log (6 / 5 : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hl]



/-- Both missing tails are exponentially small before source scaling.
This bound covers the whole interval between the new and old owner cuts. -/
theorem missing_allocation_bound (N : ℕ) (hN : 320 ≤ N) {x : ℝ}
    (hxlo : 7/20 ≤ x) (hxhi : x ≤ 81/200) :
    1-(∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      3*Real.exp (-(N : ℝ)/400000) := by
  have h := missing_allocation_cutoff_bound N hN (by linarith) hxhi
  have hl : Real.log (6/5 : ℝ)/5+Real.log (113/120 : ℝ) ≤ -(1/400000 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6/5)
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 113/120)
    linarith
  have hb : ((5/6 : ℝ)*x+(1-x))^(N+1) ≤ (113/120 : ℝ)^(N+1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have he : Real.exp (((N : ℝ)/5+1)*Real.log (6/5 : ℝ))*(113/120 : ℝ)^(N+1) =
      (113/100 : ℝ)*Real.exp ((N : ℝ)*(Real.log (6/5 : ℝ)/5+Real.log (113/120 : ℝ))) := by
    rw [show ((N : ℝ)/5+1)*Real.log (6/5 : ℝ) =
      Real.log (6/5 : ℝ)+(N : ℝ)*(Real.log (6/5 : ℝ)/5) by ring,
      Real.exp_add,Real.exp_log (by norm_num),pow_succ,
      ← Real.exp_log (by norm_num : (0 : ℝ) < 113/120),← Real.exp_nat_mul]
    simp only [Real.log_exp]
    rw [mul_add,Real.exp_add,Real.exp_log (by norm_num)]
    ring
  have ht : Real.exp (((N : ℝ)/5+1)*Real.log (6/5 : ℝ))*
      ((5/6 : ℝ)*x+(1-x))^(N+1) ≤ (113/100 : ℝ)*Real.exp (-(N : ℝ)/400000) := by
    apply (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)).trans
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) N)]
  nlinarith [Real.exp_pos (-(N : ℝ)/400000)]

/-- The original residual coefficient inherits the missing allocation
mass; no coefficient sign, count class or phase is changed. -/
theorem residual_coefficient_bound (A : Finset ℕ) (N : ℕ) (hN : 320 ≤ N)
    {L : ℝ} (hL : 0 < L) {n p : ℕ} (hn : Squarefree n)
    (hn1 : 1 < n) (hnp : ¬n.Prime) (hp : p ∈ n.primeFactors)
    (hpA : p ∈ A) (hel : eligibleCofactor p (n/p))
    (hlo : (119/200 : ℝ)*Real.log n ≤ Real.log p)
    (hhi : Real.log p ≤ (13/20 : ℝ)*Real.log n) :
    ‖residualCoefficient A L N n‖ ≤
      3*Real.exp (-(N : ℝ)/400000)*zetaMoebiusLogMajorant n := by
  let x := Real.log (n/p : ℕ)/Real.log n
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hlog : Real.log (n/p : ℕ) = Real.log n-Real.log p := by
    rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero),
      Real.log_div (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
  have hxlo : 7/20 ≤ x := (le_div_iff₀ hln).mpr (by rw [hlog]; linarith)
  have hxhi : x ≤ 81/200 := (div_le_iff₀ hln).mpr (by rw [hlog]; linarith)
  have hβ : 0 ≤ 1-allocationShare A N n := by
    linarith [(allocationShare_bounds A N hn hn1).2]
  have hmass := single_prime_mass_le_share A N hn hn1 hp hpA hel
  have hmiss := missing_allocation_bound N hN hxlo hxhi
  have hβle : 1-allocationShare A N n ≤ 3*Real.exp (-(N : ℝ)/400000) := by
    change (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      allocationShare A N n at hmass
    linarith
  rw [residualCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    boundedShare,if_pos ⟨hn,hn1,hnp⟩,abs_of_nonneg hβ]
  exact mul_le_mul hβle (SquarefreeVaughanLogSource.norm_coefficient_le hL n)
    (norm_nonneg _) (by positivity)

/-- The summability exponent is fixed independently of every arithmetic mask. -/
def paymentExponent : ℝ := 1+1/100000000

private theorem kernel_rate (N : ℕ) :
    Real.exp (-(N : ℝ)/400000)*(100000000/49999999 : ℝ)^N ≤
      (2 : ℝ)^N*Real.exp (-(N : ℝ)/500000) := by
  have hr : Real.exp (-(1/400000 : ℝ))*(100000000/49999999 : ℝ) ≤
      2*Real.exp (-(1/500000 : ℝ)) := by
    rw [Real.exp_neg,inv_mul_le_iff₀ (Real.exp_pos _),← mul_assoc,
      mul_comm (Real.exp _),mul_assoc,← Real.exp_add]
    have h := Real.add_one_le_exp (1/2000000 : ℝ)
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hr N
  simpa only [mul_pow,← Real.exp_nat_mul,show (N : ℝ)*(-(1/400000 : ℝ)) = -(N : ℝ)/400000 by ring,
    show (N : ℝ)*(-(1/500000 : ℝ)) = -(N : ℝ)/500000 by ring] using hp

/-- A literal all-count population whose owner is inside the new payable
interval. Additional masks remain in `S`. -/
def population (S A : Finset ℕ) : Finset ℕ := S.filter fun n =>
  Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧ ∃ p ∈ n.primeFactors,
    p ∈ A ∧ eligibleCofactor p (n/p) ∧
    (119/200 : ℝ)*Real.log n ≤ Real.log p ∧ Real.log p ≤ (13/20 : ℝ)*Real.log n

/-- The newly paid population is always taken from its stated signed rest. -/
theorem population_subset (S A : Finset ℕ) : population S A ⊆ S := Finset.filter_subset _ _

/-- An independent bound for the sum of the actual atom norms. Its rate
is used only relative to the existing joint credit. -/
theorem norm_mass_le (S A : Finset ℕ) (N : ℕ) (hN : 320 ≤ N)
    {L : ℝ} (hL : 0 < L) (y : ℝ) :
    (∑ n ∈ population S A,
      ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      3*zetaMoebiusLogMajorantMass paymentExponent*(2 : ℝ)^N*
        Real.exp (-(N : ℝ)/500000) := by
  have hrow (n : ℕ) (hn : n ∈ population S A) :
      ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (3*(2 : ℝ)^N*Real.exp (-(N : ℝ)/500000))*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight paymentExponent n) := by
    obtain ⟨_,hs,hn1,hnp,p,hp,hpA,hel,hlo,hhi⟩ := Finset.mem_filter.mp hn
    have hc := residual_coefficient_bound A N hN hL hs hn1 hnp hp hpA hel hlo hhi
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (100000000/49999999 : ℝ)^N*zetaPrimeExpWeight paymentExponent n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 49999999/100000000) using 1
      norm_num [paymentExponent]
    rw [norm_mul]
    apply (mul_le_mul hc hk (norm_nonneg _) (mul_nonneg (by positivity) (zetaMoebiusLogMajorant_nonneg n))).trans
    have hr := mul_le_mul_of_nonneg_left (kernel_rate N)
      (show 0 ≤ 3*zetaMoebiusLogMajorant n*zetaPrimeExpWeight paymentExponent n by
        exact mul_nonneg (mul_nonneg (by norm_num) (zetaMoebiusLogMajorant_nonneg n)) (Real.exp_nonneg _))
    convert hr using 1 <;> ring
  apply (Finset.sum_le_sum hrow).trans
  rw [← Finset.mul_sum]
  have hs := Summable.sum_le_tsum (population S A)
    (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_nonneg _))
    (summable_zetaMoebiusLogMajorant (σ := paymentExponent) (by norm_num [paymentExponent]))
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 3*(2 : ℝ)^N*Real.exp (-(N : ℝ)/500000) by positivity)
  simpa only [zetaMoebiusLogMajorantMass,zetaPrimeExpWeight,mul_assoc,mul_left_comm,mul_comm] using hm


/-- For every fixed nonzero height, the new all-count debit is eventually
an arbitrarily small fraction of the original central credit. No zero
hypothesis or source-scale smallness claim is used. -/
theorem eventually_norm_mass_credit {y ε : ℝ} (hy : y ≠ 0) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (L u : ℝ), 0 < L → 0 ≤ u →
      u^(N+1)*(∑ n ∈ population S A,
        ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          ε*ZetaRieszCentralReserve.sourceCredit u y N := by
  let c := Real.pi*Real.exp (-1)/(24000*|y|)
  have hc : 0 < c := by dsimp [c]; positivity
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1
    (Real.exp_pos (-(1/500000 : ℝ)))
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1/500000 : ℝ) < 0))).const_mul
      (3*zetaMoebiusLogMajorantMass paymentExponent)
  simp only [mul_zero,pow_one] at ht
  have he : Tendsto (fun N : ℕ => 3*zetaMoebiusLogMajorantMass paymentExponent*
      (((N : ℝ)+1)*Real.exp (-(N : ℝ)/500000))) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [] with N
    rw [← Real.exp_nat_mul]
    congr 3
    ring
  filter_upwards [he.eventually_le_const (mul_pos hε hc),eventually_ge_atTop (320 : ℕ)]
    with N hsmall hN S A L u hL hu
  have hscalar : 3*zetaMoebiusLogMajorantMass paymentExponent*
      Real.exp (-(N : ℝ)/500000) ≤ ε*c/((N : ℝ)+1) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ)+1)).mpr
    nlinarith only [hsmall]
  have hb := mul_le_mul_of_nonneg_left (norm_mass_le S A N hN hL y) (pow_nonneg hu (N+1))
  have hs := mul_le_mul_of_nonneg_left hscalar
    (show 0 ≤ u^(N+1)*(2 : ℝ)^N by positivity)
  apply hb.trans
  apply le_trans (by convert hs using 1; ring)
  dsimp only [ZetaRieszCentralReserve.sourceCredit,c]
  rw [pow_succ,mul_pow]
  ring_nf
  rfl

/-- Spending a proved norm debit on a subset of the signed rest retains
its favorable lower observation and subtracts the debit exactly once. -/
theorem floor_after_payment {S D : Finset ℕ} (f : ℕ → ℂ) {d g whole : ℝ}
    (hD : D ⊆ S) (hcost : (∑ n ∈ D, ‖f n‖) ≤ d)
    (hpaid : (∑ n ∈ S, f n).re+g ≤ whole) :
    (∑ n ∈ S\D, f n).re+max (∑ n ∈ D, f n).re 0+g-d ≤ whole := by
  have h := ZetaRieszJointPositiveFiveBounds.joint_floor_of_payment
    (S := S) (P := ∅) f (by simpa using hD) hcost (whole := (∑ n ∈ S, f n).re+2*d)
    (by simp)
  simp only [Finset.empty_union] at h
  linarith only [h,hpaid]

/-- The alternative upper observation uses the same single spending rule. -/
theorem ceiling_after_payment {S D : Finset ℕ} (f : ℕ → ℂ) {d g whole : ℝ}
    (hD : D ⊆ S) (hcost : (∑ n ∈ D, ‖f n‖) ≤ d)
    (hpaid : whole ≤ (∑ n ∈ S, f n).re-g) :
    whole ≤ (∑ n ∈ S\D, f n).re+min (∑ n ∈ D, f n).re 0-g+d := by
  have h := ZetaRieszJointPositiveFiveBounds.joint_ceiling_of_payment
    (S := S) (P := ∅) f (by simpa using hD) hcost (whole := (∑ n ∈ S, f n).re-2*d)
    (by simp)
  simp only [Finset.empty_union] at h
  linarith only [h,hpaid]


/-- On the actual cofinal core every nonzero label left after this payment
has every prime share below `119/200`; the physical and eligibility masks
are discharged from the original support, not assumed away. -/
theorem remaining_prime_log_lt (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {S : Finset ℕ}
    (hS : S ⊆ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)) {n : ℕ}
    (hnB : n ∈ S\population S (intermediatePrimes u (dyadicMomentOrder j)))
    (hcoeff : residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n ≠ 0) :
    ∀ p ∈ n.primeFactors, Real.log p < (119/200 : ℝ)*Real.log n := by
  let N := dyadicMomentOrder j
  obtain ⟨hnS0,hnnot⟩ := Finset.mem_sdiff.mp hnB
  have hncore := hS hnS0
  have hnnarrow := (Finset.mem_filter.mp hncore).1
  have hnnondominant := (Finset.mem_filter.mp hnnarrow).1
  have hnret := (Finset.mem_sdiff.mp hnnondominant).1
  have hnS := (Finset.mem_sdiff.mp hnret).1
  obtain ⟨hnfew,hw⟩ := Finset.mem_filter.mp hnS
  obtain ⟨hncentral,hc3,hcK⟩ := Finset.mem_filter.mp hnfew
  have hn : Squarefree n := by
    by_contra h
    apply hcoeff
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,h]
  have hnp : ¬n.Prime := by
    intro h
    rw [h.primeFactors,Finset.card_singleton] at hc3
    omega
  have hpX : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hncentral).1).1).2
  intro p hp
  by_contra hdom
  have hdom' : (119/200 : ℝ)*Real.log n ≤ Real.log p := le_of_not_gt hdom
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 < n := lt_of_lt_of_le hpp.one_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hpd)
  have hpN : N^2 < p := by
    by_contra hh
    have hpN' : p ≤ N^2 := le_of_not_gt hh
    have hsmall := few_smooth_divisor_log_le j hj hn hpd hcK (by
      intro q hq
      have hqp : q = p := by simpa only [hpp.primeFactors,Finset.mem_singleton] using hq
      simpa only [hqp] using hpN')
    have hlo : (7/4 : ℝ)*N < Real.log n := hw.1
    change Real.log p ≤ (N : ℝ)/4 at hsmall
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hpA : p ∈ intermediatePrimes u N :=
    (mem_intermediatePrimes u N p).mpr ⟨hpp,hpN,hpX p hp⟩
  have hel := eligible_of_three_prime_factors hn hc3 hp
  have hphi : Real.log p < (13/20 : ℝ)*Real.log n := by
    by_contra hh
    apply (Finset.mem_sdiff.mp hnnondominant).2
    exact Finset.mem_filter.mpr ⟨hnret,hn,hn1,hnp,p,hp,hpA,hel,le_of_not_gt hh⟩
  exact hnnot (Finset.mem_filter.mpr ⟨hnS0,hn,hn1,hnp,p,hp,hpA,hel,hdom',hphi.le⟩)



/-- Source scaling is applied before the debit is spent in the lower ledger. -/
theorem scaled_floor_after_payment {S D : Finset ℕ} (f : ℕ → ℂ) {a d g whole : ℝ}
    (ha : 0 ≤ a) (hD : D ⊆ S) (hcost : a*(∑ n ∈ D, ‖f n‖) ≤ d)
    (hpaid : a*(∑ n ∈ S, f n).re+g ≤ whole) :
    a*((∑ n ∈ S\D, f n).re+max (∑ n ∈ D, f n).re 0)+g-d ≤ whole := by
  have hn (n : ℕ) : ‖(a : ℂ)*f n‖ = a*‖f n‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ha]
  have hc : (∑ n ∈ D, ‖(a : ℂ)*f n‖) ≤ d := by simpa only [hn,← Finset.mul_sum] using hcost
  have h := floor_after_payment (fun n => (a : ℂ)*f n) hD hc (g := g) (whole := whole) (by
    simpa only [← Finset.mul_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hpaid)
  simpa only [← Finset.mul_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    mul_add,mul_max_of_nonneg _ _ ha,mul_zero] using h

/-- Source scaling is applied before the debit is spent in the upper ledger. -/
theorem scaled_ceiling_after_payment {S D : Finset ℕ} (f : ℕ → ℂ) {a d g whole : ℝ}
    (ha : 0 ≤ a) (hD : D ⊆ S) (hcost : a*(∑ n ∈ D, ‖f n‖) ≤ d)
    (hpaid : whole ≤ a*(∑ n ∈ S, f n).re-g) :
    whole ≤ a*((∑ n ∈ S\D, f n).re+min (∑ n ∈ D, f n).re 0)-g+d := by
  have hn (n : ℕ) : ‖(a : ℂ)*f n‖ = a*‖f n‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ha]
  have hc : (∑ n ∈ D, ‖(a : ℂ)*f n‖) ≤ d := by simpa only [hn,← Finset.mul_sum] using hcost
  have h := ceiling_after_payment (fun n => (a : ℂ)*f n) hD hc (g := g) (whole := whole) (by
    simpa only [← Finset.mul_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hpaid)
  simpa only [← Finset.mul_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    mul_add,mul_min_of_nonneg _ _ ha,mul_zero] using h

end
end RiemannGaussian.ZetaRieszJointOwnerPayment
