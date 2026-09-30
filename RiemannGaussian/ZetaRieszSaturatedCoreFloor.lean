/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedPhysical
import RiemannGaussian.ZetaRieszPairBoundary

/-!
# Exact reflected saturation in the whole physical floor

The active cofactor, rather than just the number of reflected-large primes,
detects a zero contribution. Saturation at either of two successive cutoffs
cancels entire labels. In the two-outer-prime layer the complete active-count
parity cancels, and below the first possible composite divisor the actual
short-prime prefix is evaluated with its signs intact. The whole-core floor
intersects these savings with the older reflected bounds, then transfers to
joinedPhysical with its already paid geometric error. Every favorable real
observation remains. The remaining signed budget is not bounded by 79/1000.
-/

namespace RiemannGaussian.ZetaRieszSaturatedCoreFloor
noncomputable section
open scoped BigOperators Classical
open ZetaRieszReflectedPrimeBounds ZetaRieszJointAllocation ZetaRieszParityPacket
open ZetaRieszOneSidedArithmetic ZetaRieszJoinedPhysical ZetaRieszAnnulusJoint

/-- The actual reflected active cofactor is composite and saturated. This
criterion uses prime geometry, not an estimate or a countwise allowance. -/
def SaturatedActive (L : ℝ) (n : ℕ) : Prop :=
  Squarefree n ∧ 2 ≤ (activePrimes (Real.log n-L) n).card ∧
    Real.log (activePart (Real.log n-L) n) ≤ Real.log n-L

/-- Every divisor and its sign have cancelled before any phase is used. -/
theorem coefficient_eq_zero_of_saturatedActive {L : ℝ} {n : ℕ}
    (hs : SaturatedActive L n) : SquarefreeVaughanLogSource.coefficient L n = 0 := by
  obtain ⟨hn,hc,hlog⟩ := hs
  have hprod : Squarefree (outerPart (Real.log n-L) n*activePart (Real.log n-L) n) := by
    rw [factorization _ hn]
    exact hn
  have ha1 : activePart (Real.log n-L) n ≠ 1 := by
    intro h
    rw [← activePart_primeFactors,h] at hc
    norm_num at hc
  have hap : ¬(activePart (Real.log n-L) n).Prime := by
    intro h
    rw [← activePart_primeFactors,h.primeFactors,Finset.card_singleton] at hc
    omega
  have hnc : 2 ≤ n.primeFactors.card := by
    have hh := count_split (Real.log n-L) n
    omega
  have hz := ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated
    hprod.of_mul_right ha1 hap hlog
  have hr := coefficient_eq_active hn hnc (L := L)
  rw [hz,mul_zero] at hr
  exact Complex.ext hr (ZetaRieszCosineCarrier.coefficient_im_eq_zero L n)

/-- An outer product crossing L saturates the entire active cofactor. -/
theorem saturatedActive_of_outer_log {L : ℝ} {n : ℕ} (hn : Squarefree n)
    (hc : 2 ≤ (activePrimes (Real.log n-L) n).card)
    (houter : L ≤ Real.log (outerPart (Real.log n-L) n)) : SaturatedActive L n := by
  have hprod : Squarefree (outerPart (Real.log n-L) n*activePart (Real.log n-L) n) := by
    rw [factorization _ hn]
    exact hn
  have hl : Real.log n = Real.log (outerPart (Real.log n-L) n)+
      Real.log (activePart (Real.log n-L) n) := by
    conv_lhs => rw [← factorization (Real.log n-L) hn]
    rw [Nat.cast_mul,Real.log_mul
      (by exact_mod_cast hprod.of_mul_left.ne_zero)
      (by exact_mod_cast hprod.of_mul_right.ne_zero)]
  exact ⟨hn,hc,by linarith⟩

/-- TWO reflected large primes suffice when their product reaches the
original cutoff and at least two prime factors remain. All counts >=4 enter. -/
theorem coefficient_eq_zero_of_two_outer {L : ℝ} {n : ℕ} (hn : Squarefree n)
    (hc : 4 ≤ n.primeFactors.card)
    (ho : (outerPrimes (Real.log n-L) n).card = 2)
    (houter : L ≤ Real.log (outerPart (Real.log n-L) n)) :
    SquarefreeVaughanLogSource.coefficient L n = 0 := by
  apply coefficient_eq_zero_of_saturatedActive
  apply saturatedActive_of_outer_log hn _ houter
  have hh := count_split (Real.log n-L) n
  omega

/-- Every surviving higher-count core label has TOTAL reflected-large log
strictly below L. A count bound alone does not give this additional geometry. -/
theorem nonzero_core_outer_log_lt {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hc : 5 ≤ n.primeFactors.card)
    (hz : residualCoefficient (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n ≠ 0) :
    Real.log (outerPart (Real.log n-SquarefreeVaughanLogSource.length u N) n) <
      SquarefreeVaughanLogSource.length u N := by
  by_contra! hh
  have ha := active_count_ge_two hs hc (core_cutoff_quarter hu hN hn)
  have he := coefficient_eq_zero_of_saturatedActive (saturatedActive_of_outer_log hs ha hh)
  apply hz
  simp only [residualCoefficient,he,mul_zero]

/-- The zero is the FULL physical atom, including old allocation and phase. -/
theorem fullTranslatedAtom_eq_zero {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K)
    (hs : SaturatedActive (SquarefreeVaughanLogSource.length u N) n) (y : ℝ) :
    fullTranslatedAtom u y N n = 0 := by
  rw [fullTranslatedAtom_eq_original hn hs.1 y,residualCoefficient,
    coefficient_eq_zero_of_saturatedActive hs,mul_zero,zero_mul]

/-- An independent whole-core lower bound: remove exactly the saturated
charges while retaining all favorable real observations and every other
original weight. No zero hypothesis or countwise sum completion is used. -/
theorem core_floor_without_saturated_charge (u y : ℝ) (N K : ℕ) :
    (∑ n ∈ (coreBand u N K).filter Squarefree, max (fullTranslatedAtom u y N n).re 0)-
      (∑ n ∈ ((coreBand u N K).filter Squarefree).filter
        (fun n : ℕ => ¬SaturatedActive (SquarefreeVaughanLogSource.length u N) n),
        weight (intermediatePrimes u N) N n*
          ZetaRieszSignedSperner.lowerCost (SquarefreeVaughanLogSource.length u N) y n) ≤
      (coreResponse u y N K).re := by
  rw [core_eq_fullTranslated,Complex.re_sum]
  conv_lhs => arg 2; rw [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hc := (Finset.mem_filter.mp hn).1
  have hs := (Finset.mem_filter.mp hn).2
  by_cases hz : SaturatedActive (SquarefreeVaughanLogSource.length u N) n
  · rw [if_neg (not_not.mpr hz),fullTranslatedAtom_eq_zero hc hz y]
    norm_num
  · rw [if_pos hz,fullTranslatedAtom_eq_original hc hs y]
    exact (ZetaRieszSignedSperner.residual_atom_retained_bounds (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length_pos u N) y N n).1

/-- A common geometric layer for ALL counts with two reflected-large primes.
The short remaining cutoff sees only the unit divisor of the active cofactor. -/
def TwoOuterInner (L : ℝ) (n : ℕ) : Prop :=
  Squarefree n ∧ 4 ≤ n.primeFactors.card ∧
    (outerPrimes (Real.log n-L) n).card = 2 ∧
    L-Real.log (outerPart (Real.log n-L) n) ≤
      Real.log (activePart (Real.log n-L) n).minFac

/-- Two reflected large primes remove the TOTAL-count parity exactly. The
remaining response has the short cutoff L-log(outerPart), for every active
cofactor count. This is used below to estimate the actual full atom. -/
theorem coefficient_two_outer_response {L : ℝ} {n : ℕ} (hn : Squarefree n)
    (hc : 4 ≤ n.primeFactors.card)
    (ho : (outerPrimes (Real.log n-L) n).card = 2) :
    (SquarefreeVaughanLogSource.coefficient L n).re =
      -(Real.log n/L)*VaughanLogAverage.riesz
        (L-Real.log (outerPart (Real.log n-L) n)) (activePart (Real.log n-L) n) := by
  let D := Real.log n-L
  let a := activePart D n
  let v := L-Real.log (outerPart D n)
  have hp : Squarefree (outerPart D n*a) := by
    dsimp [a]
    rw [factorization D hn]
    exact hn
  have hac : 2 ≤ a.primeFactors.card := by
    have hh := count_split D n
    rw [← activePart_primeFactors] at hh
    change (outerPrimes (Real.log n-L) n).card+a.primeFactors.card = _ at hh
    omega
  have ha1 : a ≠ 1 := by intro hh; simp [hh] at hac
  have hap : ¬a.Prime := by intro hh; simp [hh.primeFactors] at hac
  have hl : Real.log n = Real.log (outerPart D n)+Real.log a := by
    conv_lhs => rw [← factorization D hn]
    rw [Nat.cast_mul,Real.log_mul
      (by exact_mod_cast hp.of_mul_left.ne_zero)
      (by exact_mod_cast hp.of_mul_right.ne_zero)]
  have hv : Real.log a-v = D := by dsimp [v,D]; linarith
  have hr := VaughanLogAverage.riesz_reflection v hp.of_mul_right ha1 hap
  rw [hv] at hr
  have hcount : n.primeFactors.card = a.primeFactors.card+2 := by
    have hh := count_split D n
    rw [← activePart_primeFactors] at hh
    change (outerPrimes (Real.log n-L) n).card+a.primeFactors.card = _ at hh
    omega
  have hmu : (-1 : ℝ)^n.primeFactors.card*
      (ArithmeticFunction.moebius a : ℝ) = 1 := by
    rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hp.of_mul_right]
    push_cast
    rw [hcount,pow_add]
    norm_num
    rw [← mul_pow]
    norm_num
  rw [coefficient_eq_active hn (by omega : 2 ≤ n.primeFactors.card)]
  change -(Real.log n/L)*(-1 : ℝ)^n.primeFactors.card*VaughanLogAverage.riesz D a = _
  rw [hr]
  calc
    _ = -(Real.log n/L)*((-1 : ℝ)^n.primeFactors.card*
        (ArithmeticFunction.moebius a : ℝ))*VaughanLogAverage.riesz v a := by ring
    _ = _ := by rw [hmu]; dsimp [v,D]; ring

/-- A second saturation at the reflected active cofactor's short cutoff.
The number of original outer primes is unrestricted. -/
def ReflectedPrefixSaturated (L : ℝ) (n : ℕ) : Prop :=
  Squarefree n ∧ 2 ≤ (activePrimes (Real.log n-L) n).card ∧
    let a := activePart (Real.log n-L) n
    let v := L-Real.log (outerPart (Real.log n-L) n)
    2 ≤ (activePrimes v a).card ∧ Real.log (activePart v a) ≤ v

/-- A second active-prefix saturation cancels the ENTIRE original label.
This applies to every outer count, total count, phase and factorial weight. -/
theorem coefficient_eq_zero_of_reflectedPrefix {L : ℝ} {n : ℕ}
    (h : ReflectedPrefixSaturated L n) : SquarefreeVaughanLogSource.coefficient L n = 0 := by
  let D := Real.log n-L
  let a := activePart D n
  let v := L-Real.log (outerPart D n)
  have hn : Squarefree (outerPart D n*a) := by
    rw [factorization _ h.1]
    exact h.1
  have ha : Squarefree a := hn.of_mul_right
  have hb : Squarefree (activePart v a) := by
    have hs : Squarefree (outerPart v a*activePart v a) := by
      rw [factorization v ha]
      exact ha
    exact hs.of_mul_right
  have hc : 2 ≤ (activePart v a).primeFactors.card := by
    rw [activePart_primeFactors]
    exact h.2.2.1
  have hb1 : activePart v a ≠ 1 := by intro he; simp [he] at hc
  have hbp : ¬(activePart v a).Prime := by intro hp; simp [hp.primeFactors] at hc
  have hz : VaughanLogAverage.riesz v a = 0 := by
    rw [riesz_eq_active v ha]
    exact ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hb hb1 hbp h.2.2.2
  have hac : 2 ≤ a.primeFactors.card := by rw [activePart_primeFactors]; exact h.2.1
  have ha1 : a ≠ 1 := by intro he; simp [he] at hac
  have hap : ¬a.Prime := by intro hp; simp [hp.primeFactors] at hac
  have hl : Real.log n = Real.log (outerPart D n)+Real.log a := by
    conv_lhs => rw [← factorization D h.1]
    rw [Nat.cast_mul,Real.log_mul
      (by exact_mod_cast hn.of_mul_left.ne_zero)
      (by exact_mod_cast ha.ne_zero)]
  have hv : Real.log a-v = D := by dsimp [v,D]; linarith
  have hr := VaughanLogAverage.riesz_reflection v ha ha1 hap
  rw [hv,hz,mul_zero] at hr
  have hnc : 2 ≤ n.primeFactors.card := by
    have hh := count_split D n
    have := h.2.1
    change (outerPrimes (Real.log n-L) n).card+
      (activePrimes (Real.log n-L) n).card = n.primeFactors.card at hh
    omega
  have he := coefficient_eq_active h.1 hnc (L := L)
  change (SquarefreeVaughanLogSource.coefficient L n).re =
    -(Real.log n/L)*(-1 : ℝ)^n.primeFactors.card*VaughanLogAverage.riesz D a at he
  rw [hr,mul_zero] at he
  exact Complex.ext he (ZetaRieszCosineCarrier.coefficient_im_eq_zero L n)

/-- Either evaluated saturation removes the literal physical atom, with
no mask deletion, count completion, or phase restriction. -/
theorem fullTranslatedAtom_eq_zero_of_either {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (y : ℝ)
    (h : SaturatedActive (SquarefreeVaughanLogSource.length u N) n ∨
      ReflectedPrefixSaturated (SquarefreeVaughanLogSource.length u N) n) :
    fullTranslatedAtom u y N n = 0 := by
  rcases h with h | h
  · exact fullTranslatedAtom_eq_zero hn h y
  · rw [fullTranslatedAtom_eq_original hn h.1 y,residualCoefficient,
      coefficient_eq_zero_of_reflectedPrefix h,mul_zero,zero_mul]

/-- In the inner layer only the unit divisor remains. -/
theorem coefficient_two_outer_inner {L : ℝ} {n : ℕ} (h : TwoOuterInner L n) :
    (SquarefreeVaughanLogSource.coefficient L n).re =
      -(Real.log n/L)*max 0 (L-Real.log (outerPart (Real.log n-L) n)) := by
  rw [coefficient_two_outer_response h.1 h.2.1 h.2.2.1]
  congr 1
  have hp : Squarefree (outerPart (Real.log n-L) n*activePart (Real.log n-L) n) := by
    rw [factorization _ h.1]
    exact h.1
  by_cases hv : L-Real.log (outerPart (Real.log n-L) n) ≤ 0
  · rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos hv,max_eq_left hv]
  · rw [ZetaRieszTypeII.riesz_eq_cutoff_below_minFac hp.of_mul_right.ne_zero
      (by linarith) h.2.2.2,max_eq_right (by linarith)]

/-- Only the adverse cosine is charged, with the EXACT remaining pair gap. -/
def innerFloorCost (L y : ℝ) (n : ℕ) : ℝ :=
  (Real.log n/L)*max 0 (L-Real.log (outerPart (Real.log n-L) n))*
    max (Real.cos (y*Real.log n)) 0

/-- The new charge cannot exceed the previously proved signed allowance.
This comparison is independent of the count and of every prime phase. -/
theorem innerFloorCost_le_previous {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : TwoOuterInner L n) :
    innerFloorCost L y n ≤ ZetaRieszSignedSperner.lowerCost L y n := by
  have hb := (ZetaRieszSignedSperner.coefficient_phase_bounds hL y n).1
  rw [coefficient_two_outer_inner h] at hb
  by_cases hc : 0 ≤ Real.cos (y*Real.log n)
  · rw [innerFloorCost,max_eq_left hc]
    nlinarith
  · rw [innerFloorCost,max_eq_right (le_of_not_ge hc),mul_zero]
    exact (ZetaRieszSignedSperner.costs_nonneg hL y n).1

/-- On this layer the lower bound is an equality: every favorable
observation is retained and the adverse charge has no antichain loss. -/
theorem inner_floor_exact (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (y : ℝ) {n : ℕ} (h : TwoOuterInner L n) :
    let f := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max f 0-weight A N n*innerFloorCost L y n = f := by
  dsimp only
  rw [ZetaRieszOneSidedArithmetic.re_residual_atom,coefficient_two_outer_inner h]
  have hb : 0 ≤ weight A N n*(Real.log n/L)*
      max 0 (L-Real.log (outerPart (Real.log n-L) n)) := by
    positivity [weight_nonneg A N n,Real.log_natCast_nonneg n]
  by_cases hc : 0 ≤ Real.cos (y*Real.log n)
  · have hf : weight A N n*(-(Real.log n/L)*
        max 0 (L-Real.log (outerPart (Real.log n-L) n)))*Real.cos (y*Real.log n) ≤ 0 := by
      nlinarith [mul_nonneg hb hc]
    rw [mul_assoc] at hf
    rw [max_eq_right hf,innerFloorCost,max_eq_left hc]
    ring
  · have hf : 0 ≤ weight A N n*(-(Real.log n/L)*
        max 0 (L-Real.log (outerPart (Real.log n-L) n)))*Real.cos (y*Real.log n) := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hb (le_of_not_ge hc)]
    rw [mul_assoc] at hf
    rw [max_eq_left hf,innerFloorCost,max_eq_right (le_of_not_ge hc)]
    ring

/-- A quantitative saving across every count in the inner pair layer.
When its clipped gap is at most one quarter of the mean prime log, the
adverse charge is at most one quarter of the old signed charge. -/
theorem innerFloorCost_le_quarter {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : TwoOuterInner L n)
    (hgap : 4*max 0 (L-Real.log (outerPart (Real.log n-L) n)) ≤
      Real.log n/n.primeFactors.card) :
    innerFloorCost L y n ≤ (1/4 : ℝ)*ZetaRieszSignedSperner.lowerCost L y n := by
  have ht : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  have hm : 0 ≤ Real.log n/n.primeFactors.card :=
    div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg _)
  have hcap : (1 : ℝ) ≤ (ZetaRieszSignedSperner.parityCapacity (n.primeFactors.card-2) 0 : ℝ) := by
    exact_mod_cast (show 1 ≤ ZetaRieszSignedSperner.parityCapacity (n.primeFactors.card-2) 0 by
      simpa only [Nat.choose_zero_right] using
        ZetaRieszSignedSperner.choose_le_parityCapacity
          (k := n.primeFactors.card-2) (j := 0) (Nat.zero_le _) (by decide))
  have hs : Squarefree n ∧ 2 ≤ n.primeFactors.card := ⟨h.1,by have := h.2.1; omega⟩
  have hb : (Real.log n/L)*max 0 (L-Real.log (outerPart (Real.log n-L) n)) ≤
      (1/4 : ℝ)*ZetaRieszSignedSperner.signedAllowance L n 0 := by
    rw [ZetaRieszSignedSperner.signedAllowance,if_pos hs]
    have hg := mul_le_mul_of_nonneg_left hgap ht
    have hh := mul_le_mul_of_nonneg_left hcap (mul_nonneg ht hm)
    nlinarith
  have hc := mul_le_mul_of_nonneg_right hb (le_max_right (Real.cos (y*Real.log n)) 0)
  have ho : 0 ≤ ZetaRieszSignedSperner.signedAllowance L n 1*
      max (-Real.cos (y*Real.log n)) 0 :=
    mul_nonneg (ZetaRieszSignedSperner.signedAllowance_nonneg hL n 1) (le_max_right _ _)
  dsimp only [innerFloorCost,ZetaRieszSignedSperner.lowerCost]
  nlinarith

/-- Up to the first possible TWO-prime divisor, the signed Riesz response
is exactly its unit term minus the complete single-prime prefix. Large
primes and every total prime count are retained in the label. -/
theorem riesz_eq_prime_prefix {a : ℕ} (ha : Squarefree a) {v : ℝ}
    (hmin : v/2 ≤ Real.log a.minFac) :
    VaughanLogAverage.riesz v a = max 0 v-
      ∑ p ∈ a.primeFactors, max 0 (v-Real.log p) := by
  by_cases hv : v ≤ 0
  · rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos hv,max_eq_left hv]
    have hz : (∑ p ∈ a.primeFactors, max 0 (v-Real.log p)) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      exact max_eq_left (by linarith [Real.log_natCast_nonneg p])
    rw [hz,sub_self]
  · have hv0 : 0 ≤ v := by linarith
    let f := fun d : ℕ => (ArithmeticFunction.moebius d : ℝ)*max 0 (v-Real.log d)
    have h1 : 1 ∉ a.primeFactors := fun h => Nat.not_prime_one (Nat.prime_of_mem_primeFactors h)
    have hsub : insert 1 a.primeFactors ⊆ a.divisors := by
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Nat.mem_divisors.mpr ⟨one_dvd _,ha.ne_zero⟩
      · exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hd,ha.ne_zero⟩
    have he : (∑ d ∈ insert 1 a.primeFactors, f d) = ∑ d ∈ a.divisors, f d := by
      apply Finset.sum_subset hsub
      intro d hd hout
      have hd1 : d ≠ 1 := fun h => hout (by simp [h])
      have hdp : ¬d.Prime := fun h => hout (Finset.mem_insert_of_mem
        (h.mem_primeFactors (Nat.dvd_of_mem_divisors hd) ha.ne_zero))
      have hlog := ZetaRieszReflectedLinear.composite_divisor_log_ge ha hd hd1 hdp hv0
        (fun p hp => hmin.trans (Real.log_le_log
          (by exact_mod_cast Nat.minFac_pos a : (0 : ℝ) < a.minFac)
          (by exact_mod_cast (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
            (Nat.dvd_of_mem_primeFactors hp)))))
      simp only [f,max_eq_left (sub_nonpos.mpr hlog),mul_zero]
    change (∑ d ∈ a.divisors, f d) = _
    rw [← he,Finset.sum_insert h1]
    have hf : f 1 = max 0 v := by simp [f]
    have hs : (∑ p ∈ a.primeFactors, f p) =
        -(∑ p ∈ a.primeFactors, max 0 (v-Real.log p)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      simp [f,ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
    rw [hf,hs]
    ring

/-- A wider, count-independent layer than TwoOuterInner: the remaining
cutoff can pass several primes, but not a product of two of them. -/
def TwoOuterPrimePrefix (L : ℝ) (n : ℕ) : Prop :=
  Squarefree n ∧ 4 ≤ n.primeFactors.card ∧
    (outerPrimes (Real.log n-L) n).card = 2 ∧
    (L-Real.log (outerPart (Real.log n-L) n))/2 ≤
      Real.log (activePart (Real.log n-L) n).minFac

/-- An evaluated signed prime prefix, not a capacity bound. -/
def primePrefixResponse (L : ℝ) (n : ℕ) : ℝ :=
  let v := L-Real.log (outerPart (Real.log n-L) n)
  max 0 v-∑ p ∈ (activePart (Real.log n-L) n).primeFactors, max 0 (v-Real.log p)

/-- Across ALL total counts, the exact short-prime debits oppose the
remaining unit hinge before the phase or norm is applied. -/
theorem coefficient_two_outer_prime_prefix {L : ℝ} {n : ℕ}
    (h : TwoOuterPrimePrefix L n) :
    (SquarefreeVaughanLogSource.coefficient L n).re =
      -(Real.log n/L)*primePrefixResponse L n := by
  rw [coefficient_two_outer_response h.1 h.2.1 h.2.2.1]
  have hs : Squarefree (outerPart (Real.log n-L) n*activePart (Real.log n-L) n) := by
    rw [factorization _ h.1]
    exact h.1
  rw [riesz_eq_prime_prefix hs.of_mul_right h.2.2.2]
  rfl

/-- The entire adverse real part, AFTER the prime prefix has cancelled
the unit hinge. It keeps both phase orientations and has no count loss. -/
def primePrefixFloorCost (L y : ℝ) (n : ℕ) : ℝ :=
  max ((Real.log n/L)*primePrefixResponse L n*Real.cos (y*Real.log n)) 0

theorem primePrefixFloorCost_le_previous {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : TwoOuterPrimePrefix L n) :
    primePrefixFloorCost L y n ≤ ZetaRieszSignedSperner.lowerCost L y n := by
  have hb := (ZetaRieszSignedSperner.coefficient_phase_bounds hL y n).1
  rw [coefficient_two_outer_prime_prefix h] at hb
  exact max_le (by nlinarith only [hb]) (ZetaRieszSignedSperner.costs_nonneg hL y n).1

/-- This lower comparison is an equality on the whole prime-prefix layer.
In particular no favorable signed term is spent separately as a credit. -/
theorem prime_prefix_floor_exact (A : Finset ℕ) (L : ℝ) (N : ℕ) (y : ℝ) {n : ℕ}
    (h : TwoOuterPrimePrefix L n) :
    let f := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max f 0-weight A N n*primePrefixFloorCost L y n = f := by
  dsimp only
  rw [ZetaRieszOneSidedArithmetic.re_residual_atom,coefficient_two_outer_prime_prefix h]
  have hw := weight_nonneg A N n
  let x := (Real.log n/L)*primePrefixResponse L n*Real.cos (y*Real.log n)
  have he : weight A N n*(-(Real.log n/L)*primePrefixResponse L n*
      Real.cos (y*Real.log n)) = -(weight A N n*x) := by dsimp [x]; ring
  rw [he]
  change max (-(weight A N n*x)) 0-weight A N n*max x 0 = -(weight A N n*x)
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr (mul_nonneg hw hx))]
    ring
  · rw [max_eq_right (le_of_not_ge hx),
      max_eq_left (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hw (le_of_not_ge hx)))]
    ring

/-- A joint short-prime cancellation, independent of the total count.
Three actual primes each below two thirds of the short cutoff exhaust its
unit hinge. Further prefix primes only strengthen this inequality. -/
theorem primePrefixResponse_nonpos_of_three {L : ℝ} {n : ℕ} (S : Finset ℕ)
    (hS : S ⊆ (activePart (Real.log n-L) n).primeFactors) (hcard : S.card = 3)
    (hv : 0 ≤ L-Real.log (outerPart (Real.log n-L) n))
    (hsmall : ∀ p ∈ S, Real.log p ≤ (2/3 : ℝ)*(L-Real.log (outerPart (Real.log n-L) n))) :
    primePrefixResponse L n ≤ 0 := by
  let v := L-Real.log (outerPart (Real.log n-L) n)
  have hl : ∑ p ∈ S, (v/3) ≤ ∑ p ∈ S, max 0 (v-Real.log p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hh := hsmall p hp
    change Real.log p ≤ (2/3 : ℝ)*v at hh
    exact (show v/3 ≤ v-Real.log p by linarith).trans (le_max_right _ _)
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun p _ _ => le_max_left 0 (v-Real.log p))
  simp only [Finset.sum_const,nsmul_eq_mul,hcard,Nat.cast_ofNat] at hl
  change max 0 v-(∑ p ∈ (activePart (Real.log n-L) n).primeFactors,
    max 0 (v-Real.log p)) ≤ 0
  rw [max_eq_right hv]
  linarith

/-- The common three-prime cancellation supplies a nonnegative FULL
physical atom on its favorable phase. This covers every total prime count
and retains the old allocation and every core mask. -/
theorem fullTranslatedAtom_nonneg_of_three_prefix {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (y : ℝ)
    (h : TwoOuterPrimePrefix (SquarefreeVaughanLogSource.length u N) n)
    (S : Finset ℕ)
    (hS : S ⊆ (activePart (Real.log n-SquarefreeVaughanLogSource.length u N) n).primeFactors)
    (hcard : S.card = 3)
    (hv : 0 ≤ SquarefreeVaughanLogSource.length u N-
      Real.log (outerPart (Real.log n-SquarefreeVaughanLogSource.length u N) n))
    (hsmall : ∀ p ∈ S, Real.log p ≤ (2/3 : ℝ)*(SquarefreeVaughanLogSource.length u N-
      Real.log (outerPart (Real.log n-SquarefreeVaughanLogSource.length u N) n)))
    (hphase : 0 ≤ Real.cos (y*Real.log n)) : 0 ≤ (fullTranslatedAtom u y N n).re := by
  rw [fullTranslatedAtom_eq_original hn h.1 y,ZetaRieszOneSidedArithmetic.re_residual_atom,
    coefficient_two_outer_prime_prefix h]
  have hr := primePrefixResponse_nonpos_of_three S hS hcard hv hsmall
  have hc : 0 ≤ -(Real.log n/SquarefreeVaughanLogSource.length u N)*
      primePrefixResponse (SquarefreeVaughanLogSource.length u N) n := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (div_nonneg (Real.log_natCast_nonneg n)
        (SquarefreeVaughanLogSource.length_pos u N).le)) hr
  exact mul_nonneg (weight_nonneg _ _ _) (mul_nonneg hc hphase)

/-- A refinement of the existing floor charge, with exact zero and clipped
pair responses. The original phase is retained in every branch. -/
def floorCost (L y : ℝ) (n : ℕ) : ℝ :=
  if SaturatedActive L n ∨ ReflectedPrefixSaturated L n then 0
  else if TwoOuterPrimePrefix L n then primePrefixFloorCost L y n
  else ZetaRieszSignedSperner.lowerCost L y n

/-- The refinement never increases any previous signed charge. -/
theorem floorCost_le_previous {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    floorCost L y n ≤ ZetaRieszSignedSperner.lowerCost L y n := by
  unfold floorCost
  split_ifs with hs hi
  · exact (ZetaRieszSignedSperner.costs_nonneg hL y n).1
  · exact primePrefixFloorCost_le_previous hL y hi
  · rfl

theorem floorCost_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ floorCost L y n := by
  unfold floorCost
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _
  · exact (ZetaRieszSignedSperner.costs_nonneg hL y n).1

/-- The new cancellation bounds the original atom on ANY selected subset.
No core membership or removal of nonsquarefree labels is needed, so this
estimate can be spent only on the unpaid rest of an existing floor. -/
theorem residual_retained_floor (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N n : ℕ) :
    let v := (residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*floorCost L y n ≤ v := by
  dsimp only
  unfold floorCost
  split_ifs with hz hi
  · have he : SquarefreeVaughanLogSource.coefficient L n = 0 := by
      rcases hz with hz | hz
      · exact coefficient_eq_zero_of_saturatedActive hz
      · exact coefficient_eq_zero_of_reflectedPrefix hz
    simp only [residualCoefficient,he,mul_zero,zero_mul,Complex.zero_re,max_self,
      sub_zero,le_refl]
  · exact (prime_prefix_floor_exact A L N y hi).le
  · exact (ZetaRieszSignedSperner.residual_atom_retained_bounds A hL y N n).1

/-- A cancelled unit hinge incurs ZERO adverse cost on the positive
cosine phase. The entire favorable observation remains in the floor. -/
theorem floorCost_eq_zero_of_prefix_credit {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : TwoOuterPrimePrefix L n) (hcredit : primePrefixResponse L n ≤ 0)
    (hphase : 0 ≤ Real.cos (y*Real.log n)) : floorCost L y n = 0 := by
  by_cases hs : SaturatedActive L n ∨ ReflectedPrefixSaturated L n
  · simp only [floorCost,if_pos hs]
  · rw [floorCost,if_neg hs,if_pos h]
    exact max_eq_right (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (Real.log_natCast_nonneg n) hL.le) hcredit) hphase)

/-- Intersection with the previously proved reflected/complementary-divisor
costs. New exact cancellations never spend or overwrite those older savings. -/
def combinedFloorCost (L y : ℝ) (n : ℕ) : ℝ :=
  if 5 ≤ n.primeFactors.card then min (floorCost L y n)
    (ZetaRieszReflectedPrimeBounds.floorCost L y n) else floorCost L y n

theorem combinedFloorCost_le_new (L y : ℝ) (n : ℕ) :
    combinedFloorCost L y n ≤ floorCost L y n := by
  unfold combinedFloorCost
  split_ifs
  · exact min_le_left _ _
  · rfl

/-- The wider prefix computation agrees with the earlier exact inner
layer. This is a comparison on the same atom, not an additional credit. -/
theorem primePrefixFloorCost_eq_inner {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : TwoOuterInner L n) : primePrefixFloorCost L y n = innerFloorCost L y n := by
  have hp : TwoOuterPrimePrefix L n := ⟨h.1,h.2.1,h.2.2.1,by
    have := h.2.2.2
    linarith [Real.log_natCast_nonneg (activePart (Real.log n-L) n).minFac]⟩
  have he := (coefficient_two_outer_prime_prefix hp).symm.trans (coefficient_two_outer_inner h)
  have he' : (Real.log n/L)*primePrefixResponse L n =
      (Real.log n/L)*max 0 (L-Real.log (outerPart (Real.log n-L) n)) := by linarith
  have hnon : 0 ≤ (Real.log n/L)*max 0 (L-Real.log (outerPart (Real.log n-L) n)) := by
    positivity [Real.log_natCast_nonneg n]
  unfold primePrefixFloorCost innerFloorCost
  rw [he']
  by_cases hc : 0 ≤ Real.cos (y*Real.log n)
  · rw [max_eq_left hc,max_eq_left (mul_nonneg hnon hc)]
  · rw [max_eq_right (le_of_not_ge hc),
      max_eq_right (mul_nonpos_of_nonneg_of_nonpos hnon (le_of_not_ge hc)),mul_zero]

/-- The concrete three-quarter charge saving feeds the COMBINED whole
floor, with the original phase and all older reflected savings retained. -/
theorem combinedFloorCost_le_quarter {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : TwoOuterInner L n)
    (hgap : 4*max 0 (L-Real.log (outerPart (Real.log n-L) n)) ≤
      Real.log n/n.primeFactors.card) :
    combinedFloorCost L y n ≤ (1/4 : ℝ)*ZetaRieszSignedSperner.lowerCost L y n := by
  have hp : TwoOuterPrimePrefix L n := ⟨h.1,h.2.1,h.2.2.1,by
    have := h.2.2.2
    linarith [Real.log_natCast_nonneg (activePart (Real.log n-L) n).minFac]⟩
  apply (combinedFloorCost_le_new L y n).trans
  unfold floorCost
  split_ifs
  · exact mul_nonneg (by norm_num) (ZetaRieszSignedSperner.costs_nonneg hL y n).1
  · rw [primePrefixFloorCost_eq_inner hL y h]
    exact innerFloorCost_le_quarter hL y h hgap

/-- A whole-core floor which keeps the NEW prefix cancellation and the
OLDER reflected signed estimates simultaneously. The minimum is taken on
the same observation, so no favorable term is counted twice. -/
theorem core_floor_combined {u : ℝ} (hu : 1/2 ≤ u) (y : ℝ) (N K : ℕ)
    (hN : 2 ≤ N) (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ n ∈ (coreBand u N K).filter Squarefree, max (fullTranslatedAtom u y N n).re 0)-
      (∑ n ∈ (coreBand u N K).filter Squarefree,
        weight (intermediatePrimes u N) N n*combinedFloorCost
          (SquarefreeVaughanLogSource.length u N) y n) ≤ (coreResponse u y N K).re := by
  rw [core_eq_fullTranslated,Complex.re_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hc := (Finset.mem_filter.mp hn).1
  have hs := (Finset.mem_filter.mp hn).2
  have hnew : max (fullTranslatedAtom u y N n).re 0-
      weight (intermediatePrimes u N) N n*floorCost
        (SquarefreeVaughanLogSource.length u N) y n ≤ (fullTranslatedAtom u y N n).re := by
    unfold floorCost
    split_ifs with hz hi
    · rw [fullTranslatedAtom_eq_zero_of_either hc y hz]
      norm_num
    · rw [fullTranslatedAtom_eq_original hc hs y]
      exact (prime_prefix_floor_exact (intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N y hi).le
    · rw [fullTranslatedAtom_eq_original hc hs y]
      exact (ZetaRieszSignedSperner.residual_atom_retained_bounds (intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length_pos u N) y N n).1
  unfold combinedFloorCost
  split_ifs with hcount
  · have hupper : Real.log n ≤ (203/100 : ℝ)*N := (Finset.mem_filter.mp hc).2.2
    have hcut : 2*Real.log n ≤ 3*SquarefreeVaughanLogSource.length u N := by
      nlinarith [show (0 : ℝ) ≤ N by positivity]
    have hold := (ZetaRieszReflectedPrimeBounds.residual_retained_bounds
      (intermediatePrimes u N) (SquarefreeVaughanLogSource.length_pos u N) y N
      hcount hcut (core_cutoff_quarter hu hN hc)).1
    rw [← fullTranslatedAtom_eq_original hc hs y] at hold
    by_cases hh : floorCost (SquarefreeVaughanLogSource.length u N) y n ≤
        ZetaRieszReflectedPrimeBounds.floorCost (SquarefreeVaughanLogSource.length u N) y n
    · rw [min_eq_left hh]
      exact hnew
    · rw [min_eq_right (le_of_not_ge hh)]
      exact hold
  · exact hnew

/-- The independent signed lower estimate applies to the ENTIRE physical
core. Exact pair cancellation is performed before the remaining charges
are summed; all favorable observations survive. Its total cost remains open. -/
theorem core_floor (u y : ℝ) (N K : ℕ) :
    (∑ n ∈ (coreBand u N K).filter Squarefree, max (fullTranslatedAtom u y N n).re 0)-
      (∑ n ∈ (coreBand u N K).filter Squarefree,
        weight (intermediatePrimes u N) N n*floorCost
          (SquarefreeVaughanLogSource.length u N) y n) ≤ (coreResponse u y N K).re := by
  rw [core_eq_fullTranslated,Complex.re_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hc := (Finset.mem_filter.mp hn).1
  have hs := (Finset.mem_filter.mp hn).2
  unfold floorCost
  split_ifs with hz hi
  · rw [fullTranslatedAtom_eq_zero_of_either hc y hz]
    norm_num
  · rw [fullTranslatedAtom_eq_original hc hs y]
    exact (prime_prefix_floor_exact (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N y hi).le
  · rw [fullTranslatedAtom_eq_original hc hs y]
    exact (ZetaRieszSignedSperner.residual_atom_retained_bounds (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length_pos u N) y N n).1

/-- The improved independent signed estimate is attached to the actual
endgame carrier. The sole boundary cost is the previously proved geometric
error; the remaining signed charge has NOT been bounded by 79/1000. -/
theorem joined_floor {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N K : ℕ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    u^(N+1)*((∑ n ∈ (coreBand u N K).filter Squarefree,
        max (fullTranslatedAtom u y N n).re 0)-
      (∑ n ∈ (coreBand u N K).filter Squarefree,
        weight (intermediatePrimes u N) N n*floorCost
          (SquarefreeVaughanLogSource.length u N) y n))-
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  have hf := mul_le_mul_of_nonneg_left (core_floor u y N K) (pow_nonneg hu (N+1))
  have hb := joined_fullTranslated_bound hu hU N K y hL
  rw [← core_eq_fullTranslated] at hb
  have he := (Complex.abs_re_le_norm
    ((u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N K-
      coreResponse u y N K))).trans hb
  have hlo := (abs_le.mp he).1
  rw [mul_sub,Complex.sub_re] at hlo
  have hc : ((u : ℂ)^(N+1)*coreResponse u y N K).re =
      u^(N+1)*(coreResponse u y N K).re := by
    rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  rw [hc] at hlo
  linarith

/-- The endgame floor uses every old reflected bound AND the new exact
prime-prefix cancellation. All favorable observations and masks are literal.
Bounding this displayed signed budget cofinally is still required. -/
theorem joined_floor_combined {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N K : ℕ)
    (hN : 2 ≤ N) (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    u^(N+1)*((∑ n ∈ (coreBand u N K).filter Squarefree,
        max (fullTranslatedAtom u y N n).re 0)-
      (∑ n ∈ (coreBand u N K).filter Squarefree,
        weight (intermediatePrimes u N) N n*combinedFloorCost
          (SquarefreeVaughanLogSource.length u N) y n))-
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  have hu0 : 0 ≤ u := by linarith
  have hf := mul_le_mul_of_nonneg_left (core_floor_combined hu y N K hN hL)
    (pow_nonneg hu0 (N+1))
  have hb := joined_fullTranslated_bound hu0 hU N K y hL
  rw [← core_eq_fullTranslated] at hb
  have he := (Complex.abs_re_le_norm
    ((u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N K-
      coreResponse u y N K))).trans hb
  have hlo := (abs_le.mp he).1
  rw [mul_sub,Complex.sub_re] at hlo
  have hc : ((u : ℂ)^(N+1)*coreResponse u y N K).re =
      u^(N+1)*(coreResponse u y N K).re := by
    rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  rw [hc] at hlo
  linarith

end
end RiemannGaussian.ZetaRieszSaturatedCoreFloor
