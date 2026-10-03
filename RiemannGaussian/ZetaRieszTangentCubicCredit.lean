/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointNullCredit

/-!
# A cubic null retaining the three-prime population

The cubic divisor moment is not zero on count three. Keep its exact complex
total, and take the perpendicular real direction instead of discarding the
three-prime labels. This gives one further exact whole-population null.
All cutoff groups and sign crossings remain in the original cost. The
native numerical size of the resulting credit is not estimated here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszTangentCubicCredit
open ZetaRieszCutoffPeriodFloor ZetaRieszCofactorPhaseEnergy
open ZetaRieszComplexProjection ZetaRieszSignedNullGain
open ZetaRieszJointNullCredit ZetaRieszQuantitativeNullStep
open ZetaRieszJointAllocation ZetaRieszJointPrimeEnergy
open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszParityPacket

private theorem correlation_profile (X : ℕ) (S : Finset ℕ)
    (w f : ℕ → ℝ) (hf : f (X+1)=0) :
    (∑ k ∈ Finset.Icc 1 X,correlation S w k*(f k-f (k+1)))=
      ∑ n ∈ S,w n*(∑ d ∈ Finset.Icc 1 X,
        f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
  symm
  simp_rw [ZetaRieszSignedCutoffEnergy.abel_profile X f _ hf,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [correlation,sharp,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- A direction perpendicular to the EXACT complex profile moment.
It is defined at zero moment too; no nonzero-channel premise is assumed. -/
def tangentIncrement (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  let M := complexPrefix X S W f
  ((M.im*correlation S (fun n => (W n).re) k-
    M.re*correlation S (fun n => (W n).im) k)/‖M‖)*(f k-f (k+1))

/-- Whole complex-moment orthogonality makes this an exact finite null.
Neither an adverse subset nor an early cutoff is claimed to have zero sum. -/
theorem sum_tangentIncrement_zero (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (hf : f (X+1)=0) :
    (∑ k ∈ Finset.Icc 1 X,tangentIncrement X S W f k)=0 := by
  have hr := correlation_profile X S (fun n => (W n).re) f hf
  have hi := correlation_profile X S (fun n => (W n).im) f hf
  have hmr : (complexPrefix X S W f).re=
      ∑ n ∈ S,(W n).re*(∑ d ∈ Finset.Icc 1 X,
        f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
    simp only [complexPrefix,Complex.re_sum,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hmi : (complexPrefix X S W f).im=
      ∑ n ∈ S,(W n).im*(∑ d ∈ Finset.Icc 1 X,
        f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
    simp only [complexPrefix,Complex.im_sum,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
  simp only [tangentIncrement,div_mul_eq_mul_div,← Finset.sum_div,
    sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [hr,hi,← hmr,← hmi]
  simp only [mul_comm (complexPrefix X S W f).im,
    sub_self,zero_div]

/-- The exact complex defect of an arbitrary whole-profile direction.
The cubic defect is not silently replaced by zero at count three. -/
theorem sum_profile_direction (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (hf : f (X+1)=0) (a b : ℝ) :
    (∑ k ∈ Finset.Icc 1 X,
      (a*correlation S (fun n => (W n).re) k-
        b*correlation S (fun n => (W n).im) k)*(f k-f (k+1)))=
      a*(complexPrefix X S W f).re-b*(complexPrefix X S W f).im := by
  simp only [sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [correlation_profile X S (fun n => (W n).re) f hf,
    correlation_profile X S (fun n => (W n).im) f hf]
  simp only [complexPrefix,Complex.re_sum,Complex.im_sum,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_add]

/-- At the first integer cutoff EVERY label has the same divisor prefix.
Its contribution cannot be dropped when the cubic coefficient is changed. -/
theorem unit_cutoff_direction (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (a b : ℝ) :
    (a*correlation S (fun n => (W n).re) 1-
      b*correlation S (fun n => (W n).im) 1)*(f 1-f 2)=
      (a*(∑ n ∈ S,W n).re-b*(∑ n ∈ S,W n).im)*(f 1-f 2) := by
  simp [correlation,sharp,Complex.re_sum,Complex.im_sum]

/-- Two noncollinear complex moments leave no nonzero real direction
perpendicular to both. This is a two-channel obstruction, not a claim
that the native moments are noncollinear or that joint directions fail. -/
theorem coefficients_zero_of_two_moment_constraints (M Q : ℂ) {a b : ℝ}
    (hM : a*M.re-b*M.im=0) (hQ : a*Q.re-b*Q.im=0)
    (hdet : M.re*Q.im-M.im*Q.re ≠ 0) : a=0 ∧ b=0 := by
  have ha : a*(M.re*Q.im-M.im*Q.re)=0 := by
    linear_combination Q.im*hM-M.im*hQ
  have hb : b*(M.re*Q.im-M.im*Q.re)=0 := by
    linear_combination Q.re*hM-M.re*hQ
  exact ⟨(mul_eq_zero.mp ha).resolve_right hdet,(mul_eq_zero.mp hb).resolve_right hdet⟩

/-- An exact whole null AND zero first-cutoff response cannot both be
free when the two actual profile moments are noncollinear. Early debits
must then be paid or cancelled by OTHER joined directions. -/
theorem no_free_unit_cutoff_direction (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (hf : f (X+1)=0) {a b : ℝ}
    (hsum : (∑ k ∈ Finset.Icc 1 X,
      (a*correlation S (fun n => (W n).re) k-
        b*correlation S (fun n => (W n).im) k)*(f k-f (k+1)))=0)
    (hfirst : (a*correlation S (fun n => (W n).re) 1-
      b*correlation S (fun n => (W n).im) 1)*(f 1-f 2)=0)
    (hdelta : f 1-f 2 ≠ 0)
    (hdet : (complexPrefix X S W f).re*(∑ n ∈ S,W n).im-
      (complexPrefix X S W f).im*(∑ n ∈ S,W n).re ≠ 0) : a=0 ∧ b=0 := by
  rw [sum_profile_direction X S W f hf a b] at hsum
  rw [unit_cutoff_direction S W f a b] at hfirst
  exact coefficients_zero_of_two_moment_constraints _ _ hsum
    ((mul_eq_zero.mp hfirst).resolve_right hdelta) hdet

/-- At a zero profile moment this particular direction is zero; this
does not assert that other available profile directions are zero. -/
theorem tangentIncrement_of_moment_zero (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (h : complexPrefix X S W f=0) (k : ℕ) :
    tangentIncrement X S W f k=0 := by
  simp [tangentIncrement,h]

/-- The cubic moment with the full literal weight and all counts. -/
def cubicMoment (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) : ℂ :=
  complexPrefix X S W (ZetaRieszSignedNullGain.cubicProfile X N)

/-- The nonzero three-prime defect has an exact product-log coefficient;
it must not be treated as the count-four cubic null. -/
theorem thirdMoment_three_primes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hqr : q ≠ r) (hs : Squarefree (q*r)) (hpd : ¬p ∣ q*r) :
    ZetaRieszCubicPrimeEnergy.thirdMoment (p*(q*r))=
      -6*log p*log q*log r := by
  have hc : (q*r).primeFactors.card=2 := by
    rw [Nat.primeFactors_mul hq.ne_zero hr.ne_zero,hq.primeFactors,hr.primeFactors]
    simp [hqr]
  have h1 : q*r ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬(q*r).Prime := by intro h; simp [h.primeFactors] at hc
  rw [ZetaRieszCubicPrimeEnergy.thirdMoment_prime_mul hp hpd hs h1 hnp,
    ZetaRieszQuadraticPrimeEnergy.secondMoment_two_primes hq hr hqr]
  ring

/-- Count-three labels retain their genuine cubic divisor response. -/
theorem cubic_pairing_eq_third {n X : ℕ} (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (hX : n ≤ X) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 X,ZetaRieszSignedNullGain.cubicProfile X N d*
      (if d ∣ n then (μ d : ℝ) else 0))=
        ZetaRieszCubicPrimeEnergy.thirdMoment n/(N+1 : ℝ)^2 := by
  have h1 : n ≠ 1 := by intro h; simp [h] at hc
  have hp : ¬n.Prime := by intro h; simp [h.primeFactors] at hc
  simp only [ZetaRieszSignedNullGain.cubicProfile,div_mul_eq_mul_div,← Finset.sum_div]
  rw [ZetaRieszCenteredPrimeEnergy.prefix_eq_divisors (Nat.pos_of_ne_zero hs.ne_zero) hX,
    ZetaRieszCenteredPrimeEnergy.divisor_centering hs hp h1 hX]
  rfl

/-- All higher counts vanish arithmetically. The remaining complex moment
is EXACTLY the count-three moment, with the original allocation and phase. -/
theorem cubicMoment_eq_three (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (hs : ∀ n ∈ S,Squarefree n) (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card)
    (hX : ∀ n ∈ S,n ≤ X) :
    cubicMoment X N S W=
      ∑ n ∈ S.filter (fun n => n.primeFactors.card=3),
        W n*(ZetaRieszCubicPrimeEnergy.thirdMoment n/(N+1 : ℝ)^2 : ℝ) := by
  unfold cubicMoment complexPrefix
  calc
    _ = ∑ n ∈ S,W n*(ZetaRieszCubicPrimeEnergy.thirdMoment n/(N+1 : ℝ)^2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [cubic_pairing_eq_third (hs n hn) (hc n hn) (hX n hn)]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hout
      have hn3 : n.primeFactors.card ≠ 3 := by
        intro he
        exact hout (Finset.mem_filter.mpr ⟨hn,he⟩)
      rw [ZetaRieszCubicPrimeEnergy.thirdMoment_eq_zero_of_count (hs n hn)
        (by have := hc n hn; omega),zero_div,Complex.ofReal_zero,mul_zero]

/-- No count restriction is imposed on this correction. Count three is
retained and cancelled only in its WHOLE complex moment, not atomwise. -/
def cubicTangent (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) : ℕ → ℝ :=
  tangentIncrement X S W (ZetaRieszSignedNullGain.cubicProfile X N)

theorem sum_cubicTangent_zero (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 X,cubicTangent X N S W k)=0 := by
  apply sum_tangentIncrement_zero
  simp [ZetaRieszSignedNullGain.cubicProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile]

/-- One whole correction, including the former six directions. -/
def extendedIncrement (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (q : Fin 6 → ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  jointIncrement X N S W L q k+a*cubicTangent X N S W k

theorem sum_extendedIncrement_zero (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (q : Fin 6 → ℝ) (a : ℝ) (hs : ∀ n ∈ S,Squarefree n)
    (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card) (hX : ∀ n ∈ S,n ≤ X) :
    (∑ k ∈ Finset.Icc 1 X,extendedIncrement X N S W L q a k)=0 := by
  simp only [extendedIncrement,Finset.sum_add_distrib,← Finset.mul_sum,
    sum_jointIncrement_zero X N S W L q hs hc hX,sum_cubicTangent_zero,mul_zero,add_zero]

/-- Every early, late, zero and crossed cutoff group stays in the price. -/
def tangentCost (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) (a : ℝ) : ℝ :=
  blockCost (Finset.Icc 1 X) g (fun k =>
    ZetaRieszComplexNullFloor.increment X N S W L
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B) k+
        extendedIncrement X N S W L q a k)

/-- Alternative credits against ONE original price, never an unfunded
sum of the previous credit and a separately computed new credit. -/
def tangentCredit (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) (a : ℝ) : ℝ :=
  max (jointCredit X N S W L g B q)
    (max (ZetaRieszComplexNullFloor.bestCost X N S W L g B-
      tangentCost X N S W L g B q a) 0)

theorem tangentCredit_le_cost (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) (a : ℝ) :
    tangentCredit X N S W L g B q a ≤
      ZetaRieszComplexNullFloor.bestCost X N S W L g B := by
  have htc : 0 ≤ tangentCost X N S W L g B q a := by
    unfold tangentCost blockCost
    exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  exact max_le (jointCredit_le_cost _ _ _ _ _ _ _ _)
    (max_le (by linarith only [htc])
      (ZetaRieszComplexNullFloor.bestCost_nonneg _ _ _ _ _ _ _))

theorem jointCredit_le_tangentCredit (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) (a : ℝ) :
    jointCredit X N S W L g B q ≤ tangentCredit X N S W L g B q a :=
  le_max_left _ _

/-- The previous six-direction price is recovered EXACTLY at zero
new coefficient. There is no change of population, tilt or error. -/
theorem tangentCredit_zero (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) :
    tangentCredit X N S W L g B q 0=jointCredit X N S W L g B q := by
  simp only [tangentCredit,tangentCost,extendedIncrement,zero_mul,add_zero,
    jointCredit,ZetaRieszJointNullCredit.jointCost,max_self]

/-- A signed inequality for the ORIGINAL prefix, with its original
imaginary correction. Count-three cubic atoms are included, not paid by
a positive majorant. This theorem does not estimate the native credit. -/
theorem prefix_floor_with_tangent_credit (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (L : ℝ) (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) (a : ℝ)
    (hs : ∀ n ∈ S,Squarefree n) (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card)
    (hX : ∀ n ∈ S,n ≤ X) :
    -ZetaRieszComplexNullFloor.bestCost X N S W L g B+
      tangentCredit X N S W L g B q a-
        |B| * |(complexPrefix X S W (correctedProfile X L 1 0)).im| ≤
          (complexPrefix X S W (correctedProfile X L 1 0)).re := by
  let p := ZetaRieszComplexNullFloor.bestParameters X N S W L g B
  let M := complexPrefix X S W (correctedProfile X L 1 0)
  have hf := block_floor (Finset.Icc 1 X) g (fun k =>
    ZetaRieszComplexNullFloor.increment X N S W L p k+extendedIncrement X N S W L q a k)
  rw [Finset.sum_add_distrib,sum_extendedIncrement_zero X N S W L q a hs hc hX,add_zero,
    ZetaRieszComplexNullFloor.sum_increment_eq X N S W L hs hc hX] at hf
  have hm := mul_le_mul_of_nonneg_right
    (ZetaRieszComplexNullFloor.bestParameters_bound X N S W L g B 0) (abs_nonneg M.im)
  rw [← abs_mul] at hm
  have hl := neg_abs_le (p 0*M.im)
  change -tangentCost X N S W L g B q a ≤ M.re-p 0*M.im at hf
  change |p 0*M.im| ≤ |B| * |M.im| at hm
  have hold := prefix_floor_with_joint_credit X N S W L g B q hs hc hX
  have hbase := ZetaRieszComplexNullFloor.best_floor X N S W L g B hs hc hX
  unfold tangentCredit
  by_cases hx : jointCredit X N S W L g B q ≤
      max (ZetaRieszComplexNullFloor.bestCost X N S W L g B-
        tangentCost X N S W L g B q a) 0
  · rw [max_eq_right hx]
    by_cases hy : ZetaRieszComplexNullFloor.bestCost X N S W L g B-
        tangentCost X N S W L g B q a ≤ 0
    · rw [max_eq_right hy,add_zero]
      linarith only [hbase]
    · rw [max_eq_left (le_of_lt (lt_of_not_ge hy))]
      change -ZetaRieszComplexNullFloor.bestCost X N S W L g B+
        (ZetaRieszComplexNullFloor.bestCost X N S W L g B-
          tangentCost X N S W L g B q a)-|B| * |M.im| ≤ M.re
      linarith only [hf,hm,hl]
  · rw [max_eq_left (le_of_not_ge hx)]
    exact hold

/-- The exact alternative credit on the CURRENT count-cropped native
core. The cubic moment contains the original source-normalized weight. -/
def nativeTangentCredit (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) (a : ℝ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  tangentCredit X N (S.filter Squarefree) (sourceWeight A L u y N) L (cutoffPeriod y) 4 q a

theorem nativeJointCredit_le_tangentCredit (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) (a : ℝ) :
    nativeJointCredit u y j q ≤ nativeTangentCredit u y j q a :=
  jointCredit_le_tangentCredit _ _ _ _ _ _ _ _ _

theorem nativeTangentCredit_zero (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) :
    nativeTangentCredit u y j q 0=nativeJointCredit u y j q :=
  tangentCredit_zero _ _ _ _ _ _ _ _

theorem nativeTangentCredit_le_cost (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) (a : ℝ) :
    nativeTangentCredit u y j q a ≤ ZetaRieszComplexNullFloor.nativeCost u y j :=
  tangentCredit_le_cost _ _ _ _ _ _ _ _ _

/-- A stronger floor for the SAME whole carrier, retaining every count,
mask, allocation and phase. The imaginary/mask-transfer error is unchanged.
Its independent numerical cost bound remains open. -/
theorem native_floor_with_tangent_credit (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) (a : ℝ) :
    -ZetaRieszComplexNullFloor.nativeCost u y j+nativeTangentCredit u y j q a-
      ZetaRieszComplexProjection.nativeError u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let P := (u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)
  let Q := (u : ℂ)^(N+1)*coreResponse u y N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hs : ∀ n ∈ S.filter Squarefree,Squarefree n := fun _ hn => (Finset.mem_filter.mp hn).2
  have hc : ∀ n ∈ S.filter Squarefree,3 ≤ n.primeFactors.card :=
    fun _ hn => core_count (Finset.mem_filter.mp hn).1
  have hX : ∀ n ∈ S.filter Squarefree,n ≤ X :=
    fun _ hn => (Finset.le_sup (f := id) (Finset.mem_filter.mp hn).1).trans (le_max_right _ _)
  have hf := prefix_floor_with_tangent_credit X N (S.filter Squarefree) (sourceWeight A L u y N)
    L (cutoffPeriod y) 4 q a hs hc hX
  have he := native_prefix_eq A S L u y N (fun _ hn => core_count hn)
  dsimp only at he hf
  change complexPrefix X (S.filter Squarefree) (sourceWeight A L u y N)
    (correctedProfile X L 1 0)=Q at he
  rw [he] at hf
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hf
  have hr : Q.re-P.re ≤ ‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have hi : |Q.im| ≤ |P.im|+‖Q-P‖ := by
    have hh := abs_sub_le Q.im P.im 0
    simp only [sub_zero] at hh
    have hd : |Q.im-P.im| ≤ ‖Q-P‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (Q-P)
    linarith only [hh,hd]
  change -ZetaRieszComplexNullFloor.nativeCost u y j+nativeTangentCredit u y j q a-
    4*|Q.im| ≤ Q.re at hf
  change -ZetaRieszComplexNullFloor.nativeCost u y j+nativeTangentCredit u y j q a-
    (4*|P.im|+5*‖Q-P‖) ≤ P.re
  linarith only [hf,hr,hi]

/-- Explicit conditional endpoint. The cofinal numerical premise is NOT
proved by constructing the new exact null or by the finite probes. -/
theorem false_of_cofinal_tangent_credit (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho=1)
    (q : ℕ → Fin 6 → ℝ) (a : ℕ → ℝ)
    (hcost : ∃ᶠ j in atTop,
      ZetaRieszComplexNullFloor.nativeCost (3/2-rho.1.re) rho.1.im j-
        nativeTangentCredit (3/2-rho.1.re) rho.1.im j (q j) (a j) ≤ 399/5000) : False := by
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
    (tendsto_nativeError rho hrho hexposed hU)
  exact hcost.mono fun j hj => by
    have hf := native_floor_with_tangent_credit (3/2-rho.1.re) rho.1.im j (q j) (a j)
    linarith only [hj,hf]

end RiemannGaussian.ZetaRieszTangentCubicCredit
