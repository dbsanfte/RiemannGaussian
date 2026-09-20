/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAllocationWeights

/-!
# A phase-preserving bounded fraction of each original atom

The complete companion equals a genuinely convergent sum over integer labels. Each assigned atom is a fraction between zero and one of the original signed atom. This is an exact arithmetic identity and pointwise bound, not a floor for their oscillatory sum.
-/

namespace RiemannGaussian.ZetaRieszJointAllocation
noncomputable section
open scoped BigOperators Classical

open ZetaRieszJointCofactor

/-- The exact squarefree composite and coprimality restrictions of the complete companion. -/
def eligibleCofactor (p a : ℕ) : Prop :=
  Squarefree a ∧ a ≠ 1 ∧ ¬a.Prime ∧ ¬p ∣ a

/-- The companion amplitude at one integer, retaining every selected prime and cofactor condition. -/
def assignedAmplitude (A : Finset ℕ) (N n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
    if p ∈ A ∧ eligibleCofactor p (n / p) then
      Real.log (n / p : ℕ) ^ k / (k.factorial : ℝ) *
        (Real.log p ^ (N + 1 - k) / ((N + 1 - k).factorial : ℝ)) else 0

/-- The assigned real amplitude is nonnegative before applying the signed coefficient and phase. -/
theorem assignedAmplitude_nonneg (A : Finset ℕ) (N n : ℕ) : 0 ≤ assignedAmplitude A N n := by
  unfold assignedAmplitude
  exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun k _ => by split_ifs <;> positivity))

/-- Every finite prime selection inherits the complete allocation bound without counting a label twice. -/
theorem assignedAmplitude_le (A : Finset ℕ) (N : ℕ) {n : ℕ} (hn : Squarefree n) :
    assignedAmplitude A N n ≤ Real.log n ^ (N + 1) / ((N + 1).factorial : ℝ) := by
  apply le_trans _ (primeAllocation_le hn N)
  unfold assignedAmplitude primeAllocation
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro k hk
  split_ifs
  · rfl
  · positivity

/-- The companion contribution at one integer, with every distinguished prime incidence retained. -/
def assignedAtom (A : Finset ℕ) (L y : ℝ) (N n : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) / (L : ℂ) * ∑ p ∈ n.primeFactors,
    ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      if p ∈ A then compositeAtom L y k (N + 1 - k) p (n / p) else 0

/-- Complementary kernels retain exactly the product integer phase. -/
theorem kernel_split_phase {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hd : p ∣ n)
    (s : ℂ) (k l : ℕ) :
    zetaPrimeLogKernel k s (n / p) * zetaPrimeLogKernel l s p =
      ((Real.log (n / p : ℕ) ^ k / (k.factorial : ℝ) *
        (Real.log p ^ l / (l.factorial : ℝ)) : ℝ) : ℂ) * zetaPrimeFeature s n := by
  have hnp : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hp.pos
  have he := CoprimeEulerPhase.feature_mul s hnp hp.pos
  rw [Nat.div_mul_cancel hd] at he
  simp only [zetaPrimeLogKernel, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [he]
  ring

/-- All incidences at an integer share its original signed Riesz coefficient and complex phase. -/
theorem assignedAtom_eq_phase (A : Finset ℕ) (L y : ℝ) (N : ℕ) {n : ℕ}
    (hn : 0 < n) :
    assignedAtom A L y N n =
      -((N + 1 : ℕ) : ℂ) / (L : ℂ) * (VaughanLogAverage.riesz L n : ℂ) *
        (assignedAmplitude A N n : ℂ) * zetaPrimeFeature (3 / 2 + Complex.I * y) n := by
  unfold assignedAtom assignedAmplitude
  simp only [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k hk
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hpn : p * (n / p) = n := Nat.mul_div_cancel' hpd
  by_cases hpa : p ∈ A
  · rw [if_pos hpa]
    by_cases hg : eligibleCofactor p (n / p)
    · have ht : p ∈ A ∧ eligibleCofactor p (n / p) := ⟨hpa, hg⟩
      rw [if_pos ht, compositeAtom]
      dsimp only [eligibleCofactor] at hg
      rw [if_pos hg, hpn]
      rw [mul_assoc (-(VaughanLogAverage.riesz L n : ℂ)), kernel_split_phase hpp hn hpd]
      push_cast
      ring
    · have ht : ¬(p ∈ A ∧ eligibleCofactor p (n / p)) := fun h => hg h.2
      rw [if_neg ht, compositeAtom]
      dsimp only [eligibleCofactor] at hg
      rw [if_neg hg]
      simp
  · have ht : ¬(p ∈ A ∧ eligibleCofactor p (n / p)) := fun h => hpa h.1
    rw [if_neg hpa, if_neg ht]
    simp


/-- The exact fraction of the full factorial amplitude assigned to the companion. -/
def allocationShare (A : Finset ℕ) (N n : ℕ) : ℝ :=
  assignedAmplitude A N n / (Real.log n ^ (N + 1) / ((N + 1).factorial : ℝ))

/-- For an actual nonunit squarefree integer, the assigned fraction lies between zero and one. -/
theorem allocationShare_bounds (A : Finset ℕ) (N : ℕ) {n : ℕ} (hn : Squarefree n)
    (hn1 : 1 < n) : 0 ≤ allocationShare A N n ∧ allocationShare A N n ≤ 1 := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hb : 0 < Real.log n ^ (N + 1) / ((N + 1).factorial : ℝ) := by positivity
  exact ⟨div_nonneg (assignedAmplitude_nonneg A N n) hb.le,
    (div_le_one hb).mpr (assignedAmplitude_le A N hn)⟩

/-- The original coefficient and kernel retain their full product phase after the factorial shift. -/
theorem originalAtom_eq_phase {L : ℝ} (hL : 0 < L) (y : ℝ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hnp : ¬ n.Prime) :
    SquarefreeVaughanLogSource.coefficient L n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n =
      -((N + 1 : ℕ) : ℂ) / (L : ℂ) * (VaughanLogAverage.riesz L n : ℂ) *
        ((Real.log n ^ (N + 1) / ((N + 1).factorial : ℝ) : ℝ) : ℂ) *
          zetaPrimeFeature (3 / 2 + Complex.I * y) n := by
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  rw [SquarefreeVaughanLogSource.coefficient, if_pos (show Squarefree n ∧ ¬ n.Prime from ⟨hn, hnp⟩)]
  simp only [zetaPrimeLogKernel,
    Nat.factorial_succ, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_natCast, Nat.cast_mul, pow_succ]
  field_simp

/-- The actual companion atom is a nonnegative fraction of the original signed atom. -/
theorem assignedAtom_eq_share (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (N : ℕ) {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬ n.Prime) :
    assignedAtom A L y N n = (allocationShare A N n : ℂ) *
      (SquarefreeVaughanLogSource.coefficient L n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) := by
  rw [assignedAtom_eq_phase A L y N (by omega), originalAtom_eq_phase hL y N hn hnp]
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hb : Real.log n ^ (N + 1) / ((N + 1).factorial : ℝ) ≠ 0 := by positivity
  have he : assignedAmplitude A N n = allocationShare A N n *
      (Real.log n ^ (N + 1) / ((N + 1).factorial : ℝ)) := by
    exact (div_mul_cancel₀ _ hb).symm
  have hec := congrArg (fun x : ℝ => (x : ℂ)) he
  rw [Complex.ofReal_mul] at hec
  rw [hec]
  ring

/-- Subtracting the assigned atom preserves the original phase and signed coefficient. -/
theorem original_sub_assigned (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (N : ℕ) {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬ n.Prime) :
    SquarefreeVaughanLogSource.coefficient L n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n -
        assignedAtom A L y N n =
      ((1 - allocationShare A N n : ℝ) : ℂ) *
        (SquarefreeVaughanLogSource.coefficient L n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) := by
  rw [assignedAtom_eq_share A hL y N hn hn1 hnp]
  push_cast
  ring

/-- The pointwise signed subtraction has no larger norm than the original atom. -/
theorem norm_original_sub_assigned_le (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (N : ℕ) {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬ n.Prime) :
    ‖SquarefreeVaughanLogSource.coefficient L n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n -
      assignedAtom A L y N n‖ ≤
    ‖SquarefreeVaughanLogSource.coefficient L n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ := by
  rw [original_sub_assigned A hL y N hn hn1 hnp, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith [(allocationShare_bounds A N hn hn1).2])]
  have h := (allocationShare_bounds A N hn hn1).1
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)


-- The prime/cofactor incidence sum is complete, not a formal divergent rearrangement.
/-- A convergent cofactor series can be lifted to its exact multiple labels. -/
theorem hasSum_mul_lift {p : ℕ} (hp : 0 < p) (f : ℕ → ℂ) {v : ℂ} (h : HasSum f v) :
    HasSum (fun n => if p ∣ n then f (n / p) else 0) v := by
  have hi : Function.Injective (fun a : ℕ => p * a) := fun a b h => Nat.eq_of_mul_eq_mul_left hp h
  have hz : ∀ n ∉ Set.range (fun a : ℕ => p * a), (if p ∣ n then f (n / p) else 0) = 0 := by
    intro n hn
    have hd : ¬p ∣ n := by
      intro hd
      obtain ⟨a, ha⟩ := hd
      exact hn ⟨a, ha.symm⟩
    exact if_neg hd
  apply (hi.hasSum_iff hz).mp
  simpa only [Function.comp_def, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hp] using h

/-- The complete cofactor atom lifted to its integer product label. -/
def liftedAtom (L y : ℝ) (k l p n : ℕ) : ℂ :=
  if p ∣ n then compositeAtom L y k l p (n / p) else 0

/-- The lifted prime atom is supported exactly on prime-divisor incidences, including the zero case. -/
theorem liftedAtom_eq_primeFactors {p : ℕ} (hp : p.Prime) (L y : ℝ) (k l n : ℕ) :
    liftedAtom L y k l p n =
      if p ∈ n.primeFactors then compositeAtom L y k l p (n / p) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [liftedAtom, compositeAtom]
  · unfold liftedAtom
    have he : p ∣ n ↔ p ∈ n.primeFactors :=
      ⟨fun hd => Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩, Nat.dvd_of_mem_primeFactors⟩
    simp only [he]

/-- The finite prime and order sums equal the literal assigned integer atom. -/
theorem sum_lifted_eq_assigned (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (L y : ℝ) (N n : ℕ) :
    ((N + 1 : ℕ) : ℂ) / (L : ℂ) * ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      ∑ p ∈ A, liftedAtom L y k (N + 1 - k) p n = assignedAtom A L y N n := by
  unfold assignedAtom
  conv_rhs => rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑ p ∈ A, if p ∈ n.primeFactors then compositeAtom L y k (N + 1 - k) p (n / p) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact liftedAtom_eq_primeFactors (hA p hp) L y k (N + 1 - k) n
    _ = _ := by
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter, and_comm]

/-- The full original composite companion is the genuinely convergent sum of its assigned integer atoms. -/
theorem hasSum_assignedAtom (u y : ℝ) (N : ℕ) :
    HasSum (fun n => assignedAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) y N n) (compositeWing u y N) := by
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  have hp (p : ℕ) (hpA : p ∈ A) : p.Prime ∧ Real.log p ≤ L := by
    obtain ⟨hprime, _, hpx⟩ := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hpA
    exact ⟨hprime, (Real.log_lt_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpx)).le⟩
  have hsum := hasSum_sum (s := ZetaRieszWingHighOrders.unpaidOrders N) (fun k hk =>
    hasSum_sum (s := A) (fun p hpA =>
      hasSum_mul_lift (hp p hpA).1.pos (fun a => compositeAtom L y k (N + 1 - k) p a)
        (hasSum_compositeAtom (hp p hpA).1 (hp p hpA).2
          (by have := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.2; omega)
          (N + 1 - k) y).summable.hasSum))
  have h := hsum.mul_left (((N + 1 : ℕ) : ℂ) / (L : ℂ))
  change HasSum _ (compositeWing u y N) at h
  apply h.congr_fun
  intro n
  exact (sum_lifted_eq_assigned A (fun p hpA => (hp p hpA).1) L y N n).symm


/-- Every eligible prime/composite incidence produces a nonunit squarefree composite integer. -/
theorem eligible_product_good {p a : ℕ} (hp : p.Prime) (ha : eligibleCofactor p a) :
    Squarefree (p * a) ∧ 1 < p * a ∧ ¬(p * a).Prime := by
  obtain ⟨hsf, ha1, _, hpa⟩ := ha
  have ha2 : 2 ≤ a := by have := hsf.ne_zero; omega
  exact ⟨Nat.squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hpa, hp.squarefree, hsf⟩,
    by nlinarith [hp.two_le], Nat.not_prime_mul hp.ne_one ha1⟩

/-- The exact assigned fraction on its arithmetic support, zero elsewhere. -/
def boundedShare (A : Finset ℕ) (N n : ℕ) : ℝ :=
  if Squarefree n ∧ 1 < n ∧ ¬ n.Prime then allocationShare A N n else 0

/-- The full assigned-fraction function lies between zero and one at every integer. -/
theorem boundedShare_bounds (A : Finset ℕ) (N n : ℕ) :
    0 ≤ boundedShare A N n ∧ boundedShare A N n ≤ 1 := by
  unfold boundedShare
  split_ifs with hn
  · exact allocationShare_bounds A N hn.1 hn.2.1
  · norm_num

/-- No companion atom survives outside its actual squarefree composite support. -/
theorem assignedAtom_eq_zero (A : Finset ℕ) (L y : ℝ) (N n : ℕ)
    (hn : ¬(Squarefree n ∧ 1 < n ∧ ¬ n.Prime)) : assignedAtom A L y N n = 0 := by
  unfold assignedAtom
  suffices h : (∑ p ∈ n.primeFactors, ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      if p ∈ A then compositeAtom L y k (N + 1 - k) p (n / p) else 0) = 0 by rw [h, mul_zero]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro k hk
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hg : ¬eligibleCofactor p (n / p) := by
    intro ha
    have h := eligible_product_good hpp ha
    rw [Nat.mul_div_cancel' hpd] at h
    exact hn h
  dsimp only [eligibleCofactor] at hg
  simp [compositeAtom, hg]

/-- The companion has one exact bounded multiplier of each original signed atom, at every integer. -/
theorem assignedAtom_eq_boundedShare (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N n : ℕ) :
    assignedAtom A L y N n = (boundedShare A N n : ℂ) *
      (SquarefreeVaughanLogSource.coefficient L n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) := by
  by_cases hn : Squarefree n ∧ 1 < n ∧ ¬ n.Prime
  · rw [boundedShare, if_pos hn]
    exact assignedAtom_eq_share A hL y N hn.1 hn.2.1 hn.2.2
  · rw [boundedShare, if_neg hn, assignedAtom_eq_zero A L y N n hn]
    simp

/-- The original signed coefficient multiplied by its assigned companion fraction. -/
def assignedCoefficient (A : Finset ℕ) (L : ℝ) (N n : ℕ) : ℂ :=
  (boundedShare A N n : ℂ) * SquarefreeVaughanLogSource.coefficient L n

/-- The original signed coefficient multiplied by its unassigned fraction. -/
def residualCoefficient (A : Finset ℕ) (L : ℝ) (N n : ℕ) : ℂ :=
  ((1 - boundedShare A N n : ℝ) : ℂ) * SquarefreeVaughanLogSource.coefficient L n

/-- The assigned coefficient retains the original divisor majorant. -/
theorem norm_assignedCoefficient_le (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (N n : ℕ) :
    ‖assignedCoefficient A L N n‖ ≤ zetaMoebiusLogMajorant n := by
  rw [assignedCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (boundedShare_bounds A N n).1]
  exact (mul_le_of_le_one_left (norm_nonneg _) (boundedShare_bounds A N n).2).trans
    (SquarefreeVaughanLogSource.norm_coefficient_le hL n)

/-- The residual coefficient retains the original divisor majorant. -/
theorem norm_residualCoefficient_le (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (N n : ℕ) :
    ‖residualCoefficient A L N n‖ ≤ zetaMoebiusLogMajorant n := by
  rw [residualCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [(boundedShare_bounds A N n).2])]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [(boundedShare_bounds A N n).1])).trans
    (SquarefreeVaughanLogSource.norm_coefficient_le hL n)



end
end RiemannGaussian.ZetaRieszJointAllocation
