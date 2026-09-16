/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnedCells

/-!
# Complete prime intervals inside arithmetic divisor cells

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszPrimeIntervals
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTargetProfile ZetaArithmeticBandCorrelation ZetaRieszConditionedEnergy
open ZetaRieszPrimeEndpoint
open ZetaRieszPrimeCells
open ZetaRieszOwnedCells

/-- Active divisor sets decrease with the inserted prime logarithm. -/
theorem activeDivisors_antitone (L : ℝ) (n : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    activeDivisors L n y ⊆ activeDivisors L n x := by
  intro d hd
  obtain ⟨hd, hlog⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hd, by linarith⟩

/-- Every intermediate logarithm stays in the same literal divisor cell. -/
theorem activeDivisors_eq_between (L : ℝ) (n : ℕ) {x y z : ℝ}
    (hxy : x ≤ y) (hyz : y ≤ z)
    (hcell : activeDivisors L n z = activeDivisors L n x) :
    activeDivisors L n y = activeDivisors L n x := by
  apply Finset.Subset.antisymm (activeDivisors_antitone L n hxy)
  rw [← hcell]
  exact activeDivisors_antitone L n hyz

/-- Consecutive primes are not required: every intermediate positive
integer has the same cell whenever both endpoints do. -/
theorem prime_cell_between (L : ℝ) (n : ℕ) {p q r : ℕ}
    (hp : 0 < p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hcell : activeDivisors L n (Real.log r) = activeDivisors L n (Real.log p)) :
    activeDivisors L n (Real.log q) = activeDivisors L n (Real.log p) := by
  apply activeDivisors_eq_between L n
    (Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hpq))
    (Real.log_le_log (by exact_mod_cast hp.trans_le hpq) (by exact_mod_cast hqr)) hcell

/-- Membership of a positive integer product in the original band is
preserved between two endpoint products. -/
theorem product_band_between (N : ℕ) {n p q r : ℕ}
    (hpq : p ≤ q) (hqr : q ≤ r)
    (hp : p * n ∈ zetaPrimeLogBand N) (hr : r * n ∈ zetaPrimeLogBand N) :
    q * n ∈ zetaPrimeLogBand N := by
  obtain ⟨hpI, hpLog⟩ := Finset.mem_filter.mp hp
  obtain ⟨hrI, _⟩ := Finset.mem_filter.mp hr
  obtain ⟨hp1, _⟩ := Finset.mem_Icc.mp hpI
  obtain ⟨_, hrEnd⟩ := Finset.mem_Icc.mp hrI
  have hpqn : p * n ≤ q * n := Nat.mul_le_mul_right n hpq
  have hqrn : q * n ≤ r * n := Nat.mul_le_mul_right n hqr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hp1.trans hpqn, hqrn.trans hrEnd⟩, ?_⟩
  exact hpLog.trans_le (Real.log_le_log (by exact_mod_cast (show 0 < p * n by omega))
    (by exact_mod_cast hpqn))

/-- A prime above every cofactor prime is genuinely coprime to that
cofactor, so no separate divisibility selection remains in the interval. -/
theorem prime_not_dvd_of_above {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (habove : ∀ q ∈ n.primeFactors, q < p) : ¬ p ∣ n := by
  intro hpn
  exact (lt_irrefl p) (habove p (hp.mem_primeFactors hpn hn))

/-- A prime which belongs to the support and bounds it is the actual
canonical largest prime. -/
theorem largestPrime_eq_of_max {m p : ℕ} (hp : p ∈ m.primeFactors)
    (hmax : ∀ q ∈ m.primeFactors, q ≤ p) : largestPrime m = p := by
  have hm : m.primeFactors.Nonempty := ⟨p, hp⟩
  rw [largestPrime, dif_pos hm]
  exact le_antisymm (Finset.max'_le _ _ _ hmax) (Finset.le_max' _ p hp)

/-- Every prime above the cofactor support is the canonical owner of
its product, not merely a possible divisor. -/
theorem largestPrime_mul (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (hmax : ∀ q ∈ n.primeFactors, q < p) : largestPrime (p * n) = p := by
  apply largestPrime_eq_of_max
  · exact hp.mem_primeFactors (dvd_mul_right p n) (mul_ne_zero hp.ne_zero hn)
  · intro q hq
    rw [Nat.primeFactors_mul hp.ne_zero hn, hp.primeFactors, Finset.mem_union,
      Finset.mem_singleton] at hq
    rcases hq with rfl | hq
    · exact le_rfl
    · exact (hmax q hq).le

/-- The quotient owner recovers the complete original cofactor exactly. -/
theorem ownerCofactor_mul (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (hmax : ∀ q ∈ n.primeFactors, q < p) : ownerCofactor (p * n) = n := by
  rw [ownerCofactor, largestPrime_mul p n hp hn hmax]
  exact Nat.mul_div_cancel_left n hp.pos

/-- The exact interval cell key consists of the unchanged cofactor and
the active divisors at the actual prime logarithm. -/
theorem originalCellKey_mul (L : ℝ) (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (hmax : ∀ q ∈ n.primeFactors, q < p) :
    originalCellKey L (p * n) = (n, activeDivisors L n (Real.log p)) := by
  simp only [originalCellKey, ownerCofactor_mul p n hp hn hmax, largestPrime_mul p n hp hn hmax]

/-- The complete arithmetic fibre has only primality, the original
band, the owner threshold and one literal divisor-cell condition. -/
def intervalPrime (L : ℝ) (N n : ℕ) (D : Finset ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ (∀ q ∈ n.primeFactors, q < p) ∧
    p * n ∈ zetaPrimeLogBand N ∧ activeDivisors L n (Real.log p) = D

/-- Every prime between two primes of a fibre belongs to that fibre.
There are no hidden internal phase, filter or residue masks. -/
theorem intervalPrime_between (L : ℝ) (N n : ℕ) (D : Finset ℕ)
    {p q r : ℕ} (hp : intervalPrime L N n D p) (hr : intervalPrime L N n D r)
    (hq : q.Prime) (hpq : p ≤ q) (hqr : q ≤ r) : intervalPrime L N n D q := by
  refine ⟨hq, fun a ha => (hp.2.1 a ha).trans_le hpq,
    product_band_between N hpq hqr hp.2.2.1 hr.2.2.1, ?_⟩
  exact (prime_cell_between L n hp.1.pos hpq hqr (hr.2.2.2.trans hp.2.2.2.symm)).trans hp.2.2.2

end
end RiemannGaussian.ZetaRieszPrimeIntervals
