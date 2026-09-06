import RiemannGaussian.FinitePeriodicFourier
import Mathlib.Data.Nat.Factorial.Basic

/-!
# An exact finite grid for the eta divisor spectrum

The grid contains every literal divisor period and every pair period.
Annihilator divisibility proves integer separation of distinct spectrum
representatives. Its size is auxiliary and cancels from the sampling bound;
no approximate frequency rounding or independence assumption is used.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A common block scale divisible by every divisor and pair period. -/
def pairedEtaDivisorFourierBlock (D : ℕ) : ℕ := 2 * D.factorial ^ 2

/-- The band budget retains the square of the actual divisor cutoff. -/
def pairedEtaDivisorFourierBudget (D L : ℕ) : ℕ := 4 * D ^ 2 + L

/-- The finite auxiliary grid is the common block scale times the band budget. -/
def pairedEtaDivisorFourierGrid (D L : ℕ) : ℕ :=
  pairedEtaDivisorFourierBlock D * pairedEtaDivisorFourierBudget D L

/-- The exact common block scale is always positive. -/
theorem pairedEtaDivisorFourierBlock_pos (D : ℕ) : 0 < pairedEtaDivisorFourierBlock D := by
  unfold pairedEtaDivisorFourierBlock
  exact mul_pos (by norm_num) (pow_pos (Nat.factorial_pos D) _)

/-- A nonempty sample window gives a positive finite grid. -/
theorem pairedEtaDivisorFourierGrid_pos (D : ℕ) {L : ℕ} (hL : 0 < L) :
    0 < pairedEtaDivisorFourierGrid D L := by
  exact mul_pos (pairedEtaDivisorFourierBlock_pos D)
    (by unfold pairedEtaDivisorFourierBudget; omega)

/-- Every literal pair period divides the chosen common block scale. -/
theorem pairedEtaDivisorPairPeriod_dvd_block {d e D : ℕ}
    (hd : d ∈ Finset.Icc 1 D) (he : e ∈ Finset.Icc 1 D) :
    2 * d * e ∣ pairedEtaDivisorFourierBlock D := by
  have hdF := Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
  have heF := Nat.dvd_factorial (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp he).2
  simpa only [pairedEtaDivisorFourierBlock, pow_two, mul_assoc] using
    Nat.mul_dvd_mul_left 2 (Nat.mul_dvd_mul hdF heF)

/-- Every single literal divisor period divides the common block scale. -/
theorem pairedEtaDivisorPeriod_dvd_block {d D : ℕ} (hd : d ∈ Finset.Icc 1 D) :
    2 * d ∣ pairedEtaDivisorFourierBlock D := by
  have hD : 1 ≤ D := (Finset.mem_Icc.mp hd).1.trans (Finset.mem_Icc.mp hd).2
  simpa only [mul_one] using pairedEtaDivisorPairPeriod_dvd_block hd
    (Finset.mem_Icc.mpr ⟨le_rfl, hD⟩)

variable {Q : ℕ} [NeZero Q]

/-- The complete arithmetic spectrum allows every annihilator of a
literal divisor period, including all repeated frequency coincidences. -/
def pairedEtaDivisorFourierSpectrum (D : ℕ) (Q : ℕ) [NeZero Q] : Finset (ZMod Q) :=
  Finset.univ.filter (fun k ↦ ∃ d ∈ Finset.Icc 1 D, ((2 * d : ℕ) : ZMod Q) * k = 0)

/-- Spectrum membership keeps its literal divisor witness. -/
theorem mem_pairedEtaDivisorFourierSpectrum (D : ℕ) (k : ZMod Q) :
    k ∈ pairedEtaDivisorFourierSpectrum D Q ↔
      ∃ d ∈ Finset.Icc 1 D, ((2 * d : ℕ) : ZMod Q) * k = 0 := by
  simp only [pairedEtaDivisorFourierSpectrum, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Distinct spectrum representatives have the exact integer separation
forced by their divisor denominators and the chosen grid scale. -/
theorem pairedEtaDivisorFourierSpectrum_separated {D h : ℕ} (hD : 0 < D)
    (hQ : 4 * D ^ 2 * h ≤ Q) :
    ∀ k ∈ pairedEtaDivisorFourierSpectrum D Q,
      ∀ l ∈ pairedEtaDivisorFourierSpectrum D Q, k.val < l.val → k.val + h ≤ l.val := by
  intro k hk l hl hkl
  obtain ⟨d, hd, hdk⟩ := (mem_pairedEtaDivisorFourierSpectrum D k).mp hk
  obtain ⟨e, he, hel⟩ := (mem_pairedEtaDivisorFourierSpectrum D l).mp hl
  have hdv : Q ∣ 2 * d * k.val := by
    apply (ZMod.natCast_eq_zero_iff _ Q).mp
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using hdk
  have hev : Q ∣ 2 * e * l.val := by
    apply (ZMod.natCast_eq_zero_iff _ Q).mp
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using hel
  have hdk' : Q ∣ 4 * d * e * k.val := by
    convert dvd_mul_of_dvd_right hdv (2 * e) using 1
    congr 1
    ring
  have hel' : Q ∣ 4 * d * e * l.val := by
    convert dvd_mul_of_dvd_right hev (2 * d) using 1
    congr 1
    ring
  have hgap : Q ∣ 4 * d * e * (l.val - k.val) := by
    rw [Nat.mul_sub_left_distrib]
    exact Nat.dvd_sub hel' hdk'
  have hdp : 0 < d := (Finset.mem_Icc.mp hd).1
  have hep : 0 < e := (Finset.mem_Icc.mp he).1
  have hpositive : 0 < 4 * d * e * (l.val - k.val) := by
    exact mul_pos (by positivity) (Nat.sub_pos_of_lt hkl)
  have hde : 4 * d * e ≤ 4 * D ^ 2 := by
    have hh := Nat.mul_le_mul (Finset.mem_Icc.mp hd).2 (Finset.mem_Icc.mp he).2
    nlinarith
  have hbig : 4 * D ^ 2 * h ≤ 4 * D ^ 2 * (l.val - k.val) :=
    hQ.trans ((Nat.le_of_dvd hpositive hgap).trans
      (Nat.mul_le_mul_right (l.val - k.val) hde))
  have hscale : 0 < 4 * D ^ 2 := by positivity
  have hh : h ≤ l.val - k.val := by nlinarith
  omega

end

end RiemannGaussian
