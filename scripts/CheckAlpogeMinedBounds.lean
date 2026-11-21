import Formalism.ZetaNonvanishing.GzLipschitz
import RiemannGaussian.AlpogeZetaSampleBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Lean.Util.CollectAxioms

/-! # Factorial and variation bounds for the zeta ramp from four archived modules -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Formalism.LogFactorialMertensBounds
open scoped ArithmeticFunction.vonMangoldt
open AlpogeZetaSamples

/-- The archive's real positive-index sum agrees with the native reciprocal ramp. -/
theorem G_eq_archive {x : ℝ} (hx : 0 ≤ x) : G x = Formalism.Gz x := by
  suffices h : ramp x = Formalism.Sz x by simp [G, Formalism.Gz, h]
  unfold ramp Formalism.Sz
  have hi : Icc 1 ⌊x⌋₊ ⊆ range (⌊x⌋₊+1) := by
    intro n hn
    simp only [mem_Icc, mem_range] at *
    omega
  rw [← Finset.sum_subset hi (f := fun n : ℕ => Λ n * max (x/n-1) 0) (by
    intro n hn hn'
    have hz : n = 0 := by simp only [mem_Icc, mem_range] at *; omega
    simp [hz])]
  apply Finset.sum_congr rfl
  intro n hn
  have hp : (0:ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnx : (n:ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hx)
  rw [max_eq_left (sub_nonneg.mpr ((one_le_div hp).mpr hnx))]

/-- An explicit two-sided Lipschitz constant, valid including between prime-power events. -/
theorem G_lipschitz {x y : ℝ} (hx : 1/2 ≤ x) (hy : 1/2 ≤ y) :
    |G x - G y| ≤ (Real.log 4 + 7)*|x-y| := by
  rw [G_eq_archive (by linarith), G_eq_archive (by linarith)]
  apply lip_upto (⌊x⌋₊+⌊y⌋₊) y x hy _ hx
  all_goals push_cast; linarith [Nat.lt_floor_add_one x, Nat.lt_floor_add_one y,
    Nat.cast_nonneg (α := ℝ) ⌊x⌋₊, Nat.cast_nonneg (α := ℝ) ⌊y⌋₊]

/-- The complement of the fractional part of the reciprocal coordinate at a positive index. -/
def weight (N d : ℕ) : ℝ := 1 - (N % d : ℕ) / (d : ℝ)

/-- Ordinary primes with the bounded reciprocal weights that occur at the sample itself. -/
def primeSum (N : ℕ) : ℝ := ∑ p ∈ (Ioc 0 N).filter Nat.Prime, Real.log p * weight N p

private def allSum (N : ℕ) : ℝ := ∑ d ∈ Ioc 0 N, Λ d * weight N d

/-- At a positive denominator the complementary residue weight lies in the unit interval. -/
theorem weight_mem {N d : ℕ} (hd : 0 < d) : 0 ≤ weight N d ∧ weight N d ≤ 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  exact ⟨sub_nonneg.mpr ((div_le_one hd').mpr hm), sub_le_self _ (by positivity)⟩

private theorem factorial_identity (N : ℕ) :
    G N = Real.eulerMascheroniConstant*N - allSum N +
      (Real.log N.factorial - N*Real.log N + N) := by
  rw [G_eq_archive (Nat.cast_nonneg N)]
  have hf := (sum_log_eq N).symm.trans (sum_log_eq_log_factorial N)
  have he : Formalism.Sz N + allSum N = Real.log N.factorial := by
    unfold Formalism.Sz allSum
    rw [Nat.floor_natCast, Icc_one_eq_Ioc, ← Finset.sum_add_distrib, ← hf]
    apply Finset.sum_congr rfl
    intro d hd
    have hp : (0:ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
    have hdiv : (((N % d : ℕ) : ℝ) + d*((N / d : ℕ) : ℝ)) = N := by
      exact_mod_cast Nat.mod_add_div N d
    unfold weight
    rw [← mul_add]
    congr 1
    field_simp
    linarith
  unfold Formalism.Gz
  linarith

/-- The elementary remainder after centering the factorial at the Euler-constant main term. -/
theorem factorial_remainder {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ Real.log N.factorial - N*Real.log N + N ∧
    Real.log N.factorial - N*Real.log N + N ≤ 1 + Real.log N / 2 := by
  have hp : (0:ℝ) < N := by exact_mod_cast hN
  have hf := Real.log_le_log (show 0 < (N:ℝ)^N / N.factorial by positivity)
    (Real.pow_div_factorial_le_exp (N:ℝ) hp.le N)
  rw [Real.log_exp, Real.log_div (by positivity) (by positivity), Real.log_pow] at hf
  have hseq : Real.log (Stirling.stirlingSeq N) ≤ Real.log (Stirling.stirlingSeq 1) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    exact Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  rw [Stirling.log_stirlingSeq_formula, Stirling.log_stirlingSeq_formula,
    Real.log_mul (by norm_num) hp.ne', Real.log_div hp.ne' (Real.exp_pos _).ne'] at hseq
  simp at hseq
  exact ⟨by linarith, by linarith⟩

private theorem power_excess (N : ℕ) :
    0 ≤ allSum N - primeSum N ∧ allSum N - primeSum N ≤ Chebyshev.psi N - Chebyshev.theta N := by
  let s := Ioc 0 N
  have hs (f : ℕ → ℝ) : (∑ d ∈ s, Λ d * f d) -
      (∑ d ∈ s.filter Nat.Prime, Real.log d * f d) = ∑ d ∈ s.filter (fun d => ¬ d.Prime), Λ d * f d := by
    have he : (∑ d ∈ s.filter Nat.Prime, Real.log d * f d) =
        ∑ d ∈ s.filter Nat.Prime, Λ d * f d := by
      exact Finset.sum_congr rfl fun d hd => by rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hd).2]
    rw [he, ← Finset.sum_filter_add_sum_filter_not s Nat.Prime (fun d => Λ d * f d)]
    ring
  have h1 := hs (fun _ => 1)
  simp only [mul_one] at h1
  have hps : Chebyshev.psi N - Chebyshev.theta N = ∑ d ∈ s.filter (fun d => ¬ d.Prime), Λ d := by
    simpa [Chebyshev.psi, Chebyshev.theta, s] using h1
  rw [allSum, primeSum, hs, hps]
  constructor
  · exact sum_nonneg fun d hd => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (weight_mem (N := N) (mem_Ioc.mp (mem_filter.mp hd).1).1).1
  · exact sum_le_sum fun d hd => mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (weight_mem (N := N) (mem_Ioc.mp (mem_filter.mp hd).1).1).2

/-- For an upper bound on any integer sample, dropping all proper prime powers costs only
the explicit logarithmic factorial remainder. The reverse error is at most the proper-power mass. -/
theorem integer_sample_bounds {N : ℕ} (hN : 1 ≤ N) :
    Real.eulerMascheroniConstant*N - primeSum N - (Chebyshev.psi N - Chebyshev.theta N) ≤ G N ∧
    G N ≤ Real.eulerMascheroniConstant*N - primeSum N + (1 + Real.log N / 2) := by
  rw [factorial_identity]
  obtain ⟨h₁,h₂⟩ := power_excess N
  obtain ⟨h₃,h₄⟩ := factorial_remainder hN
  constructor <;> linarith

/-- In both directions the weighted ordinary-prime sum recovers the sample to square-root accuracy. -/
theorem integer_sample_abs_error : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |G N - (Real.eulerMascheroniConstant*N - primeSum N)| ≤ C*Real.sqrt N := by
  obtain ⟨K,hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max 1 K,fun N hN => ?_⟩
  obtain ⟨hl,hu⟩ := integer_sample_bounds hN
  have hp : (0:ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp)
  rw [Real.log_sqrt hp.le] at hlog
  apply abs_le.mpr
  constructor
  · linarith only [hl,(hK N).trans (mul_le_mul_of_nonneg_right
      (le_max_right 1 K) (Real.sqrt_nonneg N))]
  · linarith only [hu,hlog,mul_le_mul_of_nonneg_right (le_max_left 1 K) (Real.sqrt_nonneg N)]

/-- The fourth-power checkpoints only need primes above the square root of the cutoff. -/
def largePrimeSum (N : ℕ) : ℝ :=
  ∑ p ∈ ((Ioc 0 N).filter Nat.Prime).filter (fun p : ℕ => Real.sqrt N < p), Real.log p * weight N p

private theorem small_primes {N : ℕ} :
    0 ≤ primeSum N - largePrimeSum N ∧
    primeSum N - largePrimeSum N ≤ (Real.log 4 + 4)*Real.sqrt N := by
  let s := (Ioc 0 N).filter Nat.Prime
  let small := s.filter (fun p : ℕ => ¬ Real.sqrt N < p)
  let primes := (Ioc 0 ⌊Real.sqrt N⌋₊).filter Nat.Prime
  have hsub : small ⊆ primes := by
    intro p hp
    obtain ⟨hp,hl⟩ := mem_filter.mp hp
    obtain ⟨hI, hprime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hI).1, Nat.le_floor (not_lt.mp hl)⟩, hprime⟩
  have hlog (p : ℕ) (hp : 0 < p) : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have split : primeSum N - largePrimeSum N = ∑ p ∈ small, Real.log p * weight N p := by
    unfold primeSum largePrimeSum
    linarith only [Finset.sum_filter_add_sum_filter_not s (fun p : ℕ => Real.sqrt N < p)
      (fun p => Real.log p * weight N p)]
  rw [split]
  constructor
  · apply sum_nonneg
    intro p hp
    have hp0 := (mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
    exact mul_nonneg (hlog p hp0) (weight_mem hp0).1
  · calc
      _ ≤ ∑ p ∈ small, Real.log p := by
        apply sum_le_sum
        intro p hp
        have hp0 := (mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
        exact mul_le_of_le_one_right (hlog p hp0) (weight_mem hp0).2
      _ ≤ ∑ p ∈ primes, Real.log p := sum_le_sum_of_subset_of_nonneg hsub
        fun p hp _ => hlog p (mem_Ioc.mp (mem_filter.mp hp).1).1
      _ ≤ Chebyshev.psi (Real.sqrt N) := Chebyshev.theta_le_psi _
      _ ≤ _ := Chebyshev.psi_le_const_mul_self (Real.sqrt_nonneg N)

/-- Only ordinary primes in the band from the square root to the cutoff can affect the
integer sample beyond square-root accuracy. The upper error is at most logarithmic. -/
theorem large_prime_sample_bounds :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      Real.eulerMascheroniConstant*N - largePrimeSum N - K*Real.sqrt N ≤ G N ∧
      G N ≤ Real.eulerMascheroniConstant*N - largePrimeSum N + (1 + Real.log N / 2) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨|C| + (Real.log 4 + 4), by positivity, fun N hN => ?_⟩
  obtain ⟨hl,hu⟩ := integer_sample_bounds hN
  obtain ⟨hp,hq⟩ := small_primes (N := N)
  have h := (hC N).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg N))
  constructor <;> linarith

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.G_eq_archive, ``RiemannGaussian.AlpogeMined.G_lipschitz,
      ``RiemannGaussian.AlpogeMined.factorial_remainder, ``RiemannGaussian.AlpogeMined.integer_sample_bounds,
      ``RiemannGaussian.AlpogeMined.integer_sample_abs_error,
      ``RiemannGaussian.AlpogeMined.large_prime_sample_bounds] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axioms}"
