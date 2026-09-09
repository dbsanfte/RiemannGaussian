/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseArithmetic
import RiemannGaussian.Hybrid.EtaGeometricDecayVandermonde
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The full complex prime Gram kernel of the zeta logarithmic derivative

The Euler series at `conj s + t` is a genuine mixed Gram kernel when both
real parts exceed `1/2`. Complex coefficients, unequal real parts, and all
cross terms are retained. The eta prime-base separation theorem supplies a
finite prime-power witness for every nonzero finite combination of distinct
exponents. This distinguishes arithmetic separation from the support of a
chosen extremal phase polynomial.

All series remain in their half-plane of absolute convergence. Positivity
of this kernel does not give the missing signed Suzuki lower bound.
-/

open Complex ComplexConjugate Matrix
open scoped Classical Topology ComplexOrder

namespace RiemannGaussian

noncomputable section

/-- The complete complex prime feature. Its value at zero is harmless:
the von Mangoldt weight at zero vanishes. -/
def zetaPrimeFeature (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-(s * (Real.log n : ℂ)))

/-- The logarithmic derivative evaluated at the mixed complex parameter. -/
def zetaPrimeGram {ι : Type*} (s : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j ↦ -logDeriv riemannZeta (conj (s i) + s j)

/-- The literal finite arithmetic prefix of the mixed prime Gram kernel. -/
def zetaPrimeGramPrefix {ι : Type*} (N : ℕ) (s : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j ↦ ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℂ) *
    conj (zetaPrimeFeature (s i) n) * zetaPrimeFeature (s j) n

/-- The original mixed Euler term factors into its two prime features. -/
theorem zetaPrimeFeature_mixed (s t : ℂ) (n : ℕ) :
    conj (zetaPrimeFeature s n) * zetaPrimeFeature t n =
      zetaPrimeFeature (conj s + t) n := by
  simp only [zetaPrimeFeature, ← Complex.exp_conj, map_neg, map_mul,
    Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  ring

/-- The full feature agrees with the exact raw mode already separated by
the eta arithmetic machinery. -/
theorem zetaPrimeFeature_eq_etaGeometricDecayMode {p : ℕ} (hp : 0 < p) (s : ℂ) :
    zetaPrimeFeature s p = etaGeometricDecayMode p s := by
  unfold zetaPrimeFeature etaGeometricDecayMode
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'),
    ← Complex.natCast_log, ← Complex.exp_neg]
  congr 1
  ring

/-- Consecutive prime powers retain the exact geometric feature, including
its real decay and complex orientation. -/
theorem zetaPrimeFeature_prime_pow (s : ℂ) (p k : ℕ) :
    zetaPrimeFeature s (p ^ k) = zetaPrimeFeature s p ^ k := by
  simp only [zetaPrimeFeature, Nat.cast_pow, Real.log_pow, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem primeTerm_eq_feature (s : ℂ) (n : ℕ) :
    LSeries.term (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) s n =
      (ArithmeticFunction.vonMangoldt n : ℂ) * zetaPrimeFeature s n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
      ← Complex.natCast_log, ← Complex.exp_neg]
    unfold zetaPrimeFeature
    congr 2
    ring

/-- The complete mixed Euler series converges to the actual logarithmic
derivative; no real part or modulus has yet been taken. -/
theorem hasSum_zetaPrimeGram_entry {s t : ℂ} (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    HasSum (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) *
      conj (zetaPrimeFeature s n) * zetaPrimeFeature t n)
      (-logDeriv riemannZeta (conj s + t)) := by
  have hr : 1 < (conj s + t).re := by simp only [Complex.add_re, Complex.conj_re]; linarith
  rw [neg_logDeriv_riemannZeta_eq_vonMangoldt hr]
  apply (ArithmeticFunction.LSeriesSummable_vonMangoldt hr).hasSum.congr_fun
  intro n
  rw [primeTerm_eq_feature, ← zetaPrimeFeature_mixed]
  ring

private theorem primeGram_atom_energy {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (n : ℕ) :
    (∑ i, ∑ j, conj (c i) * c j *
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
        conj (zetaPrimeFeature (s i) n) * zetaPrimeFeature (s j) n)) =
      ((ArithmeticFunction.vonMangoldt n *
        Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n) : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The entire mixed zeta quadratic form is the genuinely convergent sum
of its complete prime-feature energies. Coefficients may be complex. -/
theorem hasSum_zetaPrimeGram_energy_complex {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    HasSum (fun n : ℕ ↦ ((ArithmeticFunction.vonMangoldt n *
      Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n) : ℝ) : ℂ))
      (∑ i, ∑ j, conj (c i) * c j * zetaPrimeGram s i j) := by
  have h (i j : ι) :=
    (hasSum_zetaPrimeGram_entry (hs i) (hs j)).mul_left (conj (c i) * c j)
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ ↦
    hasSum_sum (s := Finset.univ) (fun j _ ↦ h i j))
  exact hsum.congr_fun (fun n ↦ (primeGram_atom_energy s c n).symm)

/-- Taking the real part only after retaining the whole mixed identity
gives its nonnegative, convergent arithmetic energy. -/
theorem hasSum_zetaPrimeGram_energy {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    HasSum (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n *
      Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n))
      (∑ i, ∑ j, conj (c i) * c j * zetaPrimeGram s i j).re := by
  simpa only [Complex.ofReal_re] using
    (Complex.hasSum_re (hasSum_zetaPrimeGram_energy_complex s c hs))

/-- One prime simultaneously separates any finite set of distinct complex
probes. The prime depends on the probes, not on their coefficients. -/
theorem exists_prime_zetaPrimeFeature_injective {ι : Type*} [Fintype ι]
    (s : ι → ℂ) (hs : Function.Injective s) :
    ∃ p : ℕ, p.Prime ∧ Function.Injective (fun i ↦ zetaPrimeFeature (s i) p) := by
  obtain ⟨p, hp, _, _, hinj⟩ :=
    exists_prime_etaGeometricDecayMode_injOn Finset.univ s
      (fun _ _ _ _ hij ↦ hs hij)
  refine ⟨p, hp, fun i j hij ↦ hinj (Finset.mem_univ i) (Finset.mem_univ j) ?_⟩
  simpa only [zetaPrimeFeature_eq_etaGeometricDecayMode hp.pos] using hij

private theorem finite_geometric_block_nonzero {ι : Type*} [Fintype ι]
    (mode c : ι → ℂ) (hinj : Function.Injective mode)
    (hmode : ∀ i, mode i ≠ 0) (hc : c ≠ 0) (start : ℕ) :
    ∃ k : Fin (Fintype.card ι), ∑ i, c i * mode i ^ (start + k.val) ≠ 0 := by
  by_contra h
  push Not at h
  let e := Fintype.equivFin ι
  have hz : (fun j : Fin (Fintype.card ι) ↦ c (e.symm j) * mode (e.symm j) ^ start) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (hinj.comp e.symm.injective)
    intro k
    have he := e.symm.sum_comp (fun i ↦ c i * mode i ^ (start + k.val))
    rw [h k] at he
    simpa only [pow_add, mul_assoc, Function.comp_apply] using he
  apply hc
  funext i
  have hi : c i * mode i ^ start = 0 := by
    simpa only [Equiv.symm_apply_apply, Pi.zero_apply] using congrFun hz (e i)
  exact (mul_eq_zero.mp hi).resolve_right (pow_ne_zero start (hmode i))

/-- At a separating prime, every block of as many consecutive powers as
there are probes detects every nonzero coefficient vector. The block may
start arbitrarily late; no asymptotic limit is used. -/
theorem zetaPrimeFeature_block_nonzero {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) {p : ℕ}
    (hinj : Function.Injective (fun i ↦ zetaPrimeFeature (s i) p))
    (hc : c ≠ 0) (start : ℕ) :
    ∃ k : Fin (Fintype.card ι),
      ∑ i, c i * zetaPrimeFeature (s i) (p ^ (start + k.val)) ≠ 0 := by
  simpa only [zetaPrimeFeature_prime_pow] using
    finite_geometric_block_nonzero (fun i ↦ zetaPrimeFeature (s i) p) c hinj
      (fun i ↦ Complex.exp_ne_zero _) hc start

/-- A nonzero finite probe combination leaves strictly positive arithmetic
energy beyond every finite cutoff. This discharges the separation premise
using actual prime powers, rather than assuming an abstract positive Gram. -/
theorem zetaPrimeGram_finite_energy_lt {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re)
    (hinj : Function.Injective s) (hc : c ≠ 0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n *
      Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n)) <
      (∑ i, ∑ j, conj (c i) * c j * zetaPrimeGram s i j).re := by
  obtain ⟨p, hp, hpinj⟩ := exists_prime_zetaPrimeFeature_injective s hinj
  obtain ⟨k, hk⟩ := zetaPrimeFeature_block_nonzero s c hpinj hc (N + 1)
  let m := p ^ (N + 1 + k.val)
  have hNm : N < m := by
    have hpow : N + 1 + k.val < p ^ (N + 1 + k.val) := Nat.lt_pow_self hp.one_lt
    dsimp [m]
    omega
  have hm : m ∉ Finset.range (N + 1) := by simpa only [Finset.mem_range] using not_lt.mpr hNm
  have hΛ : ArithmeticFunction.vonMangoldt m = Real.log p := by
    rw [show m = p ^ (N + 1 + k.val) from rfl,
      ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hpos : 0 < ArithmeticFunction.vonMangoldt m *
      Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) m) := by
    rw [hΛ]
    exact mul_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) (Complex.normSq_pos.mpr hk)
  have hsum := hasSum_zetaPrimeGram_energy s c hs
  have hle := hsum.summable.sum_le_tsum (insert m (Finset.range (N + 1)))
    (fun n _ ↦ mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Complex.normSq_nonneg _))
  rw [Finset.sum_insert hm, hsum.tsum_eq] at hle
  linarith

/-- Strict positivity holds for arbitrary distinct complex probes in the
Euler Gram domain, with arbitrary nonzero complex coefficients. -/
theorem zetaPrimeGram_energy_pos {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re)
    (hinj : Function.Injective s) (hc : c ≠ 0) :
    0 < (∑ i, ∑ j, conj (c i) * c j * zetaPrimeGram s i j).re := by
  simpa using zetaPrimeGram_finite_energy_lt s c hs hinj hc 0

/-- The analytic kernel is Hermitian because its genuinely convergent
arithmetic entries preserve conjugation. -/
theorem zetaPrimeGram_isHermitian {ι : Type*}
    (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    (zetaPrimeGram s).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change conj (-logDeriv riemannZeta (conj (s j) + s i)) =
    -logDeriv riemannZeta (conj (s i) + s j)
  apply HasSum.unique _ (hasSum_zetaPrimeGram_entry (hs i) (hs j))
  apply (Complex.hasSum_conj'.mpr (hasSum_zetaPrimeGram_entry (hs j) (hs i))).congr_fun
  intro n
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- The standard complex matrix quadratic form equals the real arithmetic
energy. Its imaginary part vanishes by the full identity, not by omission. -/
theorem zetaPrimeGram_dotProduct_eq {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    star c ⬝ᵥ (zetaPrimeGram s *ᵥ c) =
      ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n *
        Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum, (hasSum_zetaPrimeGram_energy_complex s c hs).tsum_eq]
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every matrix on finitely many distinct complex probes is positive
definite. The conclusion is about the literal zeta logarithmic derivative. -/
theorem zetaPrimeGram_posDef {ι : Type*} [Fintype ι]
    (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) (hinj : Function.Injective s) :
    (zetaPrimeGram s).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (zetaPrimeGram_isHermitian s hs)
  intro c hc
  rw [zetaPrimeGram_dotProduct_eq s c hs]
  apply Complex.zero_lt_real.mpr
  rw [(hasSum_zetaPrimeGram_energy s c hs).tsum_eq]
  exact zetaPrimeGram_energy_pos s c hs hinj hc

/-- A finite prime prefix preserves the full Hermitian symmetry. -/
theorem zetaPrimeGramPrefix_isHermitian {ι : Type*} (N : ℕ) (s : ι → ℂ) :
    (zetaPrimeGramPrefix N s).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [zetaPrimeGramPrefix, Complex.star_def, map_sum, map_mul,
    Complex.conj_ofReal, Complex.conj_conj]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Exact finite-prefix arithmetic energy, with both mixed indices retained. -/
theorem zetaPrimeGramPrefix_dotProduct_eq {ι : Type*} [Fintype ι]
    (N : ℕ) (s c : ι → ℂ) :
    star c ⬝ᵥ (zetaPrimeGramPrefix N s *ᵥ c) =
      ((∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n *
        Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n) : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def,
    zetaPrimeGramPrefix, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [← primeGram_atom_energy s c n, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Subtracting any finite arithmetic prefix still leaves a positive
definite matrix. No finite collection of prime atoms exhausts this kernel. -/
theorem zetaPrimeGram_sub_prefix_posDef {ι : Type*} [Fintype ι]
    (N : ℕ) (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re)
    (hinj : Function.Injective s) :
    (zetaPrimeGram s - zetaPrimeGramPrefix N s).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    ((zetaPrimeGram_isHermitian s hs).sub (zetaPrimeGramPrefix_isHermitian N s))
  intro c hc
  rw [Matrix.sub_mulVec, dotProduct_sub, zetaPrimeGram_dotProduct_eq s c hs,
    zetaPrimeGramPrefix_dotProduct_eq N s c, ← Complex.ofReal_sub,
    Complex.zero_lt_real, sub_pos, (hasSum_zetaPrimeGram_energy s c hs).tsum_eq]
  exact zetaPrimeGram_finite_energy_lt s c hs hinj hc N

/-- The explicit arithmetic energy in one full prime-power block is an
independent lower floor for the remaining zeta energy. All mixed terms stay
inside each square. The block lies wholly beyond the displayed cutoff. -/
theorem zetaPrimeGram_prime_block_le_remainder {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re)
    {p : ℕ} (hp : p.Prime) (N start : ℕ) (hstart : 0 < start)
    (hN : N < p ^ start) :
    (∑ k : Fin (Fintype.card ι), Real.log p *
      Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) (p ^ (start + k.val)))) ≤
      (∑ i, ∑ j, conj (c i) * c j * zetaPrimeGram s i j).re -
        ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n *
          Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n) := by
  let index (k : Fin (Fintype.card ι)) := p ^ (start + k.val)
  let block := Finset.univ.image index
  have hi : Function.Injective index := by
    intro i j hij
    have he := Nat.pow_right_injective hp.two_le hij
    exact Fin.ext (Nat.add_left_cancel he)
  have hb : ∀ m ∈ block, N < m := by
    intro m hm
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hm
    exact hN.trans_le (Nat.pow_le_pow_right hp.pos (Nat.le_add_right start k.val))
  have hdis : Disjoint (Finset.range (N + 1)) block := by
    apply Finset.disjoint_left.mpr
    intro m hm hmb
    have hmN := Finset.mem_range.mp hm
    have hNm := hb m hmb
    omega
  have hsum := hasSum_zetaPrimeGram_energy s c hs
  have hle := hsum.summable.sum_le_tsum (Finset.range (N + 1) ∪ block)
    (fun n _ ↦ mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Complex.normSq_nonneg _))
  rw [Finset.sum_union hdis, hsum.tsum_eq] at hle
  have he : (∑ m ∈ block, ArithmeticFunction.vonMangoldt m *
      Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) m)) =
      ∑ k : Fin (Fintype.card ι), Real.log p *
        Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) (p ^ (start + k.val))) := by
    rw [show block = Finset.univ.image index from rfl, Finset.sum_image hi.injOn]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [index]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [he] at hle
  linarith

/-- One prime provides a strictly positive, explicit finite block floor
for every nonzero coefficient vector and every late block. No lower bound
uniform in the cutoff or the choice of probes is asserted. -/
theorem exists_prime_zetaPrimeGram_strict_block_floor {ι : Type*} [Fintype ι]
    (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) (hinj : Function.Injective s) :
    ∃ p : ℕ, p.Prime ∧ ∀ (c : ι → ℂ), c ≠ 0 → ∀ N start : ℕ,
      0 < start → N < p ^ start →
      0 < (∑ k : Fin (Fintype.card ι), Real.log p *
        Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) (p ^ (start + k.val)))) ∧
      (∑ k : Fin (Fintype.card ι), Real.log p *
        Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) (p ^ (start + k.val)))) ≤
        (∑ i, ∑ j, conj (c i) * c j * zetaPrimeGram s i j).re -
          ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n *
            Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n) := by
  obtain ⟨p, hp, hpinj⟩ := exists_prime_zetaPrimeFeature_injective s hinj
  refine ⟨p, hp, fun c hc N start hstart hN ↦ ⟨?_,
    zetaPrimeGram_prime_block_le_remainder s c hs hp N start hstart hN⟩⟩
  obtain ⟨k, hk⟩ := zetaPrimeFeature_block_nonzero s c hpinj hc start
  apply Finset.sum_pos'
    (fun _ _ ↦ mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
      (Complex.normSq_nonneg _))
  exact ⟨k, Finset.mem_univ k, mul_pos
    (Real.log_pos (by exact_mod_cast hp.one_lt)) (Complex.normSq_pos.mpr hk)⟩

/-- Every finite set of distinct probes has full matrix rank, even after
removing any finite prime prefix. Thus no fixed finite rank is selected by
the arithmetic kernel or by a chosen phase-optimizer support. -/
theorem zetaPrimeGram_sub_prefix_rank {ι : Type*} [Fintype ι]
    (N : ℕ) (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re)
    (hinj : Function.Injective s) :
    (zetaPrimeGram s - zetaPrimeGramPrefix N s).rank = Fintype.card ι := by
  exact Matrix.rank_of_isUnit _ (zetaPrimeGram_sub_prefix_posDef N s hs hinj).isUnit

/-- The strict two-probe inequality for the literal complex logarithmic
derivative retains both the real and imaginary parts of its mixed entry. -/
theorem zetaPrimeGram_strict_cauchySchwarz {s t : ℂ}
    (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) (hst : s ≠ t) :
    Complex.normSq (-logDeriv riemannZeta (conj s + t)) <
      (-logDeriv riemannZeta (conj s + s)).re *
        (-logDeriv riemannZeta (conj t + t)).re := by
  let u : Fin 2 → ℂ := ![s, t]
  have hu : ∀ i, 1 / 2 < (u i).re := by
    intro i
    fin_cases i
    · exact hs
    · exact ht
  have hinj : Function.Injective u := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [u]
  have hp := zetaPrimeGram_posDef u hu hinj
  have hd := (Complex.lt_def.mp hp.det_pos).1
  rw [Matrix.det_fin_two] at hd
  have hdiag (i : Fin 2) : (zetaPrimeGram u i i).im = 0 :=
    Complex.conj_eq_iff_im.mp (hp.isHermitian.apply i i)
  have hreverse : zetaPrimeGram u 1 0 = conj (zetaPrimeGram u 0 1) :=
    (hp.isHermitian.apply 1 0).symm
  rw [hreverse, Complex.mul_conj] at hd
  simp only [Complex.sub_re, Complex.mul_re, hdiag, mul_zero, sub_zero,
    Complex.ofReal_re, Complex.zero_re] at hd
  change Complex.normSq (zetaPrimeGram u 0 1) <
    (zetaPrimeGram u 0 0).re * (zetaPrimeGram u 1 1).re
  linarith

/-- Away from zero height, the complete complex logarithmic derivative
has strictly smaller modulus than its real-axis arithmetic mass. Unlike a
cosine-only estimate, this controls the sine channel at the same time. -/
theorem norm_neg_logDeriv_riemannZeta_lt_real_axis {σ y : ℝ}
    (hσ : 1 < σ) (hy : y ≠ 0) :
    ‖-logDeriv riemannZeta ((σ : ℂ) + I * y)‖ <
      (-logDeriv riemannZeta (σ : ℂ)).re := by
  let s : ℂ := (σ / 2 : ℝ)
  let t : ℂ := (σ / 2 : ℝ) + I * y
  have hs : 1 / 2 < s.re := by dsimp [s]; linarith
  have ht : 1 / 2 < t.re := by simp only [t, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; linarith
  have hst : s ≠ t := by
    intro he
    have hi := congrArg Complex.im he
    have : y = 0 := by simpa [s, t] using hi.symm
    exact hy this
  have he := zetaPrimeGram_strict_cauchySchwarz hs ht hst
  have hmix : conj s + t = (σ : ℂ) + I * y := by
    dsimp [s, t]
    rw [Complex.conj_ofReal]
    push_cast
    ring
  have hdiagS : conj s + s = (σ : ℂ) := by
    dsimp [s]
    rw [Complex.conj_ofReal]
    push_cast
    ring
  have hdiagT : conj t + t = (σ : ℂ) := by
    dsimp [t]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hmix, hdiagS, hdiagT, Complex.normSq_eq_norm_sq] at he
  have hmass : 0 ≤ (-logDeriv riemannZeta (σ : ℂ)).re := by
    rw [← (hasSum_zetaPhasePrimeWeight hσ).tsum_eq]
    exact tsum_nonneg (zetaPhasePrimeWeight_nonneg σ)
  nlinarith only [he, hmass, norm_nonneg (-logDeriv riemannZeta ((σ : ℂ) + I * y))]

end

end RiemannGaussian
