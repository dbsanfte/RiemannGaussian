/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerDecay
import RiemannGaussian.ZetaRoughPrimeLogSource

/-!
# The full complex quadratic form of the squarefree Euler factors

The literal marked Euler factor has a Selberg divisor diagonalization.
Its diagonal weights are exactly q^s, and its transformed coordinates
remain complex. This is the complex counterpart of the diagonalization
in Mathlib.NumberTheory.SelbergSieve, specialized to the actual local
factors p^(-s)/(1+p^(-s)). No positivity of the complex squares is asserted.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius LSeries.notation

/-- The actual local marked weight, extended multiplicatively over
distinct prime factors. The arithmetic zero index is explicitly zero. -/
def atom (s : ℂ) : ArithmeticFunction ℂ :=
  .prodPrimeFactors (fun p ↦ zetaPrimeFeature s p / (1 + zetaPrimeFeature s p))

/-- The finite marked weights are multiplicative on coprime integers. -/
theorem atom_multiplicative (s : ℂ) : (atom s).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

/-- The original exponential feature is nonzero, including at its
explicitly defined zero index. -/
theorem feature_ne_zero (s : ℂ) (n : ℕ) : zetaPrimeFeature s n ≠ 0 := Complex.exp_ne_zero _

/-- Reversing the complex parameter inverts the complete feature,
retaining both its phase and damping. -/
theorem feature_neg (s : ℂ) (n : ℕ) :
    zetaPrimeFeature (-s) n = (zetaPrimeFeature s n)⁻¹ := by
  unfold zetaPrimeFeature
  rw [← Complex.exp_neg]
  congr 1
  ring

private theorem prime_local_ne_zero {s : ℂ} (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    1 + zetaPrimeFeature s p ≠ 0 := by
  have hnorm : ‖zetaPrimeFeature s p‖ < 1 := by
    rw [norm_zetaPrimeFeature]
    apply Real.exp_lt_one_iff.mpr
    have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    nlinarith
  intro he
  have he' : zetaPrimeFeature s p = -1 := by linear_combination he
  simp [he'] at hnorm

/-- Every nonzero mark has nonzero Euler weight in the open right
half-plane. The local denominator condition is fully discharged. -/
theorem atom_ne_zero {s : ℂ} (hs : 0 < s.re) {P : ℕ} (hP : P ≠ 0) : atom s P ≠ 0 := by
  rw [atom, ArithmeticFunction.prodPrimeFactors_apply hP]
  exact Finset.prod_ne_zero_iff.mpr (fun p hp ↦ div_ne_zero (feature_ne_zero s p)
    (prime_local_ne_zero hs (Nat.prime_of_mem_primeFactors hp)))

/-- The squarefree mark contributes its literal feature times all its
reciprocal local denominators. -/
theorem atom_eq_feature_product {P : ℕ} (hP : Squarefree P) (s : ℂ) :
    atom s P = zetaPrimeFeature s P *
      ∏ p ∈ P.primeFactors, (1 + zetaPrimeFeature s p)⁻¹ := by
  have hf : zetaPrimeFeature s P = ∏ p ∈ P.primeFactors, zetaPrimeFeature s p := by
    rw [zetaPrimeFeature, CoprimeEulerPhase.squarefree_log_eq_prime_sum hP,
      Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.exp_sum]
    rfl
  rw [atom, ArithmeticFunction.prodPrimeFactors_apply hP.ne_zero, hf, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun _ _ ↦ div_eq_mul_inv _ _)

/-- The roughness factor and the entire divisibility mark separate
exactly when their prime sets are disjoint. -/
theorem multiplier_eq (S : Finset ℕ) {P : ℕ} (hP : Squarefree P)
    (hPS : ∀ a ∈ P.primeFactors, a ∉ S) (s : ℂ) :
    squarefreeEulerMultiplier S P s =
      (∏ a ∈ S, (1 + zetaPrimeFeature s a)⁻¹) * atom s P := by
  have hd : Disjoint S P.primeFactors := Finset.disjoint_left.mpr
    (fun a haS haP ↦ hPS a haP haS)
  rw [squarefreeEulerMultiplier, Finset.prod_union hd, atom_eq_feature_product hP]
  ring

private def featureArithmetic (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else zetaPrimeFeature s n, by simp⟩

private theorem featureArithmetic_multiplicative (s : ℂ) :
    (featureArithmetic s).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [featureArithmetic, zetaPrimeFeature], ?_⟩
  intro m n hm hn _
  simp only [featureArithmetic, ArithmeticFunction.coe_mk, if_neg hm, if_neg hn,
    if_neg (Nat.mul_ne_zero hm hn)]
  exact CoprimeEulerPhase.feature_mul s (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

/-- The reciprocal squarefree local weight is the exact divisor sum
of q^s. This determines the diagonal weights without any estimates. -/
theorem atom_inv_eq_divisor_sum {P : ℕ} (hP : Squarefree P) (s : ℂ) :
    (atom s P)⁻¹ = ∑ q ∈ P.divisors, zetaPrimeFeature (-s) q := by
  have h := (featureArithmetic_multiplicative (-s)).prodPrimeFactors_one_add_of_squarefree hP
  have hl : (∏ p ∈ P.primeFactors, (1 + featureArithmetic (-s) p)) =
      ∏ p ∈ P.primeFactors, (1 + zetaPrimeFeature (-s) p) := by
    apply Finset.prod_congr rfl
    intro p hp
    simp only [featureArithmetic, ArithmeticFunction.coe_mk,
      if_neg (Nat.prime_of_mem_primeFactors hp).ne_zero]
  have hr : (∑ q ∈ P.divisors, featureArithmetic (-s) q) =
      ∑ q ∈ P.divisors, zetaPrimeFeature (-s) q := by
    exact Finset.sum_congr rfl (fun q hq ↦ by
      simp only [featureArithmetic, ArithmeticFunction.coe_mk, if_neg (Nat.pos_of_mem_divisors hq).ne'])
  rw [hl, hr] at h
  rw [← h, atom, ArithmeticFunction.prodPrimeFactors_apply hP.ne_zero, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [inv_div, feature_neg]
  field_simp [feature_ne_zero s p]
  ring

/-- The full lcm entry factors through all common divisors, whose
complex phase is q^s. Shared-prime intersections are unchanged. -/
theorem atom_lcm_eq_divisor_sum {s : ℂ} (hs : 0 < s.re) {d e : ℕ} (hd : Squarefree d) :
    atom s (Nat.lcm d e) = atom s d * atom s e *
      ∑ q ∈ (Nat.gcd d e).divisors, zetaPrimeFeature (-s) q := by
  have hg : Squarefree (Nat.gcd d e) := hd.squarefree_of_dvd (Nat.gcd_dvd_left d e)
  rw [(atom_multiplicative s).map_lcm (atom_ne_zero hs hg.ne_zero), div_eq_mul_inv,
    atom_inv_eq_divisor_sum hg]

/-- The transformed coordinate keeps the original weight and exact
Euler factor over every multiple of its divisor. -/
def coordinate (T : Finset ℕ) (w : ℕ → ℂ) (s : ℂ) (q : ℕ) : ℂ :=
  ∑ d ∈ T, if q ∣ d then w d * atom s d else 0

/-- The complete bilinear Euler matrix, before taking a norm or
discarding any phase. Taking equal weights gives its complex square form. -/
def form (T : Finset ℕ) (w v : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ T, ∑ e ∈ T, w d * v e * atom s (Nat.lcm d e)

private theorem common_divisor_sum_eq {d e D : ℕ} (hd : 0 < d) (hdD : d ≤ D)
    (f : ℕ → ℂ) :
    (∑ q ∈ (Nat.gcd d e).divisors, f q) =
      ∑ q ∈ Finset.Icc 1 D, if q ∣ d ∧ q ∣ e then f q else 0 := by
  have hg : Nat.gcd d e ≠ 0 := (Nat.gcd_pos_of_pos_left e hd).ne'
  have heq : (Finset.Icc 1 D).filter (fun q ↦ q ∣ d ∧ q ∣ e) = (Nat.gcd d e).divisors := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · exact fun h ↦ ⟨h.2, hg⟩
    · intro h
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1.1 hd, (Nat.le_of_dvd hd h.1.1).trans hdD⟩, h.1⟩
  rw [← Finset.sum_filter, heq]

/-- The exact complex Selberg diagonalization for every pair of weight
families on the original finite squarefree marks. In particular, the
diagonal terms are products, not squared absolute values. -/
theorem form_eq_divisor_coordinates (T : Finset ℕ) (D : ℕ)
    (hT : ∀ d ∈ T, Squarefree d ∧ d ≤ D) (w v : ℕ → ℂ)
    {s : ℂ} (hs : 0 < s.re) :
    form T w v s = ∑ q ∈ Finset.Icc 1 D,
      zetaPrimeFeature (-s) q * coordinate T w s q * coordinate T v s q := by
  have he (d : ℕ) (hd : d ∈ T) (e : ℕ) :
      w d * v e * atom s (Nat.lcm d e) =
        ∑ q ∈ Finset.Icc 1 D, zetaPrimeFeature (-s) q *
          (if q ∣ d then w d * atom s d else 0) *
          (if q ∣ e then v e * atom s e else 0) := by
    rw [atom_lcm_eq_divisor_sum hs (hT d hd).1,
      common_divisor_sum_eq (Nat.pos_of_ne_zero (hT d hd).1.ne_zero) (hT d hd).2,
      ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hqd : q ∣ d <;> by_cases hqe : q ∣ e <;> simp [hqd, hqe]
    ring
  unfold form
  calc
    _ = ∑ d ∈ T, ∑ e ∈ T, ∑ q ∈ Finset.Icc 1 D, zetaPrimeFeature (-s) q *
        (if q ∣ d then w d * atom s d else 0) * (if q ∣ e then v e * atom s e else 0) := by
      exact Finset.sum_congr rfl (fun d hd ↦ Finset.sum_congr rfl (fun e _ ↦ he d hd e))
    _ = ∑ q ∈ Finset.Icc 1 D, ∑ d ∈ T, ∑ e ∈ T, zetaPrimeFeature (-s) q *
        (if q ∣ d then w d * atom s d else 0) * (if q ∣ e then v e * atom s e else 0) := by
      rw [eq_comm, Finset.sum_comm, Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm)]
    _ = _ := by
      simp only [coordinate, mul_assoc, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm)

/-- The diagonal correlation retains a literal complex square in each
divisor channel, with its exact q^s phase. -/
theorem form_self_eq_complex_squares (T : Finset ℕ) (D : ℕ)
    (hT : ∀ d ∈ T, Squarefree d ∧ d ≤ D) (w : ℕ → ℂ)
    {s : ℂ} (hs : 0 < s.re) :
    form T w w s = ∑ q ∈ Finset.Icc 1 D,
      zetaPrimeFeature (-s) q * coordinate T w s q ^ 2 := by
  rw [form_eq_divisor_coordinates T D hT w w hs]
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- The common complete rough squarefree quotient before inserting
the divisor weights. Ordinary primes have not been deleted. -/
def base (S : Finset ℕ) (s : ℂ) : ℂ :=
  (∏ a ∈ S, (1 + zetaPrimeFeature s a)⁻¹) * squarefreeEulerResponse s

/-- The original squarefree coefficient with two complete finite
divisor-weight sums. Both coefficient families remain complex. -/
def coefficient (S T : Finset ℕ) (w v : ℕ → ℂ) (n : ℕ) : ℂ :=
  RoughSquarefreeBare.coefficient S 1 n *
    RoughPrimeIncidence.weight T w n * RoughPrimeIncidence.weight T v n

/-- The full pair expansion holds on the literal coefficients before
the arithmetic series is summed or analytically continued. -/
theorem coefficient_eq_lcm_sum (S T : Finset ℕ) (w v : ℕ → ℂ) (n : ℕ) :
    coefficient S T w v n = ∑ d ∈ T, ∑ e ∈ T,
      (w d * v e) * RoughSquarefreeBare.coefficient S (Nat.lcm d e) n := by
  unfold coefficient RoughPrimeIncidence.weight
  conv_lhs => arg 1; rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hsf : Squarefree n <;> by_cases hrough : ∃ a ∈ S, a ∣ n <;>
    by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;>
      simp [RoughSquarefreeBare.coefficient, Nat.lcm_dvd_iff, hsf, hrough, hd, he]

/-- Every pair of squarefree marks has a squarefree lcm, including
all their shared primes. -/
theorem lcm_squarefree {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    Squarefree (Nat.lcm d e) := by
  have hn := (Nat.lcm_pos (Nat.pos_of_ne_zero hd.ne_zero) (Nat.pos_of_ne_zero he.ne_zero)).ne'
  apply (Nat.squarefree_iff_factorization_le_one hn).mpr
  intro p
  rw [Nat.factorization_lcm hd.ne_zero he.ne_zero, Finsupp.sup_apply]
  exact max_le (hd.natFactorization_le_one p) (he.natFactorization_le_one p)

/-- A shared divisor mark still avoids every originally excluded
prime. This retains the exact roughness condition under lcm insertion. -/
theorem lcm_rough (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {d e : ℕ}
    (hd : ¬∃ a ∈ S, a ∣ d) (he : ¬∃ a ∈ S, a ∣ e) :
    ∀ a ∈ (Nat.lcm d e).primeFactors, a ∉ S := by
  intro a ha haS
  have hdiv := (Nat.dvd_of_mem_primeFactors ha).trans (Nat.lcm_dvd_mul d e)
  rcases (hS a haS).dvd_mul.mp hdiv with h | h
  · exact hd ⟨a, haS, h⟩
  · exact he ⟨a, haS, h⟩

/-- The complete arithmetic correlation equals the full Euler matrix
times its common quotient. Every lcm entry has genuine convergence. -/
theorem LSeriesHasSum_coefficient (S T : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    (hT : ∀ d ∈ T, Squarefree d ∧ (¬∃ a ∈ S, a ∣ d)) (w v : ℕ → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (coefficient S T w v) s (base S s * form T w v s) := by
  have hm (d : ℕ) (hd : d ∈ T) (e : ℕ) (he : e ∈ T) :
      LSeriesHasSum (RoughSquarefreeBare.coefficient S (Nat.lcm d e)) s
        (base S s * atom s (Nat.lcm d e)) := by
    have hL := lcm_squarefree (hT d hd).1 (hT e he).1
    have hLS := lcm_rough S hS (hT d hd).2 (hT e he).2
    convert LSeriesHasSum_markedSquarefreeEuler S hS hL hLS hs using 1
    rw [multiplier_eq S hL hLS, base]
    ring
  have h := LSeriesHasSum.sum (S := T) (fun d hd ↦
    LSeriesHasSum.sum (S := T) (fun e he ↦ (hm d hd e he).smul (w d * v e)))
  convert h using 1
  · funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact coefficient_eq_lcm_sum S T w v n
  · simp only [form, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ ↦ Finset.sum_congr rfl (fun e _ ↦ by ring))

/-- Filtering impossible divisor marks leaves the arithmetic
coefficient unchanged on every integer, including the excluded integers. -/
theorem coefficient_eq_eligible (S T : Finset ℕ) (w v : ℕ → ℂ) :
    coefficient S T w v = coefficient S
      (T.filter (fun d ↦ Squarefree d ∧ (¬∃ a ∈ S, a ∣ d))) w v := by
  funext n
  by_cases hg : Squarefree n ∧ (¬∃ a ∈ S, a ∣ n)
  · have hw (f : ℕ → ℂ) : RoughPrimeIncidence.weight T f n =
        RoughPrimeIncidence.weight (T.filter (fun d ↦ Squarefree d ∧ (¬∃ a ∈ S, a ∣ d))) f n := by
      unfold RoughPrimeIncidence.weight
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d ∣ n
      · have hdg : Squarefree d ∧ (¬∃ a ∈ S, a ∣ d) :=
          ⟨hg.1.squarefree_of_dvd hd, fun ⟨a, ha, had⟩ ↦ hg.2 ⟨a, ha, had.trans hd⟩⟩
        simp [hd, hdg]
      · simp [hd]
    rw [coefficient, coefficient, hw w, hw v]
  · have hz : RoughSquarefreeBare.coefficient S 1 n = 0 := by
      simp only [RoughSquarefreeBare.coefficient, one_dvd, and_true, if_neg hg]
    simp only [coefficient, hz, zero_mul]

/-- The actual inclusive divisor cutoff with exactly its impossible
marks removed. This is a finite support identity, not a new sieve choice. -/
def eligible (D : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 D).filter (fun d ↦ Squarefree d ∧ (¬∃ a ∈ S, a ∣ d))

/-- The entire original cutoff correlation has the explicit complex
divisor-square representation, for every pair of weight families. -/
theorem LSeriesHasSum_cutoff_diagonal (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (w v : ℕ → ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (coefficient S (Finset.Icc 1 D) w v) s
      (base S s * ∑ q ∈ Finset.Icc 1 D, zetaPrimeFeature (-s) q *
        coordinate (eligible D S) w s q * coordinate (eligible D S) v s q) := by
  rw [coefficient_eq_eligible]
  have hT : ∀ d ∈ eligible D S, Squarefree d ∧ (¬∃ a ∈ S, a ∣ d) :=
    fun _ hd ↦ (Finset.mem_filter.mp hd).2
  have hb : ∀ d ∈ eligible D S, Squarefree d ∧ d ≤ D := by
    intro d hd
    exact ⟨(hT d hd).1, (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2⟩
  have h := LSeriesHasSum_coefficient S (eligible D S) hS hT w v hs
  rwa [form_eq_divisor_coordinates _ D hb w v (by linarith)] at h

/-- The complete diagonal expression for the original cutoff, with
its common quotient and both complex coordinate families. -/
def diagonal (D : ℕ) (S : Finset ℕ) (w v : ℕ → ℂ) (s : ℂ) : ℂ :=
  base S s * ∑ q ∈ Finset.Icc 1 D, zetaPrimeFeature (-s) q *
    coordinate (eligible D S) w s q * coordinate (eligible D S) v s q

/-- Every factorial moment of the diagonal expression is the original
convergent weighted arithmetic moment, with all cross terms retained. -/
theorem hasSum_cutoff_moment (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (w v : ℕ → ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ coefficient S (Finset.Icc 1 D) w v n *
      ((Real.log n : ℂ) ^ N / (N.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment N (diagonal D S w v) s) := by
  have hab : LSeries.abscissaOfAbsConv (coefficient S (Finset.Icc 1 D) w v) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro y hy
    exact (LSeriesHasSum_cutoff_diagonal D S hS w v (by simpa using hy)).LSeriesSummable
  have he : diagonal D S w v =ᶠ[𝓝 s] LSeries (coefficient S (Finset.Icc 1 D) w v) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_cutoff_diagonal D S hS w v hz).LSeries_eq.symm
  rw [signedTaylorMoment_congr N he]
  exact hasSum_signedTaylorMoment_LSeries _
    (by simp [coefficient, RoughSquarefreeBare.coefficient])
    (lt_of_le_of_lt hab (by exact_mod_cast hs)) N

/-- Every original polynomial filter commutes with the complex divisor
diagonalization. Its coefficient signs and logarithmic kernel are unchanged. -/
theorem hasSum_cutoff_filter (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (w v : ℕ → ℂ) (p : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ coefficient S (Finset.Icc 1 D) w v n * zetaPrimeFilterKernel p N s n)
      (zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k (diagonal D S w v) s) N) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (hasSum_cutoff_moment D S hS w v (N + k) hs).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ ↦ by ring)

/-- Multiplication by the full physical logarithm differentiates the
entire coupled diagonal expression, including its finite Euler factors. -/
theorem LSeriesHasSum_cutoff_log (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (w v : ℕ → ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ coefficient S (Finset.Icc 1 D) w v n * (Real.log n : ℂ)) s
      (-deriv (diagonal D S w v) s) := by
  have h := hasSum_cutoff_moment D S hS w v 1 hs
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  have hm : signedTaylorMoment 1 (diagonal D S w v) s = -deriv (diagonal D S w v) s := by
    simp [signedTaylorMoment]
  rw [hm] at h
  apply h.congr_fun
  intro n
  rw [LSeries_term_eq_zetaPrimeFeature _ (by simp)]

/-- The original Möbius square is the equal-weight member of this
arithmetic family, with its exact inclusive cutoff. -/
theorem coefficient_moebius_self (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    coefficient S (Finset.Icc 1 D) (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) n =
      RoughSquarefreeBare.coefficient S 1 n * RoughMoebiusIncidence.mask D n ^ 2 := by
  unfold coefficient RoughPrimeIncidence.weight RoughMoebiusIncidence.mask
  ring

/-- The actual ordinary-prime part of the weighted logarithmic
coefficient. Its simplification to a prime tail is proved separately. -/
def primeCorrectionCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if n.Prime then coefficient S (Finset.Icc 1 D)
    (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) n * (Real.log n : ℂ) else 0

/-- The original prime-deleted square coefficient is exactly the
complete coupled logarithmic coefficient minus its ordinary-prime part. -/
theorem squareCoefficient_eq_log_sub_prime (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    RoughMoebiusMixed.squareCoefficient D S n =
      coefficient S (Finset.Icc 1 D) (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) n *
        (Real.log n : ℂ) - primeCorrectionCoefficient D S n := by
  rw [primeCorrectionCoefficient]
  by_cases hp : n.Prime
  · simp [hp, RoughMoebiusMixed.squareCoefficient, zetaRoughSquarefreeCompositeLogWeight]
  · rw [if_neg hp, sub_zero, coefficient_moebius_self]
    by_cases hsf : Squarefree n <;> by_cases hrough : ∃ a ∈ S, a ∣ n <;>
      simp [RoughMoebiusMixed.squareCoefficient, zetaRoughSquarefreeCompositeLogWeight,
        RoughSquarefreeBare.coefficient, hp, hsf, hrough]

/-- Below the original divisor cutoff a prime has zero Möbius mask;
above it the mask is exactly one. No prime phase is altered. -/
theorem mask_on_prime {D p : ℕ} (hD : 1 ≤ D) (hp : p.Prime) :
    RoughMoebiusIncidence.mask D p = if p ≤ D then 0 else 1 := by
  by_cases h : p ≤ D
  · simp [h, RoughMoebiusIncidence.mask_eq_unit hp.pos h, hp.ne_one]
  · rw [if_neg h]
    have he := RoughMoebiusIncidence.mask_large_prime hp (by omega : D < p) 1
    simpa only [mul_one, RoughMoebiusIncidence.mask_eq_unit (by norm_num : 0 < 1) hD,
      if_true] using he

/-- The ordinary-prime correction is precisely the primes beyond
the divisor cutoff, with the original roughness and logarithm retained. -/
theorem primeCorrectionCoefficient_eq_tail {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (n : ℕ) :
    primeCorrectionCoefficient D S n =
      if n.Prime ∧ D < n then RoughSquarefreeBare.coefficient S 1 n * (Real.log n : ℂ) else 0 := by
  by_cases hp : n.Prime
  · rw [primeCorrectionCoefficient, if_pos hp, coefficient_moebius_self, mask_on_prime hD hp]
    by_cases hnD : n ≤ D <;> simp [hp, hnD, Nat.not_lt_of_ge, Nat.lt_of_not_ge]
  · simp [primeCorrectionCoefficient, hp]

/-- The literal convergent ordinary-prime correction, kept separate
from the finite divisor matrix rather than hidden in its norm allowance. -/
def primeCorrection (D : ℕ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  LSeries (primeCorrectionCoefficient D S) s

/-- The ordinary-prime correction has genuine convergence throughout
the Euler half-plane, including the unexceptional zero coefficient. -/
theorem LSeriesHasSum_primeCorrection (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (primeCorrectionCoefficient D S) s (primeCorrection D S s) := by
  have h := (LSeriesHasSum_cutoff_log D S hS (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) hs).summable
  have hi := h.indicator {n : ℕ | n.Prime}
  have hsum : LSeriesSummable (primeCorrectionCoefficient D S) s := by
    apply hi.congr
    intro n
    by_cases hp : n.Prime
    · rw [Set.indicator_of_mem (show n ∈ {k : ℕ | k.Prime} from hp)]
      simp [LSeries.term_of_ne_zero hp.ne_zero, primeCorrectionCoefficient, hp]
    · rw [Set.indicator_of_notMem (show n ∉ {k : ℕ | k.Prime} from hp)]
      simp [LSeries.term, primeCorrectionCoefficient, hp]
  exact hsum.LSeriesHasSum

/-- The literal prime-deleted Möbius-square logarithmic carrier is
the derivative of the full complex divisor diagonalization minus the
original prime tail. All coefficients and all convergence hypotheses
are discharged; this identity supplies no upper bound on the prime tail. -/
theorem LSeriesHasSum_squareCoefficient (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (RoughMoebiusMixed.squareCoefficient D S) s
      (-deriv (diagonal D S (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ))) s -
        primeCorrection D S s) := by
  have h := (LSeriesHasSum_cutoff_log D S hS (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) hs).sub
    (LSeriesHasSum_primeCorrection D S hS hs)
  convert h using 1
  funext n
  exact squareCoefficient_eq_log_sub_prime D S n

end
end RiemannGaussian.SquarefreeEulerQuadratic
