import Mathlib

/-!
# Absolute summability of the fourth-moment arc tail

For the `(1,1)` singular-series class, the absolute mass obtained after
splitting a squarefree Ramanujan frequency `q = d e` is bounded by

`#q.divisors / (Nat.totient q)^2`.

This file proves that majorant summable.  Consequently the frequency cutoff
can be sent to infinity after the height limit; a fixed floating-point tail
budget is not needed.
-/

namespace RiemannGaussian

noncomputable section

open Filter Finset
open scoped BigOperators Topology

/-- Absolute mass of all divisor splittings of a squarefree arc frequency. -/
def fourthMomentArcMass (q : ℕ) : ℝ :=
  if Squarefree q then
    (#q.divisors : ℝ) * ((q.totient : ℝ)⁻¹) ^ 2
  else 0

/-- Absolute squarefree Ramanujan coefficient at frequency `q`. -/
def fourthMomentArcBeta (q : ℕ) : ℝ :=
  if Squarefree q then ((q.totient : ℝ)⁻¹) ^ 2 else 0

/-- The absolute mass before summing over the divisor split `q = d e`. -/
def fourthMomentArcSplitMass (q : ℕ) : ℝ :=
  ∑ e ∈ q.divisors,
    ((|ArithmeticFunction.moebius e| : ℤ) : ℝ) * fourthMomentArcBeta q

lemma fourthMomentArcMass_nonneg (q : ℕ) : 0 ≤ fourthMomentArcMass q := by
  simp only [fourthMomentArcMass]
  split_ifs
  · positivity
  · exact le_rfl

lemma fourthMomentArcMass_zero : fourthMomentArcMass 0 = 0 := by
  simp [fourthMomentArcMass]

lemma fourthMomentArcMass_one : fourthMomentArcMass 1 = 1 := by
  simp [fourthMomentArcMass]

lemma fourthMomentArcMass_eq_zero_of_not_squarefree {q : ℕ}
    (hq : ¬ Squarefree q) : fourthMomentArcMass q = 0 := by
  simp [fourthMomentArcMass, hq]

/-- Regrouping the two arc indices by their product costs exactly the divisor
factor already present in `fourthMomentArcMass`. -/
lemma fourthMomentArcSplitMass_eq_mass (q : ℕ) :
    fourthMomentArcSplitMass q = fourthMomentArcMass q := by
  by_cases hq : Squarefree q
  · calc
      fourthMomentArcSplitMass q =
          ∑ _e ∈ q.divisors, fourthMomentArcBeta q := by
        apply Finset.sum_congr rfl
        intro e he
        have hedvd : e ∣ q := (Nat.mem_divisors.mp he).1
        have hesq : Squarefree e := hq.squarefree_of_dvd hedvd
        rw [ArithmeticFunction.abs_moebius, if_pos hesq]
        norm_num
      _ = (#q.divisors : ℝ) * fourthMomentArcBeta q := by simp
      _ = fourthMomentArcMass q := by
        simp [fourthMomentArcMass, fourthMomentArcBeta, hq]
  · simp [fourthMomentArcSplitMass, fourthMomentArcBeta,
      fourthMomentArcMass, hq]

lemma fourthMomentArcMass_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    fourthMomentArcMass (m * n) =
      fourthMomentArcMass m * fourthMomentArcMass n := by
  simp only [fourthMomentArcMass, Nat.squarefree_mul hmn]
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n
  · simp only [hm, hn, and_self, ↓reduceIte]
    rw [hmn.card_divisors_mul, Nat.totient_mul hmn]
    push_cast
    rw [mul_inv_rev, mul_pow]
    ring
  · simp [hm, hn]
  · simp [hm, hn]
  · simp [hm, hn]

private lemma summable_one_div_prime_sq :
    Summable (fun p : Nat.Primes =>
      1 / ((p : ℕ) : ℝ) ^ (2 : ℝ)) :=
  ((Nat.Primes.summable_rpow (r := -(2 : ℝ))).mpr (by norm_num)).congr fun p => by
    rw [Real.rpow_neg (by positivity), one_div]

lemma fourthMomentArcMass_prime_le (p : Nat.Primes) :
    fourthMomentArcMass (p : ℕ) ≤
      8 * (1 / ((p : ℕ) : ℝ) ^ (2 : ℝ)) := by
  have hp : (p : ℕ).Prime := p.2
  have hp2N : 2 ≤ (p : ℕ) := hp.two_le
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  have hp2R : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp2N
  have hpredR : (0 : ℝ) < ((p : ℕ) : ℝ) - 1 := by linarith
  have hsq : ((p : ℕ) : ℝ) ^ 2 ≤ 4 * (((p : ℕ) : ℝ) - 1) ^ 2 := by
    nlinarith [mul_nonneg hpR.le (sub_nonneg.mpr hp2R),
      sq_nonneg (((p : ℕ) : ℝ) - 2)]
  rw [fourthMomentArcMass, if_pos hp.squarefree, hp.divisors,
    Finset.card_pair hp.ne_one.symm, Nat.cast_ofNat, Nat.totient_prime hp]
  rw [Nat.cast_sub (by omega : 1 ≤ (p : ℕ)), Real.rpow_two]
  simp only [inv_eq_one_div, one_div_pow, mul_one_div, Nat.cast_one]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpredR) (sq_pos_of_pos hpR)).2
  nlinarith

/-! The following finite-Euler domination argument is adapted from the
Apache-2.0 `AxiomMath/PrimeGapsLib` proof of
`summable_norm_of_summable_primes`. -/

private theorem summable_of_squarefree_multiplicative_prime_sum
    {w : ℕ → ℝ} (hw_nonneg : ∀ q, 0 ≤ w q)
    (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hsupp : ∀ q, ¬ Squarefree q → w q = 0)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → w (m * n) = w m * w n)
    (hsumPrime : Summable (fun p : Nat.Primes => w (p : ℕ))) :
    Summable w := by
  classical
  have hge1 : ∀ p : Nat.Primes, (1 : ℝ) ≤ 1 + |w (p : ℕ)| :=
    fun _ => le_add_of_nonneg_right (abs_nonneg _)
  have hmult : Multipliable (fun p : Nat.Primes => 1 + |w (p : ℕ)|) :=
    Real.multipliable_one_add_of_summable
      (by simpa only [abs_of_nonneg (hw_nonneg _)] using hsumPrime)
  refine summable_of_sum_range_le
    (c := ∏' p : Nat.Primes, (1 + |w (p : ℕ)|))
    hw_nonneg fun N => ?_
  set primes : Finset ℕ :=
    (Finset.range N).biUnion (fun q => q.primeFactors) with hprimesDef
  have hprimes : ∀ p ∈ primes, p.Prime := by
    intro p hp
    rw [hprimesDef, Finset.mem_biUnion] at hp
    obtain ⟨q, _, hpq⟩ := hp
    exact Nat.prime_of_mem_primeFactors hpq
  set M : ℕ := ∏ p ∈ primes, p with hMdef
  have hMpf : M.primeFactors = primes := Nat.primeFactors_prod hprimes
  have hMsq : Squarefree M :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hprimes p hp) (hprimes q hq)).mpr hpq))
      (fun p hp => (hprimes p hp).squarefree)
  calc
    ∑ q ∈ Finset.range N, w q =
        ∑ q ∈ (Finset.range N).filter Squarefree, w q :=
      (Finset.sum_filter_of_ne fun q _ hne => by
        by_contra hns
        exact hne (by rw [hsupp q hns])).symm
    _ ≤ ∑ d ∈ M.divisors, w d := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_)
        (fun d _ _ => hw_nonneg d)
      rw [Finset.mem_filter] at hq
      rw [Nat.mem_divisors]
      refine ⟨?_, hMsq.ne_zero⟩
      calc
        q = ∏ p ∈ q.primeFactors, p :=
          (Nat.prod_primeFactors_of_squarefree hq.2).symm
        _ ∣ ∏ p ∈ M.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset _ _ _ (by
            rw [hMpf, hprimesDef]
            exact fun p hp => Finset.mem_biUnion.mpr ⟨q, hq.1, hp⟩)
        _ = M := Nat.prod_primeFactors_of_squarefree hMsq
    _ = ∏ p ∈ primes, (1 + |w p|) := by
      let W : ArithmeticFunction ℝ := ⟨fun q => |w q|, by simp [hw0]⟩
      have hWval : ∀ q, W q = |w q| := fun _ => rfl
      have hWmul : W.IsMultiplicative := by
        rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
        refine ⟨by rw [hWval, hw1]; norm_num, ?_⟩
        intro m n _ _ hco
        rw [hWval, hWval, hWval, hmul hco, abs_mul]
      have hprod := hWmul.prodPrimeFactors_one_add_of_squarefree hMsq
      rw [hMpf] at hprod
      simp only [hWval] at hprod
      calc
        ∑ d ∈ M.divisors, w d = ∑ d ∈ M.divisors, |w d| := by
          apply Finset.sum_congr rfl
          intro d _
          rw [abs_of_nonneg (hw_nonneg d)]
        _ = ∏ p ∈ primes, (1 + |w p|) := hprod.symm
    _ ≤ ∏' p : Nat.Primes, (1 + |w (p : ℕ)|) := by
      have hsubtype :
          ∏ p ∈ primes.subtype (fun p : ℕ => p.Prime),
              (1 + |w (p : ℕ)|) =
            ∏ p ∈ primes, (1 + |w p|) := by
        rw [Finset.prod_subtype_eq_prod_filter
          (fun q : ℕ => 1 + |w q|) (s := primes)
          (p := fun q : ℕ => q.Prime),
          Finset.filter_true_of_mem hprimes]
      rw [← hsubtype]
      exact ge_of_tendsto hmult.hasProd (Filter.eventually_atTop.mpr
        ⟨primes.subtype (fun p : ℕ => p.Prime), fun s hs =>
          Finset.prod_le_prod_of_subset_of_one_le hs
            (fun i _ => by linarith [hge1 i])
            (fun i _ _ => hge1 i)⟩)

/-- The divisor-splitting majorant for the complete arc expansion is
absolutely summable. -/
theorem fourthMomentArcMass_summable : Summable fourthMomentArcMass := by
  apply summable_of_squarefree_multiplicative_prime_sum
    fourthMomentArcMass_nonneg fourthMomentArcMass_zero
    fourthMomentArcMass_one
    (fun q hq => fourthMomentArcMass_eq_zero_of_not_squarefree hq)
    (@fourthMomentArcMass_mul_of_coprime)
  exact Summable.of_nonneg_of_le
    (fun p => fourthMomentArcMass_nonneg (p : ℕ))
    fourthMomentArcMass_prime_le
    (summable_one_div_prime_sq.mul_left 8)

/-- Absolute arc mass outside a finite frequency set. -/
def fourthMomentArcTail (s : Finset ℕ) : ℝ :=
  ∑' q : {q : ℕ // q ∉ s}, fourthMomentArcMass q

/-- The complete frequency tail tends to zero as the finite cutoff exhausts
the natural numbers. -/
theorem fourthMomentArcTail_tendsto_zero :
    Tendsto fourthMomentArcTail atTop (𝓝 0) := by
  exact tendsto_tsum_compl_atTop_zero fourthMomentArcMass

/-- Range-cutoff form used by the fourth-moment argument. -/
theorem fourthMomentArcTail_range_tendsto_zero :
    Tendsto (fun P => fourthMomentArcTail (Finset.range P)) atTop (𝓝 0) :=
  fourthMomentArcTail_tendsto_zero.comp Filter.tendsto_finset_range

end

end RiemannGaussian
