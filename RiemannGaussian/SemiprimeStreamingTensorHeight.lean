/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeStreamingTensor

/-!
# Fixed-denominator streaming tensor heights

Exact integer numerator evaluation, its rational polynomial interpretation, and
finite-jet coefficient bounds for local tensors and whole assignment accumulators.
These algebraic bounds do not assert a compiled machine or its workspace bound.
-/

namespace RiemannGaussian.SemiprimeStreamingTensorHeight
open RiemannGaussian.SemiprimeStreamingTensor
open scoped BigOperators

/-- Integer numerator of the actual depth-first evaluator with common denominator d. -/
def numerator (d : ℤ) : (w : ℕ) → ((Fin w → Bool) → ℤ) → (Fin w → ℤ) → ℤ
  | 0, T, _ => T Fin.elim0
  | w + 1, T, x =>
      (d - x 0) * numerator d w (fun a => T (Fin.cons false a)) (fun i => x i.succ) +
      x 0 * numerator d w (fun a => T (Fin.cons true a)) (fun i => x i.succ)

/-- A fixed denominator d^w suffices, independently of the number of leaves. -/
theorem numerator_cast (d : ℤ) (hd : d ≠ 0) (w : ℕ)
    (T : (Fin w → Bool) → ℤ) (x : Fin w → ℤ) :
    (numerator d w T x : ℚ) = (d : ℚ)^w *
      evaluate w (fun a => (T a : ℚ)) (fun i => (x i : ℚ) / d) := by
  induction w with
  | zero => simp [numerator, evaluate]
  | succ w ih =>
    simp only [numerator, Int.cast_add, Int.cast_mul, Int.cast_sub, evaluate, ih, pow_succ]
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    field_simp

/-- Uniform height bound; the two branches contribute no exponential bit-height. -/
theorem abs_numerator_le (d : ℤ) (w : ℕ) (T : (Fin w → Bool) → ℤ)
    (x : Fin w → ℤ) (B : ℤ) (hB : 0 ≤ B)
    (hT : ∀ a, |T a| ≤ 1) (hx : ∀ i, |x i| ≤ B) :
    |numerator d w T x| ≤ (|d| + 2 * B)^w := by
  induction w with
  | zero => simpa [numerator] using hT Fin.elim0
  | succ w ih =>
    have hC : 0 ≤ |d| + 2 * B := by positivity
    have hpow : 0 ≤ (|d| + 2 * B)^w := pow_nonneg hC _
    have hl := ih (fun a => T (Fin.cons false a)) (fun i => x i.succ)
      (fun a => hT _) (fun i => hx i.succ)
    have hr := ih (fun a => T (Fin.cons true a)) (fun i => x i.succ)
      (fun a => hT _) (fun i => hx i.succ)
    calc
      |numerator d (w+1) T x| ≤
          |d-x 0| * |numerator d w (fun a => T (Fin.cons false a)) (fun i => x i.succ)| +
          |x 0| * |numerator d w (fun a => T (Fin.cons true a)) (fun i => x i.succ)| := by
        simpa only [numerator, abs_mul] using abs_add_le
          ((d-x 0)*numerator d w (fun a => T (Fin.cons false a)) (fun i => x i.succ))
          (x 0*numerator d w (fun a => T (Fin.cons true a)) (fun i => x i.succ))
      _ ≤ (|d-x 0| + |x 0|) * (|d|+2*B)^w := by
        calc
          _ ≤ |d-x 0| * (|d|+2*B)^w + |x 0| * (|d|+2*B)^w :=
            add_le_add (mul_le_mul_of_nonneg_left hl (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
          _ = _ := by ring
      _ ≤ (|d|+2*B) * (|d|+2*B)^w := by
        apply mul_le_mul_of_nonneg_right _ hpow
        have hs := abs_sub d (x 0)
        linarith [hx 0]
      _ = (|d|+2*B)^(w+1) := by ring

/-- Products use the fixed denominator indexed by total incidence, not leaf count. -/
theorem product_numerator_cast {E : Type*} [Fintype E]
    (d : ℤ) (hd : d ≠ 0) (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (x : (e : E) → Fin (arity e) → ℤ) :
    ((∏ e, numerator d (arity e) (T e) (x e) : ℤ) : ℚ) =
      (d : ℚ)^(∑ e, arity e) *
        ∏ e, evaluate (arity e) (fun a => (T e a : ℚ)) (fun i => (x e i : ℚ) / d) := by
  classical
  push_cast
  simp_rw [numerator_cast d hd]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- Summing assignments does not multiply their fixed common denominators. -/
theorem sum_product_numerator_cast {E X : Type*} [Fintype E] [Fintype X]
    (d : ℤ) (hd : d ≠ 0) (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (x : X → (e : E) → Fin (arity e) → ℤ) :
    ((∑ a, ∏ e, numerator d (arity e) (T e) (x a e) : ℤ) : ℚ) =
      (d : ℚ)^(∑ e, arity e) *
        ∑ a, ∏ e, evaluate (arity e) (fun b => (T e b : ℚ))
          (fun i => (x a e i : ℚ) / d) := by
  classical
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simpa only [Int.cast_prod] using product_numerator_cast d hd arity T (x a)

/-- Height of a whole assignment sum: enumeration adds a cardinality factor,
not a new denominator for every assignment. -/
theorem abs_sum_product_numerator_le {E X : Type*} [Fintype E] [Fintype X]
    (d B : ℤ) (hB : 0 ≤ B) (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (x : X → (e : E) → Fin (arity e) → ℤ)
    (hT : ∀ e a, |T e a| ≤ 1) (hx : ∀ a e i, |x a e i| ≤ B) :
    |∑ a, ∏ e, numerator d (arity e) (T e) (x a e)| ≤
      (Fintype.card X : ℤ) * (|d|+2*B)^(∑ e, arity e) := by
  classical
  calc
    _ ≤ ∑ a, |∏ e, numerator d (arity e) (T e) (x a e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : X, (|d|+2*B)^(∑ e, arity e) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_le_prod₀
      · intro e he
        exact abs_nonneg _
      · intro e he
        exact abs_numerator_le _ _ _ _ _ hB (hT e) (hx a e)
    _ = _ := by simp

/-- Integer polynomial version, used before truncating to a finite jet. -/
noncomputable def polynomialNumerator (d : ℤ) : (w : ℕ) →
    ((Fin w → Bool) → ℤ) → (Fin w → Polynomial ℤ) → Polynomial ℤ
  | 0, T, _ => Polynomial.C (T Fin.elim0)
  | w+1, T, x =>
      (Polynomial.C d-x 0) * polynomialNumerator d w
        (fun a => T (Fin.cons false a)) (fun i => x i.succ) +
      x 0 * polynomialNumerator d w (fun a => T (Fin.cons true a)) (fun i => x i.succ)

/-- The polynomial numerator specializes to the same integer evaluator. -/
theorem eval_polynomialNumerator (d z : ℤ) (w : ℕ)
    (T : (Fin w → Bool) → ℤ) (x : Fin w → Polynomial ℤ) :
    (polynomialNumerator d w T x).eval z = numerator d w T (fun i => (x i).eval z) := by
  induction w with
  | zero => simp [polynomialNumerator, numerator]
  | succ w ih => simp [polynomialNumerator, numerator, ih]

/-- Exact rational-polynomial numerator identity, before finite-jet truncation. -/
theorem polynomialNumerator_map (d : ℤ) (hd : d ≠ 0) (w : ℕ)
    (T : (Fin w → Bool) → ℤ) (x : Fin w → Polynomial ℤ) :
    (polynomialNumerator d w T x).map (Int.castRingHom ℚ) =
      Polynomial.C ((d : ℚ)^w) * evaluate w
        (fun a => Polynomial.C (T a : ℚ))
        (fun i => Polynomial.C ((d : ℚ)⁻¹) * (x i).map (Int.castRingHom ℚ)) := by
  induction w with
  | zero => simp [polynomialNumerator, evaluate]
  | succ w ih =>
    simp only [polynomialNumerator, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_C, ih, evaluate, pow_succ]
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    have hinv : Polynomial.C (d : ℚ) * Polynomial.C ((d : ℚ)⁻¹) = 1 := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ hdq, Polynomial.C_1]
    rw [Polynomial.C_mul]
    linear_combination
      (Polynomial.C ((d : ℚ)^w) *
        (x 0).map (Int.castRingHom ℚ) *
        evaluate w (fun a => Polynomial.C (T (Fin.cons false a) : ℚ))
          (fun i => Polynomial.C ((d : ℚ)⁻¹) * (x i.succ).map (Int.castRingHom ℚ))) * hinv -
      (Polynomial.C ((d : ℚ)^w) *
        (x 0).map (Int.castRingHom ℚ) *
        evaluate w (fun a => Polynomial.C (T (Fin.cons true a) : ℚ))
          (fun i => Polynomial.C ((d : ℚ)⁻¹) * (x i.succ).map (Int.castRingHom ℚ))) * hinv

/-- Convolution of two finite jets has at most M contributing terms per coefficient. -/
theorem abs_coeff_mul_le (p q : Polynomial ℤ) (M : ℕ) (B C : ℤ)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hp : ∀ k < M, |p.coeff k| ≤ B) (hq : ∀ k < M, |q.coeff k| ≤ C)
    (n : ℕ) (hn : n < M) : |(p*q).coeff n| ≤ (M : ℤ)*B*C := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), |p.coeff k * q.coeff (n-k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (n+1), B*C := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [abs_mul]
      exact mul_le_mul (hp k (by omega)) (hq (n-k) (by omega)) (abs_nonneg _) hB
    _ = ((n+1 : ℕ) : ℤ)*B*C := by simp; ring
    _ ≤ (M : ℤ)*B*C := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast hn

/-- Every retained coefficient has polynomial bit-height: the bound's exponent
is local arity, not the number of Boolean assignments. -/
theorem abs_coeff_polynomialNumerator_le (d : ℤ) (w M : ℕ)
    (T : (Fin w → Bool) → ℤ) (x : Fin w → Polynomial ℤ)
    (B : ℤ) (hB : 0 ≤ B) (hT : ∀ a, |T a| ≤ 1)
    (hx : ∀ i k, k < M → |(x i).coeff k| ≤ B) :
    ∀ k < M, |(polynomialNumerator d w T x).coeff k| ≤
      ((M : ℤ) * (|d|+2*B))^w := by
  induction w with
  | zero =>
    intro k hk
    simp only [polynomialNumerator, pow_zero, Polynomial.coeff_C]
    split_ifs
    · exact hT Fin.elim0
    · simp
  | succ w ih =>
    intro k hk
    have hC : 0 ≤ (M : ℤ) * (|d|+2*B) := by positivity
    have hpow : 0 ≤ ((M : ℤ) * (|d|+2*B))^w := pow_nonneg hC _
    have hl := ih (fun a => T (Fin.cons false a)) (fun i => x i.succ)
      (fun a => hT _) (fun i k hk => hx i.succ k hk)
    have hr := ih (fun a => T (Fin.cons true a)) (fun i => x i.succ)
      (fun a => hT _) (fun i k hk => hx i.succ k hk)
    have hdsub : ∀ j < M, |(Polynomial.C d-x 0).coeff j| ≤ |d|+B := by
      intro j hj
      rw [Polynomial.coeff_sub]
      refine (abs_sub _ _).trans ?_
      have hc : |(Polynomial.C d).coeff j| ≤ |d| := by
        simp only [Polynomial.coeff_C]; split_ifs <;> simp
      linarith [hx 0 j hj]
    have hleft := abs_coeff_mul_le (Polynomial.C d-x 0) _ M (|d|+B) _
      (by positivity) hpow hdsub hl k hk
    have hright := abs_coeff_mul_le (x 0) _ M B _ hB hpow (hx 0) hr k hk
    simp only [polynomialNumerator, Polynomial.coeff_add]
    refine (abs_add_le _ _).trans ((add_le_add hleft hright).trans ?_)
    rw [pow_succ]
    ring_nf
    omega

/-- A finite product of jets, allowing empty products and nonuniform heights. -/
theorem abs_coeff_prod_le {E : Type*} (s : Finset E) (p : E → Polynomial ℤ)
    (M : ℕ) (hM : 1 ≤ M) (C : E → ℤ) (hC : ∀ e, 0 ≤ C e)
    (hp : ∀ e ∈ s, ∀ k < M, |(p e).coeff k| ≤ C e) :
    ∀ k < M, |(∏ e ∈ s, p e).coeff k| ≤ (M : ℤ)^s.card * ∏ e ∈ s, C e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, mul_one, Polynomial.coeff_one]
    split_ifs <;> simp
  | @insert e s he ih =>
    intro k hk
    have hs : ∀ a ∈ s, ∀ j < M, |(p a).coeff j| ≤ C a :=
      fun a ha => hp a (Finset.mem_insert_of_mem ha)
    have ih' := ih hs
    have hcprod : 0 ≤ (M : ℤ)^s.card * ∏ a ∈ s, C a :=
      mul_nonneg (pow_nonneg (by positivity) _) (Finset.prod_nonneg (fun a _ => hC a))
    rw [Finset.prod_insert he, Finset.card_insert_of_notMem he, Finset.prod_insert he]
    have h := abs_coeff_mul_le (p e) (∏ a ∈ s, p a) M (C e)
      ((M : ℤ)^s.card * ∏ a ∈ s, C a) (hC e) hcprod
      (hp e (Finset.mem_insert_self e s)) ih' k hk
    convert h using 1; ring

/-- Every coefficient of the entire polynomial assignment accumulator has a
single total-incidence denominator. -/
theorem sum_product_polynomialNumerator_map {E X : Type*} [Fintype E] [Fintype X]
    (d : ℤ) (hd : d ≠ 0) (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (x : X → (e : E) → Fin (arity e) → Polynomial ℤ) :
    (∑ a, ∏ e, polynomialNumerator d (arity e) (T e) (x a e)).map (Int.castRingHom ℚ) =
      Polynomial.C ((d : ℚ)^(∑ e, arity e)) *
        ∑ a, ∏ e, evaluate (arity e) (fun b => Polynomial.C (T e b : ℚ))
          (fun i => Polynomial.C ((d : ℚ)⁻¹) * (x a e i).map (Int.castRingHom ℚ)) := by
  classical
  simp only [Polynomial.map_sum, Polynomial.map_prod]
  simp_rw [polynomialNumerator_map d hd]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  rw [Finset.mul_sum]

/-- The complete finite-jet accumulator bound, with signed weights of size ≤1. -/
theorem abs_coeff_sum_product_polynomialNumerator_le
    {E X : Type*} [Fintype E] [Fintype X]
    (d B : ℤ) (hB : 0 ≤ B) (M : ℕ) (hM : 1 ≤ M)
    (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (x : X → (e : E) → Fin (arity e) → Polynomial ℤ)
    (weight : X → ℤ) (hw : ∀ a, |weight a| ≤ 1)
    (hT : ∀ e b, |T e b| ≤ 1)
    (hx : ∀ a e i k, k < M → |(x a e i).coeff k| ≤ B)
    (k : ℕ) (hk : k < M) :
    |(∑ a, Polynomial.C (weight a) *
        ∏ e, polynomialNumerator d (arity e) (T e) (x a e)).coeff k| ≤
      (Fintype.card X : ℤ) * (M : ℤ)^(Fintype.card E) *
        ((M : ℤ)*(|d|+2*B))^(∑ e, arity e) := by
  classical
  have hC : 0 ≤ (M : ℤ)*(|d|+2*B) := by positivity
  have hbound (a : X) :
      |(∏ e, polynomialNumerator d (arity e) (T e) (x a e)).coeff k| ≤
        (M : ℤ)^(Fintype.card E) * ((M : ℤ)*(|d|+2*B))^(∑ e, arity e) := by
    have h := abs_coeff_prod_le Finset.univ
      (fun e => polynomialNumerator d (arity e) (T e) (x a e)) M hM
      (fun e => ((M : ℤ)*(|d|+2*B))^(arity e)) (fun e => pow_nonneg hC _)
      (fun e _ => abs_coeff_polynomialNumerator_le d _ _ _ _ _ hB (hT e) (hx a e)) k hk
    simpa only [Finset.card_univ, Finset.prod_pow_eq_pow_sum] using h
  rw [Polynomial.finsetSum_coeff]
  calc
    _ ≤ ∑ a, |(Polynomial.C (weight a) *
        ∏ e, polynomialNumerator d (arity e) (T e) (x a e)).coeff k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : X, (M : ℤ)^(Fintype.card E) *
        ((M : ℤ)*(|d|+2*B))^(∑ e, arity e) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [Polynomial.coeff_C_mul, abs_mul]
      exact (mul_le_mul_of_nonneg_right (hw a) (abs_nonneg _)).trans (by
        simpa only [one_mul] using hbound a)
    _ = _ := by simp; ring

#print axioms abs_coeff_prod_le
#print axioms sum_product_polynomialNumerator_map
#print axioms abs_coeff_sum_product_polynomialNumerator_le
#print axioms polynomialNumerator_map
#print axioms eval_polynomialNumerator
#print axioms abs_coeff_mul_le
#print axioms abs_coeff_polynomialNumerator_le
#print axioms abs_sum_product_numerator_le
#print axioms product_numerator_cast
#print axioms sum_product_numerator_cast
#print axioms numerator_cast
#print axioms abs_numerator_le
end RiemannGaussian.SemiprimeStreamingTensorHeight
