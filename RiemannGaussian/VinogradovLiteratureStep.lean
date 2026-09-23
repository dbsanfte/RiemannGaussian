/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovUnrestrictedConditioning
import RiemannGaussian.VinogradovDiagonalExponent

/-!
# The mixed-system step in Ford and Bellotti

This follows Ford, Lemma 3.3' (arXiv:1910.08209v1, p. 29), restated as
Bellotti, Lemma 2.2 (arXiv:2306.10680v1). The next polynomial type is put
back into the literal `K` count, retaining every low-degree tail equation.
The physical endpoints, prime dilation and numerical differencing costs
are explicit. The published multi-step iteration is a further obligation.
-/

namespace RiemannGaussian.VinogradovLiteratureStep
noncomputable section
open scoped BigOperators
open Polynomial VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovPolynomialNonsingular VinogradovTypeMaximum VinogradovMixedMoments
open VinogradovMixedDifferencing VinogradovNonsingularDescent
open VinogradovMeanValue VinogradovShiftedMoment

/-- Move the now constant polynomial coordinate into the inactive block;
the coordinate itself and its tail equation are not deleted. -/
def stepEquiv (d m : ℕ) : (Fin d ⊕ Fin (m + 1)) ≃ (Fin (d + 1) ⊕ Fin m) where
  toFun := Sum.elim (fun i => Sum.inl i.castSucc)
    (Fin.cases (Sum.inl (Fin.last d)) Sum.inr)
  invFun := Sum.elim (Fin.lastCases (Sum.inr 0) Sum.inl) (fun j => Sum.inr j.succ)
  left_inv := by
    intro i
    rcases i with i | i
    · simp
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv := by
    intro i
    rcases i with i | i
    · refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    · simp

/-- Reindexing all coordinates of both blocks preserves the actual mixed moment. -/
theorem mixedMoment_reindex {ι κ a b : Type*} [Fintype ι] [Fintype κ]
    [Fintype a] [Fintype b] (r s : ℕ) (v : ι → a → ℤ) (u : κ → a → ℤ) (e : b ≃ a) :
    mixedMoment r s (fun x j => v x (e j)) (fun x j => u x (e j)) = mixedMoment r s v u := by
  classical
  rw [mixedMoment_eq_count, mixedMoment_eq_count]
  congr 1
  unfold differenceCount
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff,
    VinogradovMixedMoments.configurationFrequency, tupleFrequency, Pi.add_apply, Pi.zero_apply,
    Finset.sum_apply]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact h i
  · intro h i
    exact h (e i)

/-- The next active polynomials and the full dilated tail form exactly
the next literal `K` count, with dilation `p*q`. -/
theorem next_moment_eq_count (m d s P Q p q : ℕ) (G : Fin m → ℤ[X]) :
    mixedMoment m s (fun x : Fin P => nextFrequency d G (x.val + 1))
      (monomialTail (m + 1) d p q Q) =
      (typeCount (d + 1) P s G (monomialTail m (d + 1) 1 (p * q) Q) : ℝ) := by
  have hv : (fun x : Fin P => nextFrequency d G (x.val + 1)) =
      fun x i => fullFrequency (d + 1) G (x.val + 1) (stepEquiv d m i) := by
    funext x i
    rcases i with i | i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hu : monomialTail (m + 1) d p q Q =
      fun x i => monomialTail m (d + 1) 1 (p * q) Q x (stepEquiv d m i) := by
    funext x i
    rcases i with i | i
    · simp [monomialTail, stepEquiv]
    · refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [monomialTail, stepEquiv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hv, hu, mixedMoment_reindex, typeCount_eq_mixedMoment]

/-- The integer displacement cutoff pays exactly the reciprocal prime power
appearing in Ford's differencing inequality. -/
theorem displacement_cost_le (P p r m : ℕ) :
    2 * (2 * ((P / p ^ r : ℕ) : ℝ)) ^ m ≤
      (2 * (P : ℝ)) ^ m * (2 / (p : ℝ) ^ (r * m)) := by
  have hdiv : ((P / p ^ r : ℕ) : ℝ) ≤ (P : ℝ) / (p : ℝ) ^ r := by
    simpa only [Nat.cast_pow] using (Nat.cast_div_le (m := P) (n := p ^ r) (α := ℝ))
  calc
    _ ≤ 2 * (2 * ((P : ℝ) / (p : ℝ) ^ r)) ^ m := by gcongr
    _ = _ := by rw [← mul_div_assoc, div_pow, ← pow_mul]; ring

/-- Ford Lemma 3.3', equivalently Bellotti Lemma 2.2, for the actual
integer-endpoint counts. The next type has `T ≤ T' ≤ P*T`; its entire
tail uses dilation `p*q`. The diagonal case is included. -/
theorem exists_difference_step {m d T e : ℕ} (hm : 1 ≤ m)
    {F : Fin (m + 1) → ℤ[X]} (hF : HasType F d T e)
    (s P Q p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hP : 1 ≤ P) :
    ∃ (T' : ℕ) (G : Fin m → ℤ[X]),
      T ≤ T' ∧ T' ≤ P * T ∧ HasType G (d + 1) T' e ∧
      residueMixedMoment (m + 1) s P (p ^ r) (pow_pos hp r)
        (fullFrequency d F) (monomialTail (m + 1) d p q Q) ≤
        (2 * (P : ℝ)) ^ (m + 1) *
          max (((d + (m + 1) : ℕ) : ℝ) ^ (m + 1) * meanValue s (d + (m + 1)) Q)
            ((2 / (p : ℝ) ^ (r * (m + 1))) *
              meanValue s (d + (m + 1)) Q ^ (((m : ℝ) - 1) / (2 * (m : ℝ))) *
              (typeCount (d + 1) P s G (monomialTail m (d + 1) 1 (p * q) Q) : ℝ) ^
                (((m : ℝ) + 1) / (2 * (m : ℝ)))) := by
  have hJ : 0 ≤ meanValue s (d + (m + 1)) Q :=
    MeasureTheory.integral_nonneg (fun _ => by positivity)
  by_cases hfit : p ^ r ≤ P
  · obtain ⟨h, T', G, _hh, _hHP, _heT, hlo, hhi, _heG, htype, hbound⟩ :=
      exists_typed_difference_bound hm hF s P (p ^ r) (pow_pos hp r) hfit
        (monomialTail (m + 1) d p q Q)
    refine ⟨T', G, hlo, hhi, htype, hbound.trans ?_⟩
    rw [monomialTail_moment _ _ _ _ _ _ hp hq, next_moment_eq_count]
    apply max_le
    · calc
        _ = (2 * (P : ℝ)) ^ (m + 1) *
            ((((m + 1 : ℕ) : ℝ)) ^ (m + 1) * meanValue s (d + (m + 1)) Q) := by
          rw [← mul_assoc, ← mul_pow]
          congr 2
          ring
        _ ≤ (2 * (P : ℝ)) ^ (m + 1) *
            (((d + (m + 1) : ℕ) : ℝ) ^ (m + 1) * meanValue s (d + (m + 1)) Q) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hJ
          apply pow_le_pow_left₀ (by positivity)
          exact_mod_cast (show m + 1 ≤ d + (m + 1) by omega)
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    · calc
        _ ≤ ((2 * (P : ℝ)) ^ (m + 1) * (2 / (p : ℝ) ^ (r * (m + 1)))) *
            (typeCount (d + 1) P s G (monomialTail m (d + 1) 1 (p * q) Q) : ℝ) ^
              (((m : ℝ) + 1) / (2 * (m : ℝ))) *
            meanValue s (d + (m + 1)) Q ^ (((m : ℝ) - 1) / (2 * (m : ℝ))) := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hJ _)
          exact mul_le_mul_of_nonneg_right (displacement_cost_le P p r (m + 1))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = (2 * (P : ℝ)) ^ (m + 1) *
            ((2 / (p : ℝ) ^ (r * (m + 1))) *
              meanValue s (d + (m + 1)) Q ^ (((m : ℝ) - 1) / (2 * (m : ℝ))) *
              (typeCount (d + 1) P s G (monomialTail m (d + 1) 1 (p * q) Q) : ℝ) ^
                (((m : ℝ) + 1) / (2 * (m : ℝ)))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  · let G : Fin m → ℤ[X] := fun j => difference (1 : ℤ) (F j.succ)
    have ht : HasType G (d + 1) T e := by
      simpa only [Nat.one_mul, Nat.cast_one] using hasType_difference hF (le_refl 1)
    refine ⟨T, G, le_rfl, ?_, ht, ?_⟩
    · simpa only [one_mul] using Nat.mul_le_mul_right T hP
    rw [residueMixedMoment_eq_diagonal _ _ _ _ _ (by omega), monomialTail_moment _ _ _ _ _ _ hp hq]
    apply le_trans _ (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hJ
    rw [← mul_pow]
    apply pow_le_pow_left₀ (Nat.cast_nonneg P)
    have hk : (1 : ℝ) ≤ ((d + (m + 1) : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d + (m + 1) by omega)
    nlinarith [Nat.cast_nonneg (α := ℝ) P]

/-- All explicit conditioning costs fit inside the coefficient used in
Ford Lemma 3.2' and Bellotti Lemma 2.1. -/
theorem conditioning_cost_le (R d m p r s : ℕ) (hp : 0 < p) :
    (4 * R * d.factorial * p ^ (2 * s - d)) *
        (p ^ ((r - d) * (r - d - 1) / 2) * m.factorial) ≤
      4 * R * (d + m).factorial * p ^ (2 * s + (r - d) * (r - d + 1) / 2) := by
  have hf : d.factorial * m.factorial ≤ (d + m).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add d m)
  have he : 2 * s - d + (r - d) * (r - d - 1) / 2 ≤
      2 * s + (r - d) * (r - d + 1) / 2 := by
    apply Nat.add_le_add (Nat.sub_le _ _)
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
  calc
    _ = (4 * R * (d.factorial * m.factorial)) *
        p ^ (2 * s - d + (r - d) * (r - d - 1) / 2) := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hf) (Nat.pow_le_pow_right hp he)

/-- The full discriminant exponent fits inside the published cubic packet budget. -/
theorem packet_exponent_le_cube {d m : ℕ} (hm : 2 ≤ m) :
    (d + m + 1) * (d + 2 * m.choose 2) ≤ (d + m) ^ 3 := by
  let k := d + m
  have hk : 2 ≤ k := by dsimp only [k]; omega
  have he : d + 2 * m.choose 2 ≤ k * (k - 1) := by
    rw [VinogradovDiagonalExponent.twice_choose_two]
    have hd : d ≤ d * (k - 1) := by
      have h := Nat.mul_le_mul_left d (show 1 ≤ k - 1 by omega)
      simpa only [mul_one] using h
    have hh : m * (m - 1) ≤ m * (k - 1) :=
      Nat.mul_le_mul_left m (by dsimp only [k]; omega)
    have h := Nat.add_le_add hd hh
    dsimp only [k] at *
    nlinarith only [h]
  change (k + 1) * (d + 2 * m.choose 2) ≤ k ^ 3
  have h := Nat.mul_le_mul_left (k + 1) he
  have hk1 : k - 1 + 1 = k := by omega
  have hh := congrArg (fun n : ℕ => n * (k + 1) * k) hk1
  nlinarith only [h, hh]

/-- The paper's `k^3` primes above `M` pay the full type multiplier and
both discriminants when `P ≤ M^(k+1)`. No prime-product hypothesis is
left once the literal packet has been supplied. -/
theorem literature_packet_budget {d m P M : ℕ} (hm : 2 ≤ m) (hM : 0 < M)
    (hroot : P ≤ M ^ (d + m + 1)) (π : Finset ℕ)
    (hcard : π.card = (d + m) ^ 3) (hπ : ∀ p ∈ π, M < p) :
    P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p := by
  let k := d + m
  have hexp : (k + 1) * (d + 2 * m.choose 2) ≤ k ^ 3 := packet_exponent_le_cube hm
  have hne : π.Nonempty := Finset.card_pos.mp (by rw [hcard]; positivity)
  calc
    _ ≤ (M ^ (k + 1)) ^ (d + 2 * m.choose 2) := Nat.pow_le_pow_left hroot _
    _ = M ^ ((k + 1) * (d + 2 * m.choose 2)) := (pow_mul _ _ _).symm
    _ ≤ M ^ (k ^ 3) := Nat.pow_le_pow_right hM hexp
    _ < _ := by
      rw [← hcard, ← Finset.prod_const]
      exact Finset.prod_lt_prod_of_nonempty (fun _ _ => hM) hπ hne

/-- Real prime scales retain the packet budget even at the exact root
endpoint. Rounding the scale down before taking its power is unnecessary. -/
theorem literature_packet_budget_real {d m P : ℕ} {M : ℝ} (hm : 2 ≤ m) (hM : 1 ≤ M)
    (hroot : (P : ℝ) ≤ M ^ (d + m + 1)) (π : Finset ℕ)
    (hcard : π.card = (d + m) ^ 3) (hπ : ∀ p ∈ π, M < (p : ℝ)) :
    P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p := by
  have hk : 0 < d + m := by omega
  have hne : π.Nonempty := Finset.card_pos.mp (by rw [hcard]; positivity)
  have hr : (P : ℝ) ^ (d + 2 * m.choose 2) < ∏ p ∈ π, (p : ℝ) := by
    calc
      _ ≤ (M ^ (d + m + 1)) ^ (d + 2 * m.choose 2) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hroot _
      _ = M ^ ((d + m + 1) * (d + 2 * m.choose 2)) := (pow_mul _ _ _).symm
      _ ≤ M ^ ((d + m) ^ 3) := pow_le_pow_right₀ hM (packet_exponent_le_cube hm)
      _ < _ := by
        rw [← hcard, ← Finset.prod_const]
        exact Finset.prod_lt_prod_of_nonempty (fun _ _ => by linarith) hπ hne
  rw [← Nat.cast_prod] at hr
  exact_mod_cast hr

/-- The full original `K` count reaches the next literal `K` count with
the literature's two-branch coefficient. The supplied prime packet is an
explicit finite arithmetic premise, not an assumed moment estimate. -/
theorem exists_mixed_step_of_packet {m d T e P s M U r Q q : ℕ}
    {F : Fin (m + 1) → ℤ[X]} (hF : HasType F d T e)
    (hm : 1 ≤ m) (hP : 4 * (m + 1) ^ 4 ≤ P) (hMdeg : d + (m + 1) ≤ M)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) (π : Finset ℕ)
    (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ U)
    (hbudget : P ^ (d + 2 * (m + 1).choose 2) < ∏ p ∈ π, p)
    (hr1 : 1 ≤ r) (hr : r ≤ d + (m + 1)) (hds : d ≤ s) (hs : 1 ≤ s)
    (hq : 0 < q) (hQ : 16 * s ^ 2 * U ≤ Q) :
    ∃ (e' p T' : ℕ) (G : Fin m → ℤ[X]),
      p.Prime ∧ M < p ∧ p ≤ U ∧ ¬p ∣ T ∧
      T ≤ T' ∧ T' ≤ P * T ∧ HasType G (d + 1) T' e' ∧
      (typeCount d P s F (monomialTail (m + 1) d 1 q Q) : ℝ) ≤
        ((4 * π.card * (d + (m + 1)).factorial : ℕ) : ℝ) *
          (p : ℝ) ^ (2 * s + (r - d) * (r - d + 1) / 2) *
          (2 * (P : ℝ)) ^ (m + 1) *
          max (((d + (m + 1) : ℕ) : ℝ) ^ (m + 1) * meanValue s (d + (m + 1)) (Q / p))
            ((2 / (p : ℝ) ^ (r * (m + 1))) *
              meanValue s (d + (m + 1)) (Q / p) ^ (((m : ℝ) - 1) / (2 * (m : ℝ))) *
              (typeCount (d + 1) P s G (monomialTail m (d + 1) 1 (p * q) (Q / p)) : ℝ) ^
                (((m : ℝ) + 1) / (2 * (m : ℝ)))) := by
  obtain ⟨e', p, xi, hp, H, hH, hpM, hpU, hpT, _hxi, hcount⟩ :=
    VinogradovUnrestrictedConditioning.exists_conditioning_of_packet hF (by omega) hP hMdeg
      hT0 hT π hπ hbudget hr1 hr hds hs hq hQ
  have hPpos : 1 ≤ P := by
    have hmpos : 0 < 4 * (m + 1) ^ 4 := by positivity
    omega
  obtain ⟨T', G, hlo, hhi, hG, hstep⟩ :=
    exists_difference_step hm hH s P (Q / p) p q r hp.pos hq hPpos
  refine ⟨e', p, T', G, hp, hpM, hpU, hpT, hlo, hhi, hG, ?_⟩
  have hL : 0 ≤ residueMixedMoment (m + 1) s P (p ^ r) (pow_pos hp.pos r)
      (fullFrequency d H) (monomialTail (m + 1) d p q (Q / p)) := by
    apply MeasureTheory.integral_nonneg
    intro theta
    exact mul_nonneg (pow_nonneg (VinogradovDifferenceEnergy.residueEnergy_nonneg _ _ _ _ _) _)
      (pow_nonneg (norm_nonneg _) _)
  have hc := conditioning_cost_le π.card d (m + 1) p r s hp.pos
  have hcr :
      (((4 * π.card * d.factorial * p ^ (2 * s - d)) *
        (p ^ ((r - d) * (r - d - 1) / 2) * (m + 1).factorial) : ℕ) : ℝ) ≤
      ((4 * π.card * (d + (m + 1)).factorial : ℕ) : ℝ) *
        (p : ℝ) ^ (2 * s + (r - d) * (r - d + 1) / 2) := by exact_mod_cast hc
  rw [← Nat.cast_mul] at hcount
  have h := hcount.trans ((mul_le_mul_of_nonneg_right hcr hL).trans
    (mul_le_mul_of_nonneg_left hstep (by positivity)))
  simpa only [mul_assoc] using h

end
end RiemannGaussian.VinogradovLiteratureStep
