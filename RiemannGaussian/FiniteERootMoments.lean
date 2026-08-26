import RiemannGaussian.FiniteERootContinuity
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Collision-safe root moments for the finite homotopy

Individual root labels are not continuous through a multiple-root collision.
Symmetric functions of the full root multiset are.  This file derives
Newton's identities for a complex multiset, rewrites the elementary symmetric
functions of the roots as coefficients of the monic homotopy, and proves
continuity of every root power sum up to the degree.  Polynomial test sums over
all roots, with multiplicity, are then continuous as well.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

private theorem list_powerSum_newton (l : List ℂ) (k : ℕ) (hk : 0 < k) :
    ∑ i : Fin l.length, l.get i ^ k =
      (-1 : ℂ) ^ (k + 1) * k * (l : Multiset ℂ).esymm k -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (-1 : ℂ) ^ a.fst * (l : Multiset ℂ).esymm a.1 *
            ∑ i : Fin l.length, l.get i ^ a.2 := by
  let v : Fin l.length → ℂ := l.get
  have h := congrArg (MvPolynomial.aeval v)
    (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin l.length) ℂ k hk)
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm,
    MvPolynomial.psum, MvPolynomial.aeval_sum, MvPolynomial.aeval_X] at h
  have hv : Finset.univ.val.map v = (l : Multiset ℂ) := by
    ext z
    simp [v, List.count_eq_countP]
  simpa [v, hv] using h

/-- Newton's power-sum recurrence for a complex multiset. -/
theorem multiset_powerSum_newton (s : Multiset ℂ) (k : ℕ) (hk : 0 < k) :
    (s.map fun z ↦ z ^ k).sum =
      (-1 : ℂ) ^ (k + 1) * k * s.esymm k -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (-1 : ℂ) ^ a.fst * s.esymm a.1 *
            (s.map fun z ↦ z ^ a.2).sum := by
  have hsum (j : ℕ) :
      ∑ i : Fin s.toList.length, s.toList.get i ^ j =
        (s.map fun z ↦ z ^ j).sum := by
    simpa only [List.get_eq_getElem, Fin.sum_univ_fun_getElem,
      Multiset.sum_map_toList] using
        (Fin.sum_univ_fun_getElem s.toList fun z : ℂ ↦ z ^ j)
  have h := list_powerSum_newton s.toList k hk
  simp_rw [hsum] at h
  simpa using h

/-- The `k`th power sum of all roots of `E_tau`, counted with multiplicity. -/
def finiteERootPowerSum (A : ℝ[X]) (tau : ℝ) (k : ℕ) : ℂ :=
  ((finiteEPolynomial A tau).roots.map fun z ↦ z ^ k).sum

/-- Vieta's formula for the monic normalization of the finite homotopy. -/
theorem finiteEPolynomial_roots_esymm
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) {j : ℕ}
    (hj : j ≤ A.natDegree) :
    (finiteEPolynomial A tau).roots.esymm j =
      (-1 : ℂ) ^ j *
        (finiteEMonicPolynomial A tau).coeff (A.natDegree - j) := by
  rw [← finiteEMonicPolynomial_roots hA]
  have hp := finiteEMonicPolynomial_monic hA tau
  have h := Polynomial.coeff_eq_esymm_roots_of_splits
    (IsAlgClosed.splits (finiteEMonicPolynomial A tau))
    (k := A.natDegree - j) (by
      rw [finiteEMonicPolynomial_natDegree hA]
      exact Nat.sub_le _ _)
  rw [hp.leadingCoeff, one_mul, finiteEMonicPolynomial_natDegree hA,
    Nat.sub_sub_self hj] at h
  rw [h, ← mul_assoc, ← pow_add]
  simp

/-- Every root power sum up to the fixed degree depends continuously on the
homotopy parameter.  Multiplicities are retained, so the statement remains
valid at collisions. -/
theorem continuous_finiteERootPowerSum
    {A : ℝ[X]} (hA : A ≠ 0) {k : ℕ}
    (hk : k ≤ A.natDegree) :
    Continuous fun tau : ℝ ↦ finiteERootPowerSum A tau k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hkzero : k = 0
      · subst k
        have heq : (fun tau : ℝ ↦ finiteERootPowerSum A tau 0) =
            fun _ ↦ (A.natDegree : ℂ) := by
          funext tau
          simp [finiteERootPowerSum,
            IsAlgClosed.card_roots_eq_natDegree,
            finiteEPolynomial_natDegree hA]
        rw [heq]
        fun_prop
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
        have hformula : (fun tau : ℝ ↦ finiteERootPowerSum A tau k) =
            fun tau ↦
              (-1 : ℂ) ^ (k + 1) * k *
                  (finiteEPolynomial A tau).roots.esymm k -
                ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
                  (-1 : ℂ) ^ a.fst *
                    (finiteEPolynomial A tau).roots.esymm a.1 *
                      finiteERootPowerSum A tau a.2 := by
          funext tau
          exact multiset_powerSum_newton
            (finiteEPolynomial A tau).roots k hkpos
        rw [hformula]
        apply Continuous.sub
        · have hesymm : Continuous fun tau : ℝ ↦
              (finiteEPolynomial A tau).roots.esymm k := by
            have heq : (fun tau : ℝ ↦
                (finiteEPolynomial A tau).roots.esymm k) =
                fun tau ↦ (-1 : ℂ) ^ k *
                  (finiteEMonicPolynomial A tau).coeff
                    (A.natDegree - k) := by
              funext tau
              exact finiteEPolynomial_roots_esymm hA tau hk
            rw [heq]
            exact continuous_const.mul
              (continuous_finiteEMonicPolynomial_coeff A _)
          exact (continuous_const.mul continuous_const).mul hesymm
        · apply continuous_finsetSum
          intro a ha
          have haIoo : a.1 ∈ Set.Ioo 0 k := (Finset.mem_filter.mp ha).2
          have haone : a.1 ≤ A.natDegree :=
            (Nat.le_of_lt haIoo.2).trans hk
          have hesymm : Continuous fun tau : ℝ ↦
              (finiteEPolynomial A tau).roots.esymm a.1 := by
            have heq : (fun tau : ℝ ↦
                (finiteEPolynomial A tau).roots.esymm a.1) =
                fun tau ↦ (-1 : ℂ) ^ a.1 *
                  (finiteEMonicPolynomial A tau).coeff
                    (A.natDegree - a.1) := by
              funext tau
              exact finiteEPolynomial_roots_esymm hA tau haone
            rw [heq]
            exact continuous_const.mul
              (continuous_finiteEMonicPolynomial_coeff A _)
          have haa : a.1 + a.2 = k :=
            Finset.mem_antidiagonal.mp (Finset.mem_filter.mp ha).1
          have haonepos : 0 < a.1 := haIoo.1
          have hatwo : a.2 < k := by omega
          exact (continuous_const.mul hesymm).mul
            (ih a.2 hatwo ((Nat.le_of_lt hatwo).trans hk))

/-- Summing a polynomial test function over a multiset is the corresponding
finite linear combination of its power sums. -/
theorem multiset_sum_eval_eq_sum_powerSum
    (s : Multiset ℂ) (q : ℂ[X]) :
    (s.map q.eval).sum =
      ∑ k ∈ q.support, q.coeff k * (s.map fun z ↦ z ^ k).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, q.eval_eq_sum,
        Polynomial.sum_def]
      simp_rw [Multiset.map_cons, Multiset.sum_cons, mul_add]
      rw [Finset.sum_add_distrib]

/-- The sum of a fixed polynomial test function over all roots of `E_tau`,
with multiplicity. -/
def finiteERootEvalSum (A : ℝ[X]) (tau : ℝ) (q : ℂ[X]) : ℂ :=
  ((finiteEPolynomial A tau).roots.map q.eval).sum

/-- Every polynomial test sum of degree at most `deg A` is continuous along
the finite homotopy, including at multiple-root collisions. -/
theorem continuous_finiteERootEvalSum
    {A : ℝ[X]} (hA : A ≠ 0) (q : ℂ[X])
    (hq : q.natDegree ≤ A.natDegree) :
    Continuous fun tau : ℝ ↦ finiteERootEvalSum A tau q := by
  have heq : (fun tau : ℝ ↦ finiteERootEvalSum A tau q) =
      fun tau ↦ ∑ k ∈ q.support,
        q.coeff k * finiteERootPowerSum A tau k := by
    funext tau
    exact multiset_sum_eval_eq_sum_powerSum
      (finiteEPolynomial A tau).roots q
  rw [heq]
  apply continuous_finsetSum
  intro k hk
  have hkdegree : k ≤ A.natDegree :=
    (Polynomial.le_natDegree_of_mem_supp k hk).trans hq
  exact continuous_const.mul (continuous_finiteERootPowerSum hA hkdegree)

end

end RiemannGaussian
