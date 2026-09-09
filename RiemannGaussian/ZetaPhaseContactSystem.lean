/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseChebyshevBounds
import RiemannGaussian.ZetaPhaseContactCertificate

/-!
# The polynomial system for a structural phase optimizer

Four contact cosines and their four masses, together with an efficiency
parameter, give nine unknowns. The nine equations impose equality of the
dual coefficient constraint at the candidate support frequencies. Their
exact secant action retains all cross terms and has an explicit uniform
linearization error bound. These are ingredients for root isolation, not
an assertion that an optimizer already exists.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The nine candidate support frequencies, as an indexed family. -/
def phaseContactFrequency : Fin 9 → ℕ := ![0, 1, 2, 3, 4, 7, 10, 13, 24]

private theorem phaseContactFrequency_le (i : Fin 9) : phaseContactFrequency i ≤ 24 := by
  fin_cases i <;> norm_num [phaseContactFrequency]

/-- The coordinate of a contact cosine in the nine-dimensional system. -/
def phaseContactCosineCoordinate (j : Fin 4) : Fin 9 := ⟨j.val, by omega⟩

/-- The coordinate of a contact mass in the same system. -/
def phaseContactMassCoordinate (j : Fin 4) : Fin 9 := ⟨j.val + 4, by omega⟩

/-- The actual polynomial dual equality at each selected frequency. -/
def phaseContactSystem (u : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  u 8 * phaseContactCost (phaseContactFrequency i) - phaseContactSourceCoeff (phaseContactFrequency i) -
    ∑ j : Fin 4, u (phaseContactMassCoordinate j) *
      phaseChebyshevValue (phaseContactFrequency i) (u (phaseContactCosineCoordinate j))

/-- The exact secant action of the contact system. On the diagonal it
is the linearization used by the root-isolation map. -/
def phaseContactSecantAction (u v h : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  h 8 * phaseContactCost (phaseContactFrequency i) -
    ∑ j : Fin 4,
      (u (phaseContactMassCoordinate j) * phaseChebyshevSecant
        (u (phaseContactCosineCoordinate j)) (v (phaseContactCosineCoordinate j))
          (phaseContactFrequency i) * h (phaseContactCosineCoordinate j) +
        phaseChebyshevValue (phaseContactFrequency i) (v (phaseContactCosineCoordinate j)) *
          h (phaseContactMassCoordinate j))

/-- No remainder is discarded: the difference of the full contact system
is exactly its secant action on the difference of inputs. -/
theorem phaseContactSystem_sub_eq_secant (u v : Fin 9 → ℝ) (i : Fin 9) :
    phaseContactSystem u i - phaseContactSystem v i =
      phaseContactSecantAction u v (u - v) i := by
  have hsum :
      (∑ j : Fin 4, u (phaseContactMassCoordinate j) *
        phaseChebyshevValue (phaseContactFrequency i) (u (phaseContactCosineCoordinate j))) -
      (∑ j : Fin 4, v (phaseContactMassCoordinate j) *
        phaseChebyshevValue (phaseContactFrequency i) (v (phaseContactCosineCoordinate j))) =
      ∑ j : Fin 4,
        (u (phaseContactMassCoordinate j) * phaseChebyshevSecant
          (u (phaseContactCosineCoordinate j)) (v (phaseContactCosineCoordinate j))
            (phaseContactFrequency i) * (u (phaseContactCosineCoordinate j) - v (phaseContactCosineCoordinate j)) +
          phaseChebyshevValue (phaseContactFrequency i) (v (phaseContactCosineCoordinate j)) *
            (u (phaseContactMassCoordinate j) - v (phaseContactMassCoordinate j))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have h := phaseChebyshev_sub_eq_mul_secant (phaseContactFrequency i)
      (u (phaseContactCosineCoordinate j)) (v (phaseContactCosineCoordinate j))
    linear_combination u (phaseContactMassCoordinate j) * h
  unfold phaseContactSystem phaseContactSecantAction
  simp only [Pi.sub_apply]
  linarith

/-- Each row of the secant action stays close to its central linearization
on a cosine box. This controls all cosine--mass cross terms uniformly. -/
theorem abs_phaseContactSecantAction_sub_diagonal_le
    {u v c h : Fin 9 → ℝ} {r H : ℝ} (hr : 0 ≤ r) (hH : 0 ≤ H)
    (hc : ∀ k, |c k| ≤ 1)
    (hu : ∀ j : Fin 4, |u (phaseContactCosineCoordinate j)| ≤ 1)
    (hv : ∀ j : Fin 4, |v (phaseContactCosineCoordinate j)| ≤ 1)
    (huc : ∀ k, |u k - c k| ≤ r) (hvc : ∀ k, |v k - c k| ≤ r)
    (hh : ∀ k, |h k| ≤ H) (i : Fin 9) :
    |phaseContactSecantAction u v h i - phaseContactSecantAction c c h i| ≤
      16 * (6 : ℝ) ^ 24 * r * H := by
  let n := phaseContactFrequency i
  let W := (6 : ℝ) ^ n
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hWcap : W ≤ (6 : ℝ) ^ 24 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 6) (phaseContactFrequency_le i)
  have hterm (j : Fin 4) :
      |(u (phaseContactMassCoordinate j) * phaseChebyshevSecant
        (u (phaseContactCosineCoordinate j)) (v (phaseContactCosineCoordinate j)) n *
          h (phaseContactCosineCoordinate j) +
        phaseChebyshevValue n (v (phaseContactCosineCoordinate j)) * h (phaseContactMassCoordinate j)) -
        (c (phaseContactMassCoordinate j) * phaseChebyshevSecant
          (c (phaseContactCosineCoordinate j)) (c (phaseContactCosineCoordinate j)) n *
            h (phaseContactCosineCoordinate j) +
          phaseChebyshevValue n (c (phaseContactCosineCoordinate j)) * h (phaseContactMassCoordinate j))| ≤
        4 * W * r * H := by
    let q := phaseContactCosineCoordinate j
    let m := phaseContactMassCoordinate j
    have hd := abs_phaseChebyshevSecant_le n (hu j) (hv j)
    have hvard := abs_phaseChebyshevSecant_sub_diagonal_le n (hu j) (hv j) (hc q)
    have hvarT := abs_phaseChebyshevValue_sub_le n (hv j) (hc q)
    change |phaseChebyshevSecant (u q) (v q) n| ≤ W at hd
    change |phaseChebyshevSecant (u q) (v q) n - phaseChebyshevSecant (c q) (c q) n| ≤
      W * (|u q - c q| + |v q - c q|) at hvard
    change |phaseChebyshevValue n (v q) - phaseChebyshevValue n (c q)| ≤ W * |v q - c q| at hvarT
    have hd' : |phaseChebyshevSecant (u q) (v q) n - phaseChebyshevSecant (c q) (c q) n| ≤
        2 * W * r := by nlinarith [mul_le_mul_of_nonneg_left (huc q) hW,
          mul_le_mul_of_nonneg_left (hvc q) hW]
    have hT' : |phaseChebyshevValue n (v q) - phaseChebyshevValue n (c q)| ≤ W * r :=
      hvarT.trans (mul_le_mul_of_nonneg_left (hvc q) hW)
    have ham : |(u m - c m) * phaseChebyshevSecant (u q) (v q) n| ≤ r * W := by
      rw [abs_mul]
      exact mul_le_mul (huc m) hd (abs_nonneg _) hr
    have had : |c m * (phaseChebyshevSecant (u q) (v q) n -
        phaseChebyshevSecant (c q) (c q) n)| ≤ 2 * W * r := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hc m) (abs_nonneg _)).trans (by simpa using hd')
    have hm : |u m * phaseChebyshevSecant (u q) (v q) n -
        c m * phaseChebyshevSecant (c q) (c q) n| ≤ 3 * W * r := by
      have he : u m * phaseChebyshevSecant (u q) (v q) n -
          c m * phaseChebyshevSecant (c q) (c q) n =
          (u m - c m) * phaseChebyshevSecant (u q) (v q) n +
            c m * (phaseChebyshevSecant (u q) (v q) n - phaseChebyshevSecant (c q) (c q) n) := by ring
      rw [he]
      linarith [abs_add_le ((u m - c m) * phaseChebyshevSecant (u q) (v q) n)
        (c m * (phaseChebyshevSecant (u q) (v q) n - phaseChebyshevSecant (c q) (c q) n))]
    have hprod1 := mul_le_mul hm (hh q) (abs_nonneg _) (by positivity : 0 ≤ 3 * W * r)
    have hprod2 := mul_le_mul hT' (hh m) (abs_nonneg _) (mul_nonneg hW hr)
    have he : (u m * phaseChebyshevSecant (u q) (v q) n * h q +
        phaseChebyshevValue n (v q) * h m) -
        (c m * phaseChebyshevSecant (c q) (c q) n * h q + phaseChebyshevValue n (c q) * h m) =
        (u m * phaseChebyshevSecant (u q) (v q) n - c m * phaseChebyshevSecant (c q) (c q) n) * h q +
        (phaseChebyshevValue n (v q) - phaseChebyshevValue n (c q)) * h m := by ring
    change |(u m * phaseChebyshevSecant (u q) (v q) n * h q +
      phaseChebyshevValue n (v q) * h m) -
      (c m * phaseChebyshevSecant (c q) (c q) n * h q + phaseChebyshevValue n (c q) * h m)| ≤ _
    rw [he]
    have htri := abs_add_le
      ((u m * phaseChebyshevSecant (u q) (v q) n - c m * phaseChebyshevSecant (c q) (c q) n) * h q)
      ((phaseChebyshevValue n (v q) - phaseChebyshevValue n (c q)) * h m)
    simp only [abs_mul] at htri
    nlinarith only [htri, hprod1, hprod2]
  unfold phaseContactSecantAction
  rw [sub_sub_sub_cancel_left, abs_sub_comm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin 4, |(u (phaseContactMassCoordinate j) * phaseChebyshevSecant
        (u (phaseContactCosineCoordinate j)) (v (phaseContactCosineCoordinate j)) n *
          h (phaseContactCosineCoordinate j) +
        phaseChebyshevValue n (v (phaseContactCosineCoordinate j)) * h (phaseContactMassCoordinate j)) -
        (c (phaseContactMassCoordinate j) * phaseChebyshevSecant
          (c (phaseContactCosineCoordinate j)) (c (phaseContactCosineCoordinate j)) n *
            h (phaseContactCosineCoordinate j) +
          phaseChebyshevValue n (c (phaseContactCosineCoordinate j)) * h (phaseContactMassCoordinate j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, 4 * W * r * H := Finset.sum_le_sum (fun j _ ↦ hterm j)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hmul := mul_le_mul_of_nonneg_right hWcap (mul_nonneg hr hH)
      calc
        (4 : ℝ) * (4 * W * r * H) = 16 * (W * (r * H)) := by ring
        _ ≤ 16 * ((6 : ℝ) ^ 24 * (r * H)) := mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = _ := by ring

end

end RiemannGaussian
