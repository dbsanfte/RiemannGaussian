/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordStep

/-!
# Uniform power bounds from Ford's original mixed scales

This finite backward induction applies the original Ford 3.4 / Bellotti
2.4 scale recurrence to the literal shrinking-tuple counts. Every
physical-endpoint power is paid by the proved nonpositive scale balance.
The remaining coefficient is an explicit finite recursion, independent
of the physical endpoints; the minimum tail size is also explicit.
Short prime packets and their size conditions remain arithmetic inputs.
-/

namespace RiemannGaussian.VinogradovFordIteration
noncomputable section
open scoped BigOperators
open Polynomial VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovPolynomialNonsingular VinogradovTypeMaximum VinogradovMixedDifferencing
open VinogradovNonsingularDescent VinogradovMeanValue VinogradovLiteratureIteration
open VinogradovFordScales VinogradovPowerConditioning VinogradovFordStep

/-- The entire remaining coefficient, with packet cardinality k cubed.
It depends on neither physical endpoint. -/
def coefficient (k b s r : ℕ) (delta eta : ℝ) : ℕ → ℕ → ℝ
  | _d, 0 => 1
  | d, n + 1 => 2 ^ (b + n + 1) *
      max ((k : ℝ) ^ (b + n + 1))
        (2 * (((4 * k ^ 3 * (d + 1).factorial * (b + n).factorial : ℕ) : ℝ) *
          coefficient k b s r delta eta (d + 1) n * eta ^ primeGap k (d + 1) r s delta) ^
            ((((b + n : ℕ) : ℝ) + 1) / (2 * ((b + n : ℕ) : ℝ))))

/-- All literal quotient endpoints stay large enough through the
remaining induction when they exceed this finite natural threshold. -/
def minimumTail (s : ℕ) (U : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _d, 0 => 1
  | d, n + 1 => max 1 (max (16 * s ^ 2) (minimumTail s U (d + 1) n) * U (d + 1))

/-- Every stage retains a positive tail endpoint. -/
theorem minimumTail_pos (s : ℕ) (U : ℕ → ℕ) (d n : ℕ) : 1 ≤ minimumTail s U d n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

/-- The recursive threshold pays both conditioning and the next quotient. -/
theorem minimumTail_step (s : ℕ) (U : ℕ → ℕ) (d n : ℕ) :
    16 * s ^ 2 * U (d + 1) ≤ minimumTail s U d (n + 1) ∧
      minimumTail s U (d + 1) n * U (d + 1) ≤ minimumTail s U d (n + 1) := by
  constructor
  · exact (Nat.mul_le_mul_right _ (le_max_left _ _)).trans (le_max_right _ _)
  · exact (Nat.mul_le_mul_right _ (le_max_right _ _)).trans (le_max_right _ _)

/-- Every coefficient is nonnegative, including a possible empty tuple order. -/
theorem coefficient_nonneg (k b s r : ℕ) (delta eta : ℝ) (d n : ℕ) :
    0 ≤ coefficient k b s r delta eta d n := by
  cases n with
  | zero => norm_num [coefficient]
  | succ n =>
    rw [coefficient]
    exact mul_nonneg (by positivity) (le_max_of_le_left (by positivity))

/-- The exact original Ford recurrence pays every power of P throughout
the actual mixed-count induction. Only the explicit coefficient remains. -/
theorem residue_power_bound (k b P s r : ℕ) (M U : ℕ → ℕ) (π : ℕ → Finset ℕ)
    (phi : ℕ → ℝ) {C delta eta : ℝ}
    (hb : 2 ≤ b) (hP : 4 * k ^ 4 ≤ P) (hs : k ≤ s)
    (hr1 : 1 ≤ r) (hr : r ≤ k) (hstop : k - b ≤ r)
    (hC : 0 < C) (heta : 0 < eta)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hlambda : 0 ≤ sourceExponent k s delta)
    (hMdeg : ∀ d ≤ k, k ≤ M d)
    (hπ : ∀ d ≤ k, ∀ p ∈ π d, p.Prime ∧ M d < p ∧ p ≤ U d)
    (hcard : ∀ d ≤ k, (π d).card = k ^ 3)
    (hbudget : ∀ d ≤ k, P ^ (d + 2 * (k - d).choose 2) < ∏ p ∈ π d, p)
    (hprime : ∀ d ≤ k, (P : ℝ) ^ phi d ≤ ((M d + 1 : ℕ) : ℝ))
    (hpacket : ∀ d ≤ k, (U d : ℝ) ≤ eta * (P : ℝ) ^ phi d)
    (hphi : ∀ d ≤ k, 0 ≤ phi d)
    (hrec : ∀ d < k - b, phi d = previousScale k (d + 1) r delta (phi (d + 1)))
    (hdepth : ∀ d, 1 ≤ d → d ≤ k - b → (d : ℝ) * ((d : ℝ) - 1) ≤
      2 * delta - ((k : ℝ) - r) * ((k : ℝ) - r + 1))
    (hdiag : ∀ d, d + b = k → P < (M d + 1) ^ r)
    (hsource : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤ C * (X : ℝ) ^ sourceExponent k s delta)
    (n d : ℕ) (hk : d + (b + n) = k)
    (T e p q Q : ℕ) (hp : p.Prime) (hpM : M d < p) (hq : 0 < q)
    (hQ : minimumTail s U d n ≤ Q)
    (F : Fin (b + n) → ℤ[X]) (hF : HasType F d T e)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) :
    residueMixedMoment (b + n) s P (p ^ r) (pow_pos hp.pos r)
      (fullFrequency d F) (monomialTail (b + n) d p q Q) ≤
        C * coefficient k b s r delta eta d n * (P : ℝ) ^ (b + n) *
          (Q : ℝ) ^ sourceExponent k s delta := by
  induction n generalizing d T e p q Q with
  | zero =>
    have hdiag' : P < p ^ r :=
      (hdiag d (by simpa using hk)).trans_le (Nat.pow_le_pow_left hpM r)
    rw [residueMixedMoment_eq_diagonal _ _ _ _ _ hdiag',
      monomialTail_moment _ _ _ _ _ _ hp.pos hq, hk]
    have hj := mul_le_mul_of_nonneg_left
      (hsource Q ((minimumTail_pos s U d 0).trans hQ)) (show 0 ≤ (P : ℝ) ^ (b + 0) by positivity)
    simpa only [coefficient, mul_one, mul_assoc, mul_left_comm] using hj
  | succ n ih =>
    have hm : 2 ≤ b + n := by omega
    have hd : d < k - b := by omega
    have hdk : d + 1 < k := by omega
    have hPm : 4 * (b + n) ^ 4 ≤ P :=
      (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by omega : b + n ≤ k) 4)).trans hP
    have hM : d + 1 + (b + n) ≤ M (d + 1) := by
      have h := hMdeg (d + 1) hdk.le
      omega
    have hbgt : P ^ (d + 1 + 2 * (b + n).choose 2) < ∏ p ∈ π (d + 1), p := by
      have he : k - (d + 1) = b + n := by omega
      simpa only [he] using hbudget (d + 1) hdk.le
    have hg : 0 ≤ primeGap k (d + 1) r s delta := by
      have h : ((d + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hdk.le
      exact (sub_nonneg.mpr h).trans (primeGap_ge (by omega : d + 1 ≤ 2 * s) hdelta)
    have hkm : (k : ℝ) - (d + 1) = ((b + n : ℕ) : ℝ) := by
      have he : k = d + 1 + (b + n) := by omega
      rw [he]
      push_cast
      ring
    have hbal := scale_balance_nonpos (k := k) (d := d + 1) (r := r) (s := s)
      (by omega) (by omega) hdk (by omega) (hphi (d + 1) hdk.le)
      (hdepth (d + 1) (by omega) (by omega))
    rw [← hrec d hd] at hbal
    simp only [Nat.cast_add, Nat.cast_one] at hbal
    rw [hkm] at hbal
    have hdeg : d + (b + n + 1) = k := by omega
    have hpr : (P : ℝ) ^ phi d ≤ p :=
      (hprime d (by omega)).trans (by exact_mod_cast hpM)
    have hstep := backward_power_step (m := b + n) (d := d) hF hm hPm hM hT0 hT
      (π (d + 1)) (hπ (d + 1) hdk.le) hbgt hr1 (by omega) (by omega) (by omega)
      hp.pos hq ((minimumTail_pos s U d (n + 1)).trans hQ)
      ((minimumTail_step s U d n).1.trans hQ) ((minimumTail_step s U d n).2.trans hQ)
      hC (coefficient_nonneg k b s r delta eta (d + 1) n) hlambda heta
      (sub_nonneg.mp hg) hpr (hpacket (d + 1) hdk.le) hbal
      (by simpa only [hdeg] using hsource Q ((minimumTail_pos s U d (n + 1)).trans hQ))
      (fun T' e' p' q' X hp' G hT'0 hT' hG hp'M _hp'U hq' hX =>
        ih (d + 1) (by omega) T' e' p' q' X hp' hp'M hq' hX G hG hT'0 hT')
    apply hstep.trans
    simp only [coefficient, hk, hcard (d + 1) hdk.le, primeGap, Nat.add_assoc]
    exact le_rfl

/-- The original homogeneous moment inherits Ford's published updated
defect. Its explicit coefficient depends on the degree, iteration depth,
defect and packet width, but not on the physical endpoint. Actual prime
packets and the finite minimum-size conditions remain visible inputs. -/
theorem moment_power_bound (k b P s r : ℕ) (M U : ℕ → ℕ) (π : ℕ → Finset ℕ)
    (phi : ℕ → ℝ) {C delta eta : ℝ}
    (hb : 2 ≤ b) (hP : 4 * k ^ 4 ≤ P) (hs : k ≤ s)
    (hr1 : 1 ≤ r) (hr : r ≤ k) (hstop : k - b ≤ r)
    (hC : 0 < C) (heta : 0 < eta)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hlambda : 0 ≤ sourceExponent k s delta)
    (hMdeg : ∀ d ≤ k, k ≤ M d)
    (hπ : ∀ d ≤ k, ∀ p ∈ π d, p.Prime ∧ M d < p ∧ p ≤ U d)
    (hcard : ∀ d ≤ k, (π d).card = k ^ 3)
    (hbudget : ∀ d ≤ k, P ^ (d + 2 * (k - d).choose 2) < ∏ p ∈ π d, p)
    (hprime : ∀ d ≤ k, (P : ℝ) ^ phi d ≤ ((M d + 1 : ℕ) : ℝ))
    (hpacket : ∀ d ≤ k, (U d : ℝ) ≤ eta * (P : ℝ) ^ phi d)
    (hphi : ∀ d ≤ k, 0 ≤ phi d)
    (hrec : ∀ d < k - b, phi d = previousScale k (d + 1) r delta (phi (d + 1)))
    (hdepth : ∀ d, 1 ≤ d → d ≤ k - b → (d : ℝ) * ((d : ℝ) - 1) ≤
      2 * delta - ((k : ℝ) - r) * ((k : ℝ) - r + 1))
    (hdiag : ∀ d, d + b = k → P < (M d + 1) ^ r)
    (hsource : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤ C * (X : ℝ) ^ sourceExponent k s delta)
    (n : ℕ) (hk : b + n = k)
    (hfirst : 16 * s ^ 2 * U 0 ≤ P)
    (hfirstMin : minimumTail s U 0 n * U 0 ≤ P) :
    meanValue (s + k) k P ≤
      C * (((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
        coefficient k b s r delta eta 0 n * eta ^ primeGap k 0 r s delta) *
          (P : ℝ) ^ sourceExponent k (s + k) (nextDefect k r delta (phi 0)) := by
  subst k
  have hP0 : (0 : ℝ) < P := by
    have hbn : 0 < b + n := by omega
    have : 0 < 4 * (b + n) ^ 4 := by positivity
    exact_mod_cast (show 0 < P by omega)
  have hg : 0 ≤ primeGap (b + n) 0 r s delta := by
    have h := primeGap_ge (d := 0) (r := r) (s := s) (by omega) hdelta
    simp only [Nat.cast_zero, sub_zero] at h
    exact (Nat.cast_nonneg _).trans h
  have h := typeCount_le_of_power_bound
    (VinogradovDiagonalMoment.monomialSystem_hasType (b + n))
    (by omega) hP (by simpa only [Nat.zero_add] using hMdeg 0 (by omega))
    (by norm_num) (by simp) (π 0) (hπ 0 (by omega))
    (by simpa only [Nat.zero_add, Nat.sub_zero] using hbudget 0 (by omega))
    hr1 (by omega) (by omega) (by omega) (by norm_num : 0 < 1) hfirst hfirstMin
    (show 0 ≤ C * coefficient (b + n) b s r delta eta 0 n * (P : ℝ) ^ (b + n) from
      mul_nonneg (mul_nonneg hC.le (coefficient_nonneg _ _ _ _ _ _ _ _)) (by positivity))
    hlambda (sub_nonneg.mp hg)
    (fun e p X hp G hG hpM _hpU hX =>
      residue_power_bound (b + n) b P s r M U π phi hb hP hs hr1 hr hstop hC heta
        hdelta hlambda hMdeg hπ hcard hbudget hprime hpacket hphi hrec hdepth hdiag
        hsource n 0 (by omega) 1 e p 1 X hp hpM (by norm_num) hX G hG
        (by norm_num) (by simp))
  simp only [VinogradovDiagonalMoment.initial_count_eq, Nat.factorial_zero, mul_one,
    hcard 0 (by omega)] at h
  have hU := Real.rpow_le_rpow (Nat.cast_nonneg (U 0)) (hpacket 0 (by omega)) hg
  rw [Real.mul_rpow heta.le (Real.rpow_nonneg hP0.le _), ← Real.rpow_mul hP0.le] at hU
  apply h.trans
  calc
    _ ≤ ((4 * (b + n) ^ 3 * (b + n).factorial : ℕ) : ℝ) *
        (C * coefficient (b + n) b s r delta eta 0 n * (P : ℝ) ^ (b + n)) *
          (eta ^ primeGap (b + n) 0 r s delta *
            (P : ℝ) ^ (phi 0 * primeGap (b + n) 0 r s delta)) *
              (P : ℝ) ^ sourceExponent (b + n) s delta := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hP0.le _)
      exact mul_le_mul_of_nonneg_left hU
        (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg hC.le (coefficient_nonneg _ _ _ _ _ _ _ _)) (by positivity)))
    _ = _ := by
      rw [← next_exponent, Real.rpow_add hP0, Real.rpow_add hP0, Real.rpow_natCast]
      ring

end
end RiemannGaussian.VinogradovFordIteration
