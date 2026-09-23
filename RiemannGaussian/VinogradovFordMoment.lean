/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordCoefficient

/-!
# Ford's published coefficient on the actual homogeneous moment

This specializes the complete mixed-count induction to the numerical
coefficient k^(3k) eta^(4s+k^2). The diagonal source lower bound supplies
the needed source-exponent reserve. Short prime packets and the literal
minimum-tail conditions remain explicit; the published height threshold
and prime-packet existence are not assumed proved here.
-/

namespace RiemannGaussian.VinogradovFordMoment
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovFordScales VinogradovFordIteration
open VinogradovFordCoefficient

/-- Ford's exact stated coefficient and defect now bound the literal
homogeneous moment, conditional on the displayed prime packets and size
conditions. No intermediate mixed estimate or coefficient bound is assumed. -/
theorem published_moment_bound (k b P s r : ℕ) (M U : ℕ → ℕ) (π : ℕ → Finset ℕ)
    (phi : ℕ → ℝ) {C delta eta : ℝ}
    (hk : 26 ≤ k) (hb : 2 ≤ b) (hP : 4 * k ^ 4 ≤ P) (hs : k ≤ s)
    (hr1 : 1 ≤ r) (hr : r ≤ k) (hstop : k - b ≤ r)
    (hlimit : 10 * (k - b + 1) ≤ 9 * r)
    (hC : 0 < C) (heta : 1 ≤ eta)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hMdeg : ∀ d ≤ k, k ≤ M d)
    (hπ : ∀ d ≤ k, ∀ p ∈ π d, p.Prime ∧ M d < p ∧ p ≤ U d)
    (hcard : ∀ d ≤ k, (π d).card = k ^ 3)
    (hbudget : ∀ d ≤ k, P ^ (d + 2 * (k - d).choose 2) < ∏ p ∈ π d, p)
    (hprime : ∀ d ≤ k, (P : ℝ) ^ phi d ≤ ((M d + 1 : ℕ) : ℝ))
    (hpacket : ∀ d ≤ k, (U d : ℝ) ≤ eta * (P : ℝ) ^ phi d)
    (hphi : ∀ d ≤ k, 0 ≤ phi d)
    (hrec : ∀ d < k - b, phi d = previousScale k (d + 1) r delta (phi (d + 1)))
    (hdepth : ((k - b : ℕ) : ℝ) * (((k - b : ℕ) : ℝ) - 1) ≤
      2 * delta - ((k : ℝ) - r) * ((k : ℝ) - r + 1))
    (hdiag : ∀ d, d + b = k → P < (M d + 1) ^ r)
    (hsource : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤ C * (X : ℝ) ^ sourceExponent k s delta)
    (n : ℕ) (hkn : b + n = k)
    (hfirst : 16 * s ^ 2 * U 0 ≤ P)
    (hfirstMin : minimumTail s U 0 n * U 0 ≤ P) :
    meanValue (s + k) k P ≤
      C * ((k : ℝ) ^ (3 * k) * eta ^ (4 * s + k ^ 2)) *
        (P : ℝ) ^ sourceExponent k (s + k) (nextDefect k r delta (phi 0)) := by
  have hb3 : 3 ≤ b := by omega
  have heta0 : 0 < eta := by linarith
  have hlambda := source_exponent_ge hsource
  have hdepthAll (d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ k - b) :
      (d : ℝ) * ((d : ℝ) - 1) ≤
        2 * delta - ((k : ℝ) - r) * ((k : ℝ) - r + 1) := by
    have hdR : (d : ℝ) ≤ ((k - b : ℕ) : ℝ) := by exact_mod_cast hd
    have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    apply le_trans _ hdepth
    exact mul_le_mul hdR (by linarith) (by linarith) (Nat.cast_nonneg _)
  have h := moment_power_bound k b P s r M U π phi hb hP hs hr1 hr hstop hC heta0
    hdelta ((Nat.cast_nonneg s).trans hlambda) hMdeg hπ hcard hbudget hprime hpacket
    hphi hrec hdepthAll hdiag hsource n hkn hfirst hfirstMin
  apply h.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (full_coefficient_bound hk hb3 hs hr hstop heta hlambda n hkn) hC.le)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end
end RiemannGaussian.VinogradovFordMoment
