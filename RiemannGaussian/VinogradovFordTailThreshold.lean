/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordMoment
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Paying all literal quotient endpoints at Ford's starting height

The recursive minimum tail costs only one factor 16s squared times the
product of packet endpoints. The original depth restriction leaves a
tenth of the physical-endpoint exponent. Ford's published base pays both
that single factor and all packet-width factors, without increasing the
published starting height.
-/

namespace RiemannGaussian.VinogradovFordTailThreshold
noncomputable section
open scoped BigOperators
open VinogradovFordIteration

/-- The exact root-scale base in Ford's Lemma 3.4. -/
def publishedBase (k : ℕ) (omega : ℝ) : ℝ :=
  max (Real.exp (3 / 2 + 3 / (2 * omega)))
    (18 / omega * (k : ℝ) ^ 3 * Real.log k)

/-- The published base contains a sufficient elementary polynomial reserve. -/
theorem publishedBase_ge {k : ℕ} (hk : 26 ≤ k) {omega : ℝ}
    (homega : 0 < omega) (homegaHalf : omega ≤ 1 / 2) :
    64 * (k : ℝ) ^ 3 ≤ publishedBase k omega := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 2 ≤ Real.log (k : ℝ) := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (show (16 : ℝ) ≤ k by linarith)
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at hmono
    have htwo := Real.log_two_gt_d9
    norm_num at hmono
    linarith
  have hquot : 36 ≤ 18 / omega := (le_div_iff₀ homega).mpr (by linarith)
  apply le_trans _ (le_max_right _ _)
  have hc : 64 ≤ (18 / omega) * Real.log k := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ (18 / omega) * Real.log k - 64 by linarith)
    (show 0 ≤ (k : ℝ) ^ 3 by positivity)]

/-- The minimum endpoint pays a single conditioning constant, followed
by the product of all later packet endpoints. -/
theorem minimumTail_le_product {s : ℕ} (hs : 1 ≤ s) (U : ℕ → ℕ)
    (d n : ℕ) (hU : ∀ i ≤ d + n, 1 ≤ U i) :
    minimumTail s U d n ≤ 16 * s ^ 2 * ∏ i ∈ Finset.range n, U (d + i + 1) := by
  have hD : 1 ≤ 16 * s ^ 2 := by nlinarith [Nat.pow_le_pow_left hs 2]
  induction n generalizing d with
  | zero => simpa [minimumTail] using hD
  | succ n ih =>
    have hprod : 1 ≤ ∏ i ∈ Finset.range n, U (d + 1 + i + 1) :=
      Finset.one_le_prod (fun i hi => hU _ (by have := Finset.mem_range.mp hi; omega))
    have hconst : 16 * s ^ 2 ≤ 16 * s ^ 2 * ∏ i ∈ Finset.range n, U (d + 1 + i + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hinner := max_le hconst (ih (d + 1) (fun i hi => hU i (by omega)))
    have hbound : max (16 * s ^ 2) (minimumTail s U (d + 1) n) * U (d + 1) ≤
        16 * s ^ 2 * ∏ i ∈ Finset.range (n + 1), U (d + i + 1) := by
      apply (Nat.mul_le_mul_right _ hinner).trans_eq
      rw [Finset.prod_range_succ']
      simp only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm 1, mul_assoc]
    rw [minimumTail]
    apply max_le _ hbound
    exact (show 1 ≤ max (16 * s ^ 2) (minimumTail s U (d + 1) n) * U (d + 1) from
      one_le_mul_of_one_le_of_one_le (hD.trans (le_max_left _ _)) (hU _ (by omega))).trans hbound

/-- All initial and subsequent quotient requirements are paid by the
one complete packet-endpoint product. -/
theorem initial_minimum_le_product {s : ℕ} (hs : 1 ≤ s) (U : ℕ → ℕ)
    (n : ℕ) (hU : ∀ i ≤ n, 1 ≤ U i) :
    minimumTail s U 0 n * U 0 ≤ 16 * s ^ 2 * ∏ i ∈ Finset.range (n + 1), U i := by
  apply (Nat.mul_le_mul_right _ (minimumTail_le_product hs U 0 n (by simpa using hU))).trans_eq
  rw [Finset.prod_range_succ']
  simp only [Nat.zero_add, mul_assoc]

/-- A small fixed integer inequality pays the whole conditioning factor
after taking tenth powers. -/
theorem conditioning_polynomial {k : ℕ} (hk : 26 ≤ k) :
    16 ^ 10 * k ^ 60 ≤ 64 * k ^ (3 * (k + 1)) := by
  have hk4 : 4 ≤ k := by omega
  have hnum : 16 ^ 10 ≤ 64 * k ^ 18 := by
    apply le_trans (by norm_num : 16 ^ 10 ≤ 64 * 4 ^ 18)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk4 _)
  calc
    _ ≤ (64 * k ^ 18) * k ^ 60 := Nat.mul_le_mul_right _ hnum
    _ = 64 * k ^ 78 := by rw [mul_assoc, ← pow_add]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

/-- Ford's starting height pays all width factors at once. The proof
uses eta^10<=64 and does not replace the packet width by two. -/
theorem width_factor_le_tenth_root {k s j P : ℕ} (hk : 26 ≤ k) (hs : s ≤ k ^ 3)
    (hj : j ≤ k) {eta V : ℝ} (heta : 0 ≤ eta) (hetaMax : eta ≤ 3 / 2)
    (hV : 64 * (k : ℝ) ^ 3 ≤ V) (hP : V ^ (k + 1) ≤ P) :
    16 * (s : ℝ) ^ 2 * eta ^ j ≤ (P : ℝ) ^ (1 / 10 : ℝ) := by
  have heta10 : eta ^ 10 ≤ 64 := by
    calc
      _ ≤ (3 / 2 : ℝ) ^ 10 := pow_le_pow_left₀ heta hetaMax _
      _ ≤ _ := by norm_num
  have hetaJ : (eta ^ j) ^ 10 ≤ (64 : ℝ) ^ k := by
    calc
      _ = (eta ^ 10) ^ j := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (64 : ℝ) ^ j := pow_le_pow_left₀ (by positivity) heta10 _
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hj
  have hs20 : ((s : ℝ) ^ 2) ^ 10 ≤ (k : ℝ) ^ 60 := by
    have hsR : (s : ℝ) ≤ (k : ℝ) ^ 3 := by exact_mod_cast hs
    calc
      _ ≤ (((k : ℝ) ^ 3) ^ 2) ^ 10 := by gcongr
      _ = _ := by ring
  have hpoly : (16 : ℝ) ^ 10 * (k : ℝ) ^ 60 ≤ 64 * (k : ℝ) ^ (3 * (k + 1)) := by
    exact_mod_cast conditioning_polynomial hk
  have hpow : (16 * (s : ℝ) ^ 2 * eta ^ j) ^ 10 ≤ (P : ℝ) := by
    calc
      _ = (16 : ℝ) ^ 10 * ((s : ℝ) ^ 2) ^ 10 * (eta ^ j) ^ 10 := by rw [mul_pow, mul_pow]
      _ ≤ (16 : ℝ) ^ 10 * (k : ℝ) ^ 60 * 64 ^ k := by gcongr
      _ ≤ (64 * (k : ℝ) ^ (3 * (k + 1))) * 64 ^ k := by gcongr
      _ = (64 * (k : ℝ) ^ 3) ^ (k + 1) := by
        rw [mul_pow, pow_mul, pow_succ (64 : ℝ)]
        ring
      _ ≤ V ^ (k + 1) := pow_le_pow_left₀ (by positivity) hV _
      _ ≤ _ := hP
  have hh := Real.rpow_le_rpow (by positivity) hpow (by norm_num : (0 : ℝ) ≤ 1 / 10)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hh
  norm_num at hh
  exact hh

/-- The complete product of literal integer packet endpoints is controlled
at the diagonal scale. No floor endpoint is enlarged inside a moment. -/
theorem packet_product_le {P r j : ℕ} {eta : ℝ}
    (hP : 1 ≤ P) (U : ℕ → ℕ)
    (hU : ∀ i < j, (U i : ℝ) ≤ eta * (P : ℝ) ^ (1 / (r : ℝ))) :
    ((∏ i ∈ Finset.range j, U i : ℕ) : ℝ) ≤
      eta ^ j * (P : ℝ) ^ ((j : ℝ) / r) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _i ∈ Finset.range j, eta * (P : ℝ) ^ (1 / (r : ℝ)) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i hi => hU i (Finset.mem_range.mp hi))
    _ = (eta * (P : ℝ) ^ (1 / (r : ℝ))) ^ j := by simp
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast ((P : ℝ) ^ (1 / (r : ℝ))) j,
        ← Real.rpow_mul hP0.le]
      congr 2
      ring

/-- All actual quotient endpoints meet their recursive size conditions
at the published height. The short packets themselves remain inputs. -/
theorem tail_conditions {k s r n P : ℕ} (hk : 26 ≤ k) (hs1 : 1 ≤ s) (hs : s ≤ k ^ 3)
    (hr : 0 < r) (hrk : r ≤ k) (hdepth : 10 * (n + 1) ≤ 9 * r)
    {eta V : ℝ} (heta : 0 ≤ eta) (hetaMax : eta ≤ 3 / 2)
    (hV : 64 * (k : ℝ) ^ 3 ≤ V) (hP : V ^ (k + 1) ≤ P)
    (U : ℕ → ℕ) (hU1 : ∀ i ≤ n, 1 ≤ U i)
    (hU : ∀ i ≤ n, (U i : ℝ) ≤ eta * (P : ℝ) ^ (1 / (r : ℝ))) :
    16 * s ^ 2 * U 0 ≤ P ∧ minimumTail s U 0 n * U 0 ≤ P := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hV1 : 1 ≤ V := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 26) hkR 3]
  have hP1R : (1 : ℝ) ≤ P := (one_le_pow₀ hV1).trans hP
  have hP1 : 1 ≤ P := by exact_mod_cast hP1R
  have hP0 : (0 : ℝ) < P := by linarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hj : n + 1 ≤ k := by omega
  have hratio : ((n + 1 : ℕ) : ℝ) / r ≤ 9 / 10 := by
    apply (div_le_iff₀ hrR).mpr
    have h : 10 * ((n + 1 : ℕ) : ℝ) ≤ 9 * r := by exact_mod_cast hdepth
    linarith
  have hwidth := width_factor_le_tenth_root hk hs hj heta hetaMax hV hP
  have hprod := packet_product_le (j := n + 1) hP1 U (fun i hi => hU i (by omega))
  have hwhole : (16 * s ^ 2 * ∏ i ∈ Finset.range (n + 1), U i : ℕ) ≤ P := by
    have hh : (16 : ℝ) * (s : ℝ) ^ 2 * ((∏ i ∈ Finset.range (n + 1), U i : ℕ) : ℝ) ≤ P := by
      calc
        _ ≤ (16 * (s : ℝ) ^ 2 * eta ^ (n + 1)) * (P : ℝ) ^ (((n + 1 : ℕ) : ℝ) / r) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 16 * (s : ℝ) ^ 2)
        _ ≤ (P : ℝ) ^ (1 / 10 : ℝ) * (P : ℝ) ^ (9 / 10 : ℝ) :=
          mul_le_mul hwidth (Real.rpow_le_rpow_of_exponent_le hP1R hratio)
            (Real.rpow_nonneg hP0.le _) (Real.rpow_nonneg hP0.le _)
        _ = _ := by rw [← Real.rpow_add hP0]; norm_num
    exact_mod_cast hh
  constructor
  · apply le_trans _ hwhole
    apply Nat.mul_le_mul_left
    rw [Finset.prod_range_succ']
    exact Nat.le_mul_of_pos_left _ (by
      have hp : 1 ≤ ∏ i ∈ Finset.range n, U (i + 1) :=
        Finset.one_le_prod (fun i hi => hU1 _ (by have := Finset.mem_range.mp hi; omega))
      omega)
  · exact (initial_minimum_le_product hs1 U n hU1).trans hwhole

/-- The same published height also pays the repeated-tuple absorption
threshold at the largest active dimension. -/
theorem original_size {k P : ℕ} (hk : 26 ≤ k) {V : ℝ}
    (hV : 64 * (k : ℝ) ^ 3 ≤ V) (hP : V ^ (k + 1) ≤ P) :
    4 * k ^ 4 ≤ P := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hV1 : 1 ≤ V := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 26) hkR 3]
  have hsmall : 2 * (k : ℝ) ^ 2 ≤ 64 * (k : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (show (0 : ℝ) ≤ k - 1 by linarith)]
  have hh : 4 * (k : ℝ) ^ 4 ≤ (P : ℝ) := by
    calc
      _ = (2 * (k : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (64 * (k : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ (by positivity) hsmall _
      _ ≤ V ^ 2 := pow_le_pow_left₀ (by positivity) hV _
      _ ≤ V ^ (k + 1) := pow_le_pow_right₀ hV1 (by omega)
      _ ≤ _ := hP
  exact_mod_cast hh

/-- Ford's stated coefficient and starting height now reach the actual
moment. The short-prime supply and scale/type admissibility remain
explicit; there are no separate tail-size or mixed-bound assumptions. -/
theorem published_height_bound (k b P s r : ℕ) (M U : ℕ → ℕ) (π : ℕ → Finset ℕ)
    (phi : ℕ → ℝ) {C delta omega : ℝ}
    (hk : 26 ≤ k) (hb : 2 ≤ b) (hs : k ≤ s) (hsMax : s ≤ k ^ 3)
    (hr1 : 1 ≤ r) (hr : r ≤ k) (hstop : k - b ≤ r)
    (hlimit : 10 * (k - b + 1) ≤ 9 * r)
    (hC : 0 < C) (homega : 0 < omega) (homegaHalf : omega ≤ 1 / 2)
    (hP : publishedBase k omega ^ (k + 1) ≤ P)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hMdeg : ∀ d ≤ k, k ≤ M d)
    (hπ : ∀ d ≤ k, ∀ p ∈ π d, p.Prime ∧ M d < p ∧ p ≤ U d)
    (hcard : ∀ d ≤ k, (π d).card = k ^ 3)
    (hbudget : ∀ d ≤ k, P ^ (d + 2 * (k - d).choose 2) < ∏ p ∈ π d, p)
    (hprime : ∀ d ≤ k, (P : ℝ) ^ phi d ≤ ((M d + 1 : ℕ) : ℝ))
    (hpacket : ∀ d ≤ k, (U d : ℝ) ≤ (1 + omega) * (P : ℝ) ^ phi d)
    (hphi : ∀ d ≤ k, 0 ≤ phi d)
    (hphiMax : ∀ d ≤ k, phi d ≤ 1 / (r : ℝ))
    (hrec : ∀ d < k - b, phi d =
      VinogradovFordScales.previousScale k (d + 1) r delta (phi (d + 1)))
    (hdepth : ((k - b : ℕ) : ℝ) * (((k - b : ℕ) : ℝ) - 1) ≤
      2 * delta - ((k : ℝ) - r) * ((k : ℝ) - r + 1))
    (hdiag : ∀ d, d + b = k → P < (M d + 1) ^ r)
    (hsource : ∀ X : ℕ, 1 ≤ X → VinogradovMeanValue.meanValue s k X ≤
      C * (X : ℝ) ^ VinogradovFordScales.sourceExponent k s delta)
    (n : ℕ) (hkn : b + n = k) :
    VinogradovMeanValue.meanValue (s + k) k P ≤
      C * ((k : ℝ) ^ (3 * k) * (1 + omega) ^ (4 * s + k ^ 2)) *
        (P : ℝ) ^ VinogradovFordScales.sourceExponent k (s + k)
          (VinogradovFordScales.nextDefect k r delta (phi 0)) := by
  have hV := publishedBase_ge hk homega homegaHalf
  have hsize := original_size hk hV hP
  have hP1 : 1 ≤ P := by
    have hk0 : 0 < k := by omega
    have : 0 < 4 * k ^ 4 := by positivity
    omega
  have heta : (0 : ℝ) ≤ 1 + omega := by linarith
  have hU1 (i : ℕ) (hi : i ≤ n) : 1 ≤ U i := by
    have hic : i ≤ k := by omega
    have hpos : 0 < (π i).card := by
      rw [hcard i hic]
      exact pow_pos (by omega) _
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have hh := hπ i hic p hp
    omega
  have hU (i : ℕ) (hi : i ≤ n) :
      (U i : ℝ) ≤ (1 + omega) * (P : ℝ) ^ (1 / (r : ℝ)) := by
    have hik : i ≤ k := by omega
    exact (hpacket i hik).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP1) (hphiMax i hik)) heta)
  have htail := tail_conditions hk (by omega) hsMax (by omega) hr
    (by omega : 10 * (n + 1) ≤ 9 * r) heta (by linarith) hV hP U hU1 hU
  exact VinogradovFordMoment.published_moment_bound k b P s r M U π phi hk hb hsize hs
    hr1 hr hstop hlimit hC (by linarith) hdelta hMdeg hπ hcard hbudget hprime hpacket
    hphi hrec hdepth hdiag hsource n hkn htail.1 htail.2

end
end RiemannGaussian.VinogradovFordTailThreshold
