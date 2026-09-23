/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordSchedule
import RiemannGaussian.VinogradovFordTailThreshold

/-!
# The actual integer parameters for Ford's original iteration

The published backward scales determine the real prime scales and both
integer cutoffs. Their degree, discriminant-product, root and diagonal
conditions are proved here, including the rounding at an exact root.
Existence of the required short prime packets remains an explicit
arithmetic hypothesis; this file does not assert that supply theorem.
-/

namespace RiemannGaussian.VinogradovFordParameters
noncomputable section
open VinogradovFordScales VinogradovFordSchedule VinogradovFordTailThreshold

/-- The real prime scale at one depth of the original backward schedule. -/
def primeScale (k r n P : ℕ) (delta : ℝ) (d : ℕ) : ℝ :=
  (P : ℝ) ^ schedule k r n delta d

/-- The lower integer cutoff retains the exact real prime scale. -/
def lowerCutoff (k r n P : ℕ) (delta : ℝ) (d : ℕ) : ℕ :=
  ⌊primeScale k r n P delta d⌋₊

/-- The upper integer cutoff retains the original short-interval width. -/
def upperCutoff (k r n P : ℕ) (delta omega : ℝ) (d : ℕ) : ℕ :=
  ⌊(1 + omega) * primeScale k r n P delta d⌋₊

/-- The cubic packet pays every discriminant exponent, also at the two
unused terminal dimensions zero and one. -/
theorem packet_exponent_le {k d : ℕ} (hk : 2 ≤ k) (hd : d ≤ k) :
    (k + 1) * (d + 2 * (k - d).choose 2) ≤ k ^ 3 := by
  have he : d + 2 * (k - d).choose 2 ≤ k * (k - 1) := by
    rw [VinogradovDiagonalExponent.twice_choose_two]
    have hd1 : d ≤ d * (k - 1) := by
      simpa only [mul_one] using Nat.mul_le_mul_left d (show 1 ≤ k - 1 by omega)
    have hm : (k - d) * (k - d - 1) ≤ (k - d) * (k - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hh := Nat.add_le_add hd1 hm
    have heq : d + (k - d) = k := by omega
    nlinarith only [hh, heq]
  have hh := Nat.mul_le_mul_left (k + 1) he
  have hk1 : k - 1 + 1 = k := by omega
  have hp := congrArg (fun j : ℕ => j * (k + 1) * k) hk1
  nlinarith only [hh, hp]

/-- A supplied packet above the real root scale pays the complete type
and discriminant budget at every depth. -/
theorem packet_budget {k d P : ℕ} {M : ℝ} (hk : 2 ≤ k) (hd : d ≤ k)
    (hM : 1 ≤ M) (hroot : (P : ℝ) ≤ M ^ (k + 1)) (π : Finset ℕ)
    (hcard : π.card = k ^ 3) (hπ : ∀ p ∈ π, M < (p : ℝ)) :
    P ^ (d + 2 * (k - d).choose 2) < ∏ p ∈ π, p := by
  have hne : π.Nonempty := Finset.card_pos.mp (by rw [hcard]; positivity)
  have hh : (P : ℝ) ^ (d + 2 * (k - d).choose 2) < ∏ p ∈ π, (p : ℝ) := by
    calc
      _ ≤ (M ^ (k + 1)) ^ (d + 2 * (k - d).choose 2) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hroot _
      _ = M ^ ((k + 1) * (d + 2 * (k - d).choose 2)) := (pow_mul _ _ _).symm
      _ ≤ M ^ (k ^ 3) := pow_le_pow_right₀ hM (packet_exponent_le hk hd)
      _ < _ := by
        rw [← hcard, ← Finset.prod_const]
        exact Finset.prod_lt_prod_of_nonempty (fun _ _ => by linarith) hπ hne
  rw [← Nat.cast_prod] at hh
  exact_mod_cast hh

/-- The published height and root-scale lower bound put every real prime
scale above the published base. -/
theorem base_le_scale {k P : ℕ} {V phi : ℝ} (hV : 1 ≤ V)
    (hP : V ^ (k + 1) ≤ (P : ℝ)) (hphi : 1 / ((k : ℝ) + 1) ≤ phi) :
    V ≤ (P : ℝ) ^ phi := by
  have hP1 : (1 : ℝ) ≤ P := (one_le_pow₀ hV).trans hP
  have hr : V ≤ (P : ℝ) ^ (1 / ((k : ℝ) + 1)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by linarith) (by positivity)
      (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
    simpa only [← Nat.cast_add_one, Real.rpow_natCast] using hP
  exact hr.trans (Real.rpow_le_rpow_of_exponent_le hP1 hphi)

/-- The root condition is retained before any integer rounding. -/
theorem root_le_scale_power {k P : ℕ} {phi : ℝ} (hP : 1 ≤ P)
    (hphi : 1 / ((k : ℝ) + 1) ≤ phi) :
    (P : ℝ) ≤ ((P : ℝ) ^ phi) ^ (k + 1) := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  have hmul : (1 : ℝ) ≤ phi * ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mp hphi
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP) hmul

/-- Taking the lower floor leaves strict room at the next integer; at the
terminal scale this proves the original diagonal cutoff, even at equality. -/
theorem diagonal_cutoff {r P : ℕ} (hr : 0 < r) :
    P < (⌊(P : ℝ) ^ (1 / (r : ℝ))⌋₊ + 1) ^ r := by
  have hp : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hnext : (P : ℝ) ^ (1 / (r : ℝ)) <
      ((⌊(P : ℝ) ^ (1 / (r : ℝ))⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((P : ℝ) ^ (1 / (r : ℝ)))
  rw [one_div] at hnext
  have hh := (Real.rpow_inv_lt_iff_of_pos (y := ((⌊(P : ℝ) ^ (r : ℝ)⁻¹⌋₊ + 1 : ℕ) : ℝ))
    hp (by positivity)
    (by exact_mod_cast hr : (0 : ℝ) < r)).mp hnext
  rw [Real.rpow_natCast] at hh
  simp only [one_div]
  exact_mod_cast hh

/-- Every original admissibility condition follows for the literal scales
and floors from the scalar restrictions and the supplied short packets.
The conclusion is the published coefficient, defect and starting height. -/
theorem moment_bound_of_packets (k r n P s : ℕ) (π : ℕ → Finset ℕ)
    {C delta omega : ℝ} (hk : 26 ≤ k) (hs : k ≤ s) (hsMax : s ≤ k ^ 3)
    (hr1 : 1 ≤ r) (hr : r ≤ k) (hlimit : 10 * (n + 1) ≤ 9 * r)
    (hC : 0 < C) (homega : 0 < omega) (homegaHalf : omega ≤ 1 / 2)
    (hP : publishedBase k omega ^ (k + 1) ≤ P)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hdepth : (n : ℝ) * ((n : ℝ) - 1) ≤ depthReserve k r delta)
    (hroot : 1 / ((k : ℝ) + 1) ≤ stationaryScale k r delta)
    (hcard : ∀ d ≤ k, (π d).card = k ^ 3)
    (hπ : ∀ d ≤ k, ∀ p ∈ π d, p.Prime ∧
      primeScale k r n P delta d < (p : ℝ) ∧
        (p : ℝ) ≤ (1 + omega) * primeScale k r n P delta d)
    (hsource : ∀ X : ℕ, 1 ≤ X → VinogradovMeanValue.meanValue s k X ≤
      C * (X : ℝ) ^ sourceExponent k s delta) :
    VinogradovMeanValue.meanValue (s + k) k P ≤
      C * ((k : ℝ) ^ (3 * k) * (1 + omega) ^ (4 * s + k ^ 2)) *
        (P : ℝ) ^ sourceExponent k (s + k)
          (nextDefect k r delta (schedule k r n delta 0)) := by
  let M := lowerCutoff k r n P delta
  let U := upperCutoff k r n P delta omega
  have hn : n ≤ k := by omega
  have hb : 2 ≤ k - n := by omega
  have hV := publishedBase_ge hk homega homegaHalf
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hVk : (k : ℝ) ≤ publishedBase k omega := by
    have hh : (k : ℝ) ≤ 64 * (k : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (show (0 : ℝ) ≤ k - 1 by linarith)]
    exact hh.trans hV
  have hV1 : 1 ≤ publishedBase k omega := by linarith
  have hP1 : 1 ≤ P := by exact_mod_cast (one_le_pow₀ hV1).trans hP
  have hscale (d : ℕ) := schedule_bounds (by omega : 0 < k) (by omega : 0 < r)
    hdelta hdepth hroot d
  have hbase (d : ℕ) : publishedBase k omega ≤ primeScale k r n P delta d :=
    base_le_scale hV1 hP (hscale d).2.1
  have hnonneg (d : ℕ) : 0 ≤ primeScale k r n P delta d := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hMdeg (d : ℕ) (_hd : d ≤ k) : k ≤ M d := Nat.le_floor (hVk.trans (hbase d))
  have hpacket (d : ℕ) (_hd : d ≤ k) :
      (U d : ℝ) ≤ (1 + omega) * (P : ℝ) ^ schedule k r n delta d :=
    Nat.floor_le (mul_nonneg (by linarith) (hnonneg d))
  have hprimes (d : ℕ) (hd : d ≤ k) (p : ℕ) (hp : p ∈ π d) :
      p.Prime ∧ M d < p ∧ p ≤ U d := by
    have hh := hπ d hd p hp
    exact ⟨hh.1, (Nat.floor_lt (hnonneg d)).mpr hh.2.1, Nat.le_floor hh.2.2⟩
  have hbudget (d : ℕ) (hd : d ≤ k) :
      P ^ (d + 2 * (k - d).choose 2) < ∏ p ∈ π d, p :=
    packet_budget (by omega) hd (hV1.trans (hbase d))
      (root_le_scale_power hP1 (hscale d).2.1) (π d) (hcard d hd)
      (fun p hp => (hπ d hd p hp).2.1)
  have hprime (d : ℕ) (_hd : d ≤ k) :
      (P : ℝ) ^ schedule k r n delta d ≤ ((M d + 1 : ℕ) : ℝ) := by
    have hh := (Nat.lt_floor_add_one (primeScale k r n P delta d)).le
    simpa only [M, lowerCutoff, primeScale, Nat.cast_add, Nat.cast_one] using hh
  have hdiag (d : ℕ) (hd : d + (k - n) = k) : P < (M d + 1) ^ r := by
    have hdn : d = n := by omega
    subst d
    dsimp only [M, lowerCutoff, primeScale]
    rw [schedule_terminal k r n delta le_rfl]
    exact diagonal_cutoff (by omega)
  exact published_height_bound k (k - n) P s r M U π (schedule k r n delta)
    hk hb hs hsMax hr1 hr (by omega) (by omega) hC homega homegaHalf hP hdelta
    hMdeg hprimes hcard hbudget hprime hpacket (fun d _ => (hscale d).1.le)
    (fun d _ => (hscale d).2.2)
    (fun d hd => schedule_step k r n delta (by omega))
    (by simpa only [Nat.sub_sub_self hn, depthReserve] using hdepth) hdiag hsource n (by omega)

end
end RiemannGaussian.VinogradovFordParameters
