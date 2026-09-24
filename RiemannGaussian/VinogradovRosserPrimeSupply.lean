/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordGlobalStep
import RiemannGaussian.RosserSchoenfeldBounds
import RiemannGaussian.RosserSchoenfeldFiniteBounds

/-!
# Ford's exact short-prime packet from the published prime-count bounds

The second part of Ford's Lemma 2.1 supplies the literal `k^3` packet in
`(M,(1+omega)M]` at the original base and throughout the published width
range. The Rosser--Schoenfeld bounds on actual prime counts remain explicit
hypotheses here. This module proves their numerical and finite-set
consequence; it does not assert those still-open arithmetic estimates.
-/

namespace RiemannGaussian.VinogradovRosserPrimeSupply
noncomputable section
open Real RosserSchoenfeldComparison VinogradovFordGlobalStep
open VinogradovFordTailThreshold

private theorem rational_gap {w L : ℝ} (hw : 0 < w) (hw' : w ≤ 1 / 2)
    (hL : 3 / 2 + 3 / (2 * w) ≤ L) :
    w / (3 * L) ≤ (1 + w) / (L + w - 1 / 2) -
      1 / L * (1 + 3 / (2 * L)) := by
  have hreserve : (0 : ℝ) < 3 / (2 * w) := by positivity
  have hL0 : 0 < L := by linarith
  have hden : 0 < L + w - 1 / 2 := by linarith
  have hmul : 3 / 2 * (1 + w) ≤ w * L := by
    have h := mul_le_mul_of_nonneg_left hL hw.le
    field_simp at h
    nlinarith only [h]
  have h1 := mul_nonneg hL0.le (sub_nonneg.mpr hmul)
  have h2 := mul_nonneg (mul_nonneg hw.le hL0.le) (show 0 ≤ 1 / 2 - w by linarith)
  have h3 : 0 ≤ 1 / 2 - w := by linarith
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ hden).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < 6 * L ^ 2 by positivity)).mp
  field_simp
  nlinarith only [h1, h2, h3]

private theorem id_div_log_mono {a b : ℝ} (ha : 0 < a) (hal : 1 ≤ log a) (hab : a ≤ b) :
    a / log a ≤ b / log b := by
  have hb := ha.trans_le hab
  have hlb : 1 ≤ log b := hal.trans (log_le_log ha hab)
  have hh := log_le_sub_one_of_pos (div_pos hb ha)
  rw [log_div hb.ne' ha.ne'] at hh
  have hh' := mul_le_mul_of_nonneg_left hh ha.le
  have hc := mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ log a - 1 by linarith)
  have he : a * (b / a - 1) = b - a := by field_simp
  rw [he] at hh'
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

/-- The exact quantitative interval consequence of the two actual count bounds. -/
theorem primeCounting_gap {w x : ℝ} (hw : 0 < w) (hw' : w ≤ 1 / 2)
    (hx : exp (3 / 2 + 3 / (2 * w)) ≤ x)
    (hupper : (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x)
    (hlower : lower ((1 + w) * x) < (Nat.primeCounting ⌊(1 + w) * x⌋₊ : ℝ)) :
    w * x / (3 * log x) <
      (Nat.primeCounting ⌊(1 + w) * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx0 := (exp_pos _).trans_le hx
  have hL : 3 / 2 + 3 / (2 * w) ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hreserve : (0 : ℝ) < 3 / (2 * w) := by positivity
  have hL0 : 0 < log x := by linarith
  have hw1 : 0 < 1 + w := by linarith
  have hlogw : log (1 + w) ≤ w := by linarith [log_le_sub_one_of_pos hw1]
  have hden0 : 0 < log x + log (1 + w) - 1 / 2 := by
    have hh := log_nonneg (show 1 ≤ 1 + w by linarith)
    linarith
  have hlow : (1 + w) * x / (log x + w - 1 / 2) ≤ lower ((1 + w) * x) := by
    unfold lower
    rw [log_mul hw1.ne' hx0.ne']
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hg := mul_le_mul_of_nonneg_left (rational_gap hw hw' hL) hx0.le
  have he : x * ((1 + w) / (log x + w - 1 / 2) - 1 / log x * (1 + 3 / (2 * log x))) =
      (1 + w) * x / (log x + w - 1 / 2) - upper x := by unfold upper; ring
  rw [he] at hg
  have hh := sub_lt_sub (hlow.trans_lt hlower) hupper
  calc
    _ = x * (w / (3 * log x)) := by ring
    _ ≤ _ := hg
    _ < _ := hh

private theorem threshold_pays_count {N : ℕ} (hN : 2 ≤ N) {w x : ℝ}
    (hw : 0 < w) (hw' : w ≤ 1 / 2)
    (hsize : 6 / w ≤ (N : ℝ) / log N)
    (hx : 6 / w * N * log N ≤ x) :
    (N : ℝ) ≤ w * x / (3 * log x) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlN : 0 < log (N : ℝ) := log_pos (by linarith)
  have hlhalf : (1 / 2 : ℝ) ≤ log N := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 2) hNR
    linarith [log_two_gt_d9]
  have hw12 : (12 : ℝ) ≤ 6 / w := (le_div_iff₀ hw).mpr (by linarith)
  let b := 6 / w * N * log N
  have hb12 : 12 ≤ b := by
    have hh := mul_le_mul hw12 hNR (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 6 / w)
    have hh' := mul_le_mul hh hlhalf (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by positivity : 0 ≤ 6 / w * (N : ℝ))
    dsimp [b]
    nlinarith only [hh']
  have hb0 : 0 < b := by linarith
  have hbl : 1 ≤ log b := (le_log_iff_exp_le hb0).mpr (by linarith [exp_one_lt_d9])
  have hbN : b ≤ (N : ℝ) ^ 2 := by
    have hh := (le_div_iff₀ hlN).mp hsize
    have hh' := mul_le_mul_of_nonneg_right hh hN0.le
    dsimp [b]
    nlinarith only [hh']
  have hlog : log b ≤ 2 * log (N : ℝ) := by
    have hh := log_le_log hb0 hbN
    simpa only [log_pow, Nat.cast_ofNat] using hh
  have hbase : (N : ℝ) ≤ w * b / (3 * log b) := by
    apply (le_div_iff₀ (by linarith : 0 < 3 * log b)).mpr
    have he : w * b = 6 * N * log N := by dsimp [b]; field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hlog hN0.le]
  apply hbase.trans
  have hh := mul_le_mul_of_nonneg_left (id_div_log_mono hb0 hbl hx)
    (show 0 ≤ w / 3 by positivity)
  convert! hh using 1 <;> ring

/-- Ford Lemma 2.1, second part: the exact finite packet, conditional only
on the published pointwise inequalities for actual prime counts. -/
theorem exists_prime_packet {N : ℕ} (hN : 2 ≤ N) {w x : ℝ}
    (hw : 0 < w) (hw' : w ≤ 1 / 2) (hsize : 6 / w ≤ (N : ℝ) / log N)
    (hexp : exp (3 / 2 + 3 / (2 * w)) ≤ x) (hx : 6 / w * N * log N ≤ x)
    (hupper : (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x)
    (hlower : lower ((1 + w) * x) < (Nat.primeCounting ⌊(1 + w) * x⌋₊ : ℝ)) :
    ∃ packet : Finset ℕ, packet.card = N ∧
      ∀ p ∈ packet, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ (1 + w) * x := by
  classical
  have hx0 := (exp_pos _).trans_le hexp
  have hxy : x ≤ (1 + w) * x := by nlinarith
  have hfloor := Nat.floor_mono hxy
  have hsubset := Nat.primesLE_mono hfloor
  let S := Nat.primesLE ⌊(1 + w) * x⌋₊ \ Nat.primesLE ⌊x⌋₊
  have hcard : S.card = Nat.primeCounting ⌊(1 + w) * x⌋₊ - Nat.primeCounting ⌊x⌋₊ := by
    rw [Finset.card_sdiff_of_subset hsubset]
    simp only [Nat.primesLE_card_eq_primeCounting]
  have hbound := (threshold_pays_count hN hw hw' hsize hx).trans_lt
    (primeCounting_gap hw hw' hexp hupper hlower)
  have hcount : N ≤ S.card := by
    rw [hcard]
    have hh : (N : ℝ) < ((Nat.primeCounting ⌊(1 + w) * x⌋₊ - Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.monotone_primeCounting hfloor)]
      exact hbound
    exact (Nat.cast_le (α := ℝ)).mp hh.le
  obtain ⟨packet, hpacket, hpacketCard⟩ := Finset.exists_subset_card_eq hcount
  refine ⟨packet, hpacketCard, ?_⟩
  intro p hp
  obtain ⟨hpU, hpL⟩ := Finset.mem_sdiff.mp (hpacket hp)
  obtain ⟨hpU, hprime⟩ := Nat.mem_primesLE.mp hpU
  refine ⟨hprime, ?_, (Nat.le_floor_iff (by positivity)).mp hpU⟩
  apply (Nat.floor_lt hx0.le).mp
  have hh : ¬p ≤ ⌊x⌋₊ := by intro hh; exact hpL (Nat.mem_primesLE.mpr ⟨hh, hprime⟩)
  omega

/-- At the published range of omega, the cubic packet meets Ford's density condition. -/
theorem cubic_density {k : ℕ} (hk : 26 ≤ k) {w : ℝ} (hw : 0 < w)
    (hwLower : 1 / (3 * log k) ≤ w) :
    6 / w ≤ ((k ^ 3 : ℕ) : ℝ) / log (k ^ 3 : ℕ) := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hl : 0 < log (k : ℝ) := log_pos (by linarith)
  have hlog : log (k : ℝ) ≤ (k : ℝ) / 2 := by
    have hh := log_le_sub_one_of_pos (div_pos hk0 (by norm_num : (0 : ℝ) < 2))
    rw [log_div hk0.ne' (by norm_num)] at hh
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hw1 : 1 ≤ w * (3 * log k) := (div_le_iff₀ (by positivity)).mp hwLower
  have hlarge : 54 * log (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
    have hh := mul_nonneg (show 0 ≤ (k : ℝ) - 27 / 2 by linarith) (sq_nonneg (k : ℝ))
    nlinarith [sq_nonneg ((k : ℝ) / 2 - log k)]
  have h6 : 6 / w ≤ 18 * log k := (div_le_iff₀ hw).mpr (by nlinarith only [hw1])
  apply h6.trans
  push_cast
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  exact (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hlarge])

/-- The original short-prime hypothesis follows with no changed constant,
threshold, packet size, or width range once the two source count bounds are proved. -/
theorem shortPrimeSupply_of_primeCounting (k : ℕ) {w : ℝ} (hk : 26 ≤ k)
    (hw : 0 < w) (hw' : w ≤ 1 / 2) (hwLower : 1 / (3 * log k) ≤ w)
    (hupper : ∀ x : ℝ, 67 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x)
    (hlower : ∀ x : ℝ, 67 < x → lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ)) :
    ShortPrimeSupply k w := by
  intro M hM
  have hbase := publishedBase_ge hk hw hw'
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hM67 : 67 < M := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 26) hkR 3
    nlinarith
  have hMw : 67 < (1 + w) * M := by nlinarith
  apply exists_prime_packet (N := k ^ 3) (by nlinarith [Nat.pow_le_pow_left hk 3])
    hw hw' (cubic_density hk hw hwLower)
    ((le_max_left _ _).trans hM) _ (hupper M hM67) (hlower _ hMw)
  have hh := (le_max_right _ _).trans hM
  change 18 / w * (k : ℝ) ^ 3 * log k ≤ M at hh
  push_cast
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  convert! hh using 1
  ring

/- The finite interval is now discharged by actual kernel-checked prime counts.
The larger range remains an explicit premise; the packet target is unchanged. -/
/-- The original full-width prime supply follows once the remaining count
inequalities above 16000 are proved. The finite prefix is checked here. -/
theorem shortPrimeSupply_of_primeCounting_above_sixteen_thousand (k : ℕ) {w : ℝ}
    (hk : 26 ≤ k) (hw : 0 < w) (hw' : w ≤ 1 / 2) (hwLower : 1 / (3 * log k) ≤ w)
    (hupper : ∀ x : ℝ, 16000 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x)
    (hlower : ∀ x : ℝ, 16000 < x → lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ)) :
    ShortPrimeSupply k w := by
  apply shortPrimeSupply_of_primeCounting k hk hw hw' hwLower
  · intro x hx
    by_cases h : x ≤ 16000
    · exact (RosserSchoenfeldFiniteBounds.bounds_through_sixteen_thousand ⟨hx.le, h⟩).2
    · exact hupper x (lt_of_not_ge h)
  · intro x hx
    by_cases h : x ≤ 16000
    · exact (RosserSchoenfeldFiniteBounds.bounds_through_sixteen_thousand ⟨hx.le, h⟩).1
    · exact hlower x (lt_of_not_ge h)

end
end RiemannGaussian.VinogradovRosserPrimeSupply
