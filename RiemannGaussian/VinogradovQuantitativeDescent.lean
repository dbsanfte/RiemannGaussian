/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovRelativeProfile
import RiemannGaussian.VinogradovFiniteCritical

/-!
# Fully specified constants in the relative-defect mean-value descent

The descendant cutoff, prime packet, rounding factor, exponent decrement
and small-endpoint payment are explicit functions of the degree and relative
accuracy. The final theorem starts from the elementary factorial bound and
has no supplied mean-value hypothesis. These constants are not claimed small
enough for a uniform Vinogradov--Korobov zeta bound.
-/

namespace RiemannGaussian.VinogradovQuantitativeDescent
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovRemainderScaling
open VinogradovConditioningPowerSaving VinogradovSingularConditioning
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovNonsingularConditioning VinogradovProfileIteration
open VinogradovFirstExponent VinogradovExponentBootstrap
open VinogradovDefectRemainder VinogradovConstantPreservation VinogradovLinearProfile
open VinogradovRelativeProfile VinogradovFiniteCritical

/-- Power cutoff exponent including the final unused quotient scale. -/
def packetDepth (k q : ℕ) : ℕ := relativeDepth k q + 1

/-- An explicit number of candidate prime intervals sufficient for the packet. -/
def packetCount (k q : ℕ) : ℕ := 2 * (packetDepth k q * (k * (k - 1))) + 1

/-- The original initial-allowance coefficient after all profile steps. -/
def profileMultiplier (k : ℕ) : ℝ :=
  1 + selectionCost k k * (2 * (k : ℝ) * k) ^ (7 * k)

/-- An integer threshold paying size, prime-packet and iteration costs. -/
def primeCutoff (k q : ℕ) : ℕ :=
  max 2 (max (2 ^ packetCount k q)
    (max (4 * k ^ 4) ((2 * k * (k - 1) ^ (2 * (k * k))) ^ 2)))

/-- The exponent improvement produced by the explicit half-power saving. -/
def exponentStep (k q : ℕ) : ℝ := (1 / 2 : ℝ) / packetDepth k q

/-- The first endpoint where the original packet construction applies. -/
def endpointCutoff (k q : ℕ) : ℕ :=
  (2 ^ packetCount k q * primeCutoff k q) ^ packetDepth k q + 1

/-- The explicit large-endpoint coefficient, including both rounding costs. -/
def eventualMultiplier (k q : ℕ) : ℝ :=
  let Q := packetDepth k q
  let R := packetCount k q
  let L : ℝ := ((k * (2 * k + 1) : ℕ) : ℝ)
  max 1 ((2 * (R : ℝ)) ^ 2 * profileMultiplier k * (2 : ℝ) ^ L *
    ((2 ^ R : ℕ) : ℝ) ^ (1 / 2 : ℝ) * ((2 ^ Q : ℕ) : ℝ) ^ L)

/-- The all-endpoint coefficient also pays the finite initial interval. -/
def descentMultiplier (k q : ℕ) : ℝ :=
  max (eventualMultiplier k q) ((endpointCutoff k q : ℝ) ^ exponentStep k q)

/-- The literal global mean value improves at every large endpoint with
fully specified constants, independent of its supplied source constant. -/
theorem eventual_improvement (k q : ℕ) (hk : 4 ≤ k) (hq : 0 < q)
    (lam : ℝ)
    (hdefect : relativeDefect k q ≤ lam - 2 * (k : ℝ) * ((k : ℝ) + 1) +
      (k : ℝ) * ((k : ℝ) + 1) / 2)
    (hlamhi : lam ≤ ((k * (2 * k + 1) : ℕ) : ℝ))
    (C : ℝ) (hC : 1 ≤ C)
    (hJ : ∀ X : ℕ, 1 ≤ X → meanValue ((k + 1) * k) k X ≤ C * (X : ℝ) ^ lam)
    (X : ℕ) (hX : endpointCutoff k q ≤ X) :
    meanValue ((k + 1) * k) k X ≤
      (eventualMultiplier k q * C) * (X : ℝ) ^ (lam - exponentStep k q) := by
  let beta : ℝ := -(1 / 2)
  have hbeta : beta < 0 := by norm_num [beta]
  have hbetalow : -(1 / 2 : ℝ) ≤ beta := le_rfl
  let S := relativeDepth k q
  have hS : 2 ≤ S := relativeDepth_ge_two k q (by omega) hq
  let B := profileMultiplier k
  have hB : 1 ≤ B := by
    apply le_add_of_nonneg_right
    unfold selectionCost
    positivity
  let Q := packetDepth k q
  have hQ : 1 ≤ Q := by unfold Q packetDepth; omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  let eps := exponentStep k q
  let L : ℝ := ((k * (2 * k + 1) : ℕ) : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  let F := (2 : ℝ) ^ L
  have hF : 1 ≤ F := Real.one_le_rpow (by norm_num) hL
  let R := packetCount k q
  have hR : 2 * (Q * (k * (k - 1))) < R := by unfold R packetCount Q; omega
  have hRpos : 0 < R := by unfold R packetCount; omega
  let D := primeCutoff k q
  have hD2 : 2 ≤ D := le_max_left _ _
  have hpacket : 2 ^ R ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hsize : 4 * k ^ 4 ≤ D := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hprime : iterationConstant k k ^ 2 ≤ (D : ℝ) := by
    have hh : (2 * k * (k - 1) ^ (2 * (k * k))) ^ 2 ≤ D :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, iterationConstant] using
      (show (((2 * k * (k - 1) ^ (2 * (k * k))) ^ 2 : ℕ) : ℝ) ≤ (D : ℝ) by exact_mod_cast hh)
  let A₀ : ℝ := (2 * (R : ℝ)) ^ 2 * B * F * ((2 ^ R : ℕ) : ℝ) ^ (1 / 2 : ℝ)
  have hA₀ : 0 < A₀ := by
    have hRR : (0 : ℝ) < R := by exact_mod_cast hRpos
    dsimp only [A₀, F]
    positivity
  let A := max 1 (A₀ * ((2 ^ Q : ℕ) : ℝ) ^ L)
  have hlam1 : 1 < lam := by
    have hc := critical_exponent_gt_one (by omega : 2 ≤ k) (le_rfl : k ≤ k)
    have hd : 0 < relativeDefect k q := by unfold relativeDefect; positivity
    linarith
  let C' := C * F
  have hC' : 1 ≤ C' := by dsimp only [C']; nlinarith only [hC, hF]
  have hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → 1 ≤ X / p ^ e + 1 →
      meanValue ((k + 1) * k) k (X / p ^ e + 1) ≤ C' * ((X : ℝ) / (p : ℝ) ^ e) ^ lam := by
    intro p e X hp hX hN
    have he := VinogradovImprovedNormalization.rounded_actual_meanValue
      (zero_le_one.trans hC) (by linarith : 0 ≤ lam) hp hX hN hJ
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hlamhi) (zero_le_one.trans hC)
  let mu := lam + beta / (Q : ℝ)
  have hmu0 : 0 < mu := by
    have hdiv : -(1 / 2 : ℝ) ≤ beta / (Q : ℝ) := (le_div_iff₀ hQ0).mpr (by nlinarith)
    dsimp only [mu]
    linarith
  have hmuhi : mu ≤ L := by
    have hdiv : beta / (Q : ℝ) ≤ 0 := (div_neg_of_neg_of_pos hbeta hQ0).le
    dsimp only [mu, L]
    linarith only [hlamhi, hdiv]
  have hmu_eq : lam - eps = mu := by dsimp only [mu, eps, exponentStep, beta, Q]; ring
  have hcut (M : ℕ) (hDM : D < M) :
      meanValue ((k + 1) * k) k ((2 ^ R * M) ^ Q) ≤
        (A₀ * C) * (((2 ^ R * M) ^ Q : ℕ) : ℝ) ^ mu := by
    have hM : 1 < M := by omega
    have hpacketX := VinogradovInitialIteration.packet_budget_at_power_cutoff M R k S
      hM (hpacket.trans hDM.le) (by simpa only [Q, packetDepth, Nat.add_comm 1 S] using hR)
    have hsizeX : 4 * k ^ 4 ≤ (2 ^ R * M) ^ Q := by
      have he : M ≤ 2 ^ R * M := Nat.le_mul_of_pos_left _ (by positivity)
      exact hsize.trans (hDM.le.trans (he.trans (Nat.le_pow (by omega))))
    obtain ⟨hXdepth, _⟩ := power_cutoff_quotient (2 ^ R) M S (by positivity) (by omega)
    have he := relative_defect_global_bound k q hk hq C' hC' lam 1 hdefect hbudget M R ((2 ^ R * M) ^ Q) (by omega) hRpos
      (by simpa only [Q, packetDepth, Nat.add_comm 1 S] using hpacketX) hsizeX hXdepth
      (by exact Nat.succ_le_succ (Nat.zero_le _)) (hprime.trans (by exact_mod_cast hDM.le))
    have hid := power_cutoff_scale_identity Q (by omega) (A := ((2 ^ R : ℕ) : ℝ))
      (M := (M : ℝ)) (by positivity) (by exact_mod_cast (by omega : 0 < M)) lam beta
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hid he ⊢
    apply he.trans_eq
    calc
      _ = ((2 * (R : ℝ)) ^ 2 * (C' * B)) *
          ((((2 : ℝ) ^ R * M) ^ Q) ^ lam * (M : ℝ) ^ beta) := by
        dsimp only [B, profileMultiplier, beta]
        ring
      _ = _ := by rw [hid]; dsimp only [A₀, mu, C', beta, B, profileMultiplier]; simp only [neg_neg]; push_cast; ring
  change meanValue ((k + 1) * k) k X ≤ (A * C) * (X : ℝ) ^ (lam - eps)
  rw [hmu_eq]
  obtain ⟨M, hDM, hXY, hYX⟩ := exists_nearby_power_cutoff (2 ^ R) Q D X
    (by positivity) (by omega) (by omega) (Nat.lt_of_succ_le hX)
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((2 ^ R * M) ^ Q : ℕ))
    (by exact_mod_cast hYX : (((2 ^ R * M) ^ Q : ℕ) : ℝ) ≤ ((2 ^ Q * X : ℕ) : ℝ)) hmu0.le
  apply (meanValue_mono ((k + 1) * k) k hXY).trans ((hcut M hDM).trans _)
  calc
    _ ≤ (A₀ * C) * ((2 ^ Q * X : ℕ) : ℝ) ^ mu := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (A₀ * ((2 ^ Q : ℕ) : ℝ) ^ mu) * C * (X : ℝ) ^ mu := by
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hC)
      apply le_trans _ (le_max_right _ _)
      apply mul_le_mul_of_nonneg_left _ hA₀.le
      exact Real.rpow_le_rpow_of_exponent_le (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := Q))) hmuhi

/-- The specified exponent decrement is strictly positive. -/
theorem exponentStep_pos (k q : ℕ) : 0 < exponentStep k q := by
  unfold exponentStep packetDepth
  positivity

/-- Both endpoint regimes retain a homogeneous multiplier at least one. -/
theorem descentMultiplier_ge_one (k q : ℕ) : 1 ≤ descentMultiplier k q := by
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- The evaluated exponent improvement holds at every positive endpoint,
including the entire interval below the explicit packet cutoff. -/
theorem all_endpoint_improvement (k q : ℕ) (hk : 4 ≤ k) (hq : 0 < q)
    (lam : ℝ)
    (hdefect : relativeDefect k q ≤ lam - 2 * (k : ℝ) * ((k : ℝ) + 1) +
      (k : ℝ) * ((k : ℝ) + 1) / 2)
    (hlamhi : lam ≤ ((k * (2 * k + 1) : ℕ) : ℝ))
    (C : ℝ) (hC : 1 ≤ C)
    (hJ : ∀ X : ℕ, 1 ≤ X → meanValue ((k + 1) * k) k X ≤ C * (X : ℝ) ^ lam)
    (X : ℕ) (hX : 1 ≤ X) :
    meanValue ((k + 1) * k) k X ≤
      (descentMultiplier k q * C) * (X : ℝ) ^ (lam - exponentStep k q) := by
  by_cases hlarge : endpointCutoff k q ≤ X
  · exact (eventual_improvement k q hk hq lam hdefect hlamhi C hC hJ X hlarge).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (zero_le_one.trans hC)) (by positivity))
  · have hXp : (0 : ℝ) < X := by exact_mod_cast hX
    have hpow : (X : ℝ) ^ exponentStep k q ≤ descentMultiplier k q :=
      (Real.rpow_le_rpow hXp.le (by exact_mod_cast (show X ≤ endpointCutoff k q by omega))
        (exponentStep_pos k q).le).trans (le_max_right _ _)
    apply (hJ X hX).trans
    calc
      _ = (C * (X : ℝ) ^ (lam - exponentStep k q)) * (X : ℝ) ^ exponentStep k q := by
        rw [mul_assoc, ← Real.rpow_add hXp]
        congr 2
        ring
      _ ≤ (C * (X : ℝ) ^ (lam - exponentStep k q)) * descentMultiplier k q :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring

/-- A fixed upper bound on the number of global exponent improvements. -/
def iterationCount (k q : ℕ) : ℕ := k * (k - 1) * packetDepth k q + 1

/-- The complete coefficient, including elementary factorial data and all
global iterations, is a specified function of degree and relative accuracy. -/
def momentMultiplier (k q : ℕ) : ℝ :=
  descentMultiplier k q ^ iterationCount k q * (k.factorial : ℝ)

/-- The explicit high-moment coefficient is positive at every degree. -/
theorem momentMultiplier_pos (k q : ℕ) : 0 < momentMultiplier k q := by
  have hA : 0 < descentMultiplier k q := zero_lt_one.trans_le (descentMultiplier_ge_one k q)
  unfold momentMultiplier
  positivity

/-- An unconditional original mean-value bound with every constant specified.
The proof starts at the elementary factorial bound and discharges all
homogeneous source budgets by a finite, quantitatively bounded descent. -/
theorem relative_moment_bound (k q : ℕ) (hk : 4 ≤ k) (hq : 0 < q) (hqk : q ≤ k ^ 2)
    (X : ℕ) (hX : 1 ≤ X) :
    meanValue ((k + 1) * k) k X ≤ momentMultiplier k q * (X : ℝ) ^
      (2 * (k : ℝ) * ((k : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + relativeDefect k q) := by
  let c := 2 * (k : ℝ) * ((k : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2
  let L : ℝ := ((k * (2 * k + 1) : ℕ) : ℝ)
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hcL : c ≤ L := by
    dsimp only [c, L]
    push_cast
    nlinarith only [hkR, sq_nonneg ((k : ℝ) - 2)]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd1 : 1 ≤ relativeDefect k q := by
    unfold relativeDefect
    apply (le_div_iff₀ hqR).mpr
    simpa only [one_mul, Nat.cast_pow] using (show (q : ℝ) ≤ ((k ^ 2 : ℕ) : ℝ) by exact_mod_cast hqk)
  have hQ1 : (1 : ℝ) ≤ packetDepth k q := by
    exact_mod_cast (show 1 ≤ packetDepth k q by unfold packetDepth; omega)
  have hQ0 : (0 : ℝ) < packetDepth k q := zero_lt_one.trans_le hQ1
  have hepshalf : exponentStep k q ≤ 1 / 2 := by
    unfold exponentStep
    exact (div_le_iff₀ hQ0).mpr (by nlinarith only [hQ1])
  have hepsd : exponentStep k q ≤ relativeDefect k q / 2 := by linarith only [hepshalf, hd1]
  have hbase (Y : ℕ) (_hY : 1 ≤ Y) : meanValue ((k + 1) * k) k Y ≤
      (k.factorial : ℝ) * (Y : ℝ) ^ L := by
    simpa only [L, Real.rpow_natCast, mul_comm] using higher_meanValue_elementary k k Y
  have hA := descentMultiplier_ge_one k q
  obtain ⟨n, _hcritical, hlast, hcount, hbound⟩ := finite_linear_exponent_descent
    (fun Y => meanValue ((k + 1) * k) k Y) hcL (zero_lt_one.trans_le hd1)
    (exponentStep_pos k q) hepsd hA
    (show (1 : ℝ) ≤ k.factorial by exact_mod_cast Nat.factorial_pos k) hbase
    (fun lam hlamlo hlamhi C hC hJ Y hY =>
      all_endpoint_improvement k q hk hq lam (by dsimp only [c] at hlamlo; linarith only [hlamlo])
        hlamhi C hC hJ Y hY)
  have hcount' : (n : ℝ) * exponentStep k q ≤ L - c + exponentStep k q :=
    hcount.trans (add_le_add
      (max_le (sub_nonneg.mpr hcL) (sub_le_self _ (zero_le_one.trans hd1))) (le_refl _))
  have htimes : exponentStep k q * (2 * (packetDepth k q : ℝ)) = 1 := by
    unfold exponentStep
    field_simp
  have hm := mul_le_mul_of_nonneg_right hcount' (show 0 ≤ 2 * (packetDepth k q : ℝ) by positivity)
  simp only [add_mul, mul_assoc, htimes, mul_one] at hm
  have hgap : L - c = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    dsimp only [L, c]
    push_cast
    ring
  have hsteps : ((iterationCount k q : ℕ) : ℝ) = (L - c) * (2 * (packetDepth k q : ℝ)) + 1 := by
    unfold iterationCount
    rw [hgap]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    ring
  have hn : n ≤ iterationCount k q := by exact_mod_cast hm.trans_eq hsteps.symm
  have hcoef : descentMultiplier k q ^ n * (k.factorial : ℝ) ≤ momentMultiplier k q :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hn) (Nat.cast_nonneg _)
  have hpower := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ X by exact_mod_cast hX) hlast.le
  exact (hbound X hX).trans (mul_le_mul hcoef hpower (by positivity) (momentMultiplier_pos k q).le)

/-- Even one global improvement pays at least an exponential in the packet
depth. This audits this explicit coefficient, not the optimal mean value. -/
theorem packet_power_le_descentMultiplier (k q : ℕ) (hk : 4 ≤ k) :
    (2 : ℝ) ^ packetDepth k q ≤ descentMultiplier k q := by
  let Q := packetDepth k q
  let R := packetCount k q
  let L : ℝ := ((k * (2 * k + 1) : ℕ) : ℝ)
  have hR1 : (1 : ℝ) ≤ R := by
    exact_mod_cast (show 1 ≤ R by unfold R packetCount; omega)
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast (show 1 ≤ k * (2 * k + 1) by nlinarith only [hk])
  have hB : 1 ≤ profileMultiplier k := by
    apply le_add_of_nonneg_right
    unfold selectionCost
    positivity
  have hF : 1 ≤ (2 : ℝ) ^ L := Real.one_le_rpow (by norm_num) (zero_le_one.trans hL1)
  have hG : 1 ≤ ((2 ^ R : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (Nat.one_le_pow R 2 (by norm_num))) (by norm_num)
  have hP : 1 ≤ (2 * (R : ℝ)) ^ 2 := one_le_pow₀ (by linarith only [hR1])
  have hprefix : 1 ≤ (2 * (R : ℝ)) ^ 2 * profileMultiplier k * (2 : ℝ) ^ L *
      ((2 ^ R : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hP hB) hF) hG
  have htail : (2 : ℝ) ^ Q ≤ ((2 ^ Q : ℕ) : ℝ) ^ L := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ = ((2 : ℝ) ^ Q) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hL1
  apply htail.trans
  apply le_trans _ (le_trans (le_max_right _ _) (le_max_left _ _))
  exact le_mul_of_one_le_left (by positivity) hprefix

/-- The accumulated bound is at least `2^(packetDepth^2)`. This lower bound
concerns our chosen allowance only; it is not a lower bound on `meanValue`
or an impossibility theorem for a sharper argument. -/
theorem packet_square_power_le_momentMultiplier (k q : ℕ) (hk : 4 ≤ k) :
    (2 : ℝ) ^ (packetDepth k q ^ 2) ≤ momentMultiplier k q := by
  have hA := descentMultiplier_ge_one k q
  have hcount : packetDepth k q ≤ iterationCount k q := by
    have hk1 : 1 ≤ k * (k - 1) := Nat.mul_pos (by omega) (by omega)
    have h := Nat.mul_le_mul_right (packetDepth k q) hk1
    unfold iterationCount
    omega
  calc
    _ = ((2 : ℝ) ^ packetDepth k q) ^ packetDepth k q := by rw [pow_two, pow_mul]
    _ ≤ descentMultiplier k q ^ packetDepth k q :=
      pow_le_pow_left₀ (by positivity) (packet_power_le_descentMultiplier k q hk) _
    _ ≤ descentMultiplier k q ^ iterationCount k q := pow_le_pow_right₀ hA hcount
    _ ≤ _ := le_mul_of_one_le_right (by positivity)
      (show (1 : ℝ) ≤ k.factorial by exact_mod_cast Nat.factorial_pos k)

end
end RiemannGaussian.VinogradovQuantitativeDescent
