/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.External.Zeta23ConsecutiveBlocks

/-!
# Counting endpoint for arbitrary consecutive-block certificates

A uniform kernel floor is transported through the literal sampling Gram,
the zero-side matrix inequality, and all endpoint errors. The block size
remains arbitrary throughout; no numerical floor is assumed to have been
verified merely by stating this transport theorem.
-/

namespace RiemannGaussian.Zeta23InverseSampling
noncomputable section
open Asymptotics Complex Filter Real Topology RHLinalg
open scoped BigOperators

/-- Eliminate the retained energy while keeping every block-size dependent
constant in the finite error ledger. -/
theorem block_seam_elimination
    {k A cinv N NII E R S pad q span eta bad : ℝ}
    (hk : 0 ≤ k) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (heta0 : 0 ≤ eta)
    (hbad0 : 0 ≤ bad)
    (hseam : (2 - cinv) * N + E - R ≤ S + pad)
    (hpack : A * q ≤ E + span + 6 * (k + 1) ^ 2 * eta * q)
    (hcount : S ≤ (k + 1) * q + 2 * k + bad)
    (hq : (k + 1) * q ≤ N + NII + k) (hpad : pad ≤ k) :
    (k + 1) * (2 - cinv) * N -
        ((k + 1) * R + (k + 1) * span +
          6 * (k + 1) ^ 2 * eta * (N + NII + k) +
          (k ^ 2 + 3 * k) + bad) ≤
      (k + 1 - A) * S := by
  have hAS := mul_le_mul_of_nonneg_left hcount hA0
  have hpackM := mul_le_mul_of_nonneg_left hpack (by positivity : 0 ≤ k + 1)
  have hseamM := mul_le_mul_of_nonneg_left hseam (by positivity : 0 ≤ k + 1)
  have hqerr := mul_le_mul_of_nonneg_left hq
    (by positivity : 0 ≤ 6 * (k + 1) ^ 2 * eta)
  have hpadM := mul_le_mul_of_nonneg_left hpad (by positivity : 0 ≤ k + 1)
  have hAbad := mul_le_mul_of_nonneg_right hA1 hbad0
  have hAk := mul_le_mul_of_nonneg_right hA1 (by positivity : 0 ≤ 2 * k)
  nlinarith

/-- The complete finite-height inequality for a uniform arbitrary-block kernel floor. -/
theorem endpointBlockAffine_finite
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} (hP : P.Valid)
    (hlam : P.lam = 1) {T : ℝ}
    (hT4 : 4 ≤ T)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2)
    (hconj : Zeta23.ZeroSide.PhiHatConj T (P.atD T))
    (hreal : Zeta23.ZeroSide.PhiHatReal T (P.atD T))
    (hPois : Zeta23.ZeroSide.PoissonSq T (P.atD T))
    {θ₀ : ℝ} (hTl : Zeta23.Assembly.TailInputs Z (P.atD T) T θ₀)
    {R₁ R₂ cinv : ℝ}
    (htr : |rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        (Z.N T (2 * T) : ℝ)| ≤ R₁)
    (hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) ≤
      cinv * (Z.N T (2 * T) : ℝ) + R₂)
    (k : ℕ) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 < B) (hA1 : A ≤ 1)
    (hcert : ∀ x : ℕ → ℝ, Monotone x →
      A ≤ MontgomeryTaylorWindowEnergy.lagEnergy
        (fun t => montgomeryTaylorKernel t ^ 2) x (k + 1) + B * (x k - x 0))
    (herr1 : endpointSamplerError P T ≤ 1) :
    (k + 1 : ℕ) * (2 - cinv) * (Z.N T (2 * T) : ℝ) -
        ((k + 1 : ℕ) * (4 * R₁ + R₂ +
            3 * (Zeta23.Assembly.NII Z T : ℝ) +
            θ₀ / ((P.atD T).a T * P.L T) *
              (4 + 2 * Real.sqrt
                (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
                θ₀ / ((P.atD T).a T * P.L T))) +
          (k : ℝ) * B * P.L T * T +
          6 * (k + 1 : ℕ) ^ 2 * endpointSamplerError P T *
            ((Z.N T (2 * T) : ℝ) +
              (Zeta23.Assembly.NII Z T : ℝ) + k) +
          ((k : ℝ) ^ 2 + 3 * k) +
          ((nonInteriorSimpleZeros Z (P.atD T) T hconj).card : ℝ)) ≤
      ((k + 1 : ℕ) - A) * (Z.N0s T (2 * T) : ℝ) := by
  classical
  have hT0 : 0 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have ha : 0 < (P.atD T).a T := by
    linarith [(Zeta23.ThmD.aD_range_of hP h8 h4pi).1]
  have heta0 : 0 ≤ endpointSamplerError P T :=
    endpointSamplerError_nonneg hP h8 h4pi hTpos
  let α := (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj).S₁
  let Q : ℕ := (Fintype.card α + k) / (k + 1)
  let pad : ℕ := (k + 1) * Q - Fintype.card α
  obtain ⟨q, e, hqQ, hcard, hpad, henergy⟩ :=
    exists_literalBlockEnergy_affine_lower
      hP hlam hT4 h8 h4pi hgrid hconj k hB0 hA1 hcert herr1
  have hqQLocal : q ≤ Q := by
    simpa only [Q, α] using hqQ
  have hpadLocal : pad ≤ k := by
    simpa only [pad, Q, α] using hpad
  let E : ℝ := ∑ b : Fin Q, min
    (ZeroBlockData.offDiagEnergy
      ((zetaSimpleBlockGram hconj e).submatrix
        (fun j : Fin (k + 1) => (j, b))
        (fun j : Fin (k + 1) => (j, b)))) 1
  let tailLoss : ℝ :=
    θ₀ / ((P.atD T).a T * P.L T) *
      (4 + 2 * Real.sqrt
        (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
        θ₀ / ((P.atD T).a T * P.L T))
  let R : ℝ := 4 * R₁ + R₂ +
    3 * (Zeta23.Assembly.NII Z T : ℝ) + tailLoss
  let span : ℝ := ((k : ℝ) * B * P.L T * T) / (k + 1 : ℕ)
  let bad : ℝ :=
    ((nonInteriorSimpleZeros Z (P.atD T) T hconj).card : ℝ)
  have hseamRaw := seamA_mult2_blockCertificate
    (Z := Z) (P := P.atD T) hT0 hconj hreal hPois hTl ha hL e
  simp only [Zeta23.Params.atD_L, Fintype.card_fin] at hseamRaw
  have hseam :
      (2 - cinv) * (Z.N T (2 * T) : ℝ) + E - R ≤
        (Z.N0s T (2 * T) : ℝ) + (pad : ℝ) := by
    have htrlo : (Z.N T (2 * T) : ℝ) - R₁ ≤
        rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) := by
      linarith [(abs_le.mp htr).1]
    dsimp only [E, R, tailLoss, pad, Q, α] at hseamRaw ⊢
    linarith [hfr]
  have hpack : A * (q : ℝ) ≤
      E + span + 6 * ((k : ℝ) + 1) ^ 2 * endpointSamplerError P T * (q : ℝ) := by
    simpa only [E, span, Q, α, Nat.cast_add, Nat.cast_one] using henergy
  have hcountNat : Z.N0s T (2 * T) ≤
      (k + 1) * q + 2 * k + (nonInteriorSimpleZeros Z (P.atD T) T hconj).card := by
    have hwhole := N0s_le_interior_add_nonInterior
      (Z := Z) (P := P.atD T) hconj
    omega
  have hcount : (Z.N0s T (2 * T) : ℝ) ≤
      (k + 1 : ℕ) * (q : ℝ) + 2 * k + bad := by
    dsimp only [bad]
    exact_mod_cast hcountNat
  have hqNat : (k + 1) * q ≤ Z.N T (2 * T) +
      Zeta23.Assembly.NII Z T + k := by
    have hα : Fintype.card α = Z.s1 T := by
      dsimp only [α]
      exact card_blockData_S₁_eq_s1 hconj
    have hs1 := Zeta23.Assembly.s1_le Z hT0
    have hSN : Z.N0s T (2 * T) ≤ Z.N T (2 * T) :=
      (Z.trivial_chain T (2 * T)).1.trans
        ((Z.trivial_chain T (2 * T)).2.1.trans
          (Z.trivial_chain T (2 * T)).2.2.1)
    have hαQ : Fintype.card α ≤ (k + 1) * Q := by
      dsimp only [Q]
      exact (ConsecutiveBlockPacking.ceiling_bounds _ _).1
    have hQpad : (k + 1) * Q = Fintype.card α + pad := by
      dsimp only [pad]
      omega
    have hqMul := Nat.mul_le_mul_left (k + 1) hqQLocal
    omega
  have hq : (k + 1 : ℕ) * (q : ℝ) ≤
      (Z.N T (2 * T) : ℝ) +
        (Zeta23.Assembly.NII Z T : ℝ) + k := by
    exact_mod_cast hqNat
  have hpadR : (pad : ℝ) ≤ k := by exact_mod_cast hpadLocal
  have hbad0 : 0 ≤ bad := by
    dsimp only [bad]
    positivity
  simp only [Nat.cast_add, Nat.cast_one] at hcount hq
  have hfinal := block_seam_elimination (Nat.cast_nonneg k)
    hA0 hA1 heta0 hbad0 hseam hpack hcount hq hpadR
  dsimp only [R, span, tailLoss, bad] at hfinal ⊢
  simp only [Nat.cast_add, Nat.cast_one] at hfinal ⊢
  have hM : (k : ℝ) + 1 ≠ 0 := by positivity
  convert hfinal using 1
  field_simp


set_option maxHeartbeats 2000000 in
/-- All analytic endpoint errors vanish for every fixed block size. The only
new input is a uniform floor for the explicit limiting kernel energy. -/
theorem thmD_endpoint_block_abstract
    (Z : Zeta23.ZeroConfig) (H : Zeta23.PaperInputs Z)
    (P : Zeta23.Params) (hP : P.Valid) (hlam : P.lam = 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : Zeta23.ThmD.TracesBoundsD P aT bT JT trG trG2
      (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => Zeta23.ThmD.cRatio
      (P.lam1 T) (aT T) (bT T) (JT T)) atTop (nhds c))
    (haRange : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ)
    (hTail : ∀ᶠ T in atTop,
      Zeta23.Assembly.TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop,
      θ₀ T ≤ C * Zeta23.l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop,
      (Zeta23.Assembly.NII Z T : ℝ) ≤
        C * Real.sqrt T * Zeta23.l T)
    (hGzGp : ∀ᶠ T in atTop,
      Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = trG T ∧
      (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (nhds 0))
    (k : ℕ) (hk : 1 ≤ k)
    {A B : ℝ} (hA0 : 0 < A) (hB0 : 0 < B) (hA1 : A ≤ 1)
    (hcert : ∀ x : ℕ → ℝ, Monotone x →
      A ≤ MontgomeryTaylorWindowEnergy.lagEnergy
        (fun t => montgomeryTaylorKernel t ^ 2) x (k + 1) + B * (x k - x 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (((k + 1 : ℕ) * (2 - c⁻¹) - 2 * (k : ℝ) * Real.pi * B) / ((k + 1 : ℕ) - A) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        Z.N0s T (2 * T) := by
  have hlam0 : 0 < P.lam := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hP.lam_le_one
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  let hconjD : ∀ T : ℝ,
      Zeta23.ZeroSide.PhiHatConj T (P.atD T) := fun T =>
    Zeta23.ZeroSide.phiHatConj
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T =>
    (Zeta23.ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹
      with hcinv
  set R₁ : ℝ → ℝ := fun T =>
    C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T =>
    C₂ * P.calE T * (cinv T * N T) with hR₂
  set Bt : ℝ → ℝ := fun T =>
    θ₀ T / (aT T * P.L T) with hBt
  set eta : ℝ → ℝ := endpointSamplerError P with heta
  set bad : ℝ → ℝ := fun T =>
    ((nonInteriorSimpleZeros Z (P.atD T) T (hconjD T)).card : ℝ)
      with hbad
  set baseR : ℝ → ℝ := fun T =>
    4 * R₁ T + R₂ T + 3 * (Zeta23.Assembly.NII Z T : ℝ) +
      Bt T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + Bt T)
      with hbaseR
  set Cnum : ℝ := (k + 1 : ℕ) * (2 - c⁻¹) - 2 * (k : ℝ) * Real.pi * B with hCnum
  set err : ℝ → ℝ := fun T =>
    (k + 1 : ℕ) * baseR T +
      6 * (k + 1 : ℕ) ^ 2 * eta T * (N T + (Zeta23.Assembly.NII Z T : ℝ) + k) +
      ((k : ℝ) ^ 2 + 3 * k) + bad T +
      (k + 1 : ℕ) * |cinv T - c⁻¹| * N T +
      (k : ℝ) * B * |P.L T * T - 2 * Real.pi * N T| with herr
  have hLtop := Zeta23.ThmD.tendsto_L hP
  have hcinvTo : Tendsto cinv atTop (nhds c⁻¹) := hc.inv₀ hc0.ne'
  have h4pi : ∀ᶠ T in atTop, 4 * Real.pi * P.w ≤ P.L T :=
    hLtop.eventually_ge_atTop (4 * Real.pi * P.w)
  have hgrid : ∀ᶠ T in atTop,
      2 * Real.pi / P.L T ≤ Real.sqrt T / 2 := by
    filter_upwards [h4pi, eventually_ge_atTop (1 : ℝ)] with T hL hT
    have hLpos : 0 < P.L T := by
      nlinarith [hP.one_le_w, Real.pi_pos]
    have hs : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr hT
    rw [div_le_iff₀ hLpos]
    have hhalf : (1 / 2 : ℝ) ≤ Real.sqrt T / 2 := by linarith
    have hw0 : 0 ≤ 4 * Real.pi * P.w :=
      mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (zero_le_one.trans hP.one_le_w)
    have hs0 : 0 ≤ Real.sqrt T / 2 := by positivity
    have hm := mul_le_mul hhalf hL hw0 hs0
    have hbase : 2 * Real.pi ≤ (1 / 2 : ℝ) *
        (4 * Real.pi * P.w) := by
      have hw := mul_le_mul_of_nonneg_left hP.one_le_w
        (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith
    exact hbase.trans hm
  have hetaTo : Tendsto eta atTop (nhds 0) := by
    simpa only [eta] using tendsto_endpointSamplerError_zero hP
  have heta1 : ∀ᶠ T in atTop, eta T ≤ 1 :=
    hetaTo.eventually (eventually_le_nhds (by norm_num))
  have hmain : ∀ᶠ T in atTop,
      Cnum * N T - err T ≤ ((k + 1 : ℕ) - A) * (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hTail, hGzGp, hId, haRange,
      eventually_ge_atTop T₁, eventually_ge_atTop T₂,
      eventually_ge_atTop Zeta23.Tail.T₀, eventually_ge_atTop (4 : ℝ),
      Zeta23.Assembly.eventually_l_pos,
      Zeta23.Assembly.eventually_calE_nonneg P hlam0
        (zero_le_one.trans hP.one_le_w),
      Zeta23.ThmD.eventually_w8 hP, h4pi, hgrid, heta1]
      with T hTl hGG hid haT hT₁ hT₂ hTailT hT4 hl hE0 h8 h4 hgr he1
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos : 0 < aT T := by linarith [haT.1]
    have hLpos : 0 < P.L T := by
      simp only [Zeta23.Params.L]
      exact mul_pos hlam0 hl
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) =
        (aT T * P.L T)⁻¹ * trG T := by
      rw [Zeta23.Assembly.rtrace_hat, hGG,
        Zeta23.Assembly.rtrace_tilde_Gp, hidtr, hida]
      rfl
    have hfrEq : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) =
        ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [Zeta23.Assembly.frobSq_hat, hGG,
        Zeta23.Assembly.frobSq_tilde_Gp, hidfr, hida]
      rfl
    have htrBound : |rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        N T| ≤ R₁ T := by
      rw [hrt]
      exact Zeta23.Assembly.trGhat_sub_N_le hapos hLpos
        (by simpa only [N, R₁] using htr1 T hT₁)
    have hfrBound : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) ≤
        cinv T * N T + R₂ T := by
      rw [hfrEq]
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤
          C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have heq : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T =
          trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [heq]
      simp only [R₂]
      linarith
    have hfinite := endpointBlockAffine_finite hP hlam hT4 h8 h4 hgr
      (hconjD T) Zeta23.ZeroSide.phiHatReal
      (Zeta23.ThmD.poissonSqD hP h8) hTl htrBound hfrBound
      k hA0.le hB0 hA1 hcert he1
    have hBt0 : 0 ≤ Bt T := by
      simp only [Bt]
      exact div_nonneg hTl.theta_nonneg (mul_pos hapos hLpos).le
    have hsqrt := Real.sqrt_le_sqrt hfrBound
    have htailLe :
        θ₀ T / ((P.atD T).a T * P.L T) *
            (4 + 2 * Real.sqrt
              (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
              θ₀ T / ((P.atD T).a T * P.L T)) ≤
          Bt T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + Bt T) := by
      rw [hida]
      simp only [Bt]
      exact mul_le_mul_of_nonneg_left (by linarith) hBt0
    have hDynamic :
        (k + 1 : ℕ) * (2 - cinv T) * N T - (k : ℝ) * B * P.L T * T -
            ((k + 1 : ℕ) * baseR T +
              6 * (k + 1 : ℕ) ^ 2 * eta T *
                (N T + (Zeta23.Assembly.NII Z T : ℝ) + k) +
              ((k : ℝ) ^ 2 + 3 * k) + bad T) ≤
          ((k + 1 : ℕ) - A) * (Z.N0s T (2 * T) : ℝ) := by
      simp only [N, cinv, R₁, R₂] at hfinite
      simp only [baseR, N, cinv, R₁, R₂, Bt, eta, bad]
      have htailScaled := mul_le_mul_of_nonneg_left htailLe
        (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ (k + 1 : ℕ))
      nlinarith
    have hN0 : 0 ≤ N T := by
      simp only [N]
      positivity
    have hcinvDrift := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0)
      (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ (k + 1 : ℕ))
    have hspanDrift := mul_le_mul_of_nonneg_left
      (le_abs_self (P.L T * T - 2 * Real.pi * N T))
      (show 0 ≤ (k : ℝ) * B by positivity)
    simp only [Cnum, err]
    nlinarith
  have hNtop : Tendsto N atTop atTop :=
    Zeta23.Assembly.tendsto_N_atTop Z H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1 : ℝ)) := by
      refine Zeta23.Assembly.isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [haRange] with T haT
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [haT.1]))]
      rw [div_le_iff₀ (by linarith [haT.1])]
      nlinarith [haT.1]
    have ho := Zeta23.Assembly.isLittleO_of_bdd_mul hbd
      (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z H.RvM
        (Zeta23.Assembly.isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact ho.congr_left fun T => by simp only [R₁]; ring
  have hcinvBd : ∀ᶠ T in atTop,
      0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinvTo.eventually (eventually_ge_nhds hcpos),
      hcinvTo.eventually
        (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))]
      with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1 : ℝ)) := by
    refine Zeta23.Assembly.isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinvBd] with T h
    rw [abs_of_nonneg h.1]
    exact h.2
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (nhds 0) := by
      simpa using hcalE.const_mul C₂
    have hi : (fun T => cinv T * N T) =O[atTop] N := by
      simpa using hcinvO.mul (isBigO_refl N atTop)
    have ho := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO hi
    refine (ho.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [R₂]
  have o3 : (fun T => (Zeta23.Assembly.NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (Zeta23.Assembly.NII Z T : ℝ))
        =O[atTop] (fun T => Real.sqrt T * Zeta23.l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, Zeta23.Assembly.eventually_l_pos]
        with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO
      (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z H.RvM
        Zeta23.Assembly.isLittleO_sqrt_mul_l_Tl)
  have oBt : Tendsto Bt atTop (nhds 0) := by
    have hup : Tendsto (fun T =>
        2 * |Cθ| *
          (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T))
        atTop (nhds 0) := by
      simpa using
        (Zeta23.Assembly.tendsto_theta_over_L P hlam0 hlam1).const_mul
          (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, haRange, Zeta23.Assembly.eventually_l_pos]
        with T hTl haT hl
      have hLpos : 0 < P.L T := by
        simp only [Zeta23.Params.L]
        exact mul_pos hlam0 hl
      simp only [Bt]
      exact div_nonneg hTl.theta_nonneg (by nlinarith [haT.1])
    · filter_upwards [hTail, haRange, Zeta23.Assembly.eventually_l_pos,
        hθ, eventually_gt_atTop (0 : ℝ)]
        with T hTl haT hl hθT hT0
      have hLpos : 0 < P.L T := by
        simp only [Zeta23.Params.L]
        exact mul_pos hlam0 hl
      have hapos : 0 < aT T := by linarith [haT.1]
      have hq0 : 0 ≤ Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T := by
        positivity
      simp only [Bt]
      rw [div_le_iff₀ (mul_pos hapos hLpos)]
      calc
        θ₀ T ≤ Cθ * Zeta23.l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * Zeta23.l T * T ^ (P.lam / 2 - 1) := by
          gcongr
          exact le_abs_self _
        _ = |Cθ| *
            (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by
          field_simp
        _ ≤ (2 * |Cθ| *
            (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T)) *
              (aT T * P.L T) := by
          have heq : |Cθ| *
              (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T =
            (2 * |Cθ| *
              (Zeta23.l T * T ^ (P.lam / 2 - 1) / P.L T)) *
                (1 / 2 * P.L T) := by ring
          rw [heq]
          have hinner : 1 / 2 * P.L T ≤ aT T * P.L T :=
            mul_le_mul_of_nonneg_right haT.1 hLpos.le
          exact mul_le_mul_of_nonneg_left hinner
            (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg Cθ)) hq0)
  have obase : baseR =o[atTop] N := by
    have h := Zeta23.Assembly.err_isLittleO hNtop o1 o2 o3 oBt hcinvBd
    simpa only [baseR] using h
  have hsumO : (fun T =>
      N T + (Zeta23.Assembly.NII Z T : ℝ) + k) =O[atTop] N := by
    have hconst : (fun _ : ℝ => (k : ℝ)) =O[atTop] N :=
      (constant_isLittleO_of_tendsto_atTop hNtop (k : ℝ)).isBigO
    exact ((isBigO_refl N atTop).add o3.isBigO).add hconst
  have oeta : (fun T =>
      6 * (k + 1 : ℕ) ^ 2 * eta T *
        (N T + (Zeta23.Assembly.NII Z T : ℝ) + k)) =o[atTop] N := by
    have hetaOne : eta =o[atTop] (fun _ => (1 : ℝ)) :=
      (isLittleO_one_iff ℝ).2 hetaTo
    have h := hetaOne.mul_isBigO hsumO
    have h' : (fun T => eta T *
        (N T + (Zeta23.Assembly.NII Z T : ℝ) + k)) =o[atTop] N := by
      simpa using h
    exact (h'.const_mul_left (6 * (k + 1 : ℕ) ^ 2)).congr_left (fun T => by ring)
  have obad : bad =o[atTop] N := by
    have h := nonInteriorSimpleZeros_isLittleO_N Z H.RvM P hconjD
    simpa only [bad, N] using h
  have oconst : (fun _ : ℝ => ((k : ℝ) ^ 2 + 3 * k)) =o[atTop] N := by
    exact constant_isLittleO_of_tendsto_atTop hNtop ((k : ℝ) ^ 2 + 3 * k)
  have ocinv : (fun T => (k + 1 : ℕ) * |cinv T - c⁻¹| * N T) =o[atTop] N := by
    exact const_mul_abs_sub_mul_isLittleO (N := N) (k := (k + 1 : ℕ)) hcinvTo
  have ospan : (fun T =>
      (k : ℝ) * B * |P.L T * T - 2 * Real.pi * N T|) =o[atTop] N := by
    rw [hNdef]
    exact endpoint_span_abs_isLittleO Z H.RvM P hlam ((k : ℝ) * B)
  have herrO : err =o[atTop] N := by
    have hsum := (((((obase.const_mul_left (k + 1 : ℕ)).add oeta).add oconst).add obad).add
      ocinv).add ospan
    simpa only [err] using hsum
  have hnum := Zeta23.Assembly.eps_form_of_isLittleO hmain
    (Eventually.of_forall fun T => by simp only [N]; positivity) herrO
  intro ε hε
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < (k + 1 : ℕ) - A := by
    push_cast
    linarith
  obtain ⟨T₀, hT₀⟩ := hnum (((k + 1 : ℕ) - A) * ε) (mul_pos hd hε)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have heq : Cnum - ((k + 1 : ℕ) - A) * ε =
      ((k + 1 : ℕ) - A) * (Cnum / ((k + 1 : ℕ) - A) - ε) := by
    field_simp
  rw [heq] at h
  have hmul : ((k + 1 : ℕ) - A) *
      ((Cnum / ((k + 1 : ℕ) - A) - ε) * N T) ≤
        ((k + 1 : ℕ) - A) * (Z.N0s T (2 * T) : ℝ) := by
    simpa only [mul_assoc] using h
  have hout : (Cnum / ((k + 1 : ℕ) - A) - ε) * N T ≤
      (Z.N0s T (2 * T) : ℝ) := le_of_mul_le_mul_left hmul hd
  simpa only [Cnum] using hout


/-- The concrete Zeta23 construction discharges every analytic input of
the arbitrary-block endpoint. The explicit kernel floor remains to be supplied. -/
theorem thmD_endpoint_block_concrete
    (Z : Zeta23.ZeroConfig) (H : Zeta23.PaperInputs Z)
    (P : Zeta23.Params) (hP : P.Valid) (hlam : P.lam = 1)
    (k : ℕ) (hk : 1 ≤ k) {A B : ℝ} (hA0 : 0 < A) (hB0 : 0 < B) (hA1 : A ≤ 1)
    (hcert : ∀ x : ℕ → ℝ, Monotone x →
      A ≤ MontgomeryTaylorWindowEnergy.lagEnergy
        (fun t => montgomeryTaylorKernel t ^ 2) x (k + 1) + B * (x k - x 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (((k + 1 : ℕ) * Zeta23.ThmD.HD 1 - 2 * (k : ℝ) * Real.pi * B) / ((k + 1 : ℕ) - A) - ε) *
          (Z.N T (2 * T) : ℝ) ≤
        Z.N0s T (2 * T) := by
  have hLoc : Zeta23.ThmD.LocalHypsCoreDEventually P :=
    Zeta23.ThmD.localHypsCoreD_eventually hP
  have hTr := Zeta23.ThmD.tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := Zeta23.ThmD.tendsto_cRatio_concrete hP Z
  have hc0 := Zeta23.ThmD.cStar_pos hP.lam_pos hP.lam_le_one
  have haRange : ∀ᶠ T in atTop,
      1 / 2 ≤ (Zeta23.ThmD.concreteDataD P Z).aT T ∧
        (Zeta23.ThmD.concreteDataD P Z).aT T ≤ 1 :=
    (Zeta23.ThmD.concreteFactsD hP H hLoc).ab_range.mono fun T h =>
      ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ :=
    Zeta23.ThmD.eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Zeta23.Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := Zeta23.ThmD.eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (Zeta23.ThmD.concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (Zeta23.ThmD.concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (Zeta23.ThmD.concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Zeta23.Params.atD_trGtilde T hP,
        Zeta23.Params.atD_trGtildeSq T hP,
        Zeta23.Params.atD_a T hP⟩
  have hcalE := Zeta23.Assembly.calE_tendsto_zero P hP.lam_pos
    hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmD_endpoint_block_abstract Z H P hP hlam
    _ _ _ _ _ hTr hc0 hc haRange θ₀ hTail hθ₀ hNII hGzGp hId
      hcalE k hk hA0 hB0 hA1 hcert
  simpa only [Zeta23.ThmD.HD, hlam, one_div] using h


/-- A proved uniform block floor implies the displayed proportion for
literal simple critical-line zeros, with all nontrivial zeros counted with
analytic multiplicity in the denominator. This transfer alone does not
certify the still-to-be-supplied numerical floor. -/
theorem simpleCritical_of_blockFloor
    (k : ℕ) (hk : 1 ≤ k) {A B : ℝ}
    (hA0 : 0 < A) (hB0 : 0 < B) (hA1 : A ≤ 1)
    (hcert : ∀ x : ℕ → ℝ, Monotone x →
      A ≤ MontgomeryTaylorWindowEnergy.lagEnergy
        (fun t => montgomeryTaylorKernel t ^ 2) x (k + 1) + B * (x k - x 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (((k + 1 : ℕ) * Zeta23.ThmD.HD 1 - 2 * (k : ℝ) * Real.pi * B) /
          ((k + 1 : ℕ) - A) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) := by
  let P := Zeta23.paramsOf Zeta23.stdProfile 1
  have hP : P.Valid := Zeta23.paramsOf_valid Zeta23.taperProfile_stdProfile one_pos le_rfl
  have hlam : P.lam = 1 := rfl
  have hmain := thmD_endpoint_block_concrete Zeta23.zetaZeroConfig
    Zeta23.paperInputs_zeta P hP hlam k hk hA0 hB0 hA1 hcert
  simpa only [P, Zeta23.paramsOf, Zeta23.zetaZeroConfig_N,
    Zeta23.zetaZeroConfig_N0s] using hmain

end
end RiemannGaussian.Zeta23InverseSampling
