/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedPhysical

/-!+# One-sided cell transport for the full two-hinge physical core

This reduction keeps each signed unit-log cell assembled. An explicitly
UNPROVED one-sided arithmetic saving with any delta > u-1/2 suffices.
For the restricted radius, delta = 1/10000 gives ratio 10001/10002 < 1.
The old `LocalizedTypeIIBound` and its literal target are unchanged.
-/

namespace RiemannGaussian.ZetaRieszPhysicalCellFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJoinedPhysical ZetaRieszGammaJoint ZetaRieszParityPacket
open ZetaRieszWideOwnerAudit ZetaRieszPrimeCountFrequency

/-- One unit-log cell in the original squarefree core, retaining every mask. -/
def physicalCellBand (u : ℝ) (N K k : ℕ) : Finset ℕ :=
  ((coreBand u N K).filter Squarefree).filter (fun n => ⌊Real.log n⌋₊ = k)

/-- The whole signed cell is normalized only AFTER summing its full two-hinge
atoms. The complex phase, allocation and original finite support are intact. -/
def physicalCell (u y : ℝ) (N K k : ℕ) : ℂ :=
  (∑ n ∈ physicalCellBand u N K k, fullTranslatedAtom u y N n)/
    (ZetaRieszTypeII.cellScale (N+1) k : ℂ)

/-- Exact reconstruction uses a positive real scale and no cellwise norm. -/
theorem core_eq_physicalCells (u y : ℝ) (N K : ℕ) :
    coreResponse u y N K = ∑ k ∈ Finset.range (3*N+1),
      (ZetaRieszTypeII.cellScale (N+1) k : ℂ)*physicalCell u y N K k := by
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (coreBand u N K).filter Squarefree) (t := Finset.range (3*N+1))
    (fun n hn => Finset.mem_range.mpr (ZetaRieszTypeII.cell_index_lt
      (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1))
    (fun n => fullTranslatedAtom u y N n)
  rw [core_eq_fullTranslated,← h]
  apply Finset.sum_congr rfl
  intro k _
  change _ = (_ : ℂ)*(_/(_ : ℂ))
  rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr
    (ZetaRieszTypeII.cellScale_pos (N+1) k).ne')]
  rfl

/-- Arbitrary fixed saving, with the exact factorial normalization. -/
theorem cellScale_saving (M k : ℕ) {delta : ℝ} (hd : 0 < 1/2+delta) :
    ZetaRieszTypeII.cellScale M k*Real.exp ((1-delta)*k) ≤
      Real.exp (1/2+delta)*(1/(1/2+delta))^M := by
  have h := logMoment_exp_envelope M (by positivity : (0 : ℝ) ≤ (k+1 : ℝ))
    hd (1/2+delta)
  simp only [sub_self,neg_zero,zero_mul,Real.exp_zero,mul_one] at h
  calc
    _ = Real.exp (1/2+delta)*
        ((k+1 : ℝ)^M/(M.factorial : ℝ)*Real.exp (-(1/2+delta)*(k+1))) := by
      unfold ZetaRieszTypeII.cellScale
      rw [mul_assoc,← Real.exp_add,mul_left_comm,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      simpa only [one_div] using mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- This finite one-sided transport assumes the arithmetic saving openly.
It never replaces the signed cells by their norms. -/
theorem scaled_core_floor_of_cells {u delta C : ℝ}
    (hu : 0 ≤ u) (hd : 0 < 1/2+delta) (hC : 0 ≤ C)
    (y : ℝ) (N K A : ℕ)
    (hsave : ∀ k < 3*N+1,
      -(C*(N+1 : ℝ)^A*Real.exp ((1-delta)*k)) ≤ (physicalCell u y N K k).re) :
    -(3*C*Real.exp (1/2+delta)*(N+1 : ℝ)^(A+1)*(u/(1/2+delta))^(N+1)) ≤
      ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  let B := C*(N+1 : ℝ)^A*Real.exp (1/2+delta)*(1/(1/2+delta))^(N+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hc : -(3*N+1 : ℝ)*B ≤ (coreResponse u y N K).re := by
    rw [core_eq_physicalCells,Complex.re_sum]
    have hb k (hk : k ∈ Finset.range (3*N+1)) : -B ≤
        ((ZetaRieszTypeII.cellScale (N+1) k : ℂ)*physicalCell u y N K k).re := by
      have hh := mul_le_mul_of_nonneg_left (hsave k (Finset.mem_range.mp hk))
        (ZetaRieszTypeII.cellScale_pos (N+1) k).le
      have he := mul_le_mul_of_nonneg_left (cellScale_saving (N+1) k hd)
        (show 0 ≤ C*(N+1 : ℝ)^A by positivity)
      rw [Complex.re_ofReal_mul]
      dsimp [B]
      nlinarith
    have hs := Finset.sum_le_sum hb
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_neg,neg_mul] using hs
  have hn : -(3*(N+1 : ℝ))*B ≤ -(3*N+1 : ℝ)*B := by nlinarith
  have hs := mul_le_mul_of_nonneg_left (hn.trans hc) (pow_nonneg hu (N+1))
  have he : (u^(N+1)*(-(3*(N+1 : ℝ))*B)) =
      -(3*C*Real.exp (1/2+delta)*(N+1 : ℝ)^(A+1)*(u/(1/2+delta))^(N+1)) := by
    dsimp [B]
    simp only [div_eq_mul_inv,mul_pow,one_mul]
    rw [pow_succ (N+1 : ℝ)]
    ring
  rw [he] at hs
  simpa only [← Complex.ofReal_pow,Complex.re_ofReal_mul] using hs

/-- The new physical-cell target needs only a 1/10000 length saving on the
current radius interval. This rational calculation proves NO arithmetic input. -/
theorem restricted_saving_ratio :
    radiusCeiling/(1/2+(1/10000 : ℝ)) = 10001/10002 ∧
      (0 : ℝ) < 10001/10002 ∧ (10001/10002 : ℝ) < 1 := by
  norm_num [radiusCeiling]

/-- A one-sided saving for the assembled cells gives a vanishing floor
error for the EXISTING joinedPhysical. The arithmetic hypothesis is open;
this theorem pays only factorial transport and the known boundary. -/
theorem exists_joined_floor_error_of_cells {u delta C : ℝ}
    (hu : 0 < u) (hU : u ≤ radiusCeiling) (hd : u < 1/2+delta)
    (hC : 0 ≤ C) (y : ℝ) (A : ℕ) (orders counts : ℕ → ℕ)
    (ho : Tendsto orders atTop atTop)
    (hsave : ∀ᶠ t in atTop, ∀ k < 3*orders t+1,
      -(C*(orders t+1 : ℝ)^A*Real.exp ((1-delta)*k)) ≤
        (physicalCell u y (orders t) (counts t) k).re) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ᶠ t in atTop,
      -err t ≤ ((u : ℂ)^(orders t+1)*joinedPhysical u y (orders t) (counts t)).re := by
  let q : ℝ := 1/2+delta
  let r : ℝ := u/q
  have hq : 0 < q := hu.trans hd
  have hr : 0 < r := div_pos hu hq
  have hr1 : r < 1 := (div_lt_one hq).mpr hd
  let B : ℕ → ℝ := fun N => 3*C*Real.exp q*(N+1 : ℝ)^(A+1)*r^(N+1)
  have hB : Tendsto (fun t => B (orders t)) atTop (𝓝 0) := by
    have h := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
      (A+1) hr hr1).const_mul (3*C*Real.exp q*r)).comp ho
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [] with t
    dsimp [B]
    rw [pow_succ]
    ring
  let e : ℕ → ℂ := fun t => (u : ℂ)^(orders t+1)*
    (joinedPhysical u y (orders t) (counts t)-coreResponse u y (orders t) (counts t))
  have he : Tendsto e atTop (𝓝 0) := by
    have h := (tendsto_core_sub_joined hu hU (fun _ => y) orders counts ho).neg
    simp only [neg_zero] at h
    exact h.congr' (Eventually.of_forall fun _ => by dsimp [e]; ring)
  refine ⟨fun t => B (orders t)+‖e t‖,?_,?_⟩
  · simpa only [norm_zero,add_zero] using hB.add he.norm
  · filter_upwards [hsave] with t ht
    have hb := scaled_core_floor_of_cells hu.le hq hC y (orders t) (counts t) A ht
    have hre := (abs_le.mp (Complex.abs_re_le_norm (e t))).1
    have heq : (e t).re =
        ((u : ℂ)^(orders t+1)*joinedPhysical u y (orders t) (counts t)).re-
          ((u : ℂ)^(orders t+1)*coreResponse u y (orders t) (counts t)).re := by
      dsimp [e]
      rw [mul_sub,Complex.sub_re]
    rw [heq] at hre
    change -B (orders t) ≤ _ at hb
    linarith

/-- The requested floor follows from the explicit NEW physical-cell
inequality. No claim is made that the inequality has been proved. -/
theorem eventually_joinedPhysical_floor_of_cells {u C : ℝ}
    (hu : 0 < u) (hU : u ≤ radiusCeiling) (hC : 0 ≤ C)
    (y : ℝ) (A : ℕ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop)
    (hsave : ∀ᶠ t in atTop, ∀ k < 3*orders t+1,
      -(C*(orders t+1 : ℝ)^A*Real.exp ((9999/10000 : ℝ)*k)) ≤
        (physicalCell u y (orders t) (counts t) k).re) :
    ∀ᶠ t in atTop, -(79/1000 : ℝ) ≤
      ((u : ℂ)^(orders t+1)*joinedPhysical u y (orders t) (counts t)).re := by
  have hd : u < 1/2+(1/10000 : ℝ) :=
    hU.trans_lt (by norm_num [radiusCeiling])
  obtain ⟨err,he,hb⟩ := exists_joined_floor_error_of_cells hu hU hd hC y A orders counts ho
    (by norm_num at hsave ⊢; exact hsave)
  filter_upwards [hb,he.eventually (eventually_lt_nhds
    (by norm_num : (0 : ℝ) < 79/1000))] with t ht he'
  linarith

/-- Direct conditional simple-zero endpoint for the fixed 1/10000 saving.
The saving remains an explicit hypothesis on literal signed physical cells. -/
theorem false_of_physicalCell_saving (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1) {C : ℝ} (hC : 0 ≤ C) (A : ℕ)
    (hsave : ∀ᶠ t in atTop, ∀ k < 3*dyadicMomentOrder t+1,
      -(C*(dyadicMomentOrder t+1 : ℝ)^A*Real.exp ((9999/10000 : ℝ)*k)) ≤
        (physicalCell (3/2-rho.1.re) rho.1.im
          (dyadicMomentOrder t) (dyadicPrimeCount t) k).re) : False := by
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hf := eventually_joinedPhysical_floor_of_cells hu hU hC rho.1.im A
    dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder hsave
  apply false_of_joinedPhysical_cofinal_floor rho hrho hexposed hU hsimple
    (fun _ => 0) tendsto_const_nhds
  simpa only [sub_zero] using hf.frequently

end
end RiemannGaussian.ZetaRieszPhysicalCellFloor
