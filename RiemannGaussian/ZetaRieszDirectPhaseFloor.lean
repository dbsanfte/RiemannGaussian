/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPhaseOrbitPayment

/-!
# The joined floor with every original count retained

Apply the existing signed prefix inequality to the ORIGINAL coreResponse,
before positive-part credits, count-tail crops or supply debits. This retains
the cancellation between all original counts and radial periods. The four
already proved geometric pair payments apply without a funding witness.

The remaining energy is for these actual weights, not the funded weights.
No comparison or small bound on that energy is asserted. In particular,
this removes an auxiliary divergent debit, not the arithmetic obstruction.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszDirectPhaseFloor
open ZetaRieszParityPacket ZetaRieszAnnulusJoint ZetaRieszJointAllocation
open ZetaRieszSmoothOwnerDiscrepancy
open ZetaRieszJointPrimeEnergy ZetaRieszCutoffPeriodFloor
open ZetaRieszCofactorPhaseEnergy ZetaRieszDiagonalPayment
open ZetaRieszSharedFactorPayment ZetaRieszNearLabelPayment
open ZetaRieszPhaseOrbitPayment ZetaRieszPostHingeEnergy ZetaRieszWideOwnerAudit

/-- Only the four proved geometric prices. No relative supply cost enters. -/
def paidPrice (y : ℝ) (N : ℕ) : ℝ :=
  diagonalPrice 1 N+sharedPrice 1 N+nearPrice 1 N+orbitPrice 1 y N

theorem paidPrice_nonneg (y : ℝ) (N : ℕ) : 0 ≤ paidPrice y N := by
  unfold paidPrice diagonalPrice sharedPrice nearPrice orbitPrice
  norm_num only [radiusCeiling,one_mul]
  positivity

theorem tendsto_paidPrice (y : ℝ) : Tendsto (paidPrice y) atTop (𝓝 0) := by
  change Tendsto (fun N => diagonalPrice 1 N+sharedPrice 1 N+nearPrice 1 N+
    orbitPrice 1 y N) atTop (𝓝 0)
  simpa only [add_zero] using
    (((tendsto_diagonalPrice 1).add (tendsto_sharedPrice 1)).add
      (tendsto_nearPrice 1)).add (tendsto_orbitPrice 1 y)

/-- The literal core embeds in the same arithmetic window used in all
four payments, including its exact endpoints. -/
theorem core_subset_window (u : ℝ) (N K : ℕ) :
    coreBand u N K ⊆ literalWindow N := by
  intro n hn
  have h := (Finset.mem_filter.mp hn).2
  apply (mem_literalWindow N n).mpr
  constructor <;> nlinarith only [h.1,h.2,Nat.cast_nonneg (α := ℝ) N]

/-- A finite bound for the ACTUAL whole signed core. Every count up to
the original cutoff is retained, with its original coefficient and phase.
There is no supply selection, clipped count sum or funding coefficient. -/
theorem core_floor {u y : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (hy : 3 ≤ |y|) {N : ℕ} (hN : 65536 ≤ N) (K : ℕ) :
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let S := coreBand u N K
    let X := max 1 (S.sup id)
    let f := correctedProfile X L 1 0
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    -sqrt (max (nonOrbitEnergy X N (S.filter Squarefree) w f y) 0*
      ((129/200 : ℝ)*N))-paidPrice y N ≤
        ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N K
  let X := max 1 (S.sup id)
  let f := correctedProfile X L 1 0
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  have hX : 0 < X := by dsimp [X]; omega
  have hwin : S ⊆ literalWindow N := core_subset_window u N K
  have hswin := (Finset.filter_subset Squarefree S).trans hwin
  have hSX : S.filter Squarefree ⊆ Finset.Icc 1 X := by
    intro n hn
    obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hs.ne_zero,
      (Finset.le_sup (f := id) hn).trans (le_max_right _ _)⟩
  have hlog : log X ≤ 3*((N : ℝ)+1) := window_sup_log S hwin
  have hL : 1 ≤ L := by
    have hh := length_ge_rational hN hu hU
    have hn : (65536 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [L]
    linarith
  have hq : ∀ n ∈ S.filter Squarefree, |(1 : ℝ)| ≤ 1 := by norm_num
  have hp0 : 0 ≤ adverseProfileEnergy X (S.filter Squarefree) w f :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hcap := core_profile_bound hN hu hU K S w (Finset.Subset.refl _)
  have hpbig : adverseProfileEnergy X (S.filter Squarefree) w f ≤
      4*((N : ℝ)+1)^2 := by
    apply hcap.trans
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hd := weighted_cross_floor N A S (fun _ => 1) y
    (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hwin (by norm_num)
    (fun n hn => core_count hn) hlog
  have hsplit₁ := shared_crossCost_split X N (S.filter Squarefree) w f
  have hsplit₂ := near_crossCost_split X N (S.filter Squarefree) w f
  have hsplit₃ := orbit_crossCost_split X N (S.filter Squarefree) w f y hp0
  have he₁ := weighted_shared_price X N A (S.filter Squarefree) (fun _ => 1) y
    (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX
    (fun n hn => (Finset.mem_filter.mp hn).2) hlog hq
  have he₂ := weighted_near_price X N A (S.filter Squarefree) (fun _ => 1) y
    (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX hlog hq
  have he₃ := weighted_orbit_price X N A (S.filter Squarefree) f (fun _ => 1) y
    hy hswin (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX hlog hq hp0 hpbig
  have hcost : sqrt (max (nonOrbitEnergy X N (S.filter Squarefree) w f y) 0*
      adverseProfileEnergy X (S.filter Squarefree) w f) ≤
        sqrt (max (nonOrbitEnergy X N (S.filter Squarefree) w f y) 0*
          ((129/200 : ℝ)*N)) :=
    sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcap (le_max_right _ _))
  have hvalue : u^(N+1)*(∑ n ∈ S,
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) =
        ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
    rw [← Complex.re_sum,← Complex.ofReal_pow,Complex.re_ofReal_mul]
    rfl
  simp only [one_mul,mul_one] at hd he₁ he₂ he₃
  rw [hvalue] at hd
  dsimp only at hd he₁ he₂ he₃ hcap hcost hsplit₁ hsplit₂ hsplit₃ ⊢
  unfold paidPrice
  linarith only [hd,he₁,he₂,he₃,hcost,hsplit₁,hsplit₂,hsplit₃]

/-- The complete independent error for the existing joinedPhysical.
It includes only the paid pair prices and the proved core/joined difference. -/
def joinedError (u y : ℝ) (N K : ℕ) : ℝ :=
  paidPrice y N+‖(u : ℂ)^(N+1)*
    (coreResponse u y N K-ZetaRieszGammaJoint.joinedPhysical u y N K)‖

theorem joinedError_nonneg (u y : ℝ) (N K : ℕ) : 0 ≤ joinedError u y N K :=
  add_nonneg (paidPrice_nonneg y N) (norm_nonneg _)

/-- No exposed zero or arithmetic cancellation hypothesis enters the
error limit. Heights are fixed; the original count cutoff may move freely. -/
theorem tendsto_joinedError {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => joinedError u y (orders t) (counts t)) atTop (𝓝 0) := by
  have h := (ZetaRieszGammaJoint.tendsto_core_sub_joined hu hU
    (fun _ => y) orders counts ho).norm
  simpa only [joinedError,Function.comp_def,norm_zero,add_zero] using
    ((tendsto_paidPrice y).comp ho).add h

/-- The CURRENT source-carrying joinedPhysical itself has this direct
floor, with ALL original counts joined. The remaining energy is unpaid;
there is no fixed epsilon, supply debit, positive-part count credit or
cropped high-count tail in its weights. -/
theorem joined_floor {u y : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (hy : 3 ≤ |y|) {N : ℕ} (hN : 65536 ≤ N) (K : ℕ) :
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let S := coreBand u N K
    let X := max 1 (S.sup id)
    let f := correctedProfile X L 1 0
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    -sqrt (max (nonOrbitEnergy X N (S.filter Squarefree) w f y) 0*
      ((129/200 : ℝ)*N))-joinedError u y N K ≤
        ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  have h := core_floor hu hU hy hN K
  have hd : ((u : ℂ)^(N+1)*coreResponse u y N K).re-
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re ≤
        ‖(u : ℂ)^(N+1)*(coreResponse u y N K-
          ZetaRieszGammaJoint.joinedPhysical u y N K)‖ := by
    simpa only [mul_sub,Complex.sub_re] using Complex.re_le_norm ((u : ℂ)^(N+1)*
      (coreResponse u y N K-ZetaRieszGammaJoint.joinedPhysical u y N K))
  dsimp only [joinedError] at ⊢
  dsimp only at h
  linarith only [h,hd]

/-- An explicit geometric upper bound on the bridge error, retaining
the original physical length and all counts. Constants remain unevaluated. -/
theorem joinedError_bound {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (y : ℝ) {N : ℕ} (hN : 65536 ≤ N) (K : ℕ) :
    joinedError u y N K ≤ paidPrice y N+
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256) := by
  have hL := length_ge_rational hN hu hU
  have hlow : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact add_le_add le_rfl (ZetaRieszGammaJoint.core_joined_bound hu.le hU N K y hlow)

/-- The direct all-count inequality is available on the ORIGINAL
cofinal schedule. Its sole remaining cost is the literal signed energy. -/
theorem eventually_joined_floor {u y : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (hy : 54 ≤ y) :
    ∀ᶠ j : ℕ in atTop,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N K
      let X := max 1 (S.sup id)
      let f := correctedProfile X L 1 0
      let w := fun n => u^(N+1)*primeWeight A L y N n 1;
      -sqrt (max (nonOrbitEnergy X N (S.filter Squarefree) w f y) 0*
        ((129/200 : ℝ)*N))-joinedError u y N K ≤
          ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (eventually_ge_atTop (65536 : ℕ))] with j hj
  exact joined_floor hu hU (by rw [abs_of_pos (by linarith : 0 < y)]; linarith) hj _

end RiemannGaussian.ZetaRieszDirectPhaseFloor
