/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLowOwnerRows

/-!
# The full ownership-gap signed population

The original all-count row payment is applied simultaneously to every
outer pair with log(pb)+log p > 203N/100. No fixed owner/share cone or
saturation split remains in this payment. The original unsigned row,
phase, moving Riesz length, owner allocation and every physical/core/count
mask are retained. The quantitative cutoff remains log(pb)<=3899N/2000.

This is an independent signed bound, not the numerical whole-carrier floor.
-/

noncomputable section
open Filter Topology Real MeasureTheory Set
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszOwnerGapRows
open ZetaRieszUnifiedSignedRows ZetaRieszUnsignedDivisorError ZetaRieszSignedConvolution
open ZetaRieszSaturatedRowFloor ZetaRieszOwnerMaximal ZetaRieszFreeRadialRows
open ZetaRieszFineDivisorRows ZetaRieszPrimeCountFrequency
open ZetaRieszEdgeDivisorRows (edgeRowBudget edgeEndpointBudget edgeEndpointRate
  edgeErrorConstant edgeErrorConstant_nonneg source_scaled_edge_shells_error
  tendsto_edgeRowBudget tendsto_edgeEndpointBudget)

private theorem edgeEndpointRate_bounds : 0 < edgeEndpointRate ∧ edgeEndpointRate < 1 := by
  exact ⟨exp_pos _,exp_lt_one_iff.mpr (by norm_num)⟩

private theorem gap_eq_cut : (39/20 : ℝ)-1/2000 = 3899/2000 := by norm_num

/-- The row-dependent auxiliary length is a geometric certificate only. -/
def ownershipLength (N p b : ℕ) : ℝ :=
  (log (p*b : ℕ)+(203/100 : ℝ)*N-log p)/2

/-- All original full-window rows satisfying the exact owner gap. -/
def ownerGapRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) :=
  ((ZetaRieszAnnulusJoint.intermediatePrimes u N).product
    (Finset.Icc 2 ⌊exp ((203/100 : ℝ)*N)⌋₊)).filter fun pb =>
      Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2 ∧
      (∀ q ∈ pb.2.primeFactors, q < pb.1) ∧
      pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≠ 0 ∧
      log (pb.1*pb.2 : ℕ) ≤ (3899/2000 : ℝ)*N ∧
      log pb.1 < (243/200 : ℝ)*N ∧
      (203/100 : ℝ)*N < log (pb.1*pb.2 : ℕ)+log pb.1 ∧
      ZetaRieszFineDivisorRows.lower N pb.1 pb.2 ≤ ZetaRieszFineDivisorRows.upper N pb.1 pb.2

private theorem row_owner_mem {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ ownerGapRows u N) :
    pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N :=
  (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1

private theorem row_large {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ ownerGapRows u N) : exp ((N : ℝ)/2000) ≤ ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := by
  have hc := (Finset.mem_filter.mp h).2.2.2.2.2.1
  exact (exp_le_exp.mpr (by linarith : (N : ℝ)/2000 ≤
    (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))).trans (Nat.le_ceil _)

/-- The exact ownership certificate for the whole original radial row. -/
theorem ownerGap_row_geometry {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ ownerGapRows u N) :
    RowGeometry N (ownershipLength N pb.1 pb.2) pb.1 pb.2
      (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) := by
  obtain ⟨hprod,hs,hpd,hmax,_ha,hc,hP,hgap,hlu⟩ := Finset.mem_filter.mp h
  obtain ⟨hp,hb⟩ := Finset.mem_product.mp hprod
  have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp
  have hp0 : (0 : ℝ)<pb.1 := by exact_mod_cast hp'.1.pos
  have hb0 : (0 : ℝ)<pb.2 := by
    have hbpos : 0 < pb.2 := by have := (Finset.mem_Icc.mp hb).1; omega
    exact_mod_cast hbpos
  have hM : 0 < ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := Nat.ceil_pos.mpr (exp_pos _)
  have hX := hM.trans_le hlu
  have hlo : (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ) ≤ log (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) := by
    simpa only [log_exp,ZetaRieszFineDivisorRows.lower] using log_le_log (exp_pos _)
      (Nat.le_ceil (exp ((39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))))
  have hhi : log (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) ≤ (203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ) := by
    simpa only [log_exp,ZetaRieszFineDivisorRows.upper] using log_le_log
      (by exact_mod_cast hX : (0 : ℝ)<ZetaRieszFineDivisorRows.upper N pb.1 pb.2)
      (Nat.floor_le (exp_pos ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ))).le)
  apply ZetaRieszLowOwnerRows.full_window_geometry_of_owner_gap hp'.1
    (by have := (Finset.mem_Icc.mp hb).1; omega) hs hpd hmax hM
    (by linarith) (by linarith)
    (by linarith [Nat.cast_nonneg (α := ℝ) N]) hgap
    (by nlinarith [Nat.cast_nonneg (α := ℝ) N])

private theorem row_data {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ ownerGapRows u N) :
    log (pb.1*pb.2 : ℕ) ≤ (3899/2000 : ℝ)*N ∧
      log pb.1 < (243/200 : ℝ)*N ∧
      ZetaRieszFineDivisorRows.lower N pb.1 pb.2 ≤ ZetaRieszFineDivisorRows.upper N pb.1 pb.2 := by
  obtain ⟨_,_,_,_,_,hc,hP,_,hlu⟩ := Finset.mem_filter.mp h
  exact ⟨hc,hP,hlu⟩

private theorem coefficient_bound {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ ownerGapRows u N) :
    |((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors| ≤ (1 : ℝ)/(pb.1*pb.2 : ℕ) := by
  have hg := ownerGap_row_geometry hpb
  have hP := (row_data hpb).2.1
  have hn : (32 : ℝ)≤N := by exact_mod_cast hN
  have hL0 : 0 < SquarefreeVaughanLogSource.length u N := by linarith
  have hpb0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by
    exact_mod_cast Nat.mul_pos hg.1.pos (by have := hg.2.1; omega)
  have hH := pairHinge_bounds (SquarefreeVaughanLogSource.length u N) pb.1 pb.2
  have hHL : pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≤
      SquarefreeVaughanLogSource.length u N := by linarith [hH.2]
  have hd := density_bounds (pb.1*pb.2).primeFactors (fun _ hq => Nat.prime_of_mem_primeFactors hq)
  have hm : |(μ pb.2 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := pb.2)
  rw [abs_mul,abs_div,abs_mul,abs_of_nonneg hH.1,abs_of_nonneg hd.1,
    abs_of_pos (mul_pos hL0 hpb0)]
  have hnum : |(μ pb.2 : ℝ)| * pairHinge
      (SquarefreeVaughanLogSource.length u N) pb.1 pb.2*density (pb.1*pb.2).primeFactors ≤
      SquarefreeVaughanLogSource.length u N :=
    (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hH.1) hd.2).trans
      ((mul_le_of_le_one_left hH.1 hm).trans hHL)
  calc
    _ = (|(μ pb.2 : ℝ)| *pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2*
      density (pb.1*pb.2).primeFactors)/(SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)) := by ring
    _ ≤ SquarefreeVaughanLogSource.length u N/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hL0 hpb0).le
    _ = _ := by field_simp

set_option backward.isDefEq.respectTransparency false in
/-- All outer counts have only harmonic mass after the unsigned leg is
joined and cancelled. No exponential count majorant is charged here. -/
private theorem outer_harmonic_bound (u : ℝ) (N : ℕ) :
    (∑ pb ∈ ownerGapRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) ≤
      (1+(203/100 : ℝ)*N)^2 := by
  let B := ⌊exp ((203/100 : ℝ)*N)⌋₊
  have hBn : 0 < B := Nat.floor_pos.mpr (one_le_exp (by positivity))
  have hB : (0 : ℝ)<B := by exact_mod_cast hBn
  have hlogB : log B ≤ (203/100 : ℝ)*N := by
    have hh := log_le_log hB (Nat.floor_le (exp_pos ((203/100 : ℝ)*N)).le)
    simpa only [log_exp] using hh
  have hsub : ownerGapRows u N ⊆ (Finset.Icc 1 B).product (Finset.Icc 1 B) := by
    intro pb hpb
    have hg := ownerGap_row_geometry hpb
    have hb := (Finset.mem_product.mp (Finset.mem_filter.mp hpb).1).2
    have hp : log pb.1 ≤ (13/20 : ℝ)*((203/100 : ℝ)*N) := by
      have hP := (row_data hpb).2.1
      have hn := Nat.cast_nonneg (α := ℝ) N
      linarith
    have hpB : pb.1 ≤ B := by
      apply Nat.le_floor
      rw [← exp_log (by exact_mod_cast hg.1.pos : (0 : ℝ)<pb.1)]
      apply exp_le_exp.mpr
      linarith [Nat.cast_nonneg (α := ℝ) N]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hg.1.pos,hpB⟩,
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hb).1; omega,(Finset.mem_Icc.mp hb).2⟩⟩
  have hhar : (∑ d ∈ Finset.Icc 1 B, (d : ℝ)⁻¹) ≤ 1+(203/100 : ℝ)*N := by
    have hh := harmonic_le_one_add_log B
    rw [harmonic_eq_sum_Icc,Rat.cast_sum] at hh
    push_cast at hh
    exact hh.trans (add_le_add_right hlogB 1)
  have he : (∑ pb ∈ (Finset.Icc 1 B).product (Finset.Icc 1 B), (1 : ℝ)/(pb.1*pb.2 : ℕ)) =
      (∑ d ∈ Finset.Icc 1 B, (d : ℝ)⁻¹)^2 := by
    calc
      _ = ∑ p ∈ Finset.Icc 1 B, ∑ b ∈ Finset.Icc 1 B, (1 : ℝ)/(p*b : ℕ) :=
        Finset.sum_product (Finset.Icc 1 B) (Finset.Icc 1 B)
          (fun pb : ℕ×ℕ => (1 : ℝ)/(pb.1*pb.2 : ℕ))
      _ = _ := by
        simp only [Nat.cast_mul,one_div,mul_inv]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul,pow_two]
  calc
    _ ≤ ∑ pb ∈ (Finset.Icc 1 B).product (Finset.Icc 1 B), (1 : ℝ)/(pb.1*pb.2 : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = _ := he
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hhar 2

/-- The actual signed density main on the new original row population. -/
def ownerGapDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ ownerGapRows u N, densityRow N (SquarefreeVaughanLogSource.length u N) y
    pb.1 pb.2 (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)

/-- The entire signed main is paid before its outer rows/counts are
normed. Saturation is absent; the original allocation and phase remain. -/
theorem source_scaled_ownerGapDensityMain_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*ownerGapDensityMain u y N| ≤ fineMainBudget y N := by
  have hrow pb (hpb : pb ∈ ownerGapRows u N) :
      |u^(N+1)*densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)| ≤
        (1 : ℝ)/(pb.1*pb.2 : ℕ)*
          (((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N) := by
    rw [densityRow_physical]
    rw [show u^(N+1)*
      (((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors*
        (∑ d ∈ Finset.Ioc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2),
          physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))) =
      (((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors)*
        (u^(N+1)*(∑ d ∈ Finset.Ioc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2),
          physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))) by ring,
      abs_mul]
    exact mul_le_mul (coefficient_bound hN hL hpb)
      (full_window_weight_bound_of_gap hu hU hN (β := 1/2000) (by norm_num)
        (by simpa only [gap_eq_cut] using (row_data hpb).1) (row_data hpb).2.1 (row_data hpb).2.2 hy) (abs_nonneg _) (by positivity)
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum hrow)
  have hs : |u^(N+1)*ownerGapDensityMain u y N| ≤
      (1+(203/100 : ℝ)*N)^2*
        (((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N) := by
    rw [ownerGapDensityMain,Finset.mul_sum]
    apply hsum.trans
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (outer_harmonic_bound u N)
      (by positivity [fineRateTotal_bounds.1])
  have hp1 : (1+(203/100 : ℝ)*N)^2 ≤ 9*((N : ℝ)+1)^2 := by
    have h : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact (pow_le_pow_left₀ (by positivity) h 2).trans_eq (by ring)
  have hp2 : 13*(N : ℝ)+33+4*|y| ≤ (33+4*|y|)*((N : ℝ)+1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg y)]
  apply hs.trans
  unfold fineMainBudget
  have h := mul_le_mul hp1
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2
      (show 0 ≤ (N : ℝ)+1 by positivity))
      (pow_nonneg fineRateTotal_bounds.1.le N))
    (by positivity [fineRateTotal_bounds.1]) (by positivity)
  convert h using 1
  ring

private theorem last_boundary {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (hpb : pb ∈ ownerGapRows u N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    boundary (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) (N+1) =
        ZetaRieszFineDivisorRows.upper N pb.1 pb.2 := by
  have hg := ownerGap_row_geometry hpb
  have ha := pairHinge_active (show pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≠ 0 from (Finset.mem_filter.mp hpb).2.2.2.2.1)
  have hp0 := hg.1.pos
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hlog : log (pb.1*pb.2 : ℕ)=log pb.1+log pb.2 := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp0.ne') (by exact_mod_cast hb0.ne')]
  have hU : (ZetaRieszFineDivisorRows.upper N pb.1 pb.2 : ℝ) ≤
      exp ((131/200 : ℝ)*N) := by
    have hf := Nat.floor_le (exp_pos (((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ)))).le
    have he : ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ)) ≤ (131/200 : ℝ)*N := by
      rw [← hlog] at ha
      linarith [Nat.cast_nonneg (α := ℝ) N]
    exact hf.trans (exp_le_exp.mpr he)
  have hpow : exp ((131/200 : ℝ)*N) ≤
      ((2^(N+1)*ZetaRieszFineDivisorRows.lower N pb.1 pb.2 : ℕ) : ℝ) := by
    have hbase := row_large hpb
    have hrate : (131/200 : ℝ)*N ≤ (N+1 : ℕ)*log 2+(N : ℝ)/2000 := by
      push_cast
      nlinarith [log_two_gt_d9,log_pos (by norm_num : (1 : ℝ)<2)]
    calc
      _ ≤ exp ((N+1 : ℕ)*log 2+(N : ℝ)/2000) := exp_le_exp.mpr hrate
      _ = (2 : ℝ)^(N+1)*exp ((N : ℝ)/2000) := by rw [exp_add,exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<2)]
      _ ≤ (2 : ℝ)^(N+1)*ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by push_cast; rfl
  unfold boundary
  exact min_eq_left (by exact_mod_cast hU.trans hpow)

/-- The dyadic grid on one canonical row. -/
def rowBoundary (_u : ℝ) (N i : ℕ) (pb : ℕ×ℕ) : ℕ :=
  boundary (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
    (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) i

/-- Empty clamped shells are removed exactly, rather than estimated. -/
def shellRows (u : ℝ) (N i : ℕ) : Finset (ℕ×ℕ) :=
  (ownerGapRows u N).filter (fun pb => rowBoundary u N i pb < rowBoundary u N (i+1) pb)

private theorem shell_geometry {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) :
    RowGeometry N (ownershipLength N pb.1 pb.2) pb.1 pb.2
      (rowBoundary u N i pb) (rowBoundary u N (i+1) pb) := by
  obtain ⟨hr,hMX⟩ := Finset.mem_filter.mp hpb
  have hlu := (row_data hr).2.2
  apply geometry_subinterval (ownerGap_row_geometry hr) _ _ hMX
  · exact lower_le_boundary hlu i
  · exact min_le_left _ _

set_option maxHeartbeats 800000 in
private theorem shell_large {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) : exp ((N : ℝ)/2000) ≤ rowBoundary u N i pb := by
  have hr := (Finset.mem_filter.mp hpb).1
  have hlu := (row_data hr).2.2
  exact (row_large hr).trans
    (by exact_mod_cast lower_le_boundary hlu i)

private theorem coreRow_empty (u y : ℝ) (j p b M : ℕ) : coreRow u y j p b M M=0 := by
  simp [coreRow]

private theorem sum_shellRows_eq (u : ℝ) (N : ℕ)
    (F : (ℕ×ℕ) → ℕ → ℕ → ℝ) (hzero : ∀ pb M, F pb M M=0) :
    (∑ i ∈ Finset.range (N+1), ∑ pb ∈ shellRows u N i,
      F pb (rowBoundary u N i pb) (rowBoundary u N (i+1) pb)) =
        ∑ pb ∈ ownerGapRows u N, ∑ i ∈ Finset.range (N+1),
          F pb (rowBoundary u N i pb) (rowBoundary u N (i+1) pb) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro pb _ hnot
  have hz : rowBoundary u N i pb=rowBoundary u N (i+1) pb := by
    apply le_antisymm (boundary_mono _ _ (Nat.le_succ i))
    exact le_of_not_gt (fun h => hnot (Finset.mem_filter.mpr ⟨by assumption,h⟩))
  rw [hz,hzero]

/-- All core row atoms are reassembled exactly after the error has been
paid shellwise. Original phases, masks and count cutoff stay inside. -/
private theorem sum_coreRow_shells (u y : ℝ) (j : ℕ)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    (∑ i ∈ Finset.range (dyadicMomentOrder j+1),
      ∑ pb ∈ shellRows u (dyadicMomentOrder j) i,
        coreRow u y j pb.1 pb.2
          (rowBoundary u (dyadicMomentOrder j) i pb)
          (rowBoundary u (dyadicMomentOrder j) (i+1) pb)) =
      ∑ pb ∈ ownerGapRows u (dyadicMomentOrder j),
        coreRow u y j pb.1 pb.2 (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
          (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2) := by
  rw [sum_shellRows_eq _ _ _ (fun pb M => coreRow_empty u y j pb.1 pb.2 M)]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (row_data hpb).2.2
  unfold coreRow
  dsimp only
  change (∑ i ∈ Finset.range (dyadicMomentOrder j+1),
    ∑ d ∈ Finset.Ioc (rowBoundary _ _ i _) (rowBoundary _ _ (i+1) _), _) = _
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]

/-- The SIGNED density rows are likewise recombined before any main-term
estimate. No norm, positive part or separate prime-count cost is inserted. -/
private theorem sum_densityRow_shells (u y : ℝ) (N : ℕ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ i ∈ Finset.range (N+1), ∑ pb ∈ shellRows u N i,
      densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (rowBoundary u N i pb) (rowBoundary u N (i+1) pb)) =
      ∑ pb ∈ ownerGapRows u N,
        densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
          (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) (ZetaRieszFineDivisorRows.upper N pb.1 pb.2) := by
  rw [sum_shellRows_eq _ _ _ (fun pb M => densityRow_empty _ _ _ pb.1 pb.2 M)]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (row_data hpb).2.2
  simp only [densityRow_interval,← Finset.mul_sum]
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]

private theorem squarefree_outer {N p b M X : ℕ} {L : ℝ}
    (hg : RowGeometry N L p b M X) : Squarefree (p*b) := by
  exact Nat.squarefree_mul_iff.mpr
    ⟨hg.1.coprime_iff_not_dvd.mpr hg.2.2.2.1,hg.1.squarefree,hg.2.2.1⟩



private theorem mem_incidences {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ}
    {v : ℕ×(ℕ×ℕ)} (hv : v ∈ incidences B M X) :
    ∃ pb ∈ B, ∃ d ∈ Finset.Ioc (M pb) (X pb),
      sieve (pb.1*pb.2).primeFactors d ≠ 0 ∧ v=(pb.1*(pb.2*d),(d,pb.2)) := by
  obtain ⟨pb,hpb,hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hv
  exact ⟨pb,hpb,d,(Finset.mem_filter.mp hd).1,(Finset.mem_filter.mp hd).2,he.symm⟩

/-- A row incidence has the genuine canonical owner and an original
squarefree product label. No owner multiplicity is introduced. -/
private theorem incidence_owner {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ} {N : ℕ} {L : (ℕ×ℕ) → ℝ}
    (hg : ∀ pb ∈ B, RowGeometry N (L pb) pb.1 pb.2 (M pb) (X pb))
    {v : ℕ×(ℕ×ℕ)} (hv : v ∈ incidences B M X) :
    Squarefree v.1 ∧
      ZetaRieszPrimeEndpoint.largestPrime v.1*(v.2.2*v.2.1)=v.1 ∧
      v.2.1*v.2.2=v.1/ZetaRieszPrimeEndpoint.largestPrime v.1 := by
  obtain ⟨pb,hpb,d,hd,hs,rfl⟩ := mem_incidences hv
  have hgeom := hg pb hpb
  have hco := row_cofactor_geometry hgeom hd hs
  have howner := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d)
    hgeom.1 hco.1.ne_zero hco.2.2
  have hn : Squarefree (pb.1*(pb.2*d)) := by
    rw [sieve_eq_product_squarefree (squarefree_outer hgeom)] at hs
    split_ifs at hs with h
    · simpa only [mul_assoc] using h
    · contradiction
  refine ⟨hn,?_,?_⟩
  · rw [howner]
  · simp only [howner,Nat.mul_div_cancel_left _ hgeom.1.pos]
    ac_rfl

/-- Every selected set is a literal subset of the original cofactor
antidiagonal. This prevents spending a duplicate incidence credit. -/
private theorem selectedDivisors_subset {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ} {N : ℕ} {L : (ℕ×ℕ) → ℝ}
    (hg : ∀ pb ∈ B, RowGeometry N (L pb) pb.1 pb.2 (M pb) (X pb)) (n : ℕ) :
    selectedDivisors B M X n ⊆ (n/ZetaRieszPrimeEndpoint.largestPrime n).divisorsAntidiagonal := by
  intro db hdb
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hdb
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  have ho := incidence_owner hg hv
  apply Nat.mem_divisorsAntidiagonal.mpr
  rw [← he]
  refine ⟨ho.2.2,?_⟩
  obtain ⟨pb,hpb,d,hd,_,rfl⟩ := mem_incidences hv
  have ho := row_cofactor_geometry (hg pb hpb) hd (by assumption)
  rw [ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d) (hg pb hpb).1
    ho.1.ne_zero ho.2.2,Nat.mul_div_cancel_left _ (hg pb hpb).1.pos]
  exact ho.1.ne_zero

/-- Original row selections with distinct outer pairs cannot overlap
as divisor incidences, even when several divisors have the same label. -/
private theorem sum_rows_eq_incidences (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ) {N : ℕ} {L : (ℕ×ℕ) → ℝ}
    (hg : ∀ pb ∈ B, RowGeometry N (L pb) pb.1 pb.2 (M pb) (X pb))
    (f : ℕ → (ℕ×ℕ) → ℝ) :
    (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      if sieve (pb.1*pb.2).primeFactors d ≠ 0 then f (pb.1*(pb.2*d)) (d,pb.2) else 0) =
      ∑ v ∈ incidences B M X, f v.1 v.2 := by
  have hdis : Set.Pairwise (↑B) (fun pb pc => Disjoint
      (((Finset.Ioc (M pb) (X pb)).filter (fun d => sieve (pb.1*pb.2).primeFactors d ≠ 0)).image
        (fun d => (pb.1*(pb.2*d),(d,pb.2))))
      (((Finset.Ioc (M pc) (X pc)).filter (fun d => sieve (pc.1*pc.2).primeFactors d ≠ 0)).image
        (fun d => (pc.1*(pc.2*d),(d,pc.2))))) := by
    intro pb hpb pc hpc hne
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hw
    have hd' := Finset.mem_filter.mp hd
    have he' := Finset.mem_filter.mp he
    have hdco := row_cofactor_geometry (hg pb hpb) hd'.1 hd'.2
    have heco := row_cofactor_geometry (hg pc hpc) he'.1 he'.2
    have hownerd := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d)
      (hg pb hpb).1 hdco.1.ne_zero hdco.2.2
    have hownere := ZetaRieszPrimeIntervals.largestPrime_mul pc.1 (pc.2*e)
      (hg pc hpc).1 heco.1.ne_zero heco.2.2
    have hpe : pc.1=pb.1 := by
      have hh := congrArg ZetaRieszPrimeEndpoint.largestPrime (congrArg Prod.fst heq)
      simpa only [hownerd,hownere] using hh
    have hbe : pc.2=pb.2 := by simpa using congrArg (fun v : ℕ×(ℕ×ℕ) => v.2.2) heq
    exact hne (Prod.ext hpe.symm hbe.symm)
  rw [incidences,Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro pb hpb
  rw [Finset.sum_image (fun d _ e _ he => by simpa using congrArg (fun v : ℕ×(ℕ×ℕ) => v.2.1) he)]
  simp only [Finset.sum_filter]

private theorem sum_incidences_eq_fibers (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (f : ℕ → (ℕ×ℕ) → ℝ) :
    (∑ v ∈ incidences B M X, f v.1 v.2) =
      ∑ n ∈ (incidences B M X).image Prod.fst,
        ∑ db ∈ selectedDivisors B M X n, f n db := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (t := (incidences B M X).image Prod.fst) (g := Prod.fst)
    (fun v (hv : v ∈ incidences B M X) => Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    (fun v : ℕ×(ℕ×ℕ) => f v.1 v.2)
  rw [← hf]
  apply Finset.sum_congr rfl
  intro n _
  rw [selectedDivisors,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [(Finset.mem_filter.mp hv).2]
  · intro v hv w hw he
    exact Prod.ext ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm) he

private def incidenceWeight (A : Finset ℕ) (N : ℕ) (L y : ℝ) (n : ℕ) (db : ℕ×ℕ) : ℝ :=
  (phaseWeight (A ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L N y
    (n/ZetaRieszPrimeEndpoint.largestPrime n) (ZetaRieszPrimeEndpoint.largestPrime n)).re*
      (μ db.2 : ℝ)*pairHinge L (ZetaRieszPrimeEndpoint.largestPrime n) db.2



private theorem sum_incidenceWeight_eq_partial (A : Finset ℕ) (N n : ℕ) (L y : ℝ)
    (D : Finset (ℕ×ℕ))
    (he : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n) :
    (∑ db ∈ D, incidenceWeight A N L y n db) =
      (partialCoefficient (A ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L N
        (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n) D*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  simp only [incidenceWeight,phaseWeight,partialCoefficient,he,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro db _
  ring



private theorem row_window {N p b M X d : ℕ} {L : ℝ}
    (hg : RowGeometry N L p b M X) (hd : d ∈ Finset.Ioc M X) :
    (39/20 : ℝ)*N < log (p*(b*d) : ℕ) ∧
      log (p*(b*d) : ℕ) ≤ (203/100 : ℝ)*N := by
  have hgeom := hg
  obtain ⟨hp,hb,_,_,_,_,hM,hlo,hhi,_,_⟩ := hg
  have hd0 : 0 < d := by have := Finset.mem_Ioc.mp hd; omega
  have hb0 : 0 < b := by omega
  have ht : log (p*(b*d) : ℕ)=log (p*b : ℕ)+log d := by
    rw [show p*(b*d)=(p*b)*d by ac_rfl,Nat.cast_mul,
      log_mul (by exact_mod_cast (Nat.mul_pos hp.pos hb0).ne') (by exact_mod_cast hd0.ne')]
  have hMd : log M < log d := (log_lt_log_iff
    (by exact_mod_cast hM) (by exact_mod_cast hd0)).mpr
      (by exact_mod_cast (Finset.mem_Ioc.mp hd).1)
  have hdX : log d ≤ log X := log_le_log (by exact_mod_cast hd0)
    (by exact_mod_cast (Finset.mem_Ioc.mp hd).2)
  rw [ht]
  constructor <;> linarith

private theorem incidence_band {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ} {N : ℕ} {L : (ℕ×ℕ) → ℝ}
    (hN : 0 < N) (hg : ∀ pb ∈ B, RowGeometry N (L pb) pb.1 pb.2 (M pb) (X pb))
    {v : ℕ×(ℕ×ℕ)} (hv : v ∈ incidences B M X) : v.1 ∈ zetaPrimeLogBand N := by
  have hn := (incidence_owner hg hv).1
  obtain ⟨pb,hpb,d,hd,_,rfl⟩ := mem_incidences hv
  have hw := row_window (hg pb hpb) hd
  by_contra hnot
  have hc := zetaPrimeLogBand_complement N hn.ne_zero hnot
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  rcases hc with hlo | hhi
  · nlinarith [log_two_lt_d9]
  · nlinarith [log_two_gt_d9]



private theorem rowAtom_eq_incidenceWeight_of_geometry (A : Finset ℕ) {N p b M X d : ℕ} {L ℒ : ℝ}
    (y : ℝ) (hg : RowGeometry N ℒ p b M X) (hd : d ∈ Finset.Ioc M X)
    (hs : sieve (p*b).primeFactors d ≠ 0) :
    rowAtom A N L y p b d = incidenceWeight A N L y (p*(b*d)) (d,b) := by
  have hc := row_cofactor_geometry hg hd hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul p (b*d) hg.1 hc.1.ne_zero hc.2.2
  have hs1 : sieve (p*b).primeFactors d=1 := by
    unfold sieve at *
    split_ifs at * <;> simp_all
  simp only [rowAtom,incidenceWeight,ho,Nat.mul_div_cancel_left _ hg.1.pos,hs1,mul_one]

private theorem sum_maskedRows_eq_partial_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (u y : ℝ) (j : ℕ) (χ : ℕ → Prop) (ℒ : (ℕ×ℕ) → ℝ)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) (ℒ pb) pb.1 pb.2 (M pb) (X pb)) :
    (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      if χ (pb.1*(pb.2*d)) then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          y pb.1 pb.2 d else 0) =
      (∑ n ∈ ((incidences B M X).image Prod.fst).filter
        χ,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
          {ZetaRieszPrimeEndpoint.largestPrime n})
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n db => if χ n then
    incidenceWeight A N L y n db else 0
  have hrows : (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      if χ (pb.1*(pb.2*d)) then rowAtom A N L y pb.1 pb.2 d else 0) =
      ∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
        if sieve (pb.1*pb.2).primeFactors d ≠ 0 then f (pb.1*(pb.2*d)) (d,pb.2) else 0 := by
    apply Finset.sum_congr rfl
    intro pb hpb
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hs : sieve (pb.1*pb.2).primeFactors d=0
    · simp [rowAtom,hs]
    rw [if_pos hs,rowAtom_eq_incidenceWeight_of_geometry A y (hg pb hpb) hd hs]
  rw [hrows,sum_rows_eq_incidences B M X hg f,sum_incidences_eq_fibers]
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hk : χ n
  · simp only [f,if_pos hk]
    have he : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      obtain ⟨v,hv,hnv⟩ := Finset.mem_image.mp hn
      have ho := incidence_owner hg hv
      rw [← hnv,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    exact sum_incidenceWeight_eq_partial A N n L y _ he
  · simp only [f,if_neg hk,Finset.sum_const_zero]

private theorem sum_overflow_eq_partial_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (u y : ℝ) (j : ℕ) (ℒ : (ℕ×ℕ) → ℝ)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) (ℒ pb) pb.1 pb.2 (M pb) (X pb)) :
    (∑ pb ∈ B, overflowRow u y j pb.1 pb.2 (M pb) (X pb)) =
      (∑ n ∈ ((incidences B M X).image Prod.fst).filter
        (fun n => dyadicPrimeCount j ≤ n.primeFactors.card),
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
          {ZetaRieszPrimeEndpoint.largestPrime n})
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  convert sum_maskedRows_eq_partial_of_geometry B M X u y j
    (fun n => dyadicPrimeCount j ≤ n.primeFactors.card) ℒ hg using 1
  · apply Finset.sum_congr rfl
    intro pb _
    unfold overflowRow
    dsimp only
    apply Finset.sum_congr rfl
    intro d _
    by_cases hk : dyadicPrimeCount j ≤ (pb.1*(pb.2*d)).primeFactors.card <;> simp [hk]
  · congr 1
    apply Finset.sum_congr
    · ext n; simp
    · intro n _; rfl

private theorem incidence_log_le_twice_actual {u : ℝ} {ℒ : (ℕ×ℕ) → ℝ} {j : ℕ}
    {B : Finset (ℕ×ℕ)} {M X : ℕ×ℕ → ℕ}
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) (ℒ pb) pb.1 pb.2 (M pb) (X pb))
    {v : ℕ×(ℕ×ℕ)} (hv : v ∈ incidences B M X) :
    log v.1 ≤ 2*SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
  obtain ⟨pb,hpb,d,hd,_,rfl⟩ := mem_incidences hv
  have h := (row_window (hg pb hpb) hd).2
  nlinarith [Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]

private theorem overflowRows_bound_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (j : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (ℒ : (ℕ×ℕ) → ℝ)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) (ℒ pb) pb.1 pb.2 (M pb) (X pb)) :
    |u^(dyadicMomentOrder j+1)*∑ pb ∈ B,
      overflowRow u y j pb.1 pb.2 (M pb) (X pb)| ≤
        highCountConstant*(dyadicMomentOrder j : ℝ)*(97/100 : ℝ)^(dyadicMomentOrder j)*
          exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100)) := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let S := ((incidences B M X).image Prod.fst).filter
    (fun n => dyadicPrimeCount j ≤ n.primeFactors.card)
  let c := fun n => partialCoefficient
    (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      L N (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
        (selectedDivisors B M X n)/2
  have hn n (h : n ∈ S) : ∃ v ∈ incidences B M X, v.1=n :=
    Finset.mem_image.mp (Finset.mem_filter.mp h).1
  have hsf n (h : n ∈ S) : Squarefree n := by
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using (incidence_owner hg hv).1
  have hband : S ⊆ zetaPrimeLogBand N := by
    intro n h
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using incidence_band
      (by dsimp [N,dyadicMomentOrder,dyadicPrimeCount]; positivity) hg hv
  have hc n (h : n ∈ S) : ‖c n‖ ≤ zetaMoebiusLogMajorant n := by
    obtain ⟨v,hv,he⟩ := hn n h
    have ho := incidence_owner hg hv
    have hpn : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      rw [← he,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    have hp : 0 < ZetaRieszPrimeEndpoint.largestPrime n := by
      by_contra hh
      have h0 : ZetaRieszPrimeEndpoint.largestPrime n=0 := by omega
      rw [h0,zero_mul] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have ha : (0 : ℕ) < n/ZetaRieszPrimeEndpoint.largestPrime n := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [h0,mul_zero] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have hT : log n ≤ 2*L := by
      simpa only [he] using incidence_log_le_twice_actual hL hg hv
    have hdom := partialCoefficient_bound
      (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      N hp ha (selectedDivisors B M X n) (selectedDivisors_subset hg n)
      (SquarefreeVaughanLogSource.length_pos u N) (by simpa only [hpn] using hT)
    rw [hpn] at hdom
    dsimp [c]
    rw [norm_div]
    norm_num
    linarith
  have hnorm := ZetaRieszWeightedCount.norm_normalized_many_dyadic_le S c hc 1 j y hu hU
    (by norm_num : (0 : ℝ)<49/100) (by norm_num : (49/100 : ℝ)<1/2) hsf hband
    (fun n h => (Finset.mem_filter.mp h).2)
  have hP : (∑ k ∈ (1 : Polynomial ℂ).support,
      ‖(1 : Polynomial ℂ).coeff k‖*(49/100 : ℝ)⁻¹^k)=1 := by
    rw [← Polynomial.C_1,Polynomial.support_C (by norm_num : (1 : ℂ)≠0)]
    simp
  rw [hP,mul_one,show (3/2 : ℝ)-49/100=101/100 by norm_num] at hnorm
  have hreal : |u^(N+1)*∑ pb ∈ B, overflowRow u y j pb.1 pb.2 (M pb) (X pb)| ≤
      2*‖(u : ℂ)^(N+1)*∑ n ∈ S,
        c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
    rw [sum_overflow_eq_partial_of_geometry B M X u y j ℒ hg]
    have heq : (u : ℂ)^(N+1)*∑ n ∈ S,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n =
        2*((u : ℂ)^(N+1)*∑ n ∈ S,
          c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
      calc
        _ = (u : ℂ)^(N+1)*(2*∑ n ∈ S,
            c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          rw [ZetaRieszJointAllocation.filter_one_eq]
          dsimp [c]
          ring
        _ = _ := by ring
    have hre := Complex.abs_re_le_norm
      ((u : ℂ)^(N+1)*∑ n ∈ S,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    have hrhs : ‖(u : ℂ)^(N+1)*∑ n ∈ S,
        partialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ =
        2*‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
      rw [heq,norm_mul]
      norm_num
    simpa only [S,L,N,← Complex.ofReal_pow,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre.trans_eq hrhs
  apply hreal.trans ((mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ)≤2)).trans _)
  have hr : 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) ≤ 97/100 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  have hr0 : 0 ≤ 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  dsimp [highCountConstant]
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr N)
    (by dsimp [ZetaRieszWideOwnerAudit.radiusCeiling]
        positivity [log_pos (by norm_num : (1 : ℝ)<2)] : 0 ≤ 64*ZetaRieszWideOwnerAudit.radiusCeiling*log 2*N)
  have he := mul_le_mul_of_nonneg_right hp
    (exp_pos (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100))).le
  convert he using 1
  ring



private theorem overflow_shells_bound {ι : Type*} (I : Finset ι)
    (B : ι → Finset (ℕ×ℕ)) (M X : ι → ℕ×ℕ → ℕ)
    (j : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hI : I.card ≤ dyadicMomentOrder j+1)
    (hg : ∀ i ∈ I, ∀ pb ∈ B i, RowGeometry (dyadicMomentOrder j)
      (ownershipLength (dyadicMomentOrder j) pb.1 pb.2) pb.1 pb.2 (M i pb) (X i pb))
    (hcount : exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100)) ≤
      (101/100 : ℝ)^(dyadicMomentOrder j)) :
    |u^(dyadicMomentOrder j+1)*∑ i ∈ I, ∑ pb ∈ B i,
      overflowRow u y j pb.1 pb.2 (M i pb) (X i pb)| ≤
      highCountConstant*((dyadicMomentOrder j : ℝ)+1)^2*(49/50 : ℝ)^(dyadicMomentOrder j) := by
  let N := dyadicMomentOrder j
  let C := highCountConstant*(N : ℝ)*(97/100 : ℝ)^N*
    exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100))
  have hC : 0 ≤ C := by dsimp [C]; positivity [highCountConstant_nonneg]
  calc
    _ ≤ ∑ i ∈ I, |u^(N+1)*∑ pb ∈ B i,
        overflowRow u y j pb.1 pb.2 (M i pb) (X i pb)| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, C := Finset.sum_le_sum (fun i hi =>
      overflowRows_bound_of_geometry (B i) (M i) (X i) j hu hU y
        (fun pb => ownershipLength N pb.1 pb.2) hL (hg i hi))
    _ = (I.card : ℝ)*C := by simp
    _ ≤ ((N : ℝ)+1)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hC
    _ ≤ highCountConstant*((N : ℝ)+1)^2*
        ((97/100 : ℝ)^N*(101/100 : ℝ)^N) := by
      have hp := mul_le_mul_of_nonneg_left hcount
        (by positivity [highCountConstant_nonneg] :
          0 ≤ ((N : ℝ)+1)*highCountConstant*N*(97/100 : ℝ)^N)
      have hn : ((N : ℝ)+1)*N ≤ ((N : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
      have hpoly := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn highCountConstant_nonneg)
        (by positivity : 0 ≤ (97/100 : ℝ)^N*(101/100 : ℝ)^N)
      dsimp [C]
      nlinarith only [hp,hpoly]
    _ ≤ _ := by
      rw [← mul_pow]
      gcongr
      all_goals first | positivity [highCountConstant_nonneg] | norm_num

/-- Literal signed original core incidences of the complete ownership-gap population. -/
def ownerGapLiteralRows (u y : ℝ) (j : ℕ) : ℝ :=
  ∑ pb ∈ ownerGapRows u (dyadicMomentOrder j),
    coreRow u y j pb.1 pb.2 (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2)

set_option maxHeartbeats 1200000 in
/-- An INDEPENDENT signed bound for the ORIGINAL ownership-gap row
population, across all counts and radial positions together. No zero,
prime-density approximation or unproved cancellation premise enters. -/
theorem eventually_abs_ownerGapLiteralRows_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*ownerGapLiteralRows u y j| ≤
        edgeRowBudget y (dyadicMomentOrder j) := by
  let I := fun j => Finset.range (dyadicMomentOrder j+1)
  let B := fun j i => shellRows u (dyadicMomentOrder j) i
  let M := fun j i => rowBoundary u (dyadicMomentOrder j) i
  let X := fun j i => rowBoundary u (dyadicMomentOrder j) (i+1)
  have hgeo j i (_hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      RowGeometry (dyadicMomentOrder j) (ownershipLength (dyadicMomentOrder j) pb.1 pb.2)
        pb.1 pb.2 (M j i pb) (X j i pb) := shell_geometry hpb
  have hpA j i (_hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) :=
    row_owner_mem (Finset.mem_filter.mp hpb).1
  have hI j : (I j).card ≤ dyadicMomentOrder j+1 := by simp [I]
  have hcExp := ZetaRieszPrimeCountMass.eventually_exp_count_le_geometric
    (2*ZetaRieszPrimeCountMass.countMass (101/100)) (by norm_num : (1 : ℝ)<101/100)
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hcExp,tendsto_dyadicMomentOrder.eventually hl,
    eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ))]
    with j hcExp hlength hj hN
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hL : (11/8 : ℝ)*N ≤ L := by change _ ≤ L at hlength; nlinarith only [hlength]
  have hcount := overflow_shells_bound (I j) (B j) (M j) (X j) j
    (by linarith : 0 ≤ u) hU y hL (hI j) (hgeo j)
    (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hcExp)
  have hL0 : 0 < L := by
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hlog i (hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N := by
    have hg := hgeo j i hi pb hpb
    have hh := hg.2.2.2.2.2.2.2.2.1
    change _ ≤ (203/100 : ℝ)*N at hh
    linarith [log_natCast_nonneg (X j i pb)]
  have hPL i (hi : i ∈ I j) pb (hpb : pb ∈ B j i) : log pb.1 ≤ L := by
    have hP := (row_data (Finset.mem_filter.mp hpb).1).2.1
    change _ < (243/200 : ℝ)*N at hP
    have hn := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hT i (hi : i ∈ I j) pb (hpb : pb ∈ B j i) d
      (hd : d ∈ Finset.Icc (M j i pb+1) (X j i pb)) :
      1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    have hg := hgeo j i hi pb hpb
    have hm : 0 < M j i pb := hg.2.2.2.2.2.2.1
    have hmd : M j i pb ≤ d := by have := Finset.mem_Icc.mp hd; omega
    have hdlog := log_le_log (by exact_mod_cast hm : (0 : ℝ)<M j i pb)
      (by exact_mod_cast hmd : (M j i pb : ℝ)≤d)
    have hlo := hg.2.2.2.2.2.2.2.1
    change (39/20 : ℝ)*N ≤ _ at hlo
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have herr := source_scaled_edge_shells_error (I j) (B j) hN (M j) (X j) hL0
    (by linarith : 0 ≤ u) hU y (hI j)
    (fun i hi pb hpb => ⟨(hgeo j i hi pb hpb).1,
      (hgeo j i hi pb hpb).2.2.1,(hgeo j i hi pb hpb).2.2.2.1⟩)
    hlog (fun i hi pb hpb => (hgeo j i hi pb hpb).2.2.2.2.2.2.1)
    (fun _ _ _ hpb => (Finset.mem_filter.mp hpb).2)
    (fun i _ pb _ => boundary_le_twice _ _ i)
    (fun _ _ _ hpb => shell_large hpb) hPL hT
  have hsum : (∑ i ∈ I j, ∑ pb ∈ B j i,
      coreRow u y j pb.1 pb.2 (M j i pb) (X j i pb)) =
      (∑ i ∈ I j, ∑ pb ∈ B j i, densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))+
      (∑ i ∈ I j, ∑ pb ∈ B j i, ownedShellDiscrepancy N L y pb.1 pb.2 (M j i pb) (X j i pb))-
      (∑ i ∈ I j, ∑ pb ∈ B j i, overflowRow u y j pb.1 pb.2 (M j i pb) (X j i pb)) := by
    simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro pb hpb
    have h := coreRow_add_overflow_of_geometry (y := y) j hj hu hU hL (hgeo j i hi pb hpb) (hpA j i hi pb hpb)
    change _+_=densityRow N L y _ _ _ _+ownedShellDiscrepancy N L y _ _ _ _ at h
    linarith
  have hm := source_scaled_ownerGapDensityMain_bound (by linarith : 0 ≤ u) hU hN hL hy
  change |u^(N+1)*ownerGapLiteralRows u y j| ≤ edgeRowBudget y N
  rw [ownerGapLiteralRows,← sum_coreRow_shells u y j hL]
  change |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i, coreRow u y j pb.1 pb.2 (M j i pb) (X j i pb))| ≤ _
  rw [hsum,mul_sub,mul_add]
  have hmain : |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
      densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))| ≤ fineMainBudget y N := by
    simpa only [I,B,M,X,N,L,sum_densityRow_shells u y (dyadicMomentOrder j) hL,
      ownerGapDensityMain] using hm
  calc
    _ ≤ |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))|+
        |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          ownedShellDiscrepancy N L y pb.1 pb.2 (M j i pb) (X j i pb))|+
        |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          overflowRow u y j pb.1 pb.2 (M j i pb) (X j i pb))| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ fineMainBudget y N+
        edgeErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N+
        highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N :=
      add_le_add (add_le_add hmain herr) hcount
    _ = edgeRowBudget y N := rfl

/-- Concrete source-o(1) saving for the ORIGINAL retained signed
prime-incidence sum on the enlarged population. -/
theorem tendsto_ownerGapLiteralRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*ownerGapLiteralRows u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => edgeRowBudget y (dyadicMomentOrder j)) ?_
    ((tendsto_edgeRowBudget y).comp tendsto_dyadicMomentOrder)
  simpa only [Real.norm_eq_abs] using eventually_abs_ownerGapLiteralRows_bound hu hU hy



private theorem endpoint_cofactor {u : ℝ} {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hpb : pb ∈ ownerGapRows u N)
    (hsieve : sieve (pb.1*pb.2).primeFactors (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ≠ 0) :
    Squarefree (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ∧
      2 ≤ (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2).primeFactors.card ∧
      ∀ q ∈ (pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2).primeFactors, q < pb.1 := by
  have hg := ownerGap_row_geometry hpb
  have hd1 : 1 < ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := by
    have h := row_large hpb
    have he := add_one_le_exp ((N : ℝ)/2000)
    have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
    have hr : (1 : ℝ)<ZetaRieszFineDivisorRows.lower N pb.1 pb.2 := by linarith
    exact_mod_cast hr
  exact closed_row_cofactor_geometry hg
    (Finset.mem_Icc.mpr ⟨le_rfl,(row_data hpb).2.2⟩) hd1 hsieve


private theorem endpoint_atom_bound {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ ownerGapRows u N) (y : ℝ) :
    |rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N) N
      (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2 (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)| ≤
        radialEnvelope N*exp (-(N : ℝ)/2000)/(pb.1*pb.2 : ℕ) := by
  have hg := ownerGap_row_geometry hpb
  let d := ZetaRieszFineDivisorRows.lower N pb.1 pb.2
  let L := SquarefreeVaughanLogSource.length u N
  change |rowAtom _ N L y pb.1 pb.2 d| ≤ _
  have hd0 : 0 < d := Nat.ceil_pos.mpr (exp_pos _)
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hpb0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by exact_mod_cast Nat.mul_pos hg.1.pos hb0
  have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0 < L := by dsimp [L]; nlinarith
  have hP : log pb.1 ≤ L := by
    have hp := (row_data hpb).2.1
    dsimp [L]
    nlinarith
  by_cases hz : sieve (pb.1*pb.2).primeFactors d=0
  · simp only [rowAtom,hz,mul_zero,abs_zero]
    positivity [radialEnvelope_pos N]
  have hco := endpoint_cofactor hN hpb hz
  have houter : Squarefree (pb.1*pb.2) := Nat.squarefree_mul_iff.mpr
    ⟨hg.1.coprime_iff_not_dvd.mpr hg.2.2.2.1,hg.1.squarefree,hg.2.2.1⟩
  have hsieve : sieve (pb.1*pb.2).primeFactors d=1 := by
    rw [sieve_eq_product_squarefree houter] at hz ⊢
    by_cases hs : Squarefree ((pb.1*pb.2)*d)
    · simp only [if_pos hs]
    · simp only [if_neg hs,not_true_eq_false] at hz
  have hT : 1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    have hlo := hg.2.2.2.2.2.2.2.1
    change (39/20 : ℝ)*N ≤ log (pb.1*pb.2 : ℕ)+log d at hlo
    linarith
  have hPT : log pb.1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hg.1.ne_zero) (by exact_mod_cast hb0.ne')]
    linarith [log_natCast_nonneg pb.2,log_natCast_nonneg d]
  have hamp := ownedAmplitude_bound N (log_natCast_nonneg pb.1) hT hPT
  have hh := pairHinge_bounds L pb.1 pb.2
  have hm : |(μ pb.2 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := pb.2)
  rw [rowAtom,owner_phase_eq_amplitude (ZetaRieszAnnulusJoint.intermediatePrimes u N) N L y
    hg.1 hb0 hd0 hco.1 hco.2.1 hco.2.2
    (row_owner_mem hpb),hsieve,mul_one,abs_mul,abs_mul,abs_div,abs_mul,
    abs_of_pos (by positivity : 0 < L*(pb.1*pb.2 : ℕ)*d),abs_of_nonneg hh.1]
  have hc := abs_cos_le_one (y*(log (pb.1*pb.2 : ℕ)+log d))
  have hR := radialEnvelope_pos N
  have hnum : |ownedAmplitude N (log pb.1) (log (pb.1*pb.2 : ℕ)) d|
      *|cos (y*(log (pb.1*pb.2 : ℕ)+log d))| * |(μ pb.2 : ℝ)| * pairHinge L pb.1 pb.2 ≤
      radialEnvelope N*L := by
    have h1 := mul_le_mul hamp hc (abs_nonneg _) (radialEnvelope_pos N).le
    have h2 := mul_le_mul h1 hm (abs_nonneg _) (by positivity : 0 ≤ radialEnvelope N*1)
    exact (mul_le_mul h2 (hh.2.trans hP) hh.1 (by positivity : 0 ≤ radialEnvelope N*1*1)).trans_eq
      (by ring)
  have hdlarge := row_large hpb
  have hinv : (d : ℝ)⁻¹ ≤ exp (-(N : ℝ)/2000) := by
    rw [neg_div,exp_neg]
    exact inv_anti₀ (exp_pos _) hdlarge
  calc
    _ = (|ownedAmplitude N (log pb.1) (log (pb.1*pb.2 : ℕ)) d|
        *|cos (y*(log (pb.1*pb.2 : ℕ)+log d))| * |(μ pb.2 : ℝ)| * pairHinge L pb.1 pb.2)/
          (L*(pb.1*pb.2 : ℕ)*d) := by ring
    _ ≤ radialEnvelope N*L/(L*(pb.1*pb.2 : ℕ)*d) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = radialEnvelope N/(pb.1*pb.2 : ℕ)*(d : ℝ)⁻¹ := by field_simp
    _ ≤ radialEnvelope N/(pb.1*pb.2 : ℕ)*exp (-(N : ℝ)/2000) :=
      mul_le_mul_of_nonneg_left hinv (by positivity [radialEnvelope_pos N])
    _ = _ := by ring



/-- The original core-masked rounded endpoint of each new row. -/
def ownerGapEndpointRows (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  ∑ pb ∈ ownerGapRows u N,
    if pb.1*(pb.2*ZetaRieszFineDivisorRows.lower N pb.1 pb.2) ∈ ZetaRieszParityPacket.coreBand u N (dyadicPrimeCount j)
      then rowAtom A N L y pb.1 pb.2 (ZetaRieszFineDivisorRows.lower N pb.1 pb.2) else 0


theorem source_scaled_ownerGapEndpointRows_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (j : ℕ)
    (hN : 32 ≤ dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    |u^(dyadicMomentOrder j+1)*ownerGapEndpointRows u y j| ≤
      edgeEndpointBudget (dyadicMomentOrder j) := by
  let N := dyadicMomentOrder j
  have hsum : |ownerGapEndpointRows u y j| ≤
      radialEnvelope N*exp (-(N : ℝ)/2000)*(1+(203/100 : ℝ)*N)^2 := by
    unfold ownerGapEndpointRows
    dsimp only
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ pb ∈ ownerGapRows u N,
          radialEnvelope N*exp (-(N : ℝ)/2000)/(pb.1*pb.2 : ℕ) := by
        apply Finset.sum_le_sum
        intro pb hpb
        split_ifs
        · exact endpoint_atom_bound hN hL hpb y
        · simp only [abs_zero]
          positivity [radialEnvelope_pos N]
      _ = radialEnvelope N*exp (-(N : ℝ)/2000)*
          (∑ pb ∈ ownerGapRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pb _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (outer_harmonic_bound u N)
        (by positivity [radialEnvelope_pos N])
  have h2u : 2*u ≤ exp (1/10000 : ℝ) := by
    have he := add_one_le_exp (1/10000 : ℝ)
    have huU : u ≤ (10001/20000 : ℝ) := hU
    linarith
  have hr : (2*u)^N*exp (-(N : ℝ)/2000) ≤ edgeEndpointRate^N := by
    calc
      _ ≤ (exp (1/10000 : ℝ))^N*exp (-(N : ℝ)/2000) := by gcongr
      _ = exp (-(1/2500 : ℝ))^N := by
        rw [← exp_nat_mul,← exp_add,← exp_nat_mul]
        congr 1
        ring
      _ = _ := rfl
  have hp : (1+(203/100 : ℝ)*N)^2 ≤ 9*((N : ℝ)+1)^2 := by
    have hh : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact (pow_le_pow_left₀ (by positivity) hh 2).trans_eq (by ring)
  have hf : 2*u*((N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
  apply (mul_le_mul_of_nonneg_left hsum (pow_nonneg hu _)).trans
  have heq : u^(N+1)*(radialEnvelope N*exp (-(N : ℝ)/2000)*
      (1+(203/100 : ℝ)*N)^2) =
      (2*u*((N : ℝ)+1))*((2*u)^N*exp (-(N : ℝ)/2000))*
        (1+(203/100 : ℝ)*N)^2 := by
    unfold radialEnvelope
    rw [pow_succ,pow_succ,mul_pow]
    ring
  rw [heq]
  have hh := mul_le_mul
    (mul_le_mul hf hr (by positivity) (by positivity)) hp
    (sq_nonneg _) (by positivity [edgeEndpointRate_bounds.1])
  convert hh using 1
  unfold edgeEndpointBudget
  ring

/-- The endpoint payment tends to zero at source scale. -/
theorem tendsto_ownerGapEndpointRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*ownerGapEndpointRows u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => edgeEndpointBudget (dyadicMomentOrder j)) ?_
    (tendsto_edgeEndpointBudget.comp tendsto_dyadicMomentOrder)
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ)),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
        (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source))] with j hN hL
  have hL' : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hL]
  simpa only [Real.norm_eq_abs] using
    source_scaled_ownerGapEndpointRows_bound (by linarith : 0 ≤ u) hU y j hN hL'


/-- No original integer endpoint is dropped by the closed row identity. -/
theorem ownerGap_rows_closed_eq (u y : ℝ) (j : ℕ) :
    (∑ pb ∈ ownerGapRows u (dyadicMomentOrder j),
      ∑ d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
        (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2),
        if pb.1*(pb.2*d) ∈ ZetaRieszParityPacket.coreBand u
            (dyadicMomentOrder j) (dyadicPrimeCount j)
          then rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
            (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
            y pb.1 pb.2 d else 0) = ownerGapLiteralRows u y j+ownerGapEndpointRows u y j := by
  simp only [ownerGapLiteralRows,ownerGapEndpointRows,coreRow]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (row_data hpb).2.2
  have he : Finset.Icc (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2) =
      insert (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
        (Finset.Ioc (ZetaRieszFineDivisorRows.lower (dyadicMomentOrder j) pb.1 pb.2)
          (ZetaRieszFineDivisorRows.upper (dyadicMomentOrder j) pb.1 pb.2)) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_Ioc]
    omega
  rw [he,Finset.sum_insert (by simp)]
  ring


theorem ownerGap_literal_row_covered {u : ℝ} {N p b d : ℕ}
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (hb : 1 < b) (hs : Squarefree b) (hpd : ¬p ∣ b)
    (hmax : ∀ q ∈ b.primeFactors, q < p)
    (ha : pairHinge (SquarefreeVaughanLogSource.length u N) p b ≠ 0)
    (hc : log (p*b : ℕ) ≤ (3899/2000 : ℝ)*N)
    (hP : log p < (243/200 : ℝ)*N)
    (hgap : (203/100 : ℝ)*N < log (p*b : ℕ)+log p)
    (hlo : (39/20 : ℝ)*N < log (p*b : ℕ)+log d)
    (hhi : log (p*b : ℕ)+log d ≤ (203/100 : ℝ)*N) :
    (p,b) ∈ ownerGapRows u N ∧ d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N p b) (ZetaRieszFineDivisorRows.upper N p b) := by
  have hpP := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1
  have hb0 : 0 < b := by omega
  have hd0 : 0 < d := by
    by_contra hn
    have hd : d=0 := by omega
    rw [hd,Nat.cast_zero,log_zero,add_zero] at hlo
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hdl : ZetaRieszFineDivisorRows.lower N p b ≤ d := by
    apply Nat.ceil_le.mpr
    have hh := exp_le_exp.mpr (by linarith : (39/20 : ℝ)*N-log (p*b : ℕ) ≤ log d)
    simpa only [exp_log (by exact_mod_cast hd0 : (0 : ℝ)<d)] using hh
  have hdu : d ≤ ZetaRieszFineDivisorRows.upper N p b := by
    apply Nat.le_floor
    have hh := exp_le_exp.mpr (by linarith : log d ≤ (203/100 : ℝ)*N-log (p*b : ℕ))
    simpa only [exp_log (by exact_mod_cast hd0 : (0 : ℝ)<d)] using hh
  have hlog : log (p*b : ℕ)=log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hpP.ne_zero) (by exact_mod_cast hb0.ne')]
  have hbB : b ≤ ⌊exp ((203/100 : ℝ)*N)⌋₊ := by
    apply Nat.le_floor
    have hhlog : log b ≤ (203/100 : ℝ)*N := by
      rw [hlog] at hhi
      linarith [log_natCast_nonneg p,log_natCast_nonneg d]
    have hh := exp_le_exp.mpr hhlog
    simpa only [exp_log (by exact_mod_cast hb0 : (0 : ℝ)<b)] using hh
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨hp,Finset.mem_Icc.mpr ⟨by omega,hbB⟩⟩,hs,hpd,hmax,ha,hc,hP,hgap,
      hdl.trans hdu⟩,Finset.mem_Icc.mpr ⟨hdl,hdu⟩⟩


/-- The whole closed original ownership-gap population is independently
source-o(1), including every rounded endpoint and every prime count. -/
theorem tendsto_ownerGapClosedRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      (ownerGapLiteralRows u y j+ownerGapEndpointRows u y j)) atTop (𝓝 0) := by
  simpa only [mul_add,zero_add] using
    (tendsto_ownerGapLiteralRows hu hU hy).add (tendsto_ownerGapEndpointRows hu hU y)




/-- All four previously paid closed-row families are included in this
single common signed population. Their credits are replaced, not added. -/
theorem previous_rows_subset_ownerGap (u : ℝ) (N : ℕ) :
    fineRows u N ∪ ZetaRieszOwnerSafeRows.ownerSafeRows u N ∪
      ZetaRieszEdgeDivisorRows.edgeRows u N ∪
      ZetaRieszLowOwnerRows.lowOwnerRows u N ⊆ ownerGapRows u N := by
  intro pb hpb
  have hN := Nat.cast_nonneg (α := ℝ) N
  rcases Finset.mem_union.mp hpb with hpb | hpb
  · rcases Finset.mem_union.mp hpb with hpb | hpb
    · rcases Finset.mem_union.mp hpb with hpb | hpb
      · obtain ⟨hprod,hs,hpd,hmax,ha,hc,hP,hSat,hlu⟩ := Finset.mem_filter.mp hpb
        have hp := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp
          (Finset.mem_product.mp hprod).1).1
        have hb0 : 0 < pb.2 := by have := (Finset.mem_Icc.mp (Finset.mem_product.mp hprod).2).1; omega
        have hlog : log (pb.1*pb.2 : ℕ)=log pb.1+log pb.2 := by
          rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hb0.ne')]
        have hActive := pairHinge_active ha
        rw [← hlog] at hActive
        exact Finset.mem_filter.mpr ⟨hprod,hs,hpd,hmax,ha,by linarith,hP,by linarith,hlu⟩
      · obtain ⟨hprod,hs,hpd,hmax,ha,hc,hP,_hUnsat,hPl,hcl,hlu⟩ := Finset.mem_filter.mp hpb
        dsimp [ZetaRieszOwnerSafeRows.ownershipLength] at hcl
        exact Finset.mem_filter.mpr ⟨hprod,hs,hpd,hmax,ha,by linarith,hP,by linarith,hlu⟩
    · obtain ⟨hprod,hs,hpd,hmax,ha,hc,hP,_hcl,hPl,_hOwnership,hlu⟩ := Finset.mem_filter.mp hpb
      exact Finset.mem_filter.mpr ⟨hprod,hs,hpd,hmax,ha,hc,hP,by linarith,hlu⟩
  · obtain ⟨hprod,hs,hpd,hmax,ha,hc,hP,_hUnsat,⟨hPl,_hPu⟩,hcl,hlu⟩ := Finset.mem_filter.mp hpb
    dsimp [ZetaRieszLowOwnerRows.ownershipLength] at hcl
    exact Finset.mem_filter.mpr ⟨hprod,hs,hpd,hmax,ha,hc,hP,by linarith,hlu⟩

/-- The unsigned unit is still outside the whole common closed row. -/
theorem ownerGap_unsigned_gt_one {u : ℝ} {N : ℕ} (hN : 0 < N) {pb : ℕ×ℕ}
    (hpb : pb ∈ ownerGapRows u N) {d : ℕ}
    (hd : d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2)) : 1 < d := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hle : (ZetaRieszFineDivisorRows.lower N pb.1 pb.2 : ℝ) ≤ d := by
    exact_mod_cast (Finset.mem_Icc.mp hd).1
  have h : (1 : ℝ)<d := (one_lt_exp_iff.mpr (by linarith : (0 : ℝ)<N/2000)).trans_le
    ((row_large hpb).trans hle)
  exact_mod_cast h

/-- Every nonzero common closed row is a literal original cofactor
incidence, with the genuine largest-prime owner. -/
theorem ownerGap_closed_incidence_original {u : ℝ} {N : ℕ} (hN : 0 < N)
    {pb : ℕ×ℕ} (hpb : pb ∈ ownerGapRows u N) {d : ℕ}
    (hd : d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2))
    (hs : sieve (pb.1*pb.2).primeFactors d ≠ 0) :
    (d,pb.2) ∈ (pb.1*(pb.2*d)/ZetaRieszPrimeEndpoint.largestPrime
      (pb.1*(pb.2*d))).divisorsAntidiagonal ∧
      ZetaRieszPrimeEndpoint.largestPrime (pb.1*(pb.2*d)) = pb.1 := by
  have hg := ownerGap_row_geometry hpb
  have hc := closed_row_cofactor_geometry hg hd (ownerGap_unsigned_gt_one hN hpb hd) hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d) hg.1 hc.1.ne_zero hc.2.2
  refine ⟨?_,ho⟩
  rw [ho,Nat.mul_div_cancel_left _ hg.1.pos]
  exact Nat.mem_divisorsAntidiagonal.mpr ⟨by ac_rfl,hc.1.ne_zero⟩

/-- No common row credit overlaps the independently paid whole
large-owner labels, even at the original rounded endpoint. -/
theorem ownerGap_closed_label_not_largeOwner {u : ℝ} {N K : ℕ} (hN : 0 < N)
    {pb : ℕ×ℕ} (hpb : pb ∈ ownerGapRows u N) {d : ℕ}
    (hd : d ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2))
    (hs : sieve (pb.1*pb.2).primeFactors d ≠ 0) :
    pb.1*(pb.2*d) ∉ largeOwnerLabels u N K := by
  intro hn
  have hg := ownerGap_row_geometry hpb
  have hc := closed_row_cofactor_geometry hg hd (ownerGap_unsigned_gt_one hN hpb hd) hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d) hg.1 hc.1.ne_zero hc.2.2
  have hP := (row_data hpb).2.1
  have hhigh := (Finset.mem_filter.mp hn).2.2.2.2.1
  rw [ho] at hhigh
  linarith

/-- A remaining original incidence is either on the short unsigned leg
or within the stated logarithmic gap of its owner. This is a support
statement for the signed rest, not an allowance for its terms. -/
theorem unselected_unsigned_geometry {u : ℝ} {N p b d : ℕ}
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (hb : 1 < b) (hs : Squarefree b) (hpd : ¬p ∣ b)
    (hmax : ∀ q ∈ b.primeFactors, q < p)
    (ha : pairHinge (SquarefreeVaughanLogSource.length u N) p b ≠ 0)
    (hP : log p < (243/200 : ℝ)*N)
    (hlo : (39/20 : ℝ)*N < log (p*b : ℕ)+log d)
    (hhi : log (p*b : ℕ)+log d ≤ (203/100 : ℝ)*N)
    (hnot : (p,b) ∉ ownerGapRows u N) :
    log d < (161/2000 : ℝ)*N ∨ log p < log d+(2/25 : ℝ)*N := by
  by_contra h
  push Not at h
  have hc : log (p*b : ℕ) ≤ (3899/2000 : ℝ)*N := by linarith [h.1]
  have hgap : (203/100 : ℝ)*N < log (p*b : ℕ)+log p := by linarith [h.2]
  exact hnot (ownerGap_literal_row_covered hp hb hs hpd hmax ha hc hP hgap hlo hhi).1

/-- Outside the short-leg boundary, every unselected active incidence
has a uniform remaining owner ceiling. The original sign is untouched. -/
theorem unselected_owner_ceiling {u : ℝ} {N p b d : ℕ}
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (hb : 1 < b) (hs : Squarefree b) (hpd : ¬p ∣ b)
    (hmax : ∀ q ∈ b.primeFactors, q < p)
    (ha : pairHinge (SquarefreeVaughanLogSource.length u N) p b ≠ 0)
    (hP : log p < (243/200 : ℝ)*N)
    (hlo : (39/20 : ℝ)*N < log (p*b : ℕ)+log d)
    (hhi : log (p*b : ℕ)+log d ≤ (203/100 : ℝ)*N)
    (hnot : (p,b) ∉ ownerGapRows u N)
    (hd : (161/2000 : ℝ)*N ≤ log d)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    log p < (147/200 : ℝ)*N := by
  have hgeometry := unselected_unsigned_geometry hp hb hs hpd hmax ha hP hlo hhi hnot
  have hnear : log p < log d+(2/25 : ℝ)*N := hgeometry.resolve_left (not_lt_of_ge hd)
  have hactive := pairHinge_active ha
  have hpP := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1
  have hb0 : 0 < b := by omega
  have hlog : log (p*b : ℕ)=log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hpP.ne_zero) (by exact_mod_cast hb0.ne')]
  rw [← hlog] at hactive
  linarith

/-- One signed remainder after replacing the four old row credits by
the common population. All other incidences stay joined. -/
def ownerGapRemaining (u y : ℝ) (j : ℕ) : ℝ :=
  (coreConvolution u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
    (largeOwnerIncidences u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
      (ownerGapLiteralRows u y j+ownerGapEndpointRows u y j)

/-- The shared carrier/nonowner payment occurs once. The full common
row payment occurs once, regardless of how many older cones it contains. -/
def ownerGapErrorBudget (y : ℝ) (N : ℕ) : ℝ :=
  (joinedRowErrorBudget y N-rowErrorBudget y N)+
    ZetaRieszJointOwnerEnvelope.literalErrorBudget N+edgeRowBudget y N+edgeEndpointBudget N

/-- Every payment in the common signed ledger is source-o(1). -/
theorem tendsto_ownerGapErrorBudget (y : ℝ) :
    Tendsto (ownerGapErrorBudget y) atTop (𝓝 0) := by
  change Tendsto (fun N => (joinedRowErrorBudget y N-rowErrorBudget y N)+
    ZetaRieszJointOwnerEnvelope.literalErrorBudget N+edgeRowBudget y N+edgeEndpointBudget N)
      atTop (𝓝 0)
  simpa only [zero_sub,neg_zero,zero_add] using
    ((((tendsto_joinedRowErrorBudget y).sub (tendsto_rowErrorBudget y)).add
      ZetaRieszJointOwnerEnvelope.tendsto_literalErrorBudget).add
      (tendsto_edgeRowBudget y)).add tendsto_edgeEndpointBudget

/-- An independent geometric estimate on the WHOLE real carrier's
change after the complete ownership-gap signed population is paid. -/
theorem eventually_abs_joined_sub_ownerGapRemaining_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          ownerGapRemaining u y j)| ≤ ownerGapErrorBudget y (dyadicMomentOrder j) := by
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [eventually_abs_ownerGapLiteralRows_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually hl,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (320 : ℕ))]
    with j hNew hlength hN
  have hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hlength]
  have hEnd := source_scaled_ownerGapEndpointRows_bound (by linarith : 0 ≤ u) hU y j
    (by omega : 32 ≤ dyadicMomentOrder j) hL
  have hBase := (Complex.abs_re_le_norm ((u : ℂ)^(dyadicMomentOrder j+1)*
    (ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      coreConvolution u y (dyadicMomentOrder j) (dyadicPrimeCount j)))).trans
    (joined_sub_convolution_bound (by linarith : 0 ≤ u) hU _ _ y hL)
  have hLarge := (Complex.abs_re_le_norm ((u : ℂ)^(dyadicMomentOrder j+1)*
    largeOwnerIncidences u y (dyadicMomentOrder j) (dyadicPrimeCount j))).trans
    (source_scaled_largeOwnerIncidences_bound (by linarith : 0 ≤ u) hU hN y (dyadicPrimeCount j))
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.sub_re] at hBase
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hLarge
  have hbase' : |u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        (coreConvolution u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re)| ≤
      joinedRowErrorBudget y (dyadicMomentOrder j)-rowErrorBudget y (dyadicMomentOrder j) := by
    dsimp only [joinedRowErrorBudget]
    linarith [hBase]
  rw [ownerGapRemaining,show u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        ((coreConvolution u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          (largeOwnerIncidences u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
            (ownerGapLiteralRows u y j+ownerGapEndpointRows u y j))) =
      u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          (coreConvolution u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re)+
        u^(dyadicMomentOrder j+1)*(largeOwnerIncidences u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re+
        u^(dyadicMomentOrder j+1)*ownerGapLiteralRows u y j+
        u^(dyadicMomentOrder j+1)*ownerGapEndpointRows u y j by ring]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add hbase' hLarge)) hNew)) hEnd)

/-- The numerical floor remains an OPEN independent bound for this smaller
signed rest. No source has been discarded by the common payment. -/
theorem tendsto_joined_re_sub_ownerGapRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        ownerGapRemaining u y j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => ownerGapErrorBudget y (dyadicMomentOrder j)) ?_
    ((tendsto_ownerGapErrorBudget y).comp tendsto_dyadicMomentOrder)
  simpa only [Real.norm_eq_abs] using eventually_abs_joined_sub_ownerGapRemaining_bound hu hU hy

/-- Whole-carrier one-sided comparison after the common signed payment;
its remaining scalar still needs the independent numerical floor. -/
theorem eventually_joined_floor_with_ownerGapRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*ownerGapRemaining u y j-
        ownerGapErrorBudget y (dyadicMomentOrder j) ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_abs_joined_sub_ownerGapRemaining_bound hu hU hy] with j hj
  have h := (abs_le.mp hj).1
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  nlinarith

/-- Frozen row multipliers retain the original phase, allocation and
count masks. This exact identity is used to pay a literal count boundary. -/
theorem sum_weightedMaskedRows_eq_partial_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (u y : ℝ) (j : ℕ) (χ : ℕ → Prop) (ℒ : (ℕ×ℕ) → ℝ) (κ : ℕ×ℕ → ℝ)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) (ℒ pb) pb.1 pb.2 (M pb) (X pb)) :
    (∑ pb ∈ B, κ pb*∑ d ∈ Finset.Ioc (M pb) (X pb),
      if χ (pb.1*(pb.2*d)) then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          y pb.1 pb.2 d else 0) =
      (∑ n ∈ ((incidences B M X).image Prod.fst).filter
        χ,
        weightedPartialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
          {ZetaRieszPrimeEndpoint.largestPrime n})
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2))*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n db => if χ n then
    κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2)*incidenceWeight A N L y n db else 0
  have hrows : (∑ pb ∈ B, κ pb*∑ d ∈ Finset.Ioc (M pb) (X pb),
      if χ (pb.1*(pb.2*d)) then rowAtom A N L y pb.1 pb.2 d else 0) =
      ∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
        if sieve (pb.1*pb.2).primeFactors d ≠ 0 then f (pb.1*(pb.2*d)) (d,pb.2) else 0 := by
    apply Finset.sum_congr rfl
    intro pb hpb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hs : sieve (pb.1*pb.2).primeFactors d=0
    · simp [rowAtom,hs]
    rw [if_pos hs,rowAtom_eq_incidenceWeight_of_geometry A y (hg pb hpb) hd hs]
    have hco := row_cofactor_geometry (hg pb hpb) hd hs
    have ho := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d)
      (hg pb hpb).1 hco.1.ne_zero hco.2.2
    dsimp only [f]
    rw [ho]
    split_ifs <;> simp [N]
  rw [hrows,sum_rows_eq_incidences B M X hg f,sum_incidences_eq_fibers]
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hk : χ n
  · simp only [f,if_pos hk]
    have he : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      obtain ⟨v,hv,hnv⟩ := Finset.mem_image.mp hn
      have ho := incidence_owner hg hv
      rw [← hnv,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    simp only [incidenceWeight,phaseWeight,weightedPartialCoefficient,he,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro db _
    ring
  · simp only [f,if_neg hk,Finset.sum_const_zero]

private theorem selected_multiplier_bound {B : Finset (ℕ×ℕ)}
    {M X : ℕ×ℕ → ℕ} {N : ℕ} {ℒ : ℕ×ℕ → ℝ}
    (hg : ∀ pb ∈ B, RowGeometry N (ℒ pb) pb.1 pb.2 (M pb) (X pb))
    (κ : ℕ×ℕ → ℝ) (hκ : ∀ pb ∈ B, |κ pb| ≤ 4) {n : ℕ}
    {db : ℕ×ℕ} (hdb : db ∈ selectedDivisors B M X n) :
    |κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2)| ≤ 4 := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hdb
  obtain ⟨hv,hn⟩ := Finset.mem_filter.mp hv
  obtain ⟨pb,hpb,d,hd,hs,rfl⟩ := mem_incidences hv
  have hco := row_cofactor_geometry (hg pb hpb) hd hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d)
    (hg pb hpb).1 hco.1.ne_zero hco.2.2
  rw [← hn,ho]
  exact hκ pb hpb

/-- Independent high-count payment for arbitrary frozen multipliers
bounded by four. The low-count signed main is not normed here. -/
theorem weighted_overflowRows_bound_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (j : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (ℒ : (ℕ×ℕ) → ℝ) (κ : ℕ×ℕ → ℝ)
    (hκ : ∀ pb ∈ B, |κ pb| ≤ 4)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) (ℒ pb) pb.1 pb.2 (M pb) (X pb)) :
    |u^(dyadicMomentOrder j+1)*∑ pb ∈ B,
      κ pb*overflowRow u y j pb.1 pb.2 (M pb) (X pb)| ≤
        4*highCountConstant*(dyadicMomentOrder j : ℝ)*(97/100 : ℝ)^(dyadicMomentOrder j)*
          exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100)) := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let S := ((incidences B M X).image Prod.fst).filter
    (fun n => dyadicPrimeCount j ≤ n.primeFactors.card)
  let c := fun n => weightedPartialCoefficient
    (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      L N (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
        (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2))/8
  have hn n (h : n ∈ S) : ∃ v ∈ incidences B M X, v.1=n :=
    Finset.mem_image.mp (Finset.mem_filter.mp h).1
  have hsf n (h : n ∈ S) : Squarefree n := by
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using (incidence_owner hg hv).1
  have hband : S ⊆ zetaPrimeLogBand N := by
    intro n h
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using incidence_band
      (by dsimp [N,dyadicMomentOrder,dyadicPrimeCount]; positivity) hg hv
  have hc n (h : n ∈ S) : ‖c n‖ ≤ zetaMoebiusLogMajorant n := by
    obtain ⟨v,hv,he⟩ := hn n h
    have ho := incidence_owner hg hv
    have hpn : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      rw [← he,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    have hp : 0 < ZetaRieszPrimeEndpoint.largestPrime n := by
      by_contra hh
      have h0 : ZetaRieszPrimeEndpoint.largestPrime n=0 := by omega
      rw [h0,zero_mul] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have ha : (0 : ℕ) < n/ZetaRieszPrimeEndpoint.largestPrime n := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [h0,mul_zero] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have hT : log n ≤ 2*L := by
      simpa only [he] using incidence_log_le_twice_actual hL hg hv
    have hdom := weightedPartialCoefficient_bound
      (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      N hp ha (selectedDivisors B M X n) (selectedDivisors_subset hg n)
      (SquarefreeVaughanLogSource.length_pos u N) (by simpa only [hpn] using hT)
      (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2))
      (fun db hdb => selected_multiplier_bound hg κ hκ hdb)
    rw [hpn] at hdom
    dsimp [c]
    rw [norm_div]
    norm_num
    linarith
  have hnorm := ZetaRieszWeightedCount.norm_normalized_many_dyadic_le S c hc 1 j y hu hU
    (by norm_num : (0 : ℝ)<49/100) (by norm_num : (49/100 : ℝ)<1/2) hsf hband
    (fun n h => (Finset.mem_filter.mp h).2)
  have hP : (∑ k ∈ (1 : Polynomial ℂ).support,
      ‖(1 : Polynomial ℂ).coeff k‖*(49/100 : ℝ)⁻¹^k)=1 := by
    rw [← Polynomial.C_1,Polynomial.support_C (by norm_num : (1 : ℂ)≠0)]
    simp
  rw [hP,mul_one,show (3/2 : ℝ)-49/100=101/100 by norm_num] at hnorm
  have hreal : |u^(N+1)*∑ pb ∈ B, κ pb*overflowRow u y j pb.1 pb.2 (M pb) (X pb)| ≤
      8*‖(u : ℂ)^(N+1)*∑ n ∈ S,
        c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
    have heq := sum_weightedMaskedRows_eq_partial_of_geometry B M X u y j
      (fun n => dyadicPrimeCount j ≤ n.primeFactors.card) ℒ κ hg
    have heq' : (∑ pb ∈ B, κ pb*overflowRow u y j pb.1 pb.2 (M pb) (X pb)) =
        (∑ n ∈ S, weightedPartialCoefficient
          (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
          L N (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2))*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
      convert heq using 1
      · apply Finset.sum_congr rfl
        intro pb _
        congr 1
        unfold overflowRow
        dsimp only
        apply Finset.sum_congr rfl
        intro d _
        by_cases hk : dyadicPrimeCount j ≤ (pb.1*(pb.2*d)).primeFactors.card <;> simp [hk]
      · simp only [S,N,L]
        congr 1
        apply Finset.sum_congr
        · ext n
          simp
        · intro n _
          simp only
    rw [heq']
    have heq : (u : ℂ)^(N+1)*∑ n ∈ S,
        weightedPartialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2))*zetaPrimeLogKernel N (3/2+Complex.I*y) n =
        8*((u : ℂ)^(N+1)*∑ n ∈ S,
          c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
      calc
        _ = (u : ℂ)^(N+1)*(8*∑ n ∈ S,
            c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          rw [ZetaRieszJointAllocation.filter_one_eq]
          dsimp [c]
          ring
        _ = _ := by ring
    have hre := Complex.abs_re_le_norm
      ((u : ℂ)^(N+1)*∑ n ∈ S,
        weightedPartialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2))*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    have hrhs : ‖(u : ℂ)^(N+1)*∑ n ∈ S,
        weightedPartialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2))*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ =
        8*‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
      rw [heq,norm_mul]
      norm_num
    simpa only [S,L,N,← Complex.ofReal_pow,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre.trans_eq hrhs
  apply hreal.trans ((mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ)≤8)).trans _)
  have hr : 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) ≤ 97/100 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  have hr0 : 0 ≤ 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  dsimp [highCountConstant]
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr N)
    (by dsimp [ZetaRieszWideOwnerAudit.radiusCeiling]
        positivity [log_pos (by norm_num : (1 : ℝ)<2)] : 0 ≤ 64*ZetaRieszWideOwnerAudit.radiusCeiling*log 2*N)
  have he := mul_le_mul_of_nonneg_right hp
    (exp_pos (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100))).le
  convert mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ)≤4) using 1 <;> dsimp only [N] <;> ring


/-- An arbitrary incidence multiplier is retained before joining all original
labels and counts. This identity is used only for the independently paid
high-count boundary of the canonical clipped-block population. -/
theorem sum_incidenceWeightedRows_eq_partial_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (u y : ℝ) (j : ℕ) (χ : ℕ → Prop) (ℒ : (ℕ×ℕ) → ℝ) (κ : ℕ×ℕ → ℕ → ℝ)
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) (ℒ pb) pb.1 pb.2 (M pb) (X pb)) :
    (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      κ pb d*(if χ (pb.1*(pb.2*d)) then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          y pb.1 pb.2 d else 0)) =
      (∑ n ∈ ((incidences B M X).image Prod.fst).filter
        χ,
        weightedPartialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
          {ZetaRieszPrimeEndpoint.largestPrime n})
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2) db.1)*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n db => if χ n then
    κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2) db.1*incidenceWeight A N L y n db else 0
  have hrows : (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      κ pb d*(if χ (pb.1*(pb.2*d)) then rowAtom A N L y pb.1 pb.2 d else 0)) =
      ∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
        if sieve (pb.1*pb.2).primeFactors d ≠ 0 then f (pb.1*(pb.2*d)) (d,pb.2) else 0 := by
    apply Finset.sum_congr rfl
    intro pb hpb
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hs : sieve (pb.1*pb.2).primeFactors d=0
    · simp [rowAtom,hs]
    rw [if_pos hs,rowAtom_eq_incidenceWeight_of_geometry A y (hg pb hpb) hd hs]
    have hco := row_cofactor_geometry (hg pb hpb) hd hs
    have ho := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d)
      (hg pb hpb).1 hco.1.ne_zero hco.2.2
    dsimp only [f]
    rw [ho]
    split_ifs <;> simp [N]
  rw [hrows,sum_rows_eq_incidences B M X hg f,sum_incidences_eq_fibers]
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hk : χ n
  · simp only [f,if_pos hk]
    have he : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      obtain ⟨v,hv,hnv⟩ := Finset.mem_image.mp hn
      have ho := incidence_owner hg hv
      rw [← hnv,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    simp only [incidenceWeight,phaseWeight,weightedPartialCoefficient,he,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro db _
    ring
  · simp only [f,if_neg hk,Finset.sum_const_zero]

private theorem selected_incidence_multiplier_bound {B : Finset (ℕ×ℕ)}
    {M X : ℕ×ℕ → ℕ} {N : ℕ} {ℒ : ℕ×ℕ → ℝ}
    (hg : ∀ pb ∈ B, RowGeometry N (ℒ pb) pb.1 pb.2 (M pb) (X pb))
    (κ : ℕ×ℕ → ℕ → ℝ) (hκ : ∀ pb ∈ B, ∀ d ∈ Finset.Ioc (M pb) (X pb), |κ pb d| ≤ 4) {n : ℕ}
    {db : ℕ×ℕ} (hdb : db ∈ selectedDivisors B M X n) :
    |κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2) db.1| ≤ 4 := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hdb
  obtain ⟨hv,hn⟩ := Finset.mem_filter.mp hv
  obtain ⟨pb,hpb,d,hd,hs,rfl⟩ := mem_incidences hv
  have hco := row_cofactor_geometry (hg pb hpb) hd hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d)
    (hg pb hpb).1 hco.1.ne_zero hco.2.2
  rw [← hn,ho]
  exact hκ pb hpb d hd

/-- Independent high-count payment also tolerates the literal roughness
mask on each unsigned integer. Only this count boundary is normed. -/
theorem incidence_weighted_overflow_bound_of_geometry (B : Finset (ℕ×ℕ)) (M X : ℕ×ℕ → ℕ)
    (j : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (ℒ : (ℕ×ℕ) → ℝ) (κ : ℕ×ℕ → ℕ → ℝ)
    (hκ : ∀ pb ∈ B, ∀ d ∈ Finset.Ioc (M pb) (X pb), |κ pb d| ≤ 4)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hg : ∀ pb ∈ B, RowGeometry (dyadicMomentOrder j) (ℒ pb) pb.1 pb.2 (M pb) (X pb)) :
    |u^(dyadicMomentOrder j+1)*∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      κ pb d*(if dyadicPrimeCount j ≤ (pb.1*(pb.2*d)).primeFactors.card then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          y pb.1 pb.2 d else 0)| ≤
        4*highCountConstant*(dyadicMomentOrder j : ℝ)*(97/100 : ℝ)^(dyadicMomentOrder j)*
          exp (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100)) := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let S := ((incidences B M X).image Prod.fst).filter
    (fun n => dyadicPrimeCount j ≤ n.primeFactors.card)
  let c := fun n => weightedPartialCoefficient
    (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      L N (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
        (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2) db.1)/8
  have hn n (h : n ∈ S) : ∃ v ∈ incidences B M X, v.1=n :=
    Finset.mem_image.mp (Finset.mem_filter.mp h).1
  have hsf n (h : n ∈ S) : Squarefree n := by
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using (incidence_owner hg hv).1
  have hband : S ⊆ zetaPrimeLogBand N := by
    intro n h
    obtain ⟨v,hv,he⟩ := hn n h
    simpa only [he] using incidence_band
      (by dsimp [N,dyadicMomentOrder,dyadicPrimeCount]; positivity) hg hv
  have hc n (h : n ∈ S) : ‖c n‖ ≤ zetaMoebiusLogMajorant n := by
    obtain ⟨v,hv,he⟩ := hn n h
    have ho := incidence_owner hg hv
    have hpn : ZetaRieszPrimeEndpoint.largestPrime n*(n/ZetaRieszPrimeEndpoint.largestPrime n)=n := by
      rw [← he,← ho.2.2]
      simpa only [mul_comm v.2.1 v.2.2] using ho.2.1
    have hp : 0 < ZetaRieszPrimeEndpoint.largestPrime n := by
      by_contra hh
      have h0 : ZetaRieszPrimeEndpoint.largestPrime n=0 := by omega
      rw [h0,zero_mul] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have ha : (0 : ℕ) < n/ZetaRieszPrimeEndpoint.largestPrime n := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [h0,mul_zero] at hpn
      exact (hsf n h).ne_zero hpn.symm
    have hT : log n ≤ 2*L := by
      simpa only [he] using incidence_log_le_twice_actual hL hg hv
    have hdom := weightedPartialCoefficient_bound
      (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
      N hp ha (selectedDivisors B M X n) (selectedDivisors_subset hg n)
      (SquarefreeVaughanLogSource.length_pos u N) (by simpa only [hpn] using hT)
      (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2) db.1)
      (fun db hdb => selected_incidence_multiplier_bound hg κ hκ hdb)
    rw [hpn] at hdom
    dsimp [c]
    rw [norm_div]
    norm_num
    linarith
  have hnorm := ZetaRieszWeightedCount.norm_normalized_many_dyadic_le S c hc 1 j y hu hU
    (by norm_num : (0 : ℝ)<49/100) (by norm_num : (49/100 : ℝ)<1/2) hsf hband
    (fun n h => (Finset.mem_filter.mp h).2)
  have hP : (∑ k ∈ (1 : Polynomial ℂ).support,
      ‖(1 : Polynomial ℂ).coeff k‖*(49/100 : ℝ)⁻¹^k)=1 := by
    rw [← Polynomial.C_1,Polynomial.support_C (by norm_num : (1 : ℂ)≠0)]
    simp
  rw [hP,mul_one,show (3/2 : ℝ)-49/100=101/100 by norm_num] at hnorm
  have hreal : |u^(N+1)*∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
      κ pb d*(if dyadicPrimeCount j ≤ (pb.1*(pb.2*d)).primeFactors.card then
        rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          y pb.1 pb.2 d else 0)| ≤
      8*‖(u : ℂ)^(N+1)*∑ n ∈ S,
        c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
    have heq := sum_incidenceWeightedRows_eq_partial_of_geometry B M X u y j
      (fun n => dyadicPrimeCount j ≤ n.primeFactors.card) ℒ κ hg
    have heq' : (∑ pb ∈ B, ∑ d ∈ Finset.Ioc (M pb) (X pb),
        κ pb d*(if dyadicPrimeCount j ≤ (pb.1*(pb.2*d)).primeFactors.card then
          rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
            (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
            y pb.1 pb.2 d else 0)) =
        (∑ n ∈ S, weightedPartialCoefficient
          (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {ZetaRieszPrimeEndpoint.largestPrime n})
          L N (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2) db.1)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
      convert heq using 1
      · apply Finset.sum_congr rfl
        intro pb _
        apply Finset.sum_congr rfl
        intro d _
        by_cases hk : dyadicPrimeCount j ≤ (pb.1*(pb.2*d)).primeFactors.card <;> simp [hk]
      · congr 1
        apply Finset.sum_congr
        · ext n; simp [S]
        · intro n _; rfl
    rw [heq']
    have heq : (u : ℂ)^(N+1)*∑ n ∈ S,
        weightedPartialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2) db.1)*zetaPrimeLogKernel N (3/2+Complex.I*y) n =
        8*((u : ℂ)^(N+1)*∑ n ∈ S,
          c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
      calc
        _ = (u : ℂ)^(N+1)*(8*∑ n ∈ S,
            c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          rw [ZetaRieszJointAllocation.filter_one_eq]
          dsimp [c]
          ring
        _ = _ := by ring
    have hre := Complex.abs_re_le_norm
      ((u : ℂ)^(N+1)*∑ n ∈ S,
        weightedPartialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2) db.1)*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    have hrhs : ‖(u : ℂ)^(N+1)*∑ n ∈ S,
        weightedPartialCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
          {ZetaRieszPrimeEndpoint.largestPrime n}) L N
          (ZetaRieszPrimeEndpoint.largestPrime n) (n/ZetaRieszPrimeEndpoint.largestPrime n)
          (selectedDivisors B M X n) (fun db => κ (ZetaRieszPrimeEndpoint.largestPrime n,db.2) db.1)*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ =
        8*‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeFilterKernel 1 N (3/2+Complex.I*y) n‖ := by
      rw [heq,norm_mul]
      norm_num
    simpa only [S,L,N,← Complex.ofReal_pow,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre.trans_eq hrhs
  apply hreal.trans ((mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ)≤8)).trans _)
  have hr : 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) ≤ 97/100 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  have hr0 : 0 ≤ 16*ZetaRieszWideOwnerAudit.radiusCeiling/(17*(49/100 : ℝ)) := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  dsimp [highCountConstant]
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr N)
    (by dsimp [ZetaRieszWideOwnerAudit.radiusCeiling]
        positivity [log_pos (by norm_num : (1 : ℝ)<2)] : 0 ≤ 64*ZetaRieszWideOwnerAudit.radiusCeiling*log 2*N)
  have he := mul_le_mul_of_nonneg_right hp
    (exp_pos (2*(dyadicPrimeCount j : ℝ)*ZetaRieszPrimeCountMass.countMass (101/100))).le
  convert mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ)≤4) using 1 <;> dsimp only [N] <;> ring


end RiemannGaussian.ZetaRieszOwnerGapRows
