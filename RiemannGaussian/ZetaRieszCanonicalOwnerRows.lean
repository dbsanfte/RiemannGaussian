/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSaturatedRowFloor

/-!
# Canonical saturated owner rows

The endpoints come from the literal radial, saturation and owner-share
inequalities. A disjoint dyadic partition pays their squarefree comparison
and count-boundary errors. The final comparison floor has no externally
chosen row geometry. Its signed main and unselected incidences remain
joined and are not asserted to satisfy the numerical endgame floor.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCanonicalOwnerRows
open ZetaRieszSignedConvolution ZetaRieszUnsignedDivisorError
open ZetaRieszSaturatedRowFloor ZetaRieszPrimeCountFrequency

/-- The three literal lower thresholds, including the unsigned-leg
threshold on which the comparison error has a strict geometric saving. -/
def lowerLog (N p b : ℕ) : ℝ :=
  max ((N : ℝ)/10) (max ((39/20 : ℝ)*N-log (p*b : ℕ))
    ((20/13 : ℝ)*log p-log (p*b : ℕ)))

/-- The literal core upper endpoint intersected with cofactor saturation. -/
def upperLog (N : ℕ) (L : ℝ) (p b : ℕ) : ℝ :=
  min ((203/100 : ℝ)*N-log (p*b : ℕ)) (L-log b)

/-- The rounded lower endpoint. At most its single boundary integer is
omitted; it is not an extension of the original support. -/
def lower (N p b : ℕ) : ℕ := ⌈exp (lowerLog N p b)⌉₊

/-- The rounded upper endpoint, with both original upper inequalities. -/
def upper (N : ℕ) (L : ℝ) (p b : ℕ) : ℕ := ⌊exp (upperLog N L p b)⌋₊

private theorem lower_pos (N p b : ℕ) : 0 < lower N p b :=
  Nat.ceil_pos.mpr (exp_pos _)

private theorem lower_log_le (N p b : ℕ) : lowerLog N p b ≤ log (lower N p b) := by
  have h := log_le_log (exp_pos (lowerLog N p b)) (Nat.le_ceil (exp (lowerLog N p b)))
  simpa only [log_exp,lower] using h

private theorem upper_log_le {N p b : ℕ} {L : ℝ} (h : 0 < upper N L p b) :
    log (upper N L p b) ≤ upperLog N L p b := by
  have hu := log_le_log (by exact_mod_cast h : (0 : ℝ)<upper N L p b)
    (Nat.floor_le (exp_pos (upperLog N L p b)).le)
  simpa only [log_exp] using hu

/-- A finite, deterministic selection of every eligible outer row,
including a possibly empty rounded interval. The prime, cofactor and owner
masks are the original ones. -/
def rows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) :=
  ((ZetaRieszAnnulusJoint.intermediatePrimes u N).product
    (Finset.Icc 2 ⌊exp ((203/100 : ℝ)*N)⌋₊)).filter (fun pb =>
      Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2 ∧
      (∀ q ∈ pb.2.primeFactors, q < pb.1) ∧
      pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≠ 0 ∧
      lower N pb.1 pb.2 ≤ upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)

/-- No row-geometry hypothesis remains: each selected row satisfies the
original endpoint inequalities by its exact construction. -/
theorem rows_geometry {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (hpb : pb ∈ rows u N) :
    RowGeometry N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2
      (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) := by
  obtain ⟨hprod,hs,hpd,hmax,ha,hlu⟩ := Finset.mem_filter.mp hpb
  obtain ⟨hp,hb⟩ := Finset.mem_product.mp hprod
  have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp
  have hlow := lower_log_le N pb.1 pb.2
  have hup := upper_log_le (lt_of_lt_of_le (lower_pos N pb.1 pb.2) hlu)
  have hnlow : (N : ℝ)/10 ≤ lowerLog N pb.1 pb.2 := le_max_left _ _
  have hrlo : (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ) ≤ lowerLog N pb.1 pb.2 :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hslo : (20/13 : ℝ)*log pb.1-log (pb.1*pb.2 : ℕ) ≤ lowerLog N pb.1 pb.2 :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hrhi : upperLog N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≤
      (203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ) := min_le_left _ _
  have hshi : upperLog N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≤
      SquarefreeVaughanLogSource.length u N-log pb.2 := min_le_right _ _
  refine ⟨hp'.1,by have := (Finset.mem_Icc.mp hb).1; omega,hs,hpd,hmax,ha,
    lower_pos N pb.1 pb.2,?_,?_,?_,?_⟩ <;> linarith

/-- The same literal finite prime support is retained, without a prime
completion or a density replacement for the owner. -/
theorem rows_owner_mem {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (hpb : pb ∈ rows u N) :
    pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N :=
  (Finset.mem_product.mp (Finset.mem_filter.mp hpb).1).1

/-- All constructed rows lie above the already-paid unsigned-leg threshold. -/
theorem rows_large (N p b : ℕ) : exp ((N : ℝ)/10) ≤ lower N p b := by
  exact (exp_le_exp.mpr (le_max_left _ _)).trans (Nat.le_ceil _)

private theorem geometry_subinterval {N p b M X M' X' : ℕ} {L : ℝ}
    (hg : RowGeometry N L p b M X) (hMM : M ≤ M') (hXX : X' ≤ X) (hMX : M' < X') :
    RowGeometry N L p b M' X' := by
  obtain ⟨hp,hb,hs,hpd,hmax,ha,hM,hlo,hhi,hsat,hshare⟩ := hg
  have hM' : 0 < M' := lt_of_lt_of_le hM hMM
  have hX' : 0 < X' := hM'.trans hMX
  have hm : log M ≤ log M' := log_le_log
    (by exact_mod_cast hM) (by exact_mod_cast hMM)
  have hx : log X' ≤ log X := log_le_log
    (by exact_mod_cast hX') (by exact_mod_cast hXX)
  refine ⟨hp,hb,hs,hpd,hmax,ha,hM',?_,?_,?_,?_⟩ <;> linarith

/-- Clamped dyadic boundaries; clamping adds no atom and causes every
post-endpoint shell to be empty. -/
def boundary (M X i : ℕ) : ℕ := min X (2^i*M)

private theorem boundary_mono (M X : ℕ) : Monotone (boundary M X) := by
  intro i k hik
  unfold boundary
  exact min_le_min_left X (Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by omega) hik))

private theorem boundary_le_twice (M X i : ℕ) : boundary M X (i+1) ≤ 2*boundary M X i := by
  unfold boundary
  rw [pow_succ]
  by_cases h : X ≤ 2^i*M
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by omega)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans_eq (by ring)

/-- An exact disjoint partition, for an arbitrary signed summand. This
is used before either squarefree comparison error is estimated. -/
theorem sum_boundary_shells (M X m : ℕ) (f : ℕ → ℝ) (hMX : M ≤ X) :
    (∑ i ∈ Finset.range m, ∑ d ∈ Finset.Ioc (boundary M X i) (boundary M X (i+1)), f d) =
      ∑ d ∈ Finset.Ioc M (boundary M X m), f d := by
  induction m with
  | zero => simp [boundary,min_eq_right hMX]
  | succ m ih =>
    rw [Finset.sum_range_succ,ih]
    exact Finset.sum_Ioc_consecutive f
      (by unfold boundary; exact le_min hMX (by
        have hp : 1 ≤ 2^m := Nat.one_le_pow _ _ (by omega)
        nlinarith)) (boundary_mono M X (Nat.le_succ m))

private theorem last_boundary {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (hpb : pb ∈ rows u N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    boundary (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) (N+1) =
        upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 := by
  have hg := rows_geometry hpb
  have ha := pairHinge_active hg.2.2.2.2.2.1
  have hp0 := hg.1.pos
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hlog : log (pb.1*pb.2 : ℕ)=log pb.1+log pb.2 := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp0.ne') (by exact_mod_cast hb0.ne')]
  have hU : (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 : ℝ) ≤
      exp ((131/200 : ℝ)*N) := by
    have hf := Nat.floor_le (exp_pos (upperLog N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)).le
    have he : upperLog N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≤ (131/200 : ℝ)*N := by
      have hi := min_le_left ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ))
        (SquarefreeVaughanLogSource.length u N-log pb.2)
      rw [← hlog] at ha
      unfold upperLog
      linarith
    exact hf.trans (exp_le_exp.mpr he)
  have hpow : exp ((131/200 : ℝ)*N) ≤
      ((2^(N+1)*lower N pb.1 pb.2 : ℕ) : ℝ) := by
    have hbase := rows_large N pb.1 pb.2
    have hrate : (131/200 : ℝ)*N ≤ (N+1 : ℕ)*log 2+(N : ℝ)/10 := by
      push_cast
      nlinarith [log_two_gt_d9,log_pos (by norm_num : (1 : ℝ)<2)]
    calc
      _ ≤ exp ((N+1 : ℕ)*log 2+(N : ℝ)/10) := exp_le_exp.mpr hrate
      _ = (2 : ℝ)^(N+1)*exp ((N : ℝ)/10) := by rw [exp_add,exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<2)]
      _ ≤ (2 : ℝ)^(N+1)*lower N pb.1 pb.2 := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by push_cast; rfl
  unfold boundary
  exact min_eq_left (by exact_mod_cast hU.trans hpow)

/-- The dyadic grid on one canonical row. -/
def rowBoundary (u : ℝ) (N i : ℕ) (pb : ℕ×ℕ) : ℕ :=
  boundary (lower N pb.1 pb.2)
    (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) i

/-- Empty clamped shells are removed exactly, rather than estimated. -/
def shellRows (u : ℝ) (N i : ℕ) : Finset (ℕ×ℕ) :=
  (rows u N).filter (fun pb => rowBoundary u N i pb < rowBoundary u N (i+1) pb)

private theorem lower_le_boundary {M X : ℕ} (hMX : M ≤ X) (i : ℕ) :
    M ≤ boundary M X i := by
  unfold boundary
  exact le_min hMX (by have hp : 1 ≤ 2^i := Nat.one_le_pow _ _ (by omega); nlinarith)

private theorem shell_geometry {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) :
    RowGeometry N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2
      (rowBoundary u N i pb) (rowBoundary u N (i+1) pb) := by
  obtain ⟨hr,hMX⟩ := Finset.mem_filter.mp hpb
  have hlu := (Finset.mem_filter.mp hr).2.2.2.2.2
  apply geometry_subinterval (rows_geometry hr) _ _ hMX
  · exact lower_le_boundary hlu i
  · exact min_le_left _ _

private theorem shell_large {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) : exp ((N : ℝ)/10) ≤ rowBoundary u N i pb := by
  have hr := (Finset.mem_filter.mp hpb).1
  have hlu := (Finset.mem_filter.mp hr).2.2.2.2.2
  exact (rows_large N pb.1 pb.2).trans
    (by exact_mod_cast lower_le_boundary hlu i)

private theorem coreRow_empty (u y : ℝ) (j p b M : ℕ) : coreRow u y j p b M M=0 := by
  simp [coreRow]

private theorem densityRow_interval (N : ℕ) (L y : ℝ) (p b M X : ℕ) :
    densityRow N L y p b M X =
      ((μ b : ℝ)*pairHinge L p b/(L*(p*b : ℕ)))*density (p*b).primeFactors*
        ∑ d ∈ Finset.Ioc M X,
          ownedAmplitude N (log p) (log (p*b : ℕ)) d*
            cos (y*(log (p*b : ℕ)+log d))/(d : ℝ) := by
  unfold densityRow
  congr 1
  simp only [ZetaRieszCofactorDiscrepancy.shellWeight]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  · intro d _; rfl

private theorem densityRow_empty (N : ℕ) (L y : ℝ) (p b M : ℕ) :
    densityRow N L y p b M M=0 := by rw [densityRow_interval]; simp

private theorem sum_shellRows_eq (u : ℝ) (N : ℕ)
    (F : (ℕ×ℕ) → ℕ → ℕ → ℝ) (hzero : ∀ pb M, F pb M M=0) :
    (∑ i ∈ Finset.range (N+1), ∑ pb ∈ shellRows u N i,
      F pb (rowBoundary u N i pb) (rowBoundary u N (i+1) pb)) =
        ∑ pb ∈ rows u N, ∑ i ∈ Finset.range (N+1),
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
theorem sum_coreRow_shells (u y : ℝ) (j : ℕ)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    (∑ i ∈ Finset.range (dyadicMomentOrder j+1),
      ∑ pb ∈ shellRows u (dyadicMomentOrder j) i,
        coreRow u y j pb.1 pb.2
          (rowBoundary u (dyadicMomentOrder j) i pb)
          (rowBoundary u (dyadicMomentOrder j) (i+1) pb)) =
      ∑ pb ∈ rows u (dyadicMomentOrder j),
        coreRow u y j pb.1 pb.2 (lower (dyadicMomentOrder j) pb.1 pb.2)
          (upper (dyadicMomentOrder j)
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2) := by
  rw [sum_shellRows_eq _ _ _ (fun pb M => coreRow_empty u y j pb.1 pb.2 M)]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (Finset.mem_filter.mp hpb).2.2.2.2.2
  unfold coreRow
  dsimp only
  change (∑ i ∈ Finset.range (dyadicMomentOrder j+1),
    ∑ d ∈ Finset.Ioc (rowBoundary _ _ i _) (rowBoundary _ _ (i+1) _), _) = _
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]

/-- The SIGNED density rows are likewise recombined before any main-term
estimate. No norm, positive part or separate prime-count cost is inserted. -/
theorem sum_densityRow_shells (u y : ℝ) (N : ℕ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ i ∈ Finset.range (N+1), ∑ pb ∈ shellRows u N i,
      densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (rowBoundary u N i pb) (rowBoundary u N (i+1) pb)) =
      ∑ pb ∈ rows u N,
        densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
          (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) := by
  rw [sum_shellRows_eq _ _ _ (fun pb M => densityRow_empty _ _ _ pb.1 pb.2 M)]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (Finset.mem_filter.mp hpb).2.2.2.2.2
  simp only [densityRow_interval,← Finset.mul_sum]
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]

/-- The full signed sum of all canonical eligible rows has a paid
geometric comparison error. There is no free choice of row selection in
this statement, and no unproved cancellation premise. -/
theorem eventually_canonical_rows_floor {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*
        (∑ pb ∈ rows u (dyadicMomentOrder j),
          densityRow (dyadicMomentOrder j)
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y pb.1 pb.2
              (lower (dyadicMomentOrder j) pb.1 pb.2)
              (upper (dyadicMomentOrder j)
                (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2))-
        rowErrorBudget y (dyadicMomentOrder j) ≤
      u^(dyadicMomentOrder j+1)*∑ pb ∈ rows u (dyadicMomentOrder j),
        coreRow u y j pb.1 pb.2 (lower (dyadicMomentOrder j) pb.1 pb.2)
          (upper (dyadicMomentOrder j)
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2) := by
  have hr := eventually_signed_rows_floor
    (fun j => Finset.range (dyadicMomentOrder j+1))
    (fun j i => shellRows u (dyadicMomentOrder j) i)
    (fun j i => rowBoundary u (dyadicMomentOrder j) i)
    (fun j i => rowBoundary u (dyadicMomentOrder j) (i+1)) hu hU y
    (fun _ => by simp) (fun _ _ _ _ h => shell_geometry h)
    (fun _ _ _ _ h => rows_owner_mem (Finset.mem_filter.mp h).1)
    (fun _ _ _ _ h => (Finset.mem_filter.mp h).2)
    (fun _ i _ pb _ => boundary_le_twice _ _ i)
    (fun _ _ _ _ h => shell_large h)
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hr,tendsto_dyadicMomentOrder.eventually hl] with j hj hL
  have hL' : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hL]
  rw [sum_coreRow_shells u y j hL',sum_densityRow_shells u y _ hL'] at hj
  exact hj

/-- The exact original unselected incidence sum after replacing all
canonical eligible saturated intervals. No other incidence is discarded. -/
def canonicalRemaining (u y : ℝ) (j : ℕ) : ℝ :=
  remainingIncidences u y j (rows u (dyadicMomentOrder j))
    (fun pb => lower (dyadicMomentOrder j) pb.1 pb.2)
    (fun pb => upper (dyadicMomentOrder j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2)

/-- The signed canonical density sum, joined with all other original
incidences. An independent numerical floor for this expression is OPEN. -/
def canonicalSignedMain (u y : ℝ) (j : ℕ) : ℝ :=
  canonicalRemaining u y j+
    ∑ pb ∈ rows u (dyadicMomentOrder j),
      densityRow (dyadicMomentOrder j)
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y pb.1 pb.2
          (lower (dyadicMomentOrder j) pb.1 pb.2)
          (upper (dyadicMomentOrder j)
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) pb.1 pb.2)

/-- A checked whole-carrier comparison floor for a DETERMINISTIC part of
the literal core. All shell and count-boundary payments are automatic.
The signed canonical main remains unbounded; no numerical -79/1000 floor
or zero exclusion follows from the comparison estimate alone. -/
theorem eventually_joined_canonical_floor {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*canonicalSignedMain u y j-
        joinedRowErrorBudget y (dyadicMomentOrder j) ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have hr := eventually_canonical_rows_floor hu hU y
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hr,tendsto_dyadicMomentOrder.eventually hl] with j hj hL
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  have hL' : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by nlinarith only [hL]
  have hc := joined_sub_convolution_bound (by linarith : 0 ≤ u) hU N K y hL'
  have hre := (Complex.abs_re_le_norm ((u : ℂ)^(N+1)*
    (ZetaRieszGammaJoint.joinedPhysical u y N K-coreConvolution u y N K))).trans hc
  have hneg := (abs_le.mp hre).1
  have heq : (((u : ℂ)^(N+1)*
      (ZetaRieszGammaJoint.joinedPhysical u y N K-coreConvolution u y N K)).re) =
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re-
        u^(N+1)*(coreConvolution u y N K).re := by
    simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.sub_re,zero_mul,sub_zero]
    ring
  rw [heq,coreConvolution_eq_remaining_rows (rows u N)
    (fun pb => lower N pb.1 pb.2)
    (fun pb => upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)
    u y j (fun _ h => rows_geometry h)] at hneg
  unfold canonicalSignedMain canonicalRemaining joinedRowErrorBudget
  change u^(N+1)*_-(rowErrorBudget y N+_+_) ≤ _
  nlinarith only [hj,hneg]

/-- A literal eligible product belongs to the canonical outer row and
its entire constructed interval. The statements are only exact support
checks; no density approximation or phase norm enters. -/
theorem canonical_row_contains {u : ℝ} {N p b d : ℕ}
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (hb : 1 < b) (hs : Squarefree b) (hpd : ¬p ∣ b)
    (hmax : ∀ q ∈ b.primeFactors, q < p)
    (ha : pairHinge (SquarefreeVaughanLogSource.length u N) p b ≠ 0)
    (hd : lower N p b ≤ d)
    (hupper : log (p*b : ℕ)+log d ≤ (203/100 : ℝ)*N)
    (hsat : log b+log d ≤ SquarefreeVaughanLogSource.length u N) :
    (p,b) ∈ rows u N ∧ d ≤ upper N (SquarefreeVaughanLogSource.length u N) p b := by
  have hp0 := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1.pos
  have hb0 : 0 < b := by omega
  have hd0 : 0 < d := (lower_pos N p b).trans_le hd
  have hlog : log (p*b : ℕ)=log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp0.ne') (by exact_mod_cast hb0.ne')]
  have hdu : d ≤ upper N (SquarefreeVaughanLogSource.length u N) p b := by
    apply Nat.le_floor
    have hh : log d ≤ upperLog N (SquarefreeVaughanLogSource.length u N) p b := by
      unfold upperLog
      exact le_min (by linarith) (by linarith)
    simpa only [exp_log (by exact_mod_cast hd0 : (0 : ℝ)<d)] using exp_le_exp.mpr hh
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp,?_⟩,hs,hpd,hmax,ha,hd.trans hdu⟩,hdu⟩
  apply Finset.mem_Icc.mpr
  refine ⟨by omega,?_⟩
  apply Nat.le_floor
  have hbl : log b ≤ (203/100 : ℝ)*N := by
    linarith [log_natCast_nonneg p,log_natCast_nonneg d]
  simpa only [exp_log (by exact_mod_cast hb0 : (0 : ℝ)<b)] using exp_le_exp.mpr hbl

/-- A large unsigned divisor on the literal lower window and strict
owner-share geometry is never below the rounded canonical endpoint. -/
theorem lower_le_of_literal {N p b d : ℕ}
    (hlarge : exp ((N : ℝ)/10) ≤ d)
    (hlo : (39/20 : ℝ)*N < log (p*b : ℕ)+log d)
    (hshare : log p < (13/20 : ℝ)*(log (p*b : ℕ)+log d)) :
    lower N p b ≤ d := by
  have hd0 : (0 : ℝ)<d := (exp_pos _).trans_le hlarge
  apply Nat.ceil_le.mpr
  have hh : lowerLog N p b ≤ log d := by
    unfold lowerLog
    apply max_le
    · have h := log_le_log (exp_pos _) hlarge
      simpa only [log_exp] using h
    · exact max_le (by linarith) (by linarith)
  simpa only [exp_log hd0] using exp_le_exp.mpr hh

/-- Every eligible saturated large-divisor incidence is included, except
possibly the SINGLE rounded lower-endpoint integer. There is no anonymous
shell or radial-boundary gap in the partition. -/
theorem literal_row_covered_or_endpoint {u : ℝ} {N p b d : ℕ}
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (hb : 1 < b) (hs : Squarefree b) (hpd : ¬p ∣ b)
    (hmax : ∀ q ∈ b.primeFactors, q < p)
    (ha : pairHinge (SquarefreeVaughanLogSource.length u N) p b ≠ 0)
    (hlarge : exp ((N : ℝ)/10) ≤ d)
    (hlo : (39/20 : ℝ)*N < log (p*b : ℕ)+log d)
    (hupper : log (p*b : ℕ)+log d ≤ (203/100 : ℝ)*N)
    (hsat : log b+log d ≤ SquarefreeVaughanLogSource.length u N)
    (hshare : log p < (13/20 : ℝ)*(log (p*b : ℕ)+log d)) :
    (p,b) ∈ rows u N ∧
      (d ∈ Finset.Ioc (lower N p b) (upper N (SquarefreeVaughanLogSource.length u N) p b) ∨
        d=lower N p b) := by
  have hd := lower_le_of_literal hlarge hlo hshare
  obtain ⟨hr,hu'⟩ := canonical_row_contains hp hb hs hpd hmax ha hd hupper hsat
  refine ⟨hr,?_⟩
  by_cases he : d=lower N p b
  · exact Or.inr he
  · exact Or.inl (Finset.mem_Ioc.mpr ⟨by omega,hu'⟩)

private theorem endpoint_cofactor {u : ℝ} {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hpb : pb ∈ rows u N)
    (hsieve : sieve (pb.1*pb.2).primeFactors (lower N pb.1 pb.2) ≠ 0) :
    Squarefree (pb.2*lower N pb.1 pb.2) ∧
      2 ≤ (pb.2*lower N pb.1 pb.2).primeFactors.card ∧
      ∀ q ∈ (pb.2*lower N pb.1 pb.2).primeFactors, q < pb.1 := by
  have hg := rows_geometry hpb
  obtain ⟨hp,hb,hbs,hpd,hmax,ha,hM,_,_,hsat,_⟩ := hg
  have houter : Squarefree (pb.1*pb.2) :=
    Nat.squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hpd,hp.squarefree,hbs⟩
  have hwhole : Squarefree ((pb.1*pb.2)*lower N pb.1 pb.2) := by
    rw [sieve_eq_product_squarefree houter] at hsieve
    split_ifs at hsieve with h
    · exact h
    · contradiction
  have hc : Squarefree (pb.2*lower N pb.1 pb.2) := by
    rw [mul_assoc] at hwhole
    exact (Nat.squarefree_mul_iff.mp hwhole).2.2
  have hd1 : 1 < lower N pb.1 pb.2 := by
    have h := rows_large N pb.1 pb.2
    have he := add_one_le_exp ((N : ℝ)/10)
    have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
    have hr : (1 : ℝ)<lower N pb.1 pb.2 := by linarith
    exact_mod_cast hr
  have hdmax : lower N pb.1 pb.2 < pb.1 := by
    have hlog : log (pb.2*lower N pb.1 pb.2 : ℕ) ≤ SquarefreeVaughanLogSource.length u N := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast (by omega : 0 < pb.2).ne')
        (by exact_mod_cast hM.ne')]
      have hmu := (Finset.mem_filter.mp hpb).2.2.2.2.2
      have hm : log (lower N pb.1 pb.2) ≤
          log (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) :=
        log_le_log (by exact_mod_cast hM : (0 : ℝ)<lower N pb.1 pb.2)
        (by exact_mod_cast hmu)
      linarith
    exact active_unsigned_lt_owner hp.pos (by omega) hM hlog ha
  have hdis : Disjoint pb.2.primeFactors (lower N pb.1 pb.2).primeFactors := by
    apply Finset.disjoint_left.mpr
    intro q hq hqd
    have hqp := Nat.prime_of_mem_primeFactors hq
    exact (hqp.coprime_iff_not_dvd.mp
      ((Nat.squarefree_mul_iff.mp hc).1.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hq)))
        (Nat.dvd_of_mem_primeFactors hqd)
  refine ⟨hc,?_,?_⟩
  · rw [Nat.primeFactors_mul (by omega) hM.ne',Finset.card_union_of_disjoint hdis]
    have hbcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hb)
    have hdcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hd1)
    omega
  · intro q hq
    rw [Nat.primeFactors_mul (by omega) hM.ne',Finset.mem_union] at hq
    exact hq.elim (hmax q) (fun h => (Nat.le_of_dvd hM (Nat.dvd_of_mem_primeFactors h)).trans_lt hdmax)

/-- One actual possibly surviving rounded endpoint per canonical outer
row. Original core membership and the full squarefree sieve are retained. -/
def endpointRows (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  ∑ pb ∈ rows u N,
    if pb.1*(pb.2*lower N pb.1 pb.2) ∈ ZetaRieszParityPacket.coreBand u N (dyadicPrimeCount j)
      then rowAtom A N L y pb.1 pb.2 (lower N pb.1 pb.2) else 0

private theorem endpoint_atom_bound {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ rows u N) (y : ℝ) :
    |rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N) N
      (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2 (lower N pb.1 pb.2)| ≤
        radialEnvelope N*exp (-(N : ℝ)/10)/(pb.1*pb.2 : ℕ) := by
  have hg := rows_geometry hpb
  let d := lower N pb.1 pb.2
  let L := SquarefreeVaughanLogSource.length u N
  change |rowAtom _ N L y pb.1 pb.2 d| ≤ _
  have hd0 : 0 < d := lower_pos N pb.1 pb.2
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hpb0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by exact_mod_cast Nat.mul_pos hg.1.pos hb0
  have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0 < L := by dsimp [L]; nlinarith
  have hP : log pb.1 ≤ L := by
    obtain ⟨_,_,_,_,_,_,_,_,hhi,_,hshare⟩ := hg
    have hmU : log d ≤ log (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) :=
      log_le_log (by exact_mod_cast hd0 : (0 : ℝ)<d)
      (by exact_mod_cast (Finset.mem_filter.mp hpb).2.2.2.2.2)
    change _ ≤ (203/100 : ℝ)*N at hhi
    change log pb.1 ≤ (13/20 : ℝ)*(log (pb.1*pb.2 : ℕ)+log d) at hshare
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
    (rows_owner_mem hpb),hsieve,mul_one,abs_mul,abs_mul,abs_div,abs_mul,
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
  have hdlarge := rows_large N pb.1 pb.2
  have hinv : (d : ℝ)⁻¹ ≤ exp (-(N : ℝ)/10) := by
    rw [neg_div,exp_neg]
    exact inv_anti₀ (exp_pos _) hdlarge
  calc
    _ = (|ownedAmplitude N (log pb.1) (log (pb.1*pb.2 : ℕ)) d|
        *|cos (y*(log (pb.1*pb.2 : ℕ)+log d))| * |(μ pb.2 : ℝ)| * pairHinge L pb.1 pb.2)/
          (L*(pb.1*pb.2 : ℕ)*d) := by ring
    _ ≤ radialEnvelope N*L/(L*(pb.1*pb.2 : ℕ)*d) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = radialEnvelope N/(pb.1*pb.2 : ℕ)*(d : ℝ)⁻¹ := by field_simp
    _ ≤ radialEnvelope N/(pb.1*pb.2 : ℕ)*exp (-(N : ℝ)/10) :=
      mul_le_mul_of_nonneg_left hinv (by positivity [radialEnvelope_pos N])
    _ = _ := by ring

/-- The endpoint rate after summing ALL outer prime counts and including
the full source growth. It is charged only to the single rounded atoms. -/
def endpointRate (u : ℝ) : ℝ := 2*u*exp (-(10037/102400 : ℝ))

private theorem endpointRate_bounds {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    0 ≤ endpointRate u ∧ endpointRate u ≤ 23/25 := by
  constructor
  · unfold endpointRate; positivity
  · rw [endpointRate,exp_neg,mul_inv_le_iff₀ (exp_pos _)]
    have he := add_one_le_exp (10037/102400 : ℝ)
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith

/-- A fixed convergent all-count Euler mass; no unexplored counting
constant or separate count allowance is hidden in the endpoint payment. -/
def endpointConstant : ℝ :=
  6*ZetaRieszWideOwnerAudit.radiusCeiling*
    ZetaRieszPrimeCountMass.countMass (1025/1024)*
      exp (3*ZetaRieszPrimeCountMass.countMass (1025/1024))

private theorem endpointConstant_nonneg : 0 ≤ endpointConstant := by
  have hm := ZetaRieszPrimeCountMass.countMass_nonneg (1025/1024)
  unfold endpointConstant ZetaRieszWideOwnerAudit.radiusCeiling
  positivity

/-- A quantitative payment for EVERY possibly surviving rounded
endpoint at once, retaining actual core masks, phases and all prime counts. -/
theorem source_scaled_endpointRows_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (j : ℕ)
    (hN : 32 ≤ dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    |u^(dyadicMomentOrder j+1)*endpointRows u y j| ≤
      endpointConstant*((dyadicMomentOrder j : ℝ)+1)*(23/25 : ℝ)^(dyadicMomentOrder j) := by
  let N := dyadicMomentOrder j
  let B := rows u N
  let mass := ZetaRieszPrimeCountMass.countMass (1025/1024)
  have hmass : 0 ≤ mass := ZetaRieszPrimeCountMass.countMass_nonneg _
  have hB pb (hpb : pb ∈ B) : pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2 :=
    ⟨(rows_geometry hpb).1,(rows_geometry hpb).2.2.1,(rows_geometry hpb).2.2.2.1⟩
  have hlog pb (hpb : pb ∈ B) : log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N := by
    have hh := (rows_geometry hpb).2.2.2.2.2.2.2.2.1
    linarith [log_natCast_nonneg (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)]
  have houter := outer_cost_bound B N hB hlog
  have hsum : |endpointRows u y j| ≤
      radialEnvelope N*exp (-(N : ℝ)/10)*
        (3*exp ((203/102400 : ℝ)*N)*mass*exp (3*mass)) := by
    unfold endpointRows
    dsimp only
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ pb ∈ B, radialEnvelope N*exp (-(N : ℝ)/10)*
          ((3 : ℝ)^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ)) := by
        apply Finset.sum_le_sum
        intro pb hpb
        have ha := endpoint_atom_bound hN hL hpb y
        have hp0 := (hB pb hpb).1.pos
        have hb0 := Nat.pos_of_ne_zero (hB pb hpb).2.1.ne_zero
        have hh : 1 ≤ (3 : ℝ)^(pb.1*pb.2).primeFactors.card := one_le_pow₀ (by norm_num)
        have hfirst : |if pb.1*(pb.2*lower N pb.1 pb.2) ∈ ZetaRieszParityPacket.coreBand u N
            (dyadicPrimeCount j) then rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N) N
              (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2 (lower N pb.1 pb.2) else 0| ≤
            radialEnvelope N*exp (-(N : ℝ)/10)/(pb.1*pb.2 : ℕ) := by
          split_ifs
          · exact ha
          · simp only [abs_zero]; positivity [radialEnvelope_pos N]
        apply hfirst.trans
        have hr : 0 ≤ radialEnvelope N*exp (-(N : ℝ)/10)/(pb.1*pb.2 : ℕ) := by
          positivity [radialEnvelope_pos N]
        have hm := mul_le_mul_of_nonneg_left hh hr
        calc
          _ = (radialEnvelope N*exp (-(N : ℝ)/10)/(pb.1*pb.2 : ℕ))*1 := by ring
          _ ≤ (radialEnvelope N*exp (-(N : ℝ)/10)/(pb.1*pb.2 : ℕ))*
              (3 : ℝ)^(pb.1*pb.2).primeFactors.card := hm
          _ = _ := by ring
      _ = radialEnvelope N*exp (-(N : ℝ)/10)*
          (∑ pb ∈ B, (3 : ℝ)^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ)) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left houter (by positivity [radialEnvelope_pos N])
  have hex : exp (-(N : ℝ)/10)*exp ((203/102400 : ℝ)*N) =
      exp (-(10037/102400 : ℝ))^N := by
    rw [← exp_add,← exp_nat_mul]
    congr 1
    ring
  have hn : |u^(N+1)*endpointRows u y j| ≤
      (6*u*mass*exp (3*mass))*((N : ℝ)+1)*(endpointRate u)^N := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
    apply (mul_le_mul_of_nonneg_left hsum (pow_nonneg hu _)).trans_eq
    dsimp [radialEnvelope,endpointRate]
    rw [mul_pow,mul_pow,pow_succ,pow_succ]
    calc
      _ = (6*u*mass*exp (3*mass))*((N : ℝ)+1)*(2^N*u^N)*
          (exp (-(N : ℝ)/10)*exp ((203/102400 : ℝ)*N)) := by ring
      _ = _ := by rw [hex]; ring
  apply hn.trans
  have hr := endpointRate_bounds hu hU
  have hc : 6*u*mass*exp (3*mass) ≤ endpointConstant := by
    unfold endpointConstant
    change 6*u*mass*exp (3*mass) ≤ 6*ZetaRieszWideOwnerAudit.radiusCeiling*mass*exp (3*mass)
    gcongr
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hc (by positivity))
    (pow_le_pow_left₀ hr.1 hr.2 N) (pow_nonneg hr.1 N)
    (by positivity [endpointConstant_nonneg])

/-- The complete all-count endpoint allowance. -/
def endpointErrorBudget (N : ℕ) : ℝ := endpointConstant*((N : ℝ)+1)*(23/25 : ℝ)^N

/-- Rounding endpoints have independently vanishing source-scale cost. -/
theorem tendsto_endpointErrorBudget : Tendsto endpointErrorBudget atTop (𝓝 0) := by
  change Tendsto (fun N => endpointErrorBudget N) atTop (𝓝 0)
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1
    (by norm_num : (0 : ℝ)<23/25) (by norm_num : (23/25 : ℝ)<1)).const_mul endpointConstant
  simpa only [endpointErrorBudget,pow_one,mul_assoc,mul_zero] using ht

/-- The canonical comparison and count-boundary budget plus the paid
rounded endpoints. All terms have strict geometric rates at source scale. -/
def canonicalErrorBudget (y : ℝ) (N : ℕ) : ℝ := joinedRowErrorBudget y N+endpointErrorBudget N

/-- Every error in the canonical comparison floor tends to zero. -/
theorem tendsto_canonicalErrorBudget (y : ℝ) : Tendsto (canonicalErrorBudget y) atTop (𝓝 0) := by
  change Tendsto (fun N => canonicalErrorBudget y N) atTop (𝓝 0)
  have ht := (tendsto_joinedRowErrorBudget y).add tendsto_endpointErrorBudget
  simpa only [canonicalErrorBudget,zero_add] using ht

/-- The original numerical floor is now reduced to one explicit joined
signed expression, with both interval errors and rounded endpoints paid.
No numerical lower bound for that remaining expression is assumed or proved. -/
theorem eventually_joined_floor_without_endpoints {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*(canonicalSignedMain u y j-endpointRows u y j)-
        canonicalErrorBudget y (dyadicMomentOrder j) ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have hr := eventually_joined_canonical_floor hu hU y
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hr,tendsto_dyadicMomentOrder.eventually hl,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ))] with j hj hL hN
  have hL' : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hL]
  have he := (abs_le.mp (source_scaled_endpointRows_bound (by linarith : 0 ≤ u) hU y j hN hL')).1
  change -endpointErrorBudget _ ≤ _ at he
  unfold canonicalErrorBudget
  nlinarith only [hj,he]

end RiemannGaussian.ZetaRieszCanonicalOwnerRows
