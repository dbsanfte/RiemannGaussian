/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOrderedEulerCompletion

/-!
# Removing physical endpoints from the marked arithmetic completion

The original factorial rectangle pays the radial and share exteriors.
On their retained interior the physical prime endpoints follow from the
logarithmic geometry. All count classes and every signed arithmetic atom
remain coupled; no prime-density approximation or zero hypothesis is used.
-/

namespace RiemannGaussian.ZetaRieszPhysicalCompletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszMarkedCompletion ZetaRieszJointOwnerTransfer ZetaRieszJointBoundary
open ZetaRieszAnnulusJoint ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint

/-- The polynomial physical head eventually lies below the least-share
interior throughout the original total-log core. -/
theorem eventually_head_log :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧
      2*Real.log N < (39/4000 : ℝ)*N := by
  have hl : Tendsto (fun N : ℕ => Real.log N/((N : ℝ)+1)) atTop (nhds 0) := by
    simpa only [Function.comp_def,pow_zero,pow_one,one_mul] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/500)),
    eventually_ge_atTop 1] with N hlog hN
  have hh := (div_lt_iff₀ (by positivity : (0 : ℝ) < N+1)).mp hlog
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact ⟨hN,by nlinarith⟩

/-- Every prime in the core/share interior satisfies BOTH original
physical endpoints. Neither condition is assumed in this theorem. -/
theorem interior_physical {u : ℝ} {N n : ℕ}
    (hN : 1 ≤ N) (hhead : 2*Real.log N < (39/4000 : ℝ)*N)
    (hL : (5/4 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hn1 : 1 < n)
    (hi : ZetaRieszLeastBoundary.interior n)
    (hwindow : (39/20 : ℝ)*N < Real.log n ∧ Real.log n ≤ (203/100 : ℝ)*N) :
    ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hleast := (lt_div_iff₀ hlog).mp hi.2.1
  have hlargest := (div_lt_iff₀ hlog).mp hi.1.2
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hplog : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
  have hmin : n.minFac ≤ p := Nat.minFac_le_of_dvd hprime.two_le (Nat.dvd_of_mem_primeFactors hp)
  have hminlog : Real.log n.minFac ≤ Real.log p :=
    Real.log_le_log (by exact_mod_cast (Nat.minFac_prime hn1.ne').pos) (by exact_mod_cast hmin)
  have hmax : p ≤ largestPrime n := by
    rw [largestPrime,dif_pos (show n.primeFactors.Nonempty from ⟨p,hp⟩)]
    exact Finset.le_max' _ _ hp
  have hmaxlog : Real.log p ≤ Real.log (largestPrime n) :=
    Real.log_le_log hplog (by exact_mod_cast hmax)
  apply (mem_intermediatePrimes u N p).mpr
  refine ⟨hprime,?_,?_⟩
  · have hh : Real.log ((N : ℝ)^2) < Real.log p := by
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith [hwindow.1]
    have hnz : (0 : ℝ) < (N : ℝ)^2 := by positivity
    exact_mod_cast (Real.log_lt_log_iff hnz hplog).mp hh
  · have hh : Real.log p < SquarefreeVaughanLogSource.length u N := by
      nlinarith [hwindow.2]
    have hx : (0 : ℝ) < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2 : ℝ)^2 := by
      positivity
    have hlt := (Real.log_lt_log_iff hplog hx).mp hh
    exact_mod_cast hlt

/-- The supported arithmetic labels, with no physical cutoff. -/
def validLabel (n : ℕ) : Prop := Squarefree n ∧ 3 ≤ n.primeFactors.card

theorem validLabel_one_lt {n : ℕ} (hn : validLabel n) : 1 < n := by
  have hz := hn.1.ne_zero
  have hne : n ≠ 1 := by rintro rfl; simp [validLabel] at hn
  omega

/-- The exact signed coefficient and marked factorial incidence mass,
extended by zero off the squarefree, at-least-three-prime support. -/
def markedCoefficient (u : ℝ) (N n : ℕ) : ℂ :=
  if validLabel n then (markedMass N n : ℂ)*
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n else 0

/-- One literal complex arithmetic atom, retaining its complete phase. -/
def atom (u y : ℝ) (N n : ℕ) : ℂ :=
  markedCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The complete arithmetic series with the original factorial
rectangle. Its convergence is proved separately; no analytic continuation
is used in this definition. -/
def packet (u y : ℝ) (N : ℕ) : ℂ := ∑' n, atom u y N n

/-- The actual terms outside the original physical subset universe. -/
def missingAtom (u y : ℝ) (N n : ℕ) : ℂ :=
  if n ∈ completeBand (intermediatePrimes u N) then 0 else atom u y N n

theorem markedCoefficient_norm_le (u : ℝ) (N : ℕ) (hN : 21 ≤ N) (n : ℕ) :
    ‖markedCoefficient u N n‖ ≤ zetaMoebiusLogMajorant n := by
  by_cases hn : validLabel n
  · have hw : 0 ≤ markedMass N n :=
      Finset.sum_nonneg (fun p _ => markedWeight_nonneg N n p)
    rw [markedCoefficient,if_pos hn,norm_mul,Complex.norm_real,Real.norm_of_nonneg hw]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (marked_mass_le_one hn.1 (validLabel_one_lt hn) N hN)).trans
      (SquarefreeVaughanLogSource.norm_coefficient_le
        (SquarefreeVaughanLogSource.length_pos u N) n)
  · simp only [markedCoefficient,if_neg hn,norm_zero]
    exact zetaMoebiusLogMajorant_nonneg n

/-- Absolute convergence at the safe axis, for every fixed height and
physical order. This is not a uniform bound at source scale. -/
theorem summable_atom (u y : ℝ) (N : ℕ) (hN : 21 ≤ N) :
    Summable (atom u y N) := by
  apply ((summable_zetaMoebiusLogMajorant (by norm_num : (1 : ℝ) < 5/4)).mul_left
    ((1/4 : ℝ)⁻¹^N)).of_norm_bounded
  intro n
  have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (1/4 : ℝ)⁻¹^N*zetaPrimeExpWeight (5/4) n := by
    convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
      (by norm_num : (0 : ℝ) < 1/4) using 1
    norm_num
  rw [atom,norm_mul]
  calc
    _ ≤ zetaMoebiusLogMajorant n*((1/4 : ℝ)⁻¹^N*zetaPrimeExpWeight (5/4) n) :=
      mul_le_mul (markedCoefficient_norm_le u N hN n) hk (norm_nonneg _)
        (zetaMoebiusLogMajorant_nonneg n)
    _ = _ := by ring

theorem summable_missingAtom (u y : ℝ) (N : ℕ) (hN : 21 ≤ N) :
    Summable (missingAtom u y N) := by
  apply (summable_atom u y N hN).norm.of_norm_bounded
  intro n
  by_cases hn : n ∈ completeBand (intermediatePrimes u N)
  · simp only [missingAtom,if_pos hn,norm_zero]
    exact norm_nonneg _
  · simp only [missingAtom,if_neg hn,le_refl]

/-- Every physical subset atom agrees exactly with the original finite
completed packet. -/
theorem sum_atom_completeBand (u y : ℝ) (N : ℕ) :
    (∑ n ∈ completeBand (intermediatePrimes u N), atom u y N n) =
      completePacket u y N := by
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hs,_h1,hc,_hp⟩ := completeBand_data hn
  rw [atom,markedCoefficient,if_pos (show validLabel n from ⟨hs,hc⟩)]
  ring

/-- The physical-cutoff error is the genuinely convergent sum of
missing arithmetic labels, with the original signs unchanged. -/
theorem packet_sub_complete (u y : ℝ) (N : ℕ) (hN : 21 ≤ N) :
    packet u y N-completePacket u y N = ∑' n, missingAtom u y N n := by
  let B := completeBand (intermediatePrimes u N)
  have hs : Summable (fun n => if n ∈ B then atom u y N n else 0) := by
    exact summable_of_ne_finset_zero (s := B) (fun n hn => if_neg hn)
  have he (n : ℕ) : atom u y N n =
      (if n ∈ B then atom u y N n else 0)+missingAtom u y N n := by
    change atom u y N n = (if n ∈ B then atom u y N n else 0)+
      (if n ∈ B then 0 else atom u y N n)
    by_cases hn : n ∈ B <;> simp [hn]
  have hf : (∑' n, if n ∈ B then atom u y N n else 0) = completePacket u y N := by
    rw [tsum_eq_sum (s := B) (fun n hn => if_neg hn)]
    calc
      _ = ∑ n ∈ B, atom u y N n := Finset.sum_congr rfl (fun n hn => if_pos hn)
      _ = _ := sum_atom_completeBand u y N
  have ht : packet u y N = completePacket u y N+∑' n, missingAtom u y N n := by
    calc
      _ = ∑' n, ((if n ∈ B then atom u y N n else 0)+missingAtom u y N n) :=
        tsum_congr he
      _ = (∑' n, if n ∈ B then atom u y N n else 0)+∑' n, missingAtom u y N n :=
        hs.tsum_add (summable_missingAtom u y N hN)
      _ = _ := by rw [hf]
  rw [ht]
  ring

/-- The share-exterior allowance retains the exact one-factorial-shift
cost from the unrestricted incidence count. -/
def shareBudget (N : ℕ) : ℝ :=
  (6*radiusCeiling*(131071/262144 : ℝ)⁻¹)*((N+1 : ℝ)*exteriorRate^N)*
    zetaMoebiusLogMajorantMass (1+1/262144)

/-- The same share tail controls every actual label, even outside the
old finite physical universe. -/
theorem scaled_exterior_atom_le {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N n : ℕ) (hN : 1 ≤ N) (hn : validLabel n)
    (he : ¬ZetaRieszLeastBoundary.interior n) :
    ‖(u : ℂ)^(N+1)*atom u y N n‖ ≤
      (6*radiusCeiling*(131071/262144 : ℝ)⁻¹)*((N+1 : ℝ)*exteriorRate^N)*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
  have hw := markedMass_exterior hn.1 (validLabel_one_lt hn) hn.2 N hN he
  have hcoef := SquarefreeVaughanLogSource.norm_coefficient_le
    (SquarefreeVaughanLogSource.length_pos u N) n
  have hmajorant := zetaMoebiusLogMajorant_nonneg n
  have hk : ‖zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n‖ ≤
      (131071/262144 : ℝ)⁻¹^(N+1)*zetaPrimeExpWeight (1+1/262144) n := by
    convert norm_zetaPrimeLogKernel_le (N+1) (3/2+Complex.I*y) n
      (by norm_num : (0 : ℝ) < 131071/262144) using 1
    norm_num
  have hexp : Real.exp (-(N : ℝ)/1600) = Real.exp (-(1/1600 : ℝ))^N := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [atom,markedCoefficient,if_pos hn,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg hu,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hw.1]
  calc
    _ ≤ radiusCeiling^(N+1)*
        ((6*Real.log n*Real.exp (-(N : ℝ)/1600)*zetaMoebiusLogMajorant n)*
          ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) := by
      gcongr
      · exact mul_nonneg (mul_nonneg hw.1 (norm_nonneg _)) (norm_nonneg _)
      · unfold radiusCeiling; positivity
      · exact hw.2
    _ = 6*radiusCeiling^(N+1)*Real.exp (-(N : ℝ)/1600)*zetaMoebiusLogMajorant n*
        ((N+1 : ℝ)*‖zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n‖) := by
      rw [← log_norm_kernel]; ring
    _ ≤ 6*radiusCeiling^(N+1)*Real.exp (-(N : ℝ)/1600)*zetaMoebiusLogMajorant n*
        ((N+1 : ℝ)*((131071/262144 : ℝ)⁻¹^(N+1)*zetaPrimeExpWeight (1+1/262144) n)) := by
      gcongr
      all_goals first | exact hk | exact zetaMoebiusLogMajorant_nonneg n |
        (unfold radiusCeiling; positivity)
    _ = _ := by rw [hexp,exteriorRate,mul_pow,mul_pow,pow_succ,pow_succ]; ring

/-- No physical endpoint or fixed count ceiling is needed for the
complete finite share-exterior estimate. -/
theorem exterior_sum_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N : ℕ) (hN : 1 ≤ N) (S : Finset ℕ)
    (hS : ∀ n ∈ S, validLabel n ∧ ¬ZetaRieszLeastBoundary.interior n) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S, atom u y N n‖ ≤ shareBudget N := by
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ S,
        (6*radiusCeiling*(131071/262144 : ℝ)⁻¹)*((N+1 : ℝ)*exteriorRate^N)*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) :=
      Finset.sum_le_sum (fun n hn => scaled_exterior_atom_le hu hU y N n hN
        (hS n hn).1 (hS n hn).2)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (by apply mul_nonneg <;> first | (unfold radiusCeiling; positivity) |
          exact mul_nonneg (by positivity) (pow_nonneg exteriorRate_bounds.1 _))

theorem tendsto_shareBudget : Tendsto shareBudget atTop (nhds 0) := by
  have hr : 0 < exteriorRate := by unfold exteriorRate radiusCeiling; positivity
  change Tendsto (fun N : ℕ =>
    (6*radiusCeiling*(131071/262144 : ℝ)⁻¹)*((N+1 : ℝ)*exteriorRate^N)*
      zetaMoebiusLogMajorantMass (1+1/262144)) atTop (nhds 0)
  simpa only [pow_one,mul_zero,zero_mul] using
    ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
      1 hr exteriorRate_bounds.2).const_mul (6*radiusCeiling*(131071/262144 : ℝ)⁻¹)).mul_const
        (zetaMoebiusLogMajorantMass (1+1/262144))

/-- A nonphysical label in the core must lie in the already-paid share
exterior. This implication has no prime-count ceiling. -/
theorem missing_core_exterior {u : ℝ} {N n : ℕ}
    (hN : 1 ≤ N) (hhead : 2*Real.log N < (39/4000 : ℝ)*N)
    (hL : (5/4 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hn : validLabel n) (hnot : n ∉ completeBand (intermediatePrimes u N))
    (hwindow : (39/20 : ℝ)*N < Real.log n ∧ Real.log n ≤ (203/100 : ℝ)*N) :
    ¬ZetaRieszLeastBoundary.interior n := by
  intro hi
  apply hnot
  apply (mem_completeBand _ (fun p hp => ((mem_intermediatePrimes u N p).mp hp).1) n).mpr
  exact ⟨hn.1,hn.2,interior_physical hN hhead hL (validLabel_one_lt hn) hi hwindow⟩

/-- The finite-window proof applies to every partial sum of the missing
physical labels with one common geometric allowance. -/
theorem exists_finite_physical_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ N : ℕ, 21 ≤ N → 2*Real.log N < (39/4000 : ℝ)*N →
      ∀ u : ℝ, 0 ≤ u → u ≤ radiusCeiling →
      (5/4 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N →
      ∀ y : ℝ, ∀ S : Finset ℕ,
        ‖(u : ℂ)^(N+1)*∑ n ∈ S, missingAtom u y N n‖ ≤ r^N*C+shareBudget N := by
  obtain ⟨r,C,hr0,hr1,hC,hb⟩ := ZetaArithmeticDeviationBounds.exists_uniform_deviation_bound
    (1 : Polynomial ℂ) (by norm_num [radiusCeiling])
    (by norm_num : (0 : ℝ) < 39/20) (by norm_num) (by norm_num : (2 : ℝ) < 203/100)
    ZetaRieszParityPacket.core_window_costs.1 ZetaRieszParityPacket.core_window_costs.2
  refine ⟨r,C,hr0,hr1,hC,?_⟩
  intro N hN hhead u hu hU hL y S
  let T := S.filter (fun n => validLabel n ∧ n ∉ completeBand (intermediatePrimes u N))
  have heq : (∑ n ∈ S, missingAtom u y N n) = ∑ n ∈ T, atom u y N n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hb : n ∈ completeBand (intermediatePrimes u N)
    · simp only [missingAtom,hb,not_true_eq_false,and_false,if_true,if_false]
    · by_cases hv : validLabel n
      · simp only [missingAtom,if_neg hb,if_pos (show validLabel n ∧
          n ∉ completeBand (intermediatePrimes u N) from ⟨hv,hb⟩)]
      · simp only [missingAtom,if_neg hb,hv,false_and,if_false,atom,markedCoefficient,
          zero_mul]
  let D := LogarithmicDeviation.deviationBand T (39/20) (203/100) N
  have hrad : ‖(u : ℂ)^(N+1)*
      ((∑ n ∈ T, atom u y N n)-∑ n ∈ D, atom u y N n)‖ ≤ r^N*C := by
    simpa only [atom,SquarefreeEulerQuadratic.primeFilterKernel_one,zetaPrimeLogKernel] using
      hb N T (markedCoefficient u N) (fun n _ => markedCoefficient_norm_le u N hN n) y u hu hU
  have hshare : ‖(u : ℂ)^(N+1)*∑ n ∈ D, atom u y N n‖ ≤ shareBudget N := by
    apply exterior_sum_bound hu hU y N (by omega) D
    intro n hn
    obtain ⟨hT,hw⟩ := Finset.mem_filter.mp hn
    obtain ⟨_hS,hv,hm⟩ := Finset.mem_filter.mp hT
    exact ⟨hv,missing_core_exterior (by omega) hhead hL hv hm hw⟩
  rw [heq]
  have he : (u : ℂ)^(N+1)*∑ n ∈ T, atom u y N n =
      (u : ℂ)^(N+1)*((∑ n ∈ T, atom u y N n)-∑ n ∈ D, atom u y N n)+
        (u : ℂ)^(N+1)*∑ n ∈ D, atom u y N n := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hrad hshare)

/-- Both literal physical endpoints can be removed at source scale.
The radial allowance is geometric and the share allowance is the explicit
polynomial-times-geometric bound above, uniformly in the height. -/
theorem exists_eventual_physical_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ radiusCeiling) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ y : ℝ, ‖(u : ℂ)^(N+1)*(packet u y N-completePacket u y N)‖ ≤
        r^N*C+shareBudget N := by
  obtain ⟨r,C,hr0,hr1,hC,hb⟩ := exists_finite_physical_bound
  refine ⟨r,C,hr0,hr1,hC,?_⟩
  filter_upwards [eventually_head_log,eventually_ge_atTop 21,
    ZetaRieszMaskSupport.eventually_length_lower (by linarith : 0 < u)
      (hU.trans radius_lt_source.le)] with N hhead hN hL
  intro y
  rw [packet_sub_complete u y N hN]
  apply le_of_tendsto ((summable_missingAtom u y N hN).hasSum.mul_left
    ((u : ℂ)^(N+1))).norm
  apply Eventually.of_forall
  intro S
  simpa only [Finset.mul_sum] using hb N hN hhead.2 u (by linarith) hU hL y S

/-- The unrestricted marked arithmetic series and its physical
completion have the same source asymptotics, even at moving heights. -/
theorem tendsto_packet_sub_complete {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ radiusCeiling) (heights : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*
      (packet u (heights N) N-completePacket u (heights N) N)) atTop (nhds 0) := by
  obtain ⟨r,C,hr0,hr1,_hC,hb⟩ := exists_eventual_physical_bound hu hU
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C).add tendsto_shareBudget
  simp only [zero_mul,zero_add] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hb] with N hN
  exact hN (heights N)

/-- The CURRENT signed counts and upper-overflow boundary are
source-equivalent to the convergent unrestricted arithmetic series.
The main signed series itself is not asserted to decay. -/
theorem tendsto_packet_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (packet u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have h := ((tendsto_packet_sub_complete hu hU (fun _ => y)).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add
      (tendsto_complete_sub_current hu hU y)
  simp only [zero_add] at h
  convert h using 1
  ext j
  simp only [Function.comp_def]
  ring

/-- The ordered least-prime Euler response on a genuine prime prefix,
with the same moving length and correlated factorial rectangle. -/
def prefixEuler (u y : ℝ) (N X : ℕ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(SquarefreeVaughanLogSource.length u N : ℂ))*
    ∫ xi : ℝ in Set.Ioi 0,
      ZetaRieszMarkedEuler.orderedPair (Nat.primesLE X) N (3/2+Complex.I*y)
        (SquarefreeVaughanLogSource.length u N) xi/(xi : ℂ)^2

/-- Every prefix Euler integral is exactly its finite arithmetic sum.
Both Fourier signs are retained and their paired integral is integrable. -/
theorem prefixEuler_eq_sum (u y : ℝ) (N X : ℕ) :
    prefixEuler u y N X = ∑ n ∈ completeBand (Nat.primesLE X), atom u y N n := by
  have hA (p : ℕ) (hp : p ∈ Nat.primesLE X) : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hi (n : ℕ) (hn : n ∈ completeBand (Nat.primesLE X)) :
      MeasureTheory.IntegrableOn (fun xi : ℝ => ZetaRieszMarkedEuler.labelPair N n
        (3/2+Complex.I*y) (SquarefreeVaughanLogSource.length u N) xi/(xi : ℂ)^2) (Set.Ioi 0) := by
    obtain ⟨hs,hc,_hsub⟩ := (mem_completeBand _ hA n).mp hn
    exact ZetaRieszMarkedEuler.integrable_labelPair hs (validLabel_one_lt ⟨hs,hc⟩) N _ _
  unfold prefixEuler
  simp_rw [ZetaRieszOrderedEulerCompletion.orderedPair_eq_labels _ hA,Finset.sum_div]
  rw [MeasureTheory.integral_finsetSum _ hi,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hs,hc,_hsub⟩ := (mem_completeBand _ hA n).mp hn
  have hnp : ¬n.Prime := by
    intro hp
    rw [hp.primeFactors,Finset.card_singleton] at hc
    omega
  rw [← ZetaRieszMarkedEuler.marked_atom_eq_integral hs (validLabel_one_lt ⟨hs,hc⟩) hnp
    N _ (SquarefreeVaughanLogSource.length_pos u N),atom,markedCoefficient,
    if_pos (show validLabel n from ⟨hs,hc⟩)]
  change (markedMass N n : ℂ)*_ = _
  ring

/-- The complete arithmetic series is the limit of actual finite
ordered Euler integrals. This passage is at the safe axis, using absolute
arithmetic summability, and involves no infinite zero-mode product. -/
theorem tendsto_prefixEuler (u y : ℝ) (N : ℕ) (hN : 21 ≤ N) :
    Tendsto (prefixEuler u y N) atTop (nhds (packet u y N)) := by
  let f (X n : ℕ) : ℂ := if n ∈ completeBand (Nat.primesLE X) then atom u y N n else 0
  have hp (n : ℕ) : Tendsto (fun X => f X n) atTop (nhds (atom u y N n)) := by
    by_cases hv : validLabel n
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with X hX
      have hn : n ∈ completeBand (Nat.primesLE X) := by
        apply (mem_completeBand _ (fun p hp => (Nat.mem_primesLE.mp hp).2) n).mpr
        refine ⟨hv.1,hv.2,?_⟩
        intro p hp
        exact Nat.mem_primesLE.mpr
          ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hv.1.ne_zero) (Nat.dvd_of_mem_primeFactors hp)).trans hX,
            Nat.prime_of_mem_primeFactors hp⟩
      exact (if_pos hn).symm
    · have ha : atom u y N n = 0 := by simp only [atom,markedCoefficient,if_neg hv,zero_mul]
      rw [ha]
      have hf : (fun X => f X n) = fun _ => 0 := by
        funext X
        simp only [f,ha,ite_self]
      rw [hf]
      exact tendsto_const_nhds
  have hd : ∀ᶠ X : ℕ in atTop, ∀ n, ‖f X n‖ ≤ ‖atom u y N n‖ := by
    apply Eventually.of_forall
    intro X n
    by_cases hn : n ∈ completeBand (Nat.primesLE X)
    · simp only [f,if_pos hn,le_refl]
    · simpa only [f,if_neg hn,norm_zero] using norm_nonneg (atom u y N n)
  have ht := tendsto_tsum_of_dominated_convergence (summable_atom u y N hN).norm hp hd
  apply ht.congr'
  apply Eventually.of_forall
  intro X
  rw [prefixEuler_eq_sum]
  change (∑' n, if n ∈ completeBand (Nat.primesLE X) then atom u y N n else 0) = _
  rw [tsum_eq_sum (s := completeBand (Nat.primesLE X)) (fun n hn => if_neg hn)]
  exact Finset.sum_congr rfl (fun n hn => if_pos hn)

end
end RiemannGaussian.ZetaRieszPhysicalCompletion
