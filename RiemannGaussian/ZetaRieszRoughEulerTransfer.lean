/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOrderedEulerBound

/-!
# The literal signed packet and its paid leading Euler quotient

Removing the exponential prime head is paid by the existing rectangle
concentration. The full ordered Euler correction then decays geometrically,
with its leading quotient included. The resulting main quotient retains
both marked slots and every factorial order. It still needs a signed bound.
-/

namespace RiemannGaussian.ZetaRieszRoughEulerTransfer
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszAnnulusJoint ZetaRieszMarkedCompletion ZetaRieszPhysicalCompletion
open ZetaRieszMarkedPrimeHead ZetaRieszOrderedEulerBound ZetaRieszWideOwnerAudit

/-- The original physical prime set with only the independently paid
exponential head removed. The fixed floor is immaterial for N>=21. -/
def roughPrimes (u : ℝ) (N : ℕ) : Finset ℕ :=
  (intermediatePrimes u N).filter (fun p => 16 ≤ p ∧ (N : ℝ)/110 < Real.log p)

theorem rough_prime {u : ℝ} {N p : ℕ} (hp : p ∈ roughPrimes u N) : p.Prime :=
  ((mem_intermediatePrimes u N p).mp (Finset.mem_filter.mp hp).1).1

theorem rough_sixteen {u : ℝ} {N p : ℕ} (hp : p ∈ roughPrimes u N) : 16 ≤ p :=
  (Finset.mem_filter.mp hp).2.1

theorem rough_head {u : ℝ} {N p : ℕ} (hp : p ∈ roughPrimes u N) :
    (N : ℝ)/110 ≤ Real.log p := (Finset.mem_filter.mp hp).2.2.le

/-- A literal complete squarefree sum, with its original signed atom. -/
def roughPacket (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ completeBand (roughPrimes u N), atom u y N n

/-- The surviving main Euler quotient at the unchanged factorial
rectangle and original moving Riesz length. -/
def mainQuotient (u y : ℝ) (N : ℕ) : ℂ :=
  quotientResponse (roughPrimes u N) N (3/2+Complex.I*y) (SquarefreeVaughanLogSource.length u N)

theorem completeBand_rough (u : ℝ) (N : ℕ) (hN : 21 ≤ N) :
    completeBand (roughPrimes u N) =
      (completeBand (intermediatePrimes u N)).filter
        (fun n => ¬Real.log n.minFac ≤ (N : ℝ)/110) := by
  have hA (p : ℕ) (hp : p ∈ intermediatePrimes u N) : p.Prime :=
    ((mem_intermediatePrimes u N p).mp hp).1
  ext n
  rw [mem_completeBand _ (fun _ hp => rough_prime hp),Finset.mem_filter,
    mem_completeBand _ hA]
  constructor
  · rintro ⟨hs,hc,hp⟩
    have hn1 := validLabel_one_lt ⟨hs,hc⟩
    have hm : n.minFac ∈ n.primeFactors :=
      (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hs.ne_zero
    exact ⟨⟨hs,hc,fun p hp' => (Finset.mem_filter.mp (hp p hp')).1⟩,
      not_le.mpr (Finset.mem_filter.mp (hp n.minFac hm)).2.2⟩
  · rintro ⟨⟨hs,hc,hp⟩,hm⟩
    have hn1 := validLabel_one_lt ⟨hs,hc⟩
    refine ⟨hs,hc,?_⟩
    intro p hp'
    obtain ⟨hprime,hpN,_hpX⟩ := (mem_intermediatePrimes u N p).mp (hp p hp')
    refine Finset.mem_filter.mpr ⟨hp p hp',?_,?_⟩
    · nlinarith
    · have hh := Nat.minFac_le_of_dvd hprime.two_le (Nat.dvd_of_mem_primeFactors hp')
      exact (not_le.mp hm).trans_le (Real.log_le_log
        (by exact_mod_cast (Nat.minFac_prime hn1.ne').pos) (by exact_mod_cast hh))

/-- The removed labels are exactly the already bounded arithmetic
prime head. No additional completion or incidence debt is introduced. -/
theorem complete_sub_rough (u y : ℝ) (N : ℕ) (hN : 21 ≤ N) :
    completePacket u y N-roughPacket u y N =
      ∑ n ∈ completeBand (intermediatePrimes u N), headAtom u y N n := by
  rw [← sum_atom_completeBand,roughPacket,completeBand_rough u N hN,
    Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hm : Real.log n.minFac ≤ (N : ℝ)/110
  · simp only [hm,not_true_eq_false,if_false,sub_zero,headAtom,if_true]
  · simp only [hm,not_false_eq_true,if_true,sub_self,headAtom,if_false]

/-- Every genuine finite prime selection gives the same exact
arithmetic-to-Fourier identity, with all original marked coefficients. -/
theorem sum_atoms_eq_integral (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (u y : ℝ) (N : ℕ) :
    (∑ n ∈ completeBand A, atom u y N n) =
      ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(SquarefreeVaughanLogSource.length u N : ℂ))*
        ∫ xi : ℝ in Ioi 0, ZetaRieszMarkedEuler.orderedPair A N (3/2+Complex.I*y)
          (SquarefreeVaughanLogSource.length u N) xi/(xi : ℂ)^2 := by
  have hi (n : ℕ) (hn : n ∈ completeBand A) :
      IntegrableOn (fun xi : ℝ => ZetaRieszMarkedEuler.labelPair N n
        (3/2+Complex.I*y) (SquarefreeVaughanLogSource.length u N) xi/(xi : ℂ)^2) (Ioi 0) := by
    obtain ⟨hs,hc,_hsub⟩ := (mem_completeBand A hA n).mp hn
    exact ZetaRieszMarkedEuler.integrable_labelPair hs (validLabel_one_lt ⟨hs,hc⟩) N _ _
  simp_rw [ZetaRieszOrderedEulerCompletion.orderedPair_eq_labels A hA,Finset.sum_div]
  rw [integral_finsetSum _ hi,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hs,hc,_hsub⟩ := (mem_completeBand A hA n).mp hn
  have hnp : ¬n.Prime := by
    intro hp
    rw [hp.primeFactors,Finset.card_singleton] at hc
    omega
  rw [← ZetaRieszMarkedEuler.marked_atom_eq_integral hs (validLabel_one_lt ⟨hs,hc⟩) hnp
    N _ (SquarefreeVaughanLogSource.length_pos u N),atom,markedCoefficient,
    if_pos (show validLabel n from ⟨hs,hc⟩)]
  change (markedMass N n : ℂ)*_*_ = _
  unfold markedMass
  ring

/-- The rough arithmetic packet is exactly main quotient plus the
full correction that has already been bounded independently. -/
theorem roughPacket_split (u y : ℝ) (N : ℕ) :
    roughPacket u y N = mainQuotient u y N+
      errorResponse (roughPrimes u N) N (3/2+Complex.I*y) (SquarefreeVaughanLogSource.length u N) := by
  rw [roughPacket,sum_atoms_eq_integral _ (fun _ hp => rough_prime hp)]
  exact response_split _ (fun _ hp => rough_prime hp) (fun _ hp => rough_sixteen hp) N
    (fun _ hp => rough_head hp) safeRadius_pos (by norm_num [safeRadius]) _

/-- The arithmetic head bound applies to the actual moving physical
prime universe, without completing a cofactor or changing the masks. -/
theorem tendsto_complete_sub_rough {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*(completePacket u (heights N) N-roughPacket u (heights N) N))
      atTop (nhds 0) := by
  obtain ⟨r,C,hr0,hr1,_hC,hb⟩ := exists_finite_head_bound
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C).add tendsto_shareBudget
  simp only [zero_mul,zero_add] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop 21] with N hN
  rw [complete_sub_rough _ _ N hN]
  exact hb N hN u hu hU (heights N) _

/-- The nonlinear middle correction, including its leading quotient,
is paid at source scale for the literal prime selection and length. -/
theorem tendsto_rough_sub_main {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*(roughPacket u (heights N) N-mainQuotient u (heights N) N))
      atTop (nhds 0) := by
  simp_rw [roughPacket_split,add_sub_cancel_left]
  exact tendsto_errorResponse (roughPrimes u) (fun _ _ hp => rough_sixteen hp)
    (fun _ _ hp => rough_head hp) heights (SquarefreeVaughanLogSource.length u)
      (ZetaRieszHeadOrders.one_le_length u) hu hU

/-- The complete original physical packet differs from the leading
ordered Euler quotient by two independently paid arithmetic errors. -/
theorem tendsto_complete_sub_main {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*(completePacket u (heights N) N-mainQuotient u (heights N) N))
      atTop (nhds 0) := by
  have h := (tendsto_complete_sub_rough hu hU heights).add (tendsto_rough_sub_main hu hU heights)
  simp only [zero_add] at h
  convert h using 1
  ext N
  ring

/-- Terminal connection to the unchanged signed counts 3..55 minus
the short upper-overflow counts 3..13, on the original dyadic schedule.
The main quotient is source-equivalent, not asserted to be small. -/
theorem tendsto_main_sub_current {u : ℝ} (hu : 1/2 < u) (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (mainQuotient u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have h := (tendsto_complete_sub_current hu hU y).sub
    ((tendsto_complete_sub_main (by linarith : 0 ≤ u) hU (fun _ => y)).comp
      ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [sub_self] at h
  convert h using 1
  ext j
  simp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszRoughEulerTransfer
