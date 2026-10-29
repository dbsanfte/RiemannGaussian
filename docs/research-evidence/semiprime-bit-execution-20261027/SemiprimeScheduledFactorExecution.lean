/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePublicAcquiredExecution

/-! # Deterministic natural-input factor algorithm with a literal source guard -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeScheduledFactorExecution
open scoped BigOperators
open Filter SemiprimeMacroParameters SemiprimeCounterRate SemiprimeSourceLayoutRate
open SemiprimePublicAcquiredExecution

/-- Actual binary logarithm of the public Boolean wire count. -/
def lambda (N : ℕ) : ℕ := Nat.clog 2 (wireCount N)
/-- The actual scheduled source group count. -/
def groups (N : ℕ) : ℕ := scheduledGroupCount (lambda N)
/-- The actual scheduled number of interpolation nodes. -/
def points (N : ℕ) : ℕ := scheduledPointCount (lambda N)
/-- The actual scheduled source polynomial degree. -/
def degree (N : ℕ) : ℕ := scheduledDegree (lambda N)
/-- The actual rational source tolerance, computed without real logarithms. -/
def epsilon (N : ℕ) : ℚ := 1/(groups N*lambda N : ℕ)
/-- Precision is computed from actual total input arity, not assumed adequate. -/
def precision (N : ℕ) : ℕ := 2*wireCount N*degree N/points N+1

/-- The actual scheduled precision is the published inclusive support cutoff plus one. -/
theorem precision_formula (N : ℕ) : precision N=
    2*wireCount N*scheduledDegree (Nat.clog 2 (wireCount N))/
      scheduledPointCount (Nat.clog 2 (wireCount N))+1 := rfl

/-- Integer/rational sufficient guard used by the executable branch. -/
def fastGuard (N : ℕ) : Prop :=
  0<wireCount N ∧ 0<scopeBound (bitLength N) ∧ 2≤groups N ∧ 2≤points N ∧
  4≤degree N ∧ 4*degree N≤points N ∧ 0<epsilon N ∧ epsilon N≤1/2 ∧
  4*(2+scopeBound (bitLength N))*scheduledDimension (wireCount N)^2*(groups N*lambda N)^2≤2*wireCount N ∧
  16*points N*groups N^2≤wireCount N ∧
  32*(points N-1)*Nat.clog 2 (2*groups N*lambda N)≤degree N^2 ∧
  epsilon N*(2*wireCount N : ℕ)≤(wireCount N : ℚ)/2

/-- The runtime guard uses only decidable integer and rational operations. -/
instance fastGuardDecidable (N : ℕ) : Decidable (fastGuard N) := by
  unfold fastGuard
  infer_instance

/-- Complete elementary fallback on a literal finite candidate interval. -/
def trialFactor (N : ℕ) : Option ℕ :=
  (List.range N).find? (fun p => decide (2≤p ∧ N%p=0))

/-- Every fallback output is a proper integer divisor. -/
theorem trialFactor_sound (N p : ℕ) (h : trialFactor N=some p) : 2≤p ∧ p<N ∧ p∣N := by
  have hm := List.mem_of_find?_eq_some h
  have hp : 2≤p ∧ N%p=0 := of_decide_eq_true (List.find?_some (p := fun p => decide (2≤p ∧ N%p=0)) (l := List.range N) h)
  exact ⟨hp.1,List.mem_range.mp hm,Nat.dvd_of_mod_eq_zero hp.2⟩

/-- Ordinary proper factor pairs exist exactly when a proper divisor exists. -/
theorem ordinary_iff_divisor (N : ℕ) :
    Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) ↔ ∃ p, 2≤p ∧ p<N ∧ p∣N := by
  constructor
  · rintro ⟨⟨⟨p,q⟩,hp,hq,hprod⟩⟩
    exact ⟨p.val,hp,by nlinarith,⟨q.val,hprod.symm⟩⟩
  · rintro ⟨p,hp,hlt,hdvd⟩
    let q := N/p
    have hprod : p*q=N := Nat.mul_div_cancel' hdvd
    have hq : 2≤q := by nlinarith
    refine ⟨⟨(⟨p,by omega⟩,⟨q,?_⟩),hp,hq,hprod⟩⟩
    exact Nat.lt_succ_of_le (Nat.div_le_self N p)

/-- The fallback has no failure other than absence of a proper factor. -/
theorem trialFactor_none_iff (N : ℕ) :
    trialFactor N=none ↔ ¬Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  rw [ordinary_iff_divisor]
  unfold trialFactor
  rw [List.find?_eq_none]
  simp only [List.mem_range,decide_eq_true_eq]
  constructor
  · intro h ⟨p,hp,hlt,hdvd⟩
    exact h p hlt ⟨hp,Nat.mod_eq_zero_of_dvd hdvd⟩
  · intro h p hlt hp
    exact h ⟨p,hp.1,hlt,Nat.dvd_of_mod_eq_zero hp.2⟩

/-- Precision satisfies the exact interpolation requirement on the branch that uses it. -/
theorem precision_valid (N : ℕ) (hN : 0<N) (hQ : 0<points N) :
    0<precision N ∧ (∑ e, indexedArity N e)*degree N<points N*precision N := by
  refine ⟨Nat.succ_pos _,?_⟩
  rw [indexed_incidence_count N hN]
  exact Nat.lt_mul_div_succ _ hQ

/-- The accepted numerical guard proves the scheduled group count is positive. -/
theorem guard_groups_pos (N : ℕ) (hg : fastGuard N) : 0<groups N :=
  Nat.lt_of_lt_of_le (by decide : 0<2) hg.2.2.1

/-- The accepted numerical guard proves the interpolation count is positive. -/
theorem guard_points_pos (N : ℕ) (hg : fastGuard N) : 0<points N :=
  Nat.lt_of_lt_of_le (by decide : 0<2) hg.2.2.2.1

/-- The centered source interval starts before the last interpolation node. -/
theorem guard_interval (N : ℕ) (hg : fastGuard N) :
    OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart
      (groups N) (points N) (degree N)≤points N :=
  (Nat.le_add_right _ _).trans
    (OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart_end_le
      hg.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1)

/-- The public natural-input algorithm; all parameters and all fallback choices are computed. -/
def run (N : ℕ) : Option ℕ :=
  if hN : 0<N then
    if hr : 0<groups N then
      letI : NeZero (groups N) := ⟨Nat.ne_of_gt hr⟩
      if fastGuard N then
        factor N hN (groups N) (points N) (epsilon N) (degree N) (precision N)
      else trialFactor N
    else trialFactor N
  else none

/-- Every algorithm output is a genuine proper divisor of its original input. -/
theorem run_sound (N p : ℕ) (h : run N=some p) : 2≤p ∧ p<N ∧ p∣N := by
  by_cases hN : 0<N
  · by_cases hr : 0<groups N
    · let _ : NeZero (groups N) := ⟨Nat.ne_of_gt hr⟩
      by_cases hg : fastGuard N
      · have hQ := guard_points_pos N hg
        have hAQ := guard_interval N hg
        have hf : factor N hN (groups N) (points N) (epsilon N) (degree N) (precision N)=some p := by
          simpa only [run,dite_eq_left hN,dite_eq_left hr,ite_eq_left hg] using h
        exact factor_sound N hN (groups N) (points N) (epsilon N) (degree N) (precision N)
          (Nat.le_trans (by decide : 1≤2) hg.2.2.2.1) hAQ (precision_valid N hN hQ).1
          (precision_valid N hN hQ).2 p hf
      · exact trialFactor_sound N p (by simpa only [run,dite_eq_left hN,dite_eq_left hr,ite_eq_right hg] using h)
    · exact trialFactor_sound N p (by simpa only [run,dite_eq_left hN,dite_eq_right hr] using h)
  · have hn : (none : Option ℕ)=some p := by simpa only [run,dite_eq_right hN] using h
    cases hn

/-- The algorithm is complete on every natural input, including primes and squares. -/
theorem run_none_iff (N : ℕ) : run N=none ↔ ¬Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  by_cases hN : 0<N
  · by_cases hr : 0<groups N
    · let _ : NeZero (groups N) := ⟨Nat.ne_of_gt hr⟩
      by_cases hg : fastGuard N
      · have hQ := guard_points_pos N hg
        have hAQ := guard_interval N hg
        simp only [run,dite_eq_left hN,dite_eq_left hr,ite_eq_left hg]
        exact factor_none_iff N hN (groups N) (points N) (epsilon N) (degree N) (precision N)
          (Nat.le_trans (by decide : 1≤2) hg.2.2.2.1) hAQ (precision_valid N hN hQ).1 (precision_valid N hN hQ).2
      · simpa only [run,dite_eq_left hN,dite_eq_left hr,ite_eq_right hg] using trialFactor_none_iff N
    · simpa only [run,dite_eq_left hN,dite_eq_right hr] using trialFactor_none_iff N
  · have hn : N=0 := Nat.eq_zero_of_not_pos hN
    subst N
    rw [ordinary_iff_divisor]
    have he : run 0=none := rfl
    rw [he]
    simp only [true_iff]
    rintro ⟨p,_hp,hlt,_hdvd⟩
    exact Nat.not_lt_zero p hlt

/-- An elementary upper bound converts the integer spectral check to real-log width. -/
theorem log_nat_le_clog (a : ℕ) (ha : 0<a) : Real.log (a : ℝ) ≤ (Nat.clog 2 a : ℝ) := by
  have hp : (a : ℝ) ≤ (2 : ℝ)^Nat.clog 2 a := by exact_mod_cast Nat.le_pow_clog (by decide) a
  have hl := Real.log_le_log (by exact_mod_cast ha) hp
  rw [Real.log_pow] at hl
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  exact hl.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _))

/-- Casting a reciprocal product can be proved before inserting any public graph expressions. -/
theorem inverse_nat_cast (a b : ℕ) :
    ((1/((a*b : ℕ) : ℚ) : ℚ) : ℝ)=1/((a : ℝ)*(b : ℝ)) := by
  simp only [Rat.cast_div,Rat.cast_one,Nat.cast_mul,Rat.cast_mul,Rat.cast_natCast]

/-- Rational positivity transfers to the real comparison without expanding its argument. -/
theorem rational_pos_real (q : ℚ) (h : 0<q) : (0 : ℝ)<q := by exact_mod_cast h
/-- A rational half bound transfers without inspecting its argument's expression. -/
theorem rational_half_real (q : ℚ) (h : q≤1/2) : (q : ℝ)≤1/2 := by
  have hh : (q : ℝ)≤((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr h
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
/-- Reverse transfer of a real comparison on a rational value. -/
theorem real_pos_rational (q : ℚ) (h : (0 : ℝ)<q) : 0<q := by exact_mod_cast h
/-- Reverse transfer of the fixed half bound. -/
theorem real_half_rational (q : ℚ) (h : (q : ℝ)≤1/2) : q≤1/2 := by
  have hh : (q : ℝ)≤((1/2 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  exact Rat.cast_le.mp hh
/-- Integer spectral width casts without unfolding any public sizes. -/
theorem width_cast (a b c : ℕ) (h : 32*a*b≤c^2) :
    (32 : ℝ)*(a : ℝ)*(b : ℝ)≤(c : ℝ)^2 := by exact_mod_cast h

/-- Apply an integer width envelope to an explicitly bounded logarithm. -/
theorem width_from_log (a b c : ℕ) (x : ℝ) (hx : x≤(b : ℝ)) (h : 32*a*b≤c^2) :
    (32 : ℝ)*(a : ℝ)*x≤(c : ℝ)^2 :=
  (mul_le_mul_of_nonneg_left hx (mul_nonneg (by norm_num) (Nat.cast_nonneg a))).trans
    (width_cast a b c h)

/-- The actual decidable guard implies the generic published constructor's real guard. -/
theorem fastGuard_source (N : ℕ) (hg : fastGuard N) :
    sourceLayoutGuard (wireCount N) (scopeBound (bitLength N)) := by
  rcases hg with ⟨hn,hw,hr,hQ,hR,hsize,hpos,hhalf,hinc,hrow,hwidth,_hload⟩
  have hcast : (epsilon N : ℝ)=sourceEpsilon (lambda N) := inverse_nat_cast (groups N) (lambda N)
  have hepos : 0<sourceEpsilon (lambda N) := (rational_pos_real (epsilon N) hpos).trans_eq hcast
  have hehalf : sourceEpsilon (lambda N)≤1/2 := by
    calc
      _ = (epsilon N : ℝ) := hcast.symm
      _ ≤ _ := rational_half_real _ hhalf
  have hprod : 0<groups N*lambda N := by
    by_contra hz
    have he : groups N*lambda N=0 := Nat.eq_zero_of_not_pos hz
    simp only [epsilon,he,Nat.cast_zero,div_zero] at hpos
    exact lt_irrefl _ hpos
  have harg : 0<2*groups N*lambda N := by
    simpa only [Nat.mul_assoc] using Nat.mul_pos (by decide : 0<2) hprod
  have hid : 2/sourceEpsilon (lambda N)=((2*groups N*lambda N : ℕ) : ℝ) := by
    simp only [sourceEpsilon,one_div,div_inv_eq_mul]
    change 2*((groups N : ℝ)*(lambda N : ℝ))=_
    push_cast
    ring
  have hlog : Real.log (2/sourceEpsilon (lambda N))≤(Nat.clog 2 (2*groups N*lambda N) : ℝ) := by
    rw [hid]
    exact log_nat_le_clog _ harg
  refine ⟨hn,hw,hr,hQ,hR,hsize,hepos,hehalf,hinc,hrow,?_⟩
  exact width_from_log (points N-1) (Nat.clog 2 (2*groups N*lambda N)) (degree N)
    (Real.log (2/sourceEpsilon (lambda N))) hlog hwidth

/-- The mathematical public guard and the two already proved executable tests
force the literal runtime guard to pass. -/
theorem fastGuard_of_public (N : ℕ)
    (hg : sourceLayoutGuard (variableCount (bitLength N)) (scopeBound (bitLength N)))
    (hwidth : 32*(scheduledPointCount (Nat.clog 2 (variableCount (bitLength N)))-1)*
      Nat.clog 2 (2*scheduledGroupCount (Nat.clog 2 (variableCount (bitLength N)))*
        Nat.clog 2 (variableCount (bitLength N))) ≤ scheduledDegree (Nat.clog 2 (variableCount (bitLength N)))^2)
    (hload : SemiprimeScheduledCounter.scheduledEpsilon (variableCount (bitLength N))*
      (2*variableCount (bitLength N) : ℕ)≤(variableCount (bitLength N) : ℚ)/2) : fastGuard N := by
  rw [← wireCount_eq N] at hg hwidth hload
  rcases hg with ⟨hn,hw,hr,hQ,hR,hsize,hpos,hhalf,hinc,hrow,_hreal⟩
  have hcast : (epsilon N : ℝ)=sourceEpsilon (lambda N) := inverse_nat_cast (groups N) (lambda N)
  have hposQ : 0<epsilon N := real_pos_rational _ (hpos.trans_eq hcast.symm)
  have hhalfQ : epsilon N≤1/2 := real_half_rational _ (by
    calc
      (epsilon N : ℝ)=sourceEpsilon (lambda N) := hcast
      _ ≤ _ := hhalf)
  exact ⟨hn,hw,hr,hQ,hR,hsize,hposQ,hhalfQ,hinc,hrow,hwidth,hload⟩

/-- Public bit length really tends to infinity with the integer input. -/
theorem bitLength_tendsto : Tendsto bitLength atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2^b)] with N hN
  by_contra hz
  have hs : bitLength N≤b := Nat.le_of_lt (Nat.lt_of_not_ge hz)
  have hp := Nat.pow_le_pow_right (by decide : 0<2) hs
  have hi := input_lt_bitLength_power N
  exact Nat.not_lt_of_ge hN (hi.trans_le hp)

/-- The fallback is confined to finitely many inputs: the actual fast guard passes eventually. -/
theorem eventually_fastGuard : ∀ᶠ N : ℕ in atTop, fastGuard N := by
  have h := bitLength_tendsto.eventually SemiprimeScheduledCounter.eventually_public_executable_guards
  filter_upwards [h] with N hN
  exact fastGuard_of_public N hN.1 hN.2.1 hN.2.2

/-- Eventually the runtime actually takes the source-counter branch, not the fallback. -/
theorem eventually_run_fast : ∀ᶠ N : ℕ in atTop,
    ∃ hN : 0<N, ∃ hg : fastGuard N,
      letI : NeZero (groups N) := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<2) hg.2.2.1)⟩
      run N=factor N hN (groups N) (points N) (epsilon N) (degree N) (precision N) := by
  filter_upwards [eventually_fastGuard,eventually_gt_atTop 0] with N hg hN
  exact ⟨hN,hg,by simp only [run,dite_eq_left hN,dite_eq_left (guard_groups_pos N hg),ite_eq_left hg]⟩

end RiemannGaussian.SemiprimeScheduledFactorExecution
