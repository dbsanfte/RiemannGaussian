/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeTraceRows

/-!
# Guarded inverse-orbit compression of retained rows

The executable representative scan checks one original difference at every
whole-trace match. Its accepted rows retain one global inverse orientation,
and its representatives have distinct whole traces. Raw sign endpoints
precede this scan and the one-polynomial derivative stage follows it.

This module prices GCD queries only. The association-list specification does
not supply a fast deterministic table, a bit-machine refinement, paid row
construction, or the missing universal sixth-root collision coverage.
-/

namespace RiemannGaussian.SemiprimeGuardedTrace

open SemiprimeCartesianCompletion SemiprimeRowDerivative SemiprimeTraceRows

/-- A checked trace match either returns a proper factor or retains one
original representative. The richer input list remains available. -/
def guardTraces {n : ℕ} : List (ZMod n)ˣ → List (ZMod n)ˣ → ℕ ⊕ List (ZMod n)ˣ
  | [], reps => .inr reps
  | x::tail, reps =>
    match reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none => guardTraces tail (x::reps)
    | some y =>
      match SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val with
      | some d => .inl d
      | none => guardTraces tail reps

/-- Every checked whole-trace match uses one GCD; lookup costs are separate. -/
def guardGcdCount {n : ℕ} : List (ZMod n)ˣ → List (ZMod n)ˣ → ℕ
  | [], _ => 0
  | x::tail, reps =>
    match reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none => guardGcdCount tail (x::reps)
    | some y => 1+
      match SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val with
      | some _ => 0
      | none => guardGcdCount tail reps

theorem guardTraces_sound {n d : ℕ} (rows reps : List (ZMod n)ˣ)
    (hd : guardTraces rows reps=.inl d) : SemiprimeGroupSelection.ProperDivisor n d := by
  induction rows generalizing reps with
  | nil => simp [guardTraces] at hd
  | cons x tail ih =>
    cases hf : reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none => exact ih (x::reps) (by simpa [guardTraces,hf] using hd)
    | some y =>
      cases hc : SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val with
      | none => exact ih reps (by simpa [guardTraces,hf,hc] using hd)
      | some d' =>
        have he : d'=d := by simpa [guardTraces,hf,hc] using hd
        subst d'
        exact SemiprimeGroupSelection.checkedSignal_sound hc

theorem guardGcdCount_le {n : ℕ} (rows reps : List (ZMod n)ˣ) :
    guardGcdCount rows reps≤rows.length := by
  induction rows generalizing reps with
  | nil => simp [guardGcdCount]
  | cons x tail ih =>
    cases hf : reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none => simpa [guardGcdCount,hf] using (ih (x::reps)).trans (Nat.le_succ _)
    | some y =>
      cases hc : SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val with
      | none => simpa [guardGcdCount,hf,hc,Nat.add_comm] using Nat.succ_le_succ (ih reps)
      | some d => simp [guardGcdCount,hf,hc]

theorem guardTraces_length {n : ℕ} (rows reps out : List (ZMod n)ˣ)
    (ho : guardTraces rows reps=.inr out) : out.length≤rows.length+reps.length := by
  induction rows generalizing reps with
  | nil =>
    have he : reps=out := by simpa [guardTraces] using ho
    simp [he]
  | cons x tail ih =>
    cases hf : reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none =>
      have hh := ih (x::reps) (by simpa [guardTraces,hf] using ho)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    | some y =>
      cases hc : SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val with
      | none =>
        have hh := ih reps (by simpa [guardTraces,hf,hc] using ho)
        simp only [List.length_cons]
        omega
      | some d => simp [guardTraces,hf,hc] at ho

/-- Representatives already retained by the scan are never discarded. -/
theorem guardTraces_preserves_old {n : ℕ} (rows reps out : List (ZMod n)ˣ)
    (ho : guardTraces rows reps=.inr out) : ∀ x∈reps, x∈out := by
  induction rows generalizing reps with
  | nil =>
    have he : reps=out := by simpa [guardTraces] using ho
    simp [he]
  | cons x tail ih =>
    cases hf : reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none =>
      have hh := ih (x::reps) (by simpa [guardTraces,hf] using ho)
      exact fun y hy => hh y (List.mem_cons_of_mem x hy)
    | some y =>
      cases hc : SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val with
      | none => exact ih reps (by simpa [guardTraces,hf,hc] using ho)
      | some d => simp [guardTraces,hf,hc] at ho

/-- Every accepted original row equals a retained unit or its global
inverse. The guard theorem discharges this orientation information. -/
theorem guardTraces_orientation {n : ℕ} [NeZero n]
    (rows reps out : List (ZMod n)ˣ) (ho : guardTraces rows reps=.inr out) :
    ∀ x∈rows, ∃ r∈out, x=r ∨ x=r⁻¹ := by
  induction rows generalizing reps with
  | nil => simp
  | cons x tail ih =>
    cases hf : reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none =>
      have hh : guardTraces tail (x::reps)=.inr out := by simpa [guardTraces,hf] using ho
      intro y hy
      rcases List.mem_cons.mp hy with hxy|hy
      · subst y
        exact ⟨x,guardTraces_preserves_old tail (x::reps) out hh x (by simp),Or.inl rfl⟩
      · exact ih (x::reps) hh y hy
    | some r =>
      cases hc : SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(r : ZMod n)).val with
      | none =>
        have hh : guardTraces tail reps=.inr out := by simpa [guardTraces,hf,hc] using ho
        have hr := List.mem_of_find?_eq_some hf
        have ht : traceValue x=traceValue r := of_decide_eq_true
          (List.find?_some (p:=fun y => decide (traceValue x=traceValue y)) hf)
        intro y hy
        rcases List.mem_cons.mp hy with hxy|hy
        · subst y
          exact ⟨r,guardTraces_preserves_old tail reps out hh r hr,
            global_trace_guard_none_orientation x r ht hc⟩
        · exact ih reps hh y hy
      | some d => simp [guardTraces,hf,hc] at ho

/-- Every representative comes from the richer original carrier. -/
theorem guardTraces_reps_subset {n : ℕ} (rows reps out : List (ZMod n)ˣ)
    (ho : guardTraces rows reps=.inr out) : ∀ x∈out, x∈rows ∨ x∈reps := by
  induction rows generalizing reps with
  | nil =>
    have he : reps=out := by simpa [guardTraces] using ho
    simp [he]
  | cons x tail ih =>
    cases hf : reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none =>
      have hh := ih (x::reps) (by simpa [guardTraces,hf] using ho)
      intro y hy
      rcases hh y hy with ht|hr
      · exact Or.inl (List.mem_cons_of_mem x ht)
      · rcases List.mem_cons.mp hr with rfl|hr
        · exact Or.inl (by simp)
        · exact Or.inr hr
    | some y =>
      cases hc : SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val with
      | none =>
        have hh := ih reps (by simpa [guardTraces,hf,hc] using ho)
        exact fun z hz => (hh z hz).imp (List.mem_cons_of_mem x) id
      | some d => simp [guardTraces,hf,hc] at ho

/-- The scalar trace is injective on retained representatives only. -/
def TraceSeparated {n : ℕ} (reps : List (ZMod n)ˣ) : Prop :=
  ∀ x∈reps, ∀ y∈reps, traceValue x=traceValue y → x=y

private theorem separated_cons {n : ℕ} {x : (ZMod n)ˣ} {reps : List (ZMod n)ˣ}
    (hs : TraceSeparated reps) (hx : ∀ y∈reps, traceValue x≠traceValue y) :
    TraceSeparated (x::reps) := by
  intro a ha b hb ht
  rcases List.mem_cons.mp ha with ha|ha
  · subst a
    rcases List.mem_cons.mp hb with hb|hb
    · exact hb.symm
    · exact (hx b hb ht).elim
  · rcases List.mem_cons.mp hb with hb|hb
    · subst b
      exact (hx a ha ht.symm).elim
    · exact hs a ha b hb ht

/-- A new representative is inserted only after its whole trace fails to
match every retained one, so successful compression preserves separation. -/
theorem guardTraces_separated {n : ℕ} (rows reps out : List (ZMod n)ˣ)
    (hs : TraceSeparated reps) (ho : guardTraces rows reps=.inr out) :
    TraceSeparated out := by
  induction rows generalizing reps with
  | nil =>
    have he : reps=out := by simpa [guardTraces] using ho
    exact he ▸ hs
  | cons x tail ih =>
    cases hf : reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none =>
      have hx : ∀ y∈reps, traceValue x≠traceValue y := by
        intro y hy ht
        have hn := (List.find?_eq_none.mp hf) y hy
        simp [ht] at hn
      exact ih (x::reps) (separated_cons hs hx) (by simpa [guardTraces,hf] using ho)
    | some y =>
      cases hc : SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val with
      | none => exact ih reps hs (by simpa [guardTraces,hf,hc] using ho)
      | some d => simp [guardTraces,hf,hc] at ho

/-- Raw endpoints keep both original sign channels before folding. -/
def endpointLeaves {n : ℕ} (rows : List (ZMod n)ˣ) : List ℕ :=
  rows.flatMap fun (x : (ZMod n)ˣ) => [((x : ZMod n)-1).val,((x : ZMod n)+1).val]

theorem endpointLeaves_length {n : ℕ} (rows : List (ZMod n)ˣ) :
    (endpointLeaves rows).length=2*rows.length := by
  induction rows with
  | nil => rfl
  | cons x tail ih =>
    simp only [endpointLeaves,List.flatMap_cons,List.length_append,List.length_cons,
      List.length_nil] at *
    omega

theorem endpoints_none {n : ℕ} (rows : List (ZMod n)ˣ)
    (hn : scanProper n (endpointLeaves rows)=none) {x : (ZMod n)ˣ} (hx : x∈rows) :
    SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-1).val=none ∧
      SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)+1).val=none := by
  have hh := (scanProper_none_iff n (endpointLeaves rows)).mp hn
  exact ⟨hh _ (List.mem_flatMap.mpr ⟨x,hx,by simp⟩),
    hh _ (List.mem_flatMap.mpr ⟨x,hx,by simp⟩)⟩

/-- The complete guarded extraction procedure. It has no factor field,
private order, collision pair or explicit pair matrix as input. -/
noncomputable def guardedTraceRows {n : ℕ} (rows : List (ZMod n)ˣ) : Option ℕ :=
  match scanProper n (endpointLeaves rows) with
  | some d => some d
  | none =>
    match guardTraces rows [] with
    | .inl d => some d
    | .inr reps => recoverTraceRows reps.toFinset

theorem guardedTraceRows_sound {n d : ℕ} (rows : List (ZMod n)ˣ)
    (hd : guardedTraceRows rows=some d) : SemiprimeGroupSelection.ProperDivisor n d := by
  cases he : scanProper n (endpointLeaves rows) with
  | some d' =>
    have hh : d'=d := by simpa [guardedTraceRows,he] using hd
    subst d'
    exact scanProper_sound he
  | none =>
    cases hg : guardTraces rows [] with
    | inl d' =>
      have hh : d'=d := by simpa [guardedTraceRows,he,hg] using hd
      subst d'
      exact guardTraces_sound rows [] hg
    | inr reps => exact recoverTraceRows_sound (by simpa [guardedTraceRows,he,hg] using hd)

/-- Only derivative-stage GCD queries are counted by this component. -/
noncomputable def traceGcdCount {n : ℕ} (reps : List (ZMod n)ˣ) : ℕ :=
  recoveryGcdCount n (fun i => residueLeaves (traceRoots reps.toFinset) (i : ZMod n))
    (evaluatedColumns (traceRoots reps.toFinset) (traceRoots reps.toFinset).toList)

theorem traceGcdCount_le {n : ℕ} (reps : List (ZMod n)ˣ) :
    traceGcdCount reps≤2*reps.length :=
  (recoverTraceRows_gcd_bound reps.toFinset).trans
    (Nat.mul_le_mul_left 2 reps.toFinset_card_le)

/-- The complete guard/derivative query counter. This does not count
table searches, inverses, polynomial work or machine bit operations. -/
noncomputable def guardedTraceGcdCount {n : ℕ} (rows : List (ZMod n)ˣ) : ℕ :=
  scanGcdCount n (endpointLeaves rows)+
    match scanProper n (endpointLeaves rows) with
    | some _ => 0
    | none => guardGcdCount rows []+
      match guardTraces rows [] with
      | .inl _ => 0
      | .inr reps => traceGcdCount reps

/-- Both endpoints, at most one whole-trace guard per row, and one folded
derivative recovery use at most five GCD queries per original unit. -/
theorem guardedTraceGcdCount_le {n : ℕ} (rows : List (ZMod n)ˣ) :
    guardedTraceGcdCount rows≤5*rows.length := by
  have he : scanGcdCount n (endpointLeaves rows)≤2*rows.length := by
    simpa [endpointLeaves_length] using scanGcdCount_le n (endpointLeaves rows)
  have hg := guardGcdCount_le rows []
  cases hs : scanProper n (endpointLeaves rows) with
  | some d => simp only [guardedTraceGcdCount,hs,Nat.add_zero]; omega
  | none =>
    cases ho : guardTraces rows [] with
    | inl d => simp only [guardedTraceGcdCount,hs,ho,Nat.add_zero]; omega
    | inr reps =>
      have hl : reps.length≤rows.length := by simpa using guardTraces_length rows [] reps ho
      have hr := traceGcdCount_le reps
      simp only [guardedTraceGcdCount,hs,ho]
      calc
        _ ≤ 2*rows.length+(rows.length+2*rows.length) :=
          Nat.add_le_add he (Nat.add_le_add hg (hr.trans (Nat.mul_le_mul_left 2 hl)))
        _ = 5*rows.length := by omega

private theorem trace_eq_of_orientation {R : Type*} [CommRing R] {x r : Rˣ}
    (h : x=r ∨ x=r⁻¹) : traceValue x=traceValue r := by
  rcases h with h|h
  · rw [h]
  · rw [h,traceValue_inv]

/-- Every original trace remains present in the accepted folded carrier. -/
theorem guardTraces_trace_mem {n : ℕ} [NeZero n]
    (rows out : List (ZMod n)ˣ) (ho : guardTraces rows []=.inr out)
    {x : (ZMod n)ˣ} (hx : x∈rows) : traceValue x∈traceRoots out.toFinset := by
  obtain ⟨r,hr,hxr⟩ := guardTraces_orientation rows [] out ho x hx
  exact Finset.mem_image.mpr ⟨r,List.mem_toFinset.mpr hr,(trace_eq_of_orientation hxr).symm⟩

/-- Once every whole-trace check has passed, equal original traces have
one consistent global orientation; no mixed component match was dropped. -/
theorem guardTraces_same_trace_orientation {n : ℕ} [NeZero n]
    (rows out : List (ZMod n)ˣ) (ho : guardTraces rows []=.inr out)
    {x y : (ZMod n)ˣ} (hx : x∈rows) (hy : y∈rows)
    (ht : traceValue x=traceValue y) : x=y ∨ y=x⁻¹ := by
  obtain ⟨r,hr,hxr⟩ := guardTraces_orientation rows [] out ho x hx
  obtain ⟨s,hs,hys⟩ := guardTraces_orientation rows [] out ho y hy
  have hsep := guardTraces_separated rows [] out (by simp [TraceSeparated]) ho
  have he : traceValue r=traceValue s :=
    (trace_eq_of_orientation hxr).symm.trans (ht.trans (trace_eq_of_orientation hys))
  have hrs : r=s := hsep r hr s hs he
  subst s
  rcases hxr with hxr|hxr <;> rcases hys with hys|hys
  · exact Or.inl (hxr.trans hys.symm)
  · exact Or.inr (by rw [hxr]; exact hys)
  · exact Or.inr (by rw [hxr,inv_inv]; exact hys)
  · exact Or.inl (hxr.trans hys.symm)

/-- Failed raw endpoint checks also make the self-product a global zero
or a unit. This retains local self-inversion without squaring a signal. -/
theorem self_product_none_of_endpoints {n : ℕ} [NeZero n] (x : ZMod n)
    (hm : SemiprimeGroupSelection.checkedSignal n (x-1).val=none)
    (hp : SemiprimeGroupSelection.checkedSignal n (x+1).val=none) :
    SemiprimeGroupSelection.checkedSignal n (x*x-1).val=none := by
  rw [checkedSignal_none_iff]
  have he : (x-1)*(x+1)=x*x-1 := by ring
  rcases (checkedSignal_none_iff _).mp hm with hz|hu
  · left; rw [←he,hz,zero_mul]
  · rcases (checkedSignal_none_iff _).mp hp with hz|hv
    · left; rw [←he,hz,mul_zero]
    · right; rw [←he]; exact hu.mul hv

private theorem inverse_difference_checkedSignal {n : ℕ} (x : (ZMod n)ˣ) :
    SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-((x⁻¹ : (ZMod n)ˣ) : ZMod n)).val=
      SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)*(x : ZMod n)-1).val := by
  simp only [SemiprimeGroupSelection.checkedSignal,SemiprimeReciprocalRows.inverse_residual_gcd]

/-- Exhaustion exposes all the actual failed stages, rather than assuming
the needed mathematical collision coverage in a hidden premise. -/
theorem guardedTraceRows_none_stages {n : ℕ} (rows : List (ZMod n)ˣ)
    (hn : guardedTraceRows rows=none) :
    scanProper n (endpointLeaves rows)=none ∧
      ∃ out, guardTraces rows []=.inr out ∧ recoverTraceRows out.toFinset=none := by
  cases he : scanProper n (endpointLeaves rows) with
  | some d => simp [guardedTraceRows,he] at hn
  | none =>
    refine ⟨rfl,?_⟩
    cases hg : guardTraces rows [] with
    | inl d => simp [guardedTraceRows,he,hg] at hn
    | inr out => exact ⟨out,rfl,by simpa [guardedTraceRows,he,hg] using hn⟩

/-- Every proper ordinary or product-one pair hit survives all guards and
the single trace polynomial. This is a supplied-hit preservation theorem,
not an assumption or proof of universal sixth-root row coverage. -/
theorem guardedTraceRows_none_pair_checks {n : ℕ} [NeZero n]
    (rows : List (ZMod n)ˣ) (hn : guardedTraceRows rows=none)
    {x y : (ZMod n)ˣ} (hx : x∈rows) (hy : y∈rows) :
    SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val=none ∧
      SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)*(y : ZMod n)-1).val=none := by
  obtain ⟨hend,out,hguard,hfold⟩ := guardedTraceRows_none_stages rows hn
  have hsign := endpoints_none rows hend hx
  have hself := self_product_none_of_endpoints (x : ZMod n) hsign.1 hsign.2
  by_cases ht : traceValue x=traceValue y
  · rcases guardTraces_same_trace_orientation rows out hguard hx hy ht with he|he
    · subst y
      exact ⟨by simp [SemiprimeGroupSelection.checkedSignal],hself⟩
    · subst y
      have hp : (x : ZMod n)*((x⁻¹ : (ZMod n)ˣ) : ZMod n)=1 := by simp
      exact ⟨by rw [inverse_difference_checkedSignal]; exact hself,
        by simp [hp,SemiprimeGroupSelection.checkedSignal]⟩
  · have hh : n.gcd (traceValue x-traceValue y).val=1 :=
      (recoverRows_none_iff (traceRoots out.toFinset)).mp hfold
        (traceValue x) (guardTraces_trace_mem rows out hguard hx)
        (traceValue y) (guardTraces_trace_mem rows out hguard hy) (Ne.symm ht)
    have hu := (trace_difference_isUnit_iff x y).mp
      ((SemiprimeBulkNorm.gcd_one_iff_unit _).mp hh)
    exact ⟨(checkedSignal_none_iff _).mpr (Or.inr hu.1),
      (checkedSignal_none_iff _).mpr (Or.inr hu.2)⟩

/-- The complete guarded procedure detects every proper original pair
in either channel, including diagonal reciprocal hits and saturation. -/
theorem guardedTraceRows_succeeds_of_pair {n : ℕ} [NeZero n]
    (rows : List (ZMod n)ˣ) {x y : (ZMod n)ˣ} (hx : x∈rows) (hy : y∈rows)
    (hp : SemiprimeGroupSelection.ProperDivisor n (n.gcd ((x : ZMod n)-(y : ZMod n)).val) ∨
      SemiprimeGroupSelection.ProperDivisor n (n.gcd ((x : ZMod n)*(y : ZMod n)-1).val)) :
    ∃ d, guardedTraceRows rows=some d := by
  cases hn : guardedTraceRows rows with
  | some d => exact ⟨d,rfl⟩
  | none =>
    have hh := guardedTraceRows_none_pair_checks rows hn hx hy
    rcases hp with hp|hp
    · have hc : SemiprimeGroupSelection.checkedSignal n
          ((x : ZMod n)-(y : ZMod n)).val=some (n.gcd ((x : ZMod n)-(y : ZMod n)).val) := by
        simp [SemiprimeGroupSelection.checkedSignal,hp.1,hp.2.1]
      rw [hh.1] at hc
      contradiction
    · have hc : SemiprimeGroupSelection.checkedSignal n
          ((x : ZMod n)*(y : ZMod n)-1).val=some (n.gcd ((x : ZMod n)*(y : ZMod n)-1).val) := by
        simp [SemiprimeGroupSelection.checkedSignal,hp.1,hp.2.1]
      rw [hh.2] at hc
      contradiction

/-- A proper raw endpoint hit is also recovered by the complete procedure. -/
theorem guardedTraceRows_succeeds_of_endpoint {n : ℕ} (rows : List (ZMod n)ˣ)
    {v : ℕ} (hv : v∈endpointLeaves rows)
    (hp : SemiprimeGroupSelection.ProperDivisor n (n.gcd v)) :
    ∃ d, guardedTraceRows rows=some d := by
  cases hn : guardedTraceRows rows with
  | some d => exact ⟨d,rfl⟩
  | none =>
    have he := (guardedTraceRows_none_stages rows hn).1
    have hh := (scanProper_none_iff n (endpointLeaves rows)).mp he v hv
    have hc : SemiprimeGroupSelection.checkedSignal n v=some (n.gcd v) := by
      simp [SemiprimeGroupSelection.checkedSignal,hp.1,hp.2.1]
    rw [hh] at hc
    contradiction

/-- Failed original ordinary checks let the actual representative scan
finish; the scope contains every input and every retained representative. -/
theorem guardTraces_exists_of_pair_checks {n : ℕ}
    (rows reps scope : List (ZMod n)ˣ)
    (hrows : ∀ x∈rows, x∈scope) (hreps : ∀ x∈reps, x∈scope)
    (hall : ∀ x∈scope, ∀ y∈scope,
      SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val=none) :
    ∃ out, guardTraces rows reps=.inr out := by
  induction rows generalizing reps with
  | nil => exact ⟨reps,rfl⟩
  | cons x tail ih =>
    have htail : ∀ y∈tail, y∈scope := fun y hy => hrows y (List.mem_cons_of_mem x hy)
    cases hf : reps.find? (fun y => decide (traceValue x=traceValue y)) with
    | none =>
      have hnew : ∀ y∈x::reps, y∈scope := by
        intro y hy
        rcases List.mem_cons.mp hy with hxy|hy
        · exact hxy ▸ hrows x (by simp)
        · exact hreps y hy
      obtain ⟨out,ho⟩ := ih (x::reps) htail hnew
      exact ⟨out,by simpa [guardTraces,hf] using ho⟩
    | some y =>
      have hc := hall x (hrows x (by simp)) y (hreps y (List.mem_of_find?_eq_some hf))
      obtain ⟨out,ho⟩ := ih reps htail hreps
      exact ⟨out,by simpa [guardTraces,hf,hc] using ho⟩

/-- Distinct global traces have unit differences when every original
ordinary and reciprocal pair check fails. This proves that the folded
polynomial adds no new proper-factor channel to that original carrier. -/
theorem recoverTraceRows_none_of_pair_checks {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)ˣ)
    (hall : ∀ x∈S, ∀ y∈S,
      SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val=none ∧
        SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)*(y : ZMod n)-1).val=none) :
    recoverTraceRows S=none := by
  apply (recoverRows_none_iff (traceRoots S)).mpr
  intro t ht u hu hne
  obtain ⟨x,hx,htx⟩ := Finset.mem_image.mp ht
  obtain ⟨y,hy,hty⟩ := Finset.mem_image.mp hu
  have hnt : traceValue x≠traceValue y := by
    intro he
    exact hne (hty.symm.trans (he.symm.trans htx))
  have hd : (x : ZMod n)-(y : ZMod n)≠0 := by
    intro he
    exact hnt (congrArg traceValue (Units.ext (sub_eq_zero.mp he)))
  have hp : (x : ZMod n)*(y : ZMod n)-1≠0 := by
    intro he
    have hh : traceValue x-traceValue y=0 := by rw [trace_difference,he,mul_zero]
    exact hnt (sub_eq_zero.mp hh)
  have hc := hall x hx y hy
  have hdu := ((checkedSignal_none_iff _).mp hc.1).resolve_left hd
  have hpu := ((checkedSignal_none_iff _).mp hc.2).resolve_left hp
  apply (SemiprimeBulkNorm.gcd_one_iff_unit _).mpr
  rw [←htx,←hty]
  exact (trace_difference_isUnit_iff x y).mpr ⟨hdu,hpu⟩

/-- Exact exhaustion criterion for the complete guarded procedure. It
preserves precisely the original pair-hit union and raw endpoint channel;
it does not create universal coverage by compressing those observables. -/
theorem guardedTraceRows_none_iff {n : ℕ} [NeZero n] (rows : List (ZMod n)ˣ) :
    guardedTraceRows rows=none ↔ scanProper n (endpointLeaves rows)=none ∧
      ∀ x∈rows, ∀ y∈rows,
        SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)-(y : ZMod n)).val=none ∧
          SemiprimeGroupSelection.checkedSignal n ((x : ZMod n)*(y : ZMod n)-1).val=none := by
  constructor
  · intro hn
    exact ⟨(guardedTraceRows_none_stages rows hn).1,
      fun _ hx _ hy => guardedTraceRows_none_pair_checks rows hn hx hy⟩
  · rintro ⟨he,hall⟩
    obtain ⟨out,ho⟩ := guardTraces_exists_of_pair_checks rows [] rows
      (fun _ hx => hx) (by simp) (fun x hx y hy => (hall x hx y hy).1)
    have hsub : ∀ x∈out, x∈rows := by
      intro x hx
      simpa using guardTraces_reps_subset rows [] out ho x hx
    have hf : recoverTraceRows out.toFinset=none := by
      apply recoverTraceRows_none_of_pair_checks
      intro x hx y hy
      exact hall x (hsub x (List.mem_toFinset.mp hx)) y (hsub y (List.mem_toFinset.mp hy))
    simp [guardedTraceRows,he,ho,hf]

/-- Actual packet powers remain in their original list before any trace
projection. The constructor takes no hidden factor or component order. -/
def publicUnitRows {n : ℕ} (m : ℕ) (g : (ZMod n)ˣ) : List (ZMod n)ˣ :=
  (SemiprimeEuclidRowFamily.publicPackets n m).map
    fun w => g^SemiprimeEuclidRowFamily.packetExponent m w

theorem publicUnitRows_mem_of_exponent {n m : ℕ} (g : (ZMod n)ˣ) {e : ℤ}
    (he : e∈SemiprimeEuclidRowFamily.publicExponents n m) : g^e∈publicUnitRows m g := by
  obtain ⟨w,hw,hwe⟩ := List.mem_map.mp he
  exact List.mem_map.mpr ⟨w,hw,by rw [hwe]⟩

/-- Complete guarded extraction on the public retained quadratic family. -/
noncomputable def publicGuardedTraceRows {n : ℕ} (m : ℕ) (g : (ZMod n)ˣ) : Option ℕ :=
  guardedTraceRows (publicUnitRows m g)

theorem publicGuardedTraceRows_sound {n m d : ℕ} {g : (ZMod n)ˣ}
    (hd : publicGuardedTraceRows m g=some d) : SemiprimeGroupSelection.ProperDivisor n d :=
  guardedTraceRows_sound _ hd

theorem publicGuardedTraceRows_gcd_bound {n m : ℕ} (g : (ZMod n)ˣ) :
    guardedTraceGcdCount (publicUnitRows m g)≤
      5*(SemiprimeEuclidRowFamily.publicPackets n m).length := by
  simpa [publicUnitRows] using guardedTraceGcdCount_le (publicUnitRows m g)

/-- A proper pair in either original public channel is enough for the
complete guarded detector. The proving pair is not an algorithm input. -/
theorem publicGuardedTraceRows_succeeds_of_pair {n m : ℕ} [NeZero n]
    (g : (ZMod n)ˣ) {e f : ℤ}
    (he : e∈SemiprimeEuclidRowFamily.publicExponents n m)
    (hf : f∈SemiprimeEuclidRowFamily.publicExponents n m)
    (hp : SemiprimeGroupSelection.ProperDivisor n
        (n.gcd (((g^e : (ZMod n)ˣ) : ZMod n)-((g^f : (ZMod n)ˣ) : ZMod n)).val) ∨
      SemiprimeGroupSelection.ProperDivisor n
        (n.gcd (((g^e : (ZMod n)ˣ) : ZMod n)*((g^f : (ZMod n)ˣ) : ZMod n)-1).val)) :
    ∃ d, publicGuardedTraceRows m g=some d :=
  guardedTraceRows_succeeds_of_pair _
    (publicUnitRows_mem_of_exponent g he) (publicUnitRows_mem_of_exponent g hf) hp

/-- The complete public guarded procedure recovers on the larger
ordinary-row stress input. It retains both raw endpoint orientations and
uses neither the proving pair nor component factors as source inputs. -/
theorem control_public_guarded_recovers :
    ∃ d, publicGuardedTraceRows 3691 SemiprimeReciprocalRows.controlBase=some d ∧
      SemiprimeGroupSelection.ProperDivisor 2518766418595894637609 d := by
  have hp : SemiprimeGroupSelection.ProperDivisor 2518766418595894637609
      ((2518766418595894637609 : ℕ).gcd
        (((SemiprimeReciprocalRows.controlBase^(3596798445668641429783915 : ℤ) :
          (ZMod 2518766418595894637609)ˣ) : ZMod 2518766418595894637609)*
          ((SemiprimeReciprocalRows.controlBase^(3037632300775047433790237 : ℤ) :
          (ZMod 2518766418595894637609)ˣ) : ZMod 2518766418595894637609)-1).val) := by
    rw [SemiprimeReciprocalRows.control_values.1,SemiprimeReciprocalRows.control_values.2]
    exact SemiprimeReciprocalRows.control_product_pair
  obtain ⟨d,hd⟩ := publicGuardedTraceRows_succeeds_of_pair SemiprimeReciprocalRows.controlBase
    SemiprimeReciprocalRows.control_exponents.1 SemiprimeReciprocalRows.control_exponents.2 (Or.inr hp)
  exact ⟨d,hd,publicGuardedTraceRows_sound hd⟩

end RiemannGaussian.SemiprimeGuardedTrace
