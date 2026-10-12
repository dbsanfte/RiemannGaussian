/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorOrderedGapAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Native three-fraction recurrence and whole-word collapse gate

The successor is derived from actual adjacency, not postulated as a Farey
walk. A whole finite denominator word is determined by its first primitive
pair and the literal cutoff. Joining any mask on that word therefore remains
one actual Mobius test; no extra free-array bound follows from this recurrence.
Selected signed word kernels and independently proved estimates remain open.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorFareyWalkAudit
open Complex Filter ArithmeticOperatorOrderedGapGeometry
open ArithmeticOperatorOrderedGapAudit

/-- Literal denominator successor; the remainder formula keeps all cutoff endpoints. -/
def nextDenom (N q r : ℕ) : ℕ := N - (N+q)%r

/-- The exact integer quotient in the classical Farey recurrence. -/
def index (N q r : ℕ) : ℕ := (N+q)/r

theorem nextDenom_eq_quotient {N q r : ℕ} (ht : triangle N q r) :
    nextDenom N q r = index N q r * r - q := by
  obtain ⟨hq,hqN,hr,hrN,_⟩ := ht
  have hm := Nat.mod_lt (N+q) hr
  have he := Nat.mod_add_div (N+q) r
  rw [Nat.mul_comm r] at he
  unfold nextDenom index
  omega

/-- Addition, quotient and successor meet in one exact integer constraint. -/
theorem recurrence {N q r : ℕ} (ht : triangle N q r) :
    q + nextDenom N q r = index N q r * r := by
  obtain ⟨_,_,hr,hrN,_⟩ := ht
  have hm := Nat.mod_lt (N+q) hr
  have he := Nat.mod_add_div (N+q) r
  rw [Nat.mul_comm r] at he
  unfold nextDenom index
  omega

theorem nextDenom_pos {N q r : ℕ} (ht : triangle N q r) :
    0 < nextDenom N q r := by
  have hm := Nat.mod_lt (N+q) ht.2.2.1
  have hrN := ht.2.2.2.1
  unfold nextDenom
  omega

theorem next_triangle {N q r : ℕ} (ht : triangle N q r) :
    triangle N r (nextDenom N q r) := by
  have hm := Nat.mod_lt (N+q) ht.2.2.1
  have hn := nextDenom_pos ht
  have hrN := ht.2.2.2.1
  refine ⟨ht.2.2.1,hrN,hn,Nat.sub_le _ _,?_⟩
  unfold nextDenom
  omega

/-- Every common divisor, including proper prime powers, is unchanged by the recurrence. -/
theorem next_coprime {N q r : ℕ} (ht : triangle N q r) (hc : q.Coprime r) :
    r.Coprime (nextDenom N q r) := by
  let d := Nat.gcd r (nextDenom N q r)
  have hdr : d∣r := Nat.gcd_dvd_left _ _
  have hdt : d∣nextDenom N q r := Nat.gcd_dvd_right _ _
  have hs : d∣q+nextDenom N q r := by
    rw [recurrence ht]
    exact dvd_mul_of_dvd_right hdr _
  have hdq : d∣q := (Nat.dvd_add_iff_left hdt).mpr hs
  have hdg : d∣Nat.gcd q r := Nat.dvd_gcd hdq hdr
  rw [hc.gcd_eq_one] at hdg
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hdg)

/-- Reversing the ordered pair gives the exact inverse; no limiting gap law is used. -/
theorem previousDenom {N q r : ℕ} (ht : triangle N q r) :
    nextDenom N (nextDenom N q r) r = q := by
  have he := recurrence ht
  have hr := ht.2.2.1
  have hqN := ht.2.1
  have hqr := ht.2.2.2.2
  have hshape : N + nextDenom N q r = (N-q) + index N q r*r := by omega
  have hm : N-q<r := by omega
  change N - (N + nextDenom N q r) % r = q
  rw [hshape,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hm]
  omega

/-- Two genuine consecutive gaps, with the shared numerator and all endpoints literal. -/
def actualTriple (N q r t : ℕ) : Prop :=
  ∃ a c e : ℕ, actualGap N a q c r ∧ actualGap N c r e t

/-- The actual order exclusions force the recurrence; it is not a definition of adjacency. -/
theorem actual_triple_recurrence {N q r t : ℕ} (hg : actualTriple N q r t) :
    triangle N q r ∧ q.Coprime r ∧ r ≠ 1 ∧ t=nextDenom N q r := by
  obtain ⟨a,c,e,hleft,hright⟩ := hg
  obtain ⟨ht,hd⟩ := actual_gap_triangle hleft
  obtain ⟨ht',hd'⟩ := actual_gap_triangle hright
  have hc := (coprime_of_det hd).2.1
  have hsum : c*(q+t)=(a+e)*r := by nlinarith
  have hdiv : r∣q+t := hc.symm.dvd_of_dvd_mul_left (by
    rw [hsum]
    exact dvd_mul_left r (a+e))
  let k := (q+t)/r
  have he : k*r=q+t := Nat.div_mul_cancel hdiv
  have htN := ht'.2.2.2.1
  have hk : (N+q)/r=k := Nat.div_eq_of_lt_le (by omega) (by
    have hh := ht'.2.2.2.2
    nlinarith)
  have hs : t=nextDenom N q r := by
    rw [nextDenom_eq_quotient ht]
    unfold index
    rw [hk,he]
    omega
  have hr1 : r≠1 := by
    intro h
    have hcpos : 0<c := by nlinarith
    have hclt := hright.2.2.2.2.1
    omega
  exact ⟨ht,(coprime_of_det hd).2.2,hr1,hs⟩

/-- Conversely the recurrence supplies the genuine next gap unless the middle fraction is 1/1. -/
theorem actualTriple_iff (N q r t : ℕ) :
    actualTriple N q r t ↔ triangle N q r ∧ q.Coprime r ∧ r≠1 ∧
      t=nextDenom N q r := by
  constructor
  · exact actual_triple_recurrence
  · rintro ⟨ht,hc,hr1,rfl⟩
    obtain ⟨a,c,hleft⟩ := triangle_has_actual_gap ht hc
    obtain ⟨_,hd⟩ := actual_gap_triangle hleft
    have hcr : c≤r := hleft.2.2.2.2.2.1
    have hcpr := (coprime_of_det hd).2.1
    have hclt : c<r := lt_of_le_of_ne hcr (by
      intro he
      have hh := hcpr.gcd_eq_one
      rw [he,Nat.gcd_self] at hh
      exact hr1 hh)
    obtain ⟨v,e,hright⟩ := triangle_has_actual_gap (next_triangle ht) (next_coprime ht hc)
    obtain ⟨_,hd'⟩ := actual_gap_triangle hright
    have hvlt : v<r := hright.2.2.2.2.1
    let : NeZero r := ⟨ht.2.2.1.ne'⟩
    have hu : IsUnit (q : ZMod r) := by
      simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime q hc).isUnit
    have h0 := congrArg (fun n : ℕ => (n : ZMod r)) hd
    have h1 := congrArg (fun n : ℕ => (n : ZMod r)) hd'
    have h2 := congrArg (fun n : ℕ => (n : ZMod r)) (recurrence ht)
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,ZMod.natCast_self,mul_zero] at h0 h1 h2
    have heq : (c : ZMod r)*(q : ZMod r)=(v : ZMod r)*(q : ZMod r) := by
      linear_combination h0 - h1 - (v : ZMod r)*h2
    have hcv := congrArg ZMod.val (hu.mul_right_cancel heq)
    rw [ZMod.val_natCast_of_lt hclt,ZMod.val_natCast_of_lt hvlt] at hcv
    subst v
    exact ⟨a,c,e,hleft,hright⟩

/-- Literal three-fraction sum, excluding no adjacency or endpoint by convention. -/
def tripleSum (N : ℕ) (W : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ q∈Finset.Icc 1 N,∑ r∈Finset.Icc 1 N,∑ t∈Finset.Icc 1 N,
    if actualTriple N q r t then W q r t else 0

/-- The actual third fraction is one determined mask, with the terminal 1/1 deletion explicit. -/
theorem tripleSum_eq_pair_mask (N : ℕ) (W : ℕ → ℕ → ℕ → ℂ) :
    tripleSum N W = pairs N (fun q r => if r=1 then 0 else W q r (nextDenom N q r)) := by
  unfold tripleSum pairs
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  obtain ⟨hq0,hqN⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hr0,hrN⟩ := Finset.mem_Icc.mp hr
  by_cases hp : N<q+r ∧ q.Coprime r
  · rw [ite_eq_left hp]
    dsimp only
    by_cases hr1 : r=1
    · rw [ite_eq_left hr1]
      apply Finset.sum_eq_zero
      intro t _
      exact ite_eq_right (fun hg => (actual_triple_recurrence hg).2.2.1 hr1)
    · rw [ite_eq_right hr1]
      have ht : triangle N q r := ⟨hq0,hqN,hr0,hrN,hp.1⟩
      have hn : nextDenom N q r∈Finset.Icc 1 N :=
        Finset.mem_Icc.mpr ⟨nextDenom_pos ht,Nat.sub_le _ _⟩
      calc
        _ = ∑ t∈Finset.Icc 1 N,
            if t=nextDenom N q r then W q r t else 0 := by
          apply Finset.sum_congr rfl
          intro t _
          by_cases he : t=nextDenom N q r
          · subst t
            rw [ite_eq_left ((actualTriple_iff N q r _).mpr ⟨ht,hp.2,hr1,rfl⟩),
              ite_eq_left rfl]
          · rw [ite_eq_right (fun hg => he (actual_triple_recurrence hg).2.2.2),
              ite_eq_right he]
        _ = _ := by simp [hn]
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro t _
    exact ite_eq_right (fun hg => by
      obtain ⟨ht,hc,_,_⟩ := actual_triple_recurrence hg
      exact hp ⟨ht.2.2.2.2,hc⟩)

/-- Exactly one first pair has the terminal middle denominator 1. -/
theorem terminal_pair_count {N : ℕ} (hN : 0<N) :
    pairs N (fun _ r => if r=1 then 1 else 0) = 1 := by
  unfold pairs
  have h1 : 1∈Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl,hN⟩
  have hNN : N∈Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hN,le_rfl⟩
  calc
    _ = ∑ q∈Finset.Icc 1 N,∑ r∈Finset.Icc 1 N,
        if r=1 then (if q=N then (1 : ℂ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r _
      have hqN := (Finset.mem_Icc.mp hq).2
      by_cases hr : r=1
      · subst r
        by_cases he : q=N
        · subst q; simp
        · have hn : ¬N<q+1 := by omega
          simp [hn,he]
      · simp [hr]
    _ = 1 := by simp [h1,hNN]

/-- Higher adjacency counts add no new source: the only change is the literal terminal head. -/
theorem triple_count {N : ℕ} (hN : 0<N) :
    tripleSum N (fun _ _ _ => 1) = count N - 1 := by
  rw [tripleSum_eq_pair_mask]
  conv_rhs => rw [←terminal_pair_count hN]
  unfold count pairs
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases ht : N<q+r ∧ q.Coprime r <;> by_cases hr : r=1 <;> simp [ht,hr]

/-- Exact free inverse control for any native correlated triple mask. -/
theorem tripleSum_eq_actual_scalar (N : ℕ) (W : ℕ → ℕ → ℕ → ℂ) :
    tripleSum N W = ∑ d∈Finset.Icc 1 N,
      ArithmeticOperatorMoebiusCoprimeAudit.column 0 d *
        joinedKernel N (fun q r => if r=1 then 0 else W q r (nextDenom N q r)) d := by
  rw [tripleSum_eq_pair_mask,pairs_eq_actual_inverse,freePairs_eq_scalar]

/-- Native triple completion still needs an independent signed inverse-Mobius estimate. -/
theorem free_triple_bound_iff (N : ℕ) (W : ℕ → ℕ → ℕ → ℂ) (B : ℝ) :
    (∀ w : ℕ → ℂ,‖freePairs N w (fun q r => if r=1 then 0 else W q r (nextDenom N q r))‖≤B) ↔
      0≤B ∧ ∀ d∈Finset.Icc 1 N,
        joinedKernel N (fun q r => if r=1 then 0 else W q r (nextDenom N q r)) d=0 := by
  exact free_bound_iff N _ B

/-- Complete response of actual triple-count increments; the removed unit contributes exactly one. -/
def tripleResponse (z : ℂ) : ℂ := countResponse z - 1

/-- Actual phased native cutoff increments, including the lost unit head. -/
def tripleIncrement (y : ℝ) (n : ℕ) : ℂ :=
  (tripleSum n (fun _ _ _ => 1)-tripleSum (n-1) (fun _ _ _ => 1))*
    SuzukiCarryCorrelation.primePhase y n

/-- The entire higher-adjacency change is the single literal unit endpoint. -/
theorem tripleIncrement_eq (y : ℝ) (n : ℕ) :
    tripleIncrement y n=increment y n-LSeries.delta n := by
  cases n with
  | zero => simp [tripleIncrement,tripleSum,increment,count,pairs,LSeries.delta]
  | succ n =>
    cases n with
    | zero =>
      rw [tripleIncrement,triple_count (by decide : 0<1)]
      simp [tripleSum,increment,count,pairs,LSeries.delta,SuzukiCarryCorrelation.primePhase]
    | succ n =>
      have hsub : n+1+1-1=n+1 := by omega
      have hn : n+1+1≠1 := by omega
      simp only [tripleIncrement,increment,hsub,
        triple_count (by omega : 0<n+1+1),triple_count (by omega : 0<n+1),
        LSeries.delta,hn,ite_false]
      ring

/-- The defining native Euler series is only claimed on its genuine convergent half-plane. -/
theorem triple_increment_euler_response (y : ℝ) {s : ℂ} (hs : 2<s.re) :
    LSeries (tripleIncrement y) s=tripleResponse (s+I*y) := by
  have hf : LSeriesSummable (increment y) s := by
    apply LSeriesSummable_of_le_const_mul_rpow hs
    refine ⟨(1 : ℝ),fun n _ => ?_⟩
    simp only [increment_eq,norm_mul,SuzukiCarryCorrelation.norm_primePhase,
      Complex.norm_natCast,mul_one,show (2 : ℝ)-1=1 by norm_num,Real.rpow_one,one_mul]
    exact_mod_cast Nat.totient_le n
  have hg : LSeriesSummable LSeries.delta s := by
    change Summable (fun n => LSeries.term LSeries.delta s n)
    simp_rw [LSeries.term_delta]
    exact (hasSum_ite_eq (1 : ℕ) (1 : ℂ)).summable
  have he : tripleIncrement y=increment y-LSeries.delta :=
    funext (tripleIncrement_eq y)
  rw [he,LSeries_sub hf hg,increment_euler_response y hs]
  simp [tripleResponse,LSeries_delta]

/-- The original genuine zero singularity survives, at its full actual multiplicity. -/
theorem triple_actual_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun z : ℂ => (z-rho.1)^(analyticZetaZeroMultiplicity rho)*tripleResponse z)
      (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨v,hv,ht⟩ := actual_zero_source rho
  have hs : Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => z-rho.1) := by fun_prop
    simpa only [sub_self] using
      (hc.continuousAt (x := rho.1)).tendsto.mono_left
        nhdsWithin_le_nhds
  have hp := hs.pow (analyticZetaZeroMultiplicity rho)
  rw [zero_pow (analyticZetaZeroMultiplicity_positive rho).ne'] at hp
  refine ⟨v,hv,?_⟩
  simpa only [tripleResponse,mul_sub,mul_one,sub_zero] using ht.sub hp

/-- Density centering does not delete any actual off-line source. -/
def centeredTripleResponse (z : ℂ) : ℂ := (z-2)*tripleResponse z

/-- The actual two-dimensional density pole is removable after centering; no zero source is paid. -/
theorem triple_centered_density_analytic :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 2 ∧
      centeredTripleResponse=ᶠ[𝓝[≠] (2 : ℂ)] E := by
  obtain ⟨E,hE,he⟩ := centered_density_analytic
  refine ⟨fun z => E z-(z-2),hE.sub (analyticAt_id.sub analyticAt_const),?_⟩
  filter_upwards [he] with z hz
  rw [←hz]
  unfold centeredTripleResponse tripleResponse centeredCountResponse
  ring

theorem triple_centered_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun z : ℂ => (z-rho.1)^(analyticZetaZeroMultiplicity rho)*centeredTripleResponse z)
      (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨v,hv,ht⟩ := triple_actual_zero_source rho
  have hn : rho.1-2≠0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.sub_re] at hr
    linarith [NontrivialZetaZero.re_lt_one rho]
  refine ⟨(rho.1-2)*v,mul_ne_zero hn hv,?_⟩
  have hs : Tendsto (fun z : ℂ => z-2) (𝓝[≠] rho.1) (𝓝 (rho.1-2)) :=
    (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  convert hs.mul ht using 1
  funext z
  unfold centeredTripleResponse
  ring

/-- The finite native denominator evolution, including its terminal cyclic continuation. -/
def step (N : ℕ) (v : ℕ×ℕ) : ℕ×ℕ := (v.2,nextDenom N v.1 v.2)

/-- All finite word lengths retain the original cutoff and initial ordered pair. -/
def walk (N : ℕ) : ℕ → (ℕ×ℕ) → (ℕ×ℕ)
  | 0,v => v
  | k+1,v => step N (walk N k v)

theorem walk_primitive {N q r : ℕ} (ht : triangle N q r) (hc : q.Coprime r)
    (k : ℕ) :
    triangle N (walk N k (q,r)).1 (walk N k (q,r)).2 ∧
      (walk N k (q,r)).1.Coprime (walk N k (q,r)).2 := by
  induction k with
  | zero => exact ⟨ht,hc⟩
  | succ k ih => exact ⟨next_triangle ih.1,next_coprime ih.1 ih.2⟩

/-- Any correlated finite-word mask is kept as one mask on the original primitive pair. -/
def wordMask (N : ℕ) (J : ℕ) (W : (Fin (J+1) → ℕ×ℕ) → ℂ)
    (q r : ℕ) : ℂ := W (fun i => walk N i.val (q,r))

/-- Conversely every original pair mask is a word mask: the unrestricted native classes coincide. -/
theorem every_pair_mask_is_word_mask (N J : ℕ) (V : ℕ → ℕ → ℂ) :
    ∃ W : (Fin (J+1) → ℕ×ℕ) → ℂ,wordMask N J W=V := by
  refine ⟨fun v => V (v 0).1 (v 0).2,?_⟩
  rfl

/-- Native cyclic word sum; no phase, sign or non-wrapping endpoint mask is separated. -/
def wordSum (N J : ℕ) (W : (Fin (J+1) → ℕ×ℕ) → ℂ) : ℂ :=
  pairs N (wordMask N J W)

/-- The free inverse-array counterpart is only a collapse control, not a genuine Farey measure. -/
def freeWordSum (N J : ℕ) (W : (Fin (J+1) → ℕ×ℕ) → ℂ) (w : ℕ → ℂ) : ℂ :=
  freePairs N w (wordMask N J W)

/-- The entire finite word still has just one signed inverse-Mobius kernel. -/
theorem wordSum_eq_actual_scalar (N J : ℕ) (W : (Fin (J+1) → ℕ×ℕ) → ℂ) :
    wordSum N J W = ∑ d∈Finset.Icc 1 N,
      ArithmeticOperatorMoebiusCoprimeAudit.column 0 d * joinedKernel N (wordMask N J W) d := by
  unfold wordSum
  rw [pairs_eq_actual_inverse,freePairs_eq_scalar]

/-- Even arbitrary growing word length gives no all-weight estimate from recurrence alone. -/
theorem free_word_bound_iff (N J : ℕ) (W : (Fin (J+1) → ℕ×ℕ) → ℂ) (B : ℝ) :
    (∀ w : ℕ → ℂ,‖freeWordSum N J W w‖≤B) ↔
      0≤B ∧ ∀ d∈Finset.Icc 1 N,joinedKernel N (wordMask N J W) d=0 := by
  exact free_bound_iff N (wordMask N J W) B

end RiemannGaussian.ArithmeticOperatorFareyWalkAudit

#lint+ in RiemannGaussian.ArithmeticOperatorFareyWalkAudit
#lint+ in RiemannGaussian.ArithmeticOperatorFareyFourierAudit
#lint+ in RiemannGaussian.ArithmeticOperatorOrderedGapGeometry
#lint+ in RiemannGaussian.ArithmeticOperatorOrderedGapAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  let prefixes := #["RiemannGaussian.ArithmeticOperatorFareyWalkAudit",
    "RiemannGaussian.ArithmeticOperatorFareyFourierAudit",
    "RiemannGaussian.ArithmeticOperatorOrderedGapGeometry",
    "RiemannGaussian.ArithmeticOperatorOrderedGapAudit"]
  let mut namespaces : Array Json := #[]
  for nsRoot in prefixes do
    let mut nsDeclarations : Nat := 0
    let mut nsTheorems : Nat := 0
    for (n,ci) in env.constants.toList do
      unless (n.toString.splitOn nsRoot).length > 1 do continue
      nsDeclarations := nsDeclarations + 1
      if ci.isTheorem then nsTheorems := nsTheorems + 1
    namespaces := namespaces.push (Json.mkObj [("namespace",toJson nsRoot),
      ("declarations",toJson nsDeclarations),("theoremsIncludingGeneratedHelpers",toJson nsTheorems),
      ("namespaceLinters",toJson (15:Nat))])
  for (n,ci) in env.constants.toList do
    unless prefixes.any (fun nsRoot => (n.toString.splitOn nsRoot).length > 1) do continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty native-walk audit."
  logInfo m!"Native-walk audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-native-walk"
  IO.FS.writeFile ".lake/arithmetic-operator-native-walk/axioms.json"
    (Json.mkObj [("scope",toJson "actual recurrence and whole-word identity-only collapse"),
      ("onlyStandardAxioms",toJson true),("totalNamespaceLinters",toJson (60:Nat)),
      ("namespaces",Json.arr namespaces),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
