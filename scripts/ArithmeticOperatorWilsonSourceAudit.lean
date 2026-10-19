/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.NumberTheory.Wilson
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual Wilson factorial codes: source deletion and exact rescaling collapse

For every integer n>4, the literal factorial residue is zero on composites
and n-1 on primes. A centered periodic code with uniformly bounded slope
therefore deletes every positive-power source, even with arbitrary complex
log-bounded weights. Exact amplitude rescaling recovers the ordinary prime
sum. Growing slopes, joint-row identities and Wilson quotients are outside
this scoped obstruction. No prime distribution theorem is used.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
namespace OpenAIReview.WilsonSource
attribute [local instance] Classical.propDecidable

open scoped Nat
open Finset

theorem two_factors_dvd {a b n : ℕ} (ha : 0<a) (hb : 0<b)
    (han : a≤n) (hbn : b≤n) (hab : a≠b) : a*b∣(Nat.factorial n) := by
  have hs : ({a,b}:Finset ℕ) ⊆ Ico 1 (n+1) := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [mem_Ico] <;> omega
  have hh := Finset.prod_dvd_prod_of_subset ({a,b}:Finset ℕ)
    (Ico 1 (n+1)) (fun x:ℕ=>x) hs
  simpa [Finset.prod_Ico_id_eq_factorial, hab] using hh

theorem composite_factorial {n : ℕ} (hn : 4<n) (hp : ¬n.Prime) : n∣(Nat.factorial (n-1)) := by
  obtain ⟨a,b,ha,hb,hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2≤n)).mp hp
  have hap : 0<a := by nlinarith
  have hbp : 0<b := by nlinarith
  have han : a≤n-1 := by omega
  have hbn : b≤n-1 := by omega
  by_cases heq : a=b
  · subst b
    have ha3 : 3≤a := by nlinarith
    have h1 : a≤n-1 := by omega
    have hna : 2*a<n := by nlinarith
    have h2 : 2*a≤n-1 := by omega
    have hd := two_factors_dvd (by omega : 0<a) (by omega : 0<2*a) h1 h2 (by omega)
    exact dvd_trans (by rw [←hab]; exact ⟨2,by ring⟩) hd
  · simpa only [hab] using two_factors_dvd hap hbp han hbn heq

theorem prime_residue {n : ℕ} (hp : n.Prime) : (Nat.factorial (n-1)) % n = n-1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  have : Fact (k+1).Prime := ⟨hp⟩
  have h := congrArg ZMod.val (ZMod.wilsons_lemma (k+1))
  simpa only [ZMod.val_natCast, ZMod.val_neg_one, Nat.add_sub_cancel, Nat.succ_eq_add_one] using h


/-- The literal centered code of the factorial residue, including composite integers. -/
noncomputable def code (F : ℝ→ℂ) (n : ℕ) : ℂ :=
  F (((Nat.factorial (n-1)%n:ℕ):ℝ)/(n:ℝ))-F 0

theorem code_eq (F : ℝ→ℂ) {n : ℕ} (hn : 4<n) :
    code F n = if n.Prime then F (1-1/(n:ℝ))-F 0 else 0 := by
  unfold code
  split_ifs with hp
  · rw [prime_residue hp, Nat.cast_sub (by omega : 1≤n)]
    congr 2
    push_cast
    field_simp
  · rw [Nat.mod_eq_zero_of_dvd (composite_factorial hn hp)]
    simp

theorem code_bound (F : ℝ→ℂ) (K : ℝ) (hK : 0≤K)
    (hper : F 1=F 0) (hlip : ∀x:ℝ, ‖F x-F 1‖≤K*|x-1|)
    {n : ℕ} (hn : 4<n) : ‖code F n‖≤K/(n:ℝ) := by
  rw [code_eq F hn]
  split_ifs with hp
  · rw [←hper]
    calc
      _ ≤ K*|(1-1/(n:ℝ))-1| := hlip _
      _ = K/(n:ℝ) := by
        rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
        ring
  · simpa using div_nonneg hK (Nat.cast_nonneg n)

theorem packet_bound (X : ℕ) (hX : 5≤X) (F : ℝ→ℂ)
    (K W : ℝ) (hK : 0≤K) (hW : 0≤W)
    (hper : F 1=F 0) (hlip : ∀x:ℝ, ‖F x-F 1‖≤K*|x-1|)
    (w : ℕ→ℂ) (hw : ∀n∈Icc X (2*X),‖w n‖≤W) :
    ‖∑n∈Icc X (2*X),w n*code F n‖≤2*K*W := by
  have hXp : 0<(X:ℝ) := by positivity
  calc
    _ ≤ ∑n∈Icc X (2*X),‖w n*code F n‖ := norm_sum_le _ _
    _ ≤ ∑_n∈Icc X (2*X), W*(K/(X:ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hlo := (mem_Icc.mp hn).1
      have hn5 : 4<n := by omega
      rw [norm_mul]
      exact mul_le_mul (hw n hn)
        ((code_bound F K hK hper hlip hn5).trans
          (div_le_div_of_nonneg_left hK hXp (by exact_mod_cast hlo)))
        (norm_nonneg _) hW
    _ = ((X:ℝ)+1)*(W*(K/(X:ℝ))) := by
      simp only [sum_const, Nat.card_Icc, nsmul_eq_mul]
      have hc : 2*X+1-X=X+1 := by omega
      rw [hc]
      push_cast
      rfl
    _ ≤ 2*K*W := by
      have hX1 : 1≤(X:ℝ) := by exact_mod_cast (show 1≤X by omega)
      apply (le_of_sub_nonneg ?_)
      field_simp
      nlinarith [mul_nonneg hK hW, mul_nonneg (sub_nonneg.mpr hX1) (mul_nonneg hK hW)]


open Filter
open scoped Topology

theorem rescaled_code (F : ℝ→ℂ) (n : ℕ) (hn : 4<n)
    (hp : n.Prime → F (1-1/(n:ℝ))-F 0≠0) :
    code F n/(F (1-1/(n:ℝ))-F 0) = if n.Prime then 1 else 0 := by
  rw [code_eq F hn]
  split_ifs with h
  · exact div_self (hp h)
  · simp

theorem rescaled_packet (F : ℝ→ℂ) (S : Finset ℕ) (w : ℕ→ℂ)
    (hS : ∀n∈S,4<n)
    (hp : ∀n∈S,n.Prime → F (1-1/(n:ℝ))-F 0≠0) :
    (∑n∈S,w n*(code F n/(F (1-1/(n:ℝ))-F 0))) =
      ∑n∈S,if n.Prime then w n else 0 := by
  apply sum_congr rfl
  intro n hn
  rw [rescaled_code F n (hS n hn) (hp n hn)]
  split_ifs <;> simp

theorem log_dyadic_ratio_tendsto {β : ℝ} (hβ : 0<β) :
    Tendsto (fun X:ℕ => (Real.log 2+Real.log (X:ℝ))/(X:ℝ)^β)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun X:ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := (isLittleO_log_rpow_atTop hβ).tendsto_div_nhds_zero.comp hc
  have hi := (tendsto_rpow_atTop hβ).comp hc |>.inv_tendsto_atTop
  have hh := (hi.const_mul (Real.log 2)).add hl
  simpa [Function.comp_def, Pi.inv_apply, add_div, div_eq_mul_inv, add_mul] using hh

/-- Every fixed-slope centered Wilson code loses every positive-power source,
even for arbitrary complex weights bounded by log n and moving codes. -/
theorem no_positive_power_source (F : ℕ→ℝ→ℂ) (K : ℝ) (hK : 0≤K)
    (hper : ∀X,F X 1=F X 0)
    (hlip : ∀X x, ‖F X x-F X 1‖≤K*|x-1|)
    (w : ℕ→ℕ→ℂ)
    (hw : ∀X n,n∈Icc X (2*X) → ‖w X n‖≤Real.log (n:ℝ))
    {β : ℝ} (hβ : 0<β) :
    Tendsto (fun X:ℕ => ‖∑n∈Icc X (2*X),w X n*code (F X) n‖/(X:ℝ)^β)
      atTop (𝓝 0) := by
  have hu := (log_dyadic_ratio_tendsto hβ).const_mul (2*K)
  have ht : Tendsto (fun X:ℕ => 2*K*(Real.log 2+Real.log (X:ℝ))/(X:ℝ)^β)
      atTop (𝓝 0) := by simpa only [mul_zero,mul_div_assoc] using hu
  apply squeeze_zero' (Eventually.of_forall (fun X=>div_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))) ?_ ht
  filter_upwards [eventually_ge_atTop 5] with X hX
  have hXp : 0<(X:ℝ) := by positivity
  have hW : 0≤Real.log (2*(X:ℝ)) := Real.log_nonneg (by
    have : (5:ℝ)≤X := by exact_mod_cast hX
    linarith)
  have hw' : ∀n∈Icc X (2*X), ‖w X n‖≤Real.log (2*(X:ℝ)) := by
    intro n hn
    have hlo := (mem_Icc.mp hn).1
    have hnpos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    exact (hw X n hn).trans (Real.log_le_log hnpos
      (by exact_mod_cast (mem_Icc.mp hn).2))
  have hb := packet_bound X hX (F X) K (Real.log (2*(X:ℝ))) hK hW
    (hper X) (hlip X) (w X) hw'
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt hXp)] at hb
  exact div_le_div_of_nonneg_right hb (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end OpenAIReview.WilsonSource
#lint+ in OpenAIReview.WilsonSource

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    details := details.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  logInfo m!"Wilson source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-wilson-source-gate/axioms.json"
    (Json.mkObj [("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr details)]).pretty
