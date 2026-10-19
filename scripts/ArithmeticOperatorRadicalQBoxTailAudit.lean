/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal coprime logarithmic tent tail

The finite coprime tent has a nonnegative, exponentially small deficit
from the infinite coprime first logarithmic moment. The algebraic norm,
divisor regrouping, entire Dirichlet series and source conclusions are
separate paper-level statements, not hypotheses or conclusions here.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Topology
namespace OpenAIReview.RadicalQBoxTail

/-- Literal inverse-binary logarithmic layer; its zero layer is zero. -/
def g (k : ℕ) : ℝ := -Real.log (1-(1/2:ℝ)^k)
/-- Literal tent multiplicity, including both finite endpoints. -/
def tent (d k : ℕ) : ℕ := min k (2*d-k)
/-- Infinite coprime first-moment coefficient, with index zero excluded. -/
def bterm (d k : ℕ) : ℝ := if 1≤k ∧ k.Coprime d then (k:ℝ)*g k else 0
/-- The zero-extended finite coprime tent coefficient. -/
def cterm (d k : ℕ) : ℝ :=
  if k<2*d ∧ 1≤k ∧ k.Coprime d then (tent d k:ℝ)*(g k-g (k+d)) else 0
/-- The infinite coprime logarithmic moment. -/
def B (d : ℕ) : ℝ := ∑' k:ℕ,bterm d k
/-- The actual finite coprime tent sum on `1 <= k < 2*d`. -/
def c (d : ℕ) : ℝ := ∑ k∈Finset.range (2*d),
  if 1≤k ∧ k.Coprime d then (tent d k:ℝ)*(g k-g (k+d)) else 0

/-- The literal logarithmic layers are nonnegative, including index zero. -/
theorem g_nonneg (k : ℕ) : 0≤g k := by
  by_cases hk:k=0
  · simp [g,hk]
  · have hp:(1/2:ℝ)^k<1 := pow_lt_one₀ (by norm_num) (by norm_num) hk
    have hlog:=Real.log_nonpos (by linarith :0≤1-(1/2:ℝ)^k)
      (by linarith [pow_nonneg (by norm_num :0≤(1/2:ℝ)) k] :1-(1/2:ℝ)^k≤1)
    simpa [g] using neg_nonneg.mpr hlog

/-- The exact logarithm is bounded by twice its binary power. -/
theorem g_le (k : ℕ) : g k≤2*(1/2:ℝ)^k := by
  by_cases hk:k=0
  · norm_num [g,hk]
  · have hhalf:(1/2:ℝ)^k≤1/2 := by
      simpa using pow_le_pow_of_le_one (by norm_num :0≤(1/2:ℝ))
        (by norm_num : (1/2:ℝ)≤1) (show 1≤k by omega)
    have hx:0≤(1/2:ℝ)^k := by positivity
    have hp:0<1-(1/2:ℝ)^k := by linarith
    have hl:=Real.one_sub_inv_le_log_of_pos hp
    have hi: (1-(1/2:ℝ)^k)⁻¹-1≤2*(1/2:ℝ)^k := by
      rw [sub_le_iff_le_add,←one_div,div_le_iff₀ hp]
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hhalf)]
    unfold g
    linarith

/-- A positive-index logarithmic layer decreases under an index shift. -/
theorem g_shift_le (k d : ℕ) (hk:1≤k) : g (k+d)≤g k := by
  have hp:0<1-(1/2:ℝ)^k := sub_pos.mpr
    (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
  have he:(1/2:ℝ)^(k+d)≤(1/2:ℝ)^k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hh:=Real.log_le_log hp (by linarith :1-(1/2:ℝ)^k≤1-(1/2:ℝ)^(k+d))
  unfold g
  linarith

/-- The actual finite coefficient is nonnegative and below its infinite layer. -/
theorem cterm_bounds (d k : ℕ) : 0≤cterm d k ∧ cterm d k≤bterm d k := by
  by_cases h:k<2*d ∧ 1≤k ∧ k.Coprime d
  · have hg:=g_shift_le k d h.2.1
    have hw:(tent d k:ℝ)≤k := by exact_mod_cast (Nat.min_le_left k (2*d-k))
    have hw0:0≤(tent d k:ℝ) := by positivity
    simp only [cterm,ite_eq_left h,bterm,ite_eq_left h.2]
    refine ⟨mul_nonneg hw0 (sub_nonneg.mpr hg),?_⟩
    calc
      _ ≤ (tent d k:ℝ)*g k := mul_le_mul_of_nonneg_left (by linarith [g_nonneg (k+d)]) hw0
      _ ≤ _ := mul_le_mul_of_nonneg_right hw (g_nonneg k)
  · simp only [cterm,ite_eq_right h]
    constructor
    · rfl
    · unfold bterm
      split_ifs <;> positivity [g_nonneg k]

/-- Every infinite coprime layer is bounded by a summable first geometric moment. -/
theorem bterm_bounds (d k : ℕ) : 0≤bterm d k ∧ bterm d k≤2*((k:ℝ)*(1/2:ℝ)^k) := by
  unfold bterm
  split_ifs
  · constructor
    · exact mul_nonneg (Nat.cast_nonneg k) (g_nonneg k)
    · nlinarith [mul_le_mul_of_nonneg_left (g_le k) (Nat.cast_nonneg k)]
  · constructor <;> positivity

/-- Coprime restriction retains absolute summability of the actual log moment. -/
theorem bterm_summable (d : ℕ) : Summable (bterm d) := by
  apply Summable.of_nonneg_of_le (fun k=>(bterm_bounds d k).1)
    (fun k=>(bterm_bounds d k).2)
  exact ((hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num :‖(1/2:ℝ)‖<1)).summable).mul_left 2

/-- The zero-extended finite tent is summable without dropping its mask. -/
theorem cterm_summable (d : ℕ) : Summable (cterm d) :=
  Summable.of_nonneg_of_le (fun k=>(cterm_bounds d k).1)
    (fun k=>(cterm_bounds d k).2) (bterm_summable d)

/-- Exact bridge from the zero extension to the original finite endpoints. -/
theorem tsum_cterm (d : ℕ) : (∑' k:ℕ,cterm d k)=c d := by
  rw [tsum_eq_sum (s:=Finset.range (2*d))]
  · unfold c
    apply Finset.sum_congr rfl
    intro k hk
    simp [cterm,Finset.mem_range.mp hk]
  · intro k hk
    simp [cterm,show ¬k<2*d by simpa using hk]

/-- On the retained lower half, the deficit is only the shifted logarithm. -/
theorem lower_deficit_le (d k : ℕ) (hd:1≤d) (hk:k≤d) :
    bterm d k-cterm d k≤2*(1/2:ℝ)^d*((k:ℝ)*(1/2:ℝ)^k) := by
  by_cases h:1≤k ∧ k.Coprime d
  · have ht:k<2*d := by omega
    have hw:tent d k=k := min_eq_left (by omega)
    simp only [bterm,ite_eq_left h,cterm,ite_eq_left (show k<2*d ∧ 1≤k ∧ k.Coprime d from ⟨ht,h⟩),hw]
    have hh:=mul_le_mul_of_nonneg_left (g_le (k+d)) (Nat.cast_nonneg k)
    rw [pow_add] at hh
    nlinarith
  · simp [bterm,cterm,h]

/-- The elementary geometric first moment is exactly two. -/
theorem first_moment : (∑' k:ℕ,(k:ℝ)*(1/2:ℝ)^k)=2 := by
  rw [tsum_coe_mul_geometric_of_norm_lt_one (by norm_num :‖(1/2:ℝ)‖<1)]
  norm_num

/-- An exact shifted geometric majorant retains the first omitted index. -/
theorem shifted_majorant (d : ℕ) :
    (∑' j:ℕ,2*((j+d+1:ℕ):ℝ)*(1/2:ℝ)^(j+d+1))=
      (2*(d:ℝ)+4)*(1/2:ℝ)^d := by
  have hs:=hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num :‖(1/2:ℝ)‖<1)
  have hg:=hasSum_geometric_of_lt_one (by norm_num :0≤(1/2:ℝ)) (by norm_num :(1/2:ℝ)<1)
  have h:=((hs.add (hg.mul_left ((d:ℝ)+1))).mul_left (2*(1/2:ℝ)^(d+1))).tsum_eq
  convert h using 1
  · congr 1
    funext j
    simp only [Nat.cast_add,Nat.cast_one,pow_add]
    ring
  · norm_num at *
    rw [pow_succ]
    ring

/-- The literal finite/infinite signed error has a uniform binary tail. -/
theorem deficit_bound (d : ℕ) (hd:1≤d) :
    0≤B d-c d ∧ B d-c d≤16*((d:ℝ)+1)*(1/2:ℝ)^d := by
  let e : ℕ→ℝ := fun k=>bterm d k-cterm d k
  have hs:Summable e := (bterm_summable d).sub (cterm_summable d)
  have he:∑' k:ℕ,e k=B d-c d := by
    change (∑' k:ℕ,(bterm d k-cterm d k))=B d-c d
    rw [(bterm_summable d).tsum_sub (cterm_summable d),tsum_cterm]
    rfl
  have hn:∀k,0≤e k := fun k=>sub_nonneg.mpr (cterm_bounds d k).2
  have hprefix:(∑ k∈Finset.range (d+1),e k)≤4*(1/2:ℝ)^d := by
    calc
      _ ≤ ∑ k∈Finset.range (d+1),2*(1/2:ℝ)^d*((k:ℝ)*(1/2:ℝ)^k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact lower_deficit_le d k hd (by simpa using Finset.mem_range.mp hk)
      _ ≤ ∑' k:ℕ,2*(1/2:ℝ)^d*((k:ℝ)*(1/2:ℝ)^k) := by
        apply Summable.sum_le_tsum
        · intro k _
          positivity
        · exact (hasSum_coe_mul_geometric_of_norm_lt_one
            (by norm_num :‖(1/2:ℝ)‖<1)).summable.mul_left _
      _ = _ := by rw [tsum_mul_left,first_moment];ring
  have htail:(∑' j:ℕ,e (j+(d+1)))≤(2*(d:ℝ)+4)*(1/2:ℝ)^d := by
    have hmajor:Summable (fun j:ℕ=>2*((j+d+1:ℕ):ℝ)*(1/2:ℝ)^(j+d+1)) := by
      convert ((summable_nat_add_iff (d+1)).mpr
        ((hasSum_coe_mul_geometric_of_norm_lt_one
          (by norm_num :‖(1/2:ℝ)‖<1)).summable.mul_left 2)) using 1
      simp only [Nat.add_assoc,mul_assoc]
    calc
      _ ≤ ∑' j:ℕ,2*((j+d+1:ℕ):ℝ)*(1/2:ℝ)^(j+d+1) := by
        apply ((summable_nat_add_iff (d+1)).mpr hs).tsum_le_tsum _ hmajor
        intro j
        have hb: e (j+(d+1))≤bterm d (j+(d+1)) := by
          dsimp [e]
          linarith [(cterm_bounds d (j+(d+1))).1]
        exact hb.trans (by simpa [Nat.add_assoc,mul_assoc] using (bterm_bounds d (j+(d+1))).2)
      _ = _ := shifted_majorant d
  refine ⟨by rw [←he];exact tsum_nonneg hn,?_⟩
  have hsplit:=hs.sum_add_tsum_nat_add (d+1)
  rw [he] at hsplit
  have hpow:0≤(1/2:ℝ)^d := by positivity
  have hd0:0≤(d:ℝ) := Nat.cast_nonneg d
  nlinarith [mul_nonneg hd0 hpow]

/-- Every polynomial absolute moment of the actual coprime tent residual is finite. -/
theorem summable_polynomial_deficit (k : ℕ) :
    Summable (fun d:ℕ=>‖(d:ℝ)^k*(B d-c d)‖) := by
  have hp (j:ℕ) : Summable (fun d:ℕ=>(d:ℝ)^j*(1/2:ℝ)^d) :=
    summable_pow_mul_geometric_of_norm_lt_one j (by norm_num :‖(1/2:ℝ)‖<1)
  have hs:=((hp (k+1)).add (hp k)).mul_left 16
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 1] with d hd
  have hb:=deficit_bound d hd
  have hn:0≤(d:ℝ)^k*(B d-c d) := mul_nonneg (by positivity) hb.1
  rw [Real.norm_eq_abs,abs_of_nonneg,Real.norm_eq_abs,abs_of_nonneg hn]
  · have hmul:=mul_le_mul_of_nonneg_left hb.2 (show 0≤(d:ℝ)^k by positivity)
    convert hmul using 1
    ring
  · exact abs_nonneg _

end OpenAIReview.RadicalQBoxTail

#lint+ in OpenAIReview.RadicalQBoxTail

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
  unless declarations>0 do throwError "Empty radical q-box tail audit."
  logInfo m!"Radical q-box tail audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-radical-qbox-tail-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-radical-qbox-tail-gate/axioms.json"
    (Json.mkObj [("scope",toJson "literal finite/infinite coprime logarithmic tent tail; algebraic norm and Dirichlet source bridge remain paper-level"),
      ("namespaceLinters",toJson (15:Nat)),("onlyStandardAxioms",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr details)]).pretty
