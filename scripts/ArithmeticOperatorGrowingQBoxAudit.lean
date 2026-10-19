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
# Growing boxed-product ordinary-log source audit

The exact finite boxed product has a positive Lambert expansion with factor
`(1-q^((k+1)*N))^3`. Its logarithm differs from a constant by at most a
geometric tail. Reciprocal-base height is retained exactly, and every
polynomial absolute moment of the centered remainder is summable.

MacMahon/Jacobi--Trudi identification with an actual growing-rank integer
Gaussian determinant is paper-level in the companion source audit. This
file proves the explicit finite product, not an unformalized determinant
bridge. It gives no prime-depth-phase estimate or RH exclusion.
-/
open scoped BigOperators Topology
open Filter Asymptotics
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
namespace OpenAIReview.GrowingQBox

/-- Positive Lambert-series layer. -/
def layer (q : ℝ) (k : ℕ) : ℝ :=
  q^(k+1)/(((k:ℝ)+1)*(1-q^(k+1))^2)
/-- Ordinary logarithmic sum of the literal finite cube product. -/
def boxLog (q : ℝ) (N : ℕ) : ℝ :=
  ∑ i∈Finset.range N, ∑ j∈Finset.range N,
    ((-Real.log (1-q^(i+j+1)))-(-Real.log (1-q^(N+i+j+1))))
/-- The finite limiting logarithmic constant for `0 <= q < 1`. -/
def limit (q : ℝ) : ℝ := ∑' k:ℕ,layer q k
/-- The literal finite MacMahon cube product, defined at any real base. -/
def boxProduct (q : ℝ) (N : ℕ) : ℝ :=
  ∏ i∈Finset.range N, ∏ j∈Finset.range N,
    (1-q^(N+i+j+1))/(1-q^(i+j+1))

/-- Elementary uniform bounds for a positive power of a base below one. -/
theorem pow_small {q:ℝ} (h0:0≤q) (h1:q<1) (k:ℕ) :
    0≤q^(k+1) ∧ q^(k+1)<1 ∧ q^(k+1)≤q := by
  refine ⟨pow_nonneg h0 _,pow_lt_one₀ h0 h1 (by omega),?_⟩
  simpa using pow_le_pow_of_le_one h0 h1.le (show 1≤k+1 by omega)

/-- Every Lambert layer is nonnegative. -/
theorem layer_nonneg {q:ℝ} (h0:0≤q) (k:ℕ) : 0≤layer q k := by
  unfold layer; positivity

/-- An elementary summable geometric bound for each layer. -/
theorem layer_bound {q:ℝ} (h0:0≤q) (h1:q<1) (k:ℕ) :
    layer q k≤((1-q)^2)⁻¹*q^(k+1) := by
  have hp:=pow_small h0 h1 k
  have hd:0<1-q := sub_pos.mpr h1
  have he:0<1-q^(k+1) := sub_pos.mpr hp.2.1
  have hden : (1-q)^2≤((k:ℝ)+1)*(1-q^(k+1))^2 := by
    have hs:(1-q)^2≤(1-q^(k+1))^2 := by nlinarith [sq_nonneg (q-q^(k+1))]
    have hk:(0:ℝ)≤k := Nat.cast_nonneg k
    nlinarith [sq_nonneg (1-q^(k+1))]
  unfold layer
  calc
    _ ≤ q^(k+1)/(1-q)^2 := div_le_div_of_nonneg_left hp.1 (sq_pos_of_pos hd) hden
    _ = _ := by ring

/-- The Lambert series is absolutely summable. -/
theorem layer_summable {q:ℝ} (h0:0≤q) (h1:q<1) : Summable (layer q) := by
  have hg := (summable_geometric_of_lt_one h0 h1).mul_left (((1-q)^2)⁻¹*q)
  apply Summable.of_nonneg_of_le (layer_nonneg h0) _ hg
  intro k
  simpa only [pow_succ, mul_assoc, mul_comm q, mul_left_comm q] using layer_bound h0 h1 k

/-- Exact finite double geometric summation retains all three cube faces. -/
theorem finite_kernel (x:ℝ) (hx:x≠1) (N k:ℕ) :
    (∑ i∈Finset.range N,∑ j∈Finset.range N,
      (x^(i+j+1)-x^(N+i+j+1))/((k:ℝ)+1)) =
    x/(((k:ℝ)+1)*(1-x)^2)*(1-x^N)^3 := by
  have hk:((k:ℝ)+1)≠0 := by positivity
  have he : x-1≠0 := sub_ne_zero.mpr hx
  have hsum : (∑ i∈Finset.range N,∑ j∈Finset.range N,
      (x^(i+j+1)-x^(N+i+j+1))) =
      x*(1-x^N)*(∑ i∈Finset.range N,x^i)^2 := by
    simp only [pow_add,pow_one,Finset.sum_sub_distrib,←Finset.sum_mul,
      ←Finset.mul_sum]
    ring
  simp_rw [←Finset.sum_div]
  rw [hsum,geom_sum_eq hx]
  field_simp
  ring

/-- Exact infinite expansion of the finite logarithmic product. -/
theorem boxLog_hasSum {q:ℝ} (h0:0≤q) (h1:q<1) (N:ℕ) :
    HasSum (fun k:ℕ=>layer q k*(1-q^((k+1)*N))^3) (boxLog q N) := by
  have hs : ∀ i∈Finset.range N, ∀ j∈Finset.range N,
      HasSum (fun k:ℕ=> (q^(i+j+1))^(k+1)/((k:ℝ)+1) -
        (q^(N+i+j+1))^(k+1)/((k:ℝ)+1))
        ((-Real.log (1-q^(i+j+1)))-(-Real.log (1-q^(N+i+j+1)))) := by
    intro i _ j _
    exact (Real.hasSum_pow_div_log_of_abs_lt_one (by
      rw [abs_of_nonneg (pow_nonneg h0 _)];exact (pow_small h0 h1 (i+j)).2.1)).sub
      (Real.hasSum_pow_div_log_of_abs_lt_one (by
      rw [abs_of_nonneg (pow_nonneg h0 _)];exact (pow_small h0 h1 (N+i+j)).2.1))
  have hh:=hasSum_sum (fun i hi=>hasSum_sum (hs i hi))
  unfold boxLog
  convert hh using 1
  funext k
  have hp : q^(k+1)≠1 := ne_of_lt (pow_small h0 h1 k).2.1
  have he : ∀ a:ℕ,(q^a)^(k+1)=(q^(k+1))^a := by
    intro a; simp only [←pow_mul, Nat.mul_comm a]
  simp only [he,←sub_div]
  simpa only [layer,pow_mul] using (finite_kernel (q^(k+1)) hp N k).symm

/-- The omitted three-face factor has linear upper bound. -/
theorem cube_bounds {x:ℝ} (h0:0≤x) (h1:x≤1) :
    0≤1-(1-x)^3 ∧ 1-(1-x)^3≤3*x := by
  have hsq:=sq_nonneg (1-x)
  have hc : x^3≤x^2 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h1)]
  constructor <;> nlinarith [mul_nonneg h0 hsq]

/-- Explicit geometric defect from the limiting constant, with its sign. -/
theorem boxLog_gap {q:ℝ} (h0:0≤q) (h1:q<1) (N:ℕ) :
    0≤limit q-boxLog q N ∧ limit q-boxLog q N≤3*limit q*q^N := by
  have hs:=layer_summable h0 h1
  have hd : HasSum (fun k:ℕ=>layer q k*(1-(1-q^((k+1)*N))^3))
      (limit q-boxLog q N) := by
    convert hs.hasSum.sub (boxLog_hasSum h0 h1 N) using 1
    · funext k;ring
    · rfl
  have hg:=hs.mul_right (3*q^N)
  have hnon : ∀k:ℕ,0≤layer q k*(1-(1-q^((k+1)*N))^3) := by
    intro k
    exact mul_nonneg (layer_nonneg h0 k) (cube_bounds (pow_nonneg h0 _)
      (pow_le_one₀ h0 h1.le)).1
  refine ⟨by rw [←hd.tsum_eq];exact tsum_nonneg hnon,?_⟩
  calc
    limit q-boxLog q N = ∑' k:ℕ,layer q k*(1-(1-q^((k+1)*N))^3) := hd.tsum_eq.symm
    _ ≤ ∑' k:ℕ,layer q k*(3*q^N) := hd.summable.tsum_le_tsum (fun k=>?_) hg
    _ = 3*limit q*q^N := by rw [tsum_mul_right];unfold limit;ring
  have hx:=cube_bounds (pow_nonneg h0 ((k+1)*N)) (pow_le_one₀ h0 h1.le)
  have hp:q^((k+1)*N)≤q^N := pow_le_pow_of_le_one h0 h1.le (by
    rw [Nat.add_mul, Nat.one_mul]; omega)
  exact mul_le_mul_of_nonneg_left (hx.2.trans (by nlinarith)) (layer_nonneg h0 k)

/-- The complete centered logarithm has geometric decay. -/
theorem boxLog_error_geometric {q:ℝ} (h0:0≤q) (h1:q<1) :
    (fun N:ℕ=>boxLog q N-limit q) =O[atTop] (fun N=>q^N) := by
  apply IsBigO.of_bound (3*limit q)
  filter_upwards [] with N
  have h:=boxLog_gap h0 h1 N
  rw [Real.norm_eq_abs,abs_of_nonpos (by linarith : boxLog q N-limit q≤0),
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg h0 _)]
  linarith

/-- The literal finite product is positive for a base below one. -/
theorem boxProduct_pos {q:ℝ} (h0:0≤q) (h1:q<1) (N:ℕ) :
    0<boxProduct q N := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact div_pos (sub_pos.mpr (pow_small h0 h1 (N+i+j)).2.1)
    (sub_pos.mpr (pow_small h0 h1 (i+j)).2.1)

/-- Exact bridge from the finite product to its logarithmic sum. -/
theorem log_boxProduct {q:ℝ} (h0:0≤q) (h1:q<1) (N:ℕ) :
    Real.log (boxProduct q N)=boxLog q N := by
  have hpos (i j:ℕ) : 0<(1-q^(N+i+j+1))/(1-q^(i+j+1)) :=
    div_pos (sub_pos.mpr (pow_small h0 h1 (N+i+j)).2.1)
      (sub_pos.mpr (pow_small h0 h1 (i+j)).2.1)
  unfold boxProduct boxLog
  rw [Real.log_prod (by intro i _;exact (Finset.prod_pos (fun j _=>hpos i j)).ne')]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_prod (by intro j _;exact (hpos i j).ne')]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.log_div (sub_pos.mpr (pow_small h0 h1 (N+i+j)).2.1).ne'
    (sub_pos.mpr (pow_small h0 h1 (i+j)).2.1).ne']
  ring

/-- Exact reciprocal-base identity for one finite-product entry. -/
theorem quotient_reciprocal {b:ℝ} (hb:1<b) (N a:ℕ) (ha:0<a) :
    (1-b^(N+a))/(1-b^a)=b^N*((1-(b⁻¹)^(N+a))/(1-(b⁻¹)^a)) := by
  have hb0 : b≠0 := ne_of_gt (lt_trans zero_lt_one hb)
  have hba : b^a≠1 := ne_of_gt (one_lt_pow₀ hb (by omega :a≠0))
  rw [inv_pow,inv_pow,pow_add]
  field_simp
  ring

/-- Exact cubic height of the whole finite product. -/
theorem boxProduct_reciprocal {b:ℝ} (hb:1<b) (N:ℕ) :
    boxProduct b N=b^(N^3)*boxProduct b⁻¹ N := by
  unfold boxProduct
  conv_lhs =>
    arg 2
    intro i
    arg 2
    intro j
    rw [show N+i+j+1=N+(i+j+1) by omega,
      quotient_reciprocal hb N (i+j+1) (by omega)]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range,
    ←pow_mul]
  have he:N*N*N=N^3 := by ring
  rw [he]
  simp only [Nat.add_assoc]

/-- The full cubic height is retained in the ordinary logarithm. -/
theorem log_boxProduct_large {b:ℝ} (hb:1<b) (N:ℕ) :
    Real.log (boxProduct b N)=(N:ℝ)^3*Real.log b+boxLog b⁻¹ N := by
  have hb0 : 0<b := lt_trans zero_lt_one hb
  have hq0:0≤b⁻¹ := (inv_pos.mpr hb0).le
  have hq1:b⁻¹<1 := (inv_lt_one₀ hb0).mpr hb
  rw [boxProduct_reciprocal hb,Real.log_mul (pow_ne_zero _ hb0.ne')
    (boxProduct_pos hq0 hq1 N).ne',Real.log_pow,log_boxProduct hq0 hq1]
  simp

/-- Every polynomially weighted absolute residual is summable. -/
theorem summable_polynomial_boxLog_error {q:ℝ} (h0:0≤q) (h1:q<1) (k:ℕ) :
    Summable (fun N:ℕ=>‖(N:ℝ)^k*(boxLog q N-limit q)‖) := by
  have h := (isBigO_refl (fun N:ℕ=>(N:ℝ)^k) atTop).mul
    (boxLog_error_geometric h0 h1)
  exact summable_of_isBigO_nat
    (summable_norm_pow_mul_geometric_of_norm_lt_one k (by
      simpa [Real.norm_eq_abs,abs_of_nonneg h0] using h1)) h.norm_norm

/-- Centering the actual large-base finite product leaves a geometric remainder. -/
theorem boxProduct_large_residual_geometric {b:ℝ} (hb:1<b) :
    (fun N:ℕ=>Real.log (boxProduct b N)-
      ((N:ℝ)^3*Real.log b+limit b⁻¹)) =O[atTop] (fun N=> (b⁻¹)^N) := by
  have hb0:0<b := lt_trans zero_lt_one hb
  have he : (fun N:ℕ=>Real.log (boxProduct b N)-
      ((N:ℝ)^3*Real.log b+limit b⁻¹)) = (fun N:ℕ=>boxLog b⁻¹ N-limit b⁻¹) := by
    funext N
    rw [log_boxProduct_large hb]
    ring
  rw [he]
  exact boxLog_error_geometric (inv_nonneg.mpr hb0.le) ((inv_lt_one₀ hb0).mpr hb)

end OpenAIReview.GrowingQBox

#lint+ in OpenAIReview.GrowingQBox


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
  unless declarations>0 do throwError "Empty growing q-box audit."
  logInfo m!"Growing q-box audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-growing-qbox-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-growing-qbox-source-gate/axioms.json"
    (Json.mkObj [("scope",toJson "exact finite boxed product; growing Jacobi--Trudi determinant and row Dirichlet continuation remain paper-level"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr details)]).pretty
