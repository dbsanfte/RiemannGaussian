/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorRadicalQBoxTailAudit
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms
/-!
# Exact divisor grouping for the moving radical-base cube norm

The finite gcd profile groups into primitive cofactor rows with the exact
square multiplicity `(N/d)^2`. The literal logarithmic coefficient keeps
both numerator and denominator and all endpoints. The general field-norm
and Jacobi--Trudi identifications are paper-level in the companion audit;
they are not declared as assumptions or new axioms here. This file does
not claim a prime-phase bound or an RH exclusion.
-/
open scoped BigOperators Topology
open Filter Asymptotics
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
namespace OpenAIReview.RadicalQBox

/-- The exact multiplicity of an antidiagonal in the finite square. -/
def tent (N a : ℕ) : ℕ := min a (2*N-a)
/-- The exact positive cofactor band with its coprimality mask. -/
def primitiveBand (d : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 (2*d)).filter (Nat.Coprime d)

/-- Dilation retains the integer tent multiplicity exactly. -/
theorem tent_mul (g d k : ℕ) : tent (g*d) (g*k)=g*tent d k := by
  unfold tent
  rw [show 2*(g*d)=g*(2*d) by ring,←Nat.mul_sub]
  by_cases h:k≤2*d-k
  · rw [min_eq_left h,min_eq_left (Nat.mul_le_mul_left g h)]
  · rw [min_eq_right (by omega :2*d-k≤k),
      min_eq_right (Nat.mul_le_mul_left g (by omega :2*d-k≤k))]

/-- Exact bijection from one gcd fiber to the primitive cofactor band. -/
theorem fiber_sum {N g:ℕ} (hN:0<N) (hg:g∣N) (F:ℕ→ℝ) :
    (∑ a∈(Finset.Ioo 0 (2*N)).filter (fun a=>N.gcd a=g),F a)=
      ∑ k∈primitiveBand (N/g),F (g*k) := by
  have hg0:0<g := Nat.pos_of_dvd_of_pos hg hN
  obtain ⟨d,rfl⟩:=hg
  rw [Nat.mul_div_cancel_left d hg0]
  symm
  refine Finset.sum_bij (fun k _=>g*k) ?_ ?_ ?_ (by intros;rfl)
  · intro k hk
    obtain ⟨hkI,hcop⟩:=Finset.mem_filter.mp hk
    obtain ⟨hk0,hk2⟩:=Finset.mem_Ioo.mp hkI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioo.mpr ⟨Nat.mul_pos hg0 hk0,?_⟩,?_⟩
    · rw [show 2*(g*d)=g*(2*d) by ring]
      exact (Nat.mul_lt_mul_left hg0).mpr hk2
    · rw [Nat.gcd_mul_left,hcop.gcd_eq_one,mul_one]
  · intro k hk l hl he
    exact Nat.eq_of_mul_eq_mul_left hg0 he
  · intro a ha
    obtain ⟨haI,hgcd⟩:=Finset.mem_filter.mp ha
    obtain ⟨ha0,ha2⟩:=Finset.mem_Ioo.mp haI
    have hga:g∣a := by rw [←hgcd];exact Nat.gcd_dvd_right _ _
    obtain ⟨k,rfl⟩:=hga
    have hk0:0<k := by
      by_contra h
      have hk:k=0 := by omega
      simp [hk] at ha0
    have hk2:k<2*d := by
      rw [show 2*(g*d)=g*(2*d) by ring] at ha2
      exact (Nat.mul_lt_mul_left hg0).mp ha2
    have hcop:Nat.Coprime d k := by
      rw [Nat.gcd_mul_left] at hgcd
      exact (show d.gcd k=1 by nlinarith)
    exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hk0,hk2⟩,hcop⟩,rfl⟩

/-- The complete finite gcd-weighted residual for arbitrary real row data. -/
def rawResidual (N:ℕ) (G:ℕ→ℕ→ℝ) : ℝ :=
  ∑ a∈Finset.Ioo 0 (2*N),
    (tent N a:ℝ)*(N.gcd a:ℝ)*G (N/(N.gcd a)) (a/(N.gcd a))
/-- One primitive cofactor row, with every tent and coprimality weight. -/
def primitiveResidual (d:ℕ) (G:ℕ→ℕ→ℝ) : ℝ :=
  ∑ k∈primitiveBand d,(tent d k:ℝ)*G d k

/-- Joining gcd fibers gives the exact divisor convolution, with no discarded boundary. -/
theorem residual_divisor_sum {N:ℕ} (hN:0<N) (G:ℕ→ℕ→ℝ) :
    rawResidual N G=
      ∑ d∈N.divisors,((N/d:ℕ):ℝ)^2*primitiveResidual d G := by
  unfold rawResidual
  rw [←Finset.sum_fiberwise_of_maps_to
    (t:=N.divisors) (g:=fun a=>N.gcd a)
    (fun a _=>Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hN.ne'⟩)]
  have hf : ∀g∈N.divisors,
      (∑ a∈(Finset.Ioo 0 (2*N)).filter (fun a=>N.gcd a=g),
        (tent N a:ℝ)*(N.gcd a:ℝ)*G (N/(N.gcd a)) (a/(N.gcd a)))=
      (g:ℝ)^2*primitiveResidual (N/g) G := by
    intro g hg
    have hgd:=Nat.dvd_of_mem_divisors hg
    have hg0:=Nat.pos_of_dvd_of_pos hgd hN
    rw [fiber_sum hN hgd]
    have hNeq:N=g*(N/g) := by rw [mul_comm,Nat.div_mul_cancel hgd]
    unfold primitiveResidual
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hcop:Nat.Coprime (N/g) k := (Finset.mem_filter.mp hk).2
    have hgg:N.gcd (g*k)=g := by
      conv_lhs => lhs;rw[hNeq]
      rw [Nat.gcd_mul_left,hcop.gcd_eq_one,mul_one]
    rw [hgg,Nat.mul_div_cancel_left k hg0]
    have ht:tent N (g*k)=g*tent (N/g) k := by
      conv_lhs => arg 1;rw[hNeq]
      exact tent_mul _ _ _
    rw [ht]
    push_cast
    ring
  rw [Finset.sum_congr rfl hf]
  rw [←Nat.sum_div_divisors N (fun d=>((N/d:ℕ):ℝ)^2*primitiveResidual d G)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hN.ne']

/-- The literal difference of the two finite logarithmic factors at base one-half. -/
def logAtom (d k:ℕ) : ℝ :=
  Real.log (1-(1/2:ℝ)^(d+k))-Real.log (1-(1/2:ℝ)^k)

/-- The explicit gcd logarithmic profile obtained from the full radical norm on paper. -/
def normResidual (N:ℕ) : ℝ :=
  ∑ a∈Finset.Ioo 0 (2*N),
    (tent N a:ℝ)*(N.gcd a:ℝ)*
      (Real.log (1-(1/2:ℝ)^((N+a)/(N.gcd a)))-
        Real.log (1-(1/2:ℝ)^(a/(N.gcd a))))

/-- Exact match of the explicit logarithmic profile to its integer gcd coordinates. -/
theorem normResidual_eq_raw (N:ℕ) : normResidual N=rawResidual N logAtom := by
  unfold normResidual rawResidual logAtom
  apply Finset.sum_congr rfl
  intro a _
  rw [Nat.add_div_of_dvd_right (Nat.gcd_dvd_left N a)]

/-- The logarithmic profile retains the square divisor multiplicity and every coprime row. -/
theorem normResidual_divisor_sum {N:ℕ} (hN:0<N) :
    normResidual N=
      ∑ d∈N.divisors,((N/d:ℕ):ℝ)^2*primitiveResidual d logAtom := by
  rw [normResidual_eq_raw,residual_divisor_sum hN]


/-- The primitive logarithmic row is exactly the independently bounded coprime tent. -/
theorem primitiveResidual_eq_tail (d:ℕ) :
    primitiveResidual d logAtom=OpenAIReview.RadicalQBoxTail.c d := by
  unfold primitiveResidual primitiveBand OpenAIReview.RadicalQBoxTail.c
  rw [←Finset.sum_filter]
  have hs : (Finset.Ioo 0 (2*d)).filter (Nat.Coprime d)=
      (Finset.range (2*d)).filter (fun k=>1≤k ∧ k.Coprime d) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_Ioo,Finset.mem_range,
      show d.Coprime k↔k.Coprime d from Nat.coprime_comm]
    omega
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  simp only [logAtom,OpenAIReview.RadicalQBoxTail.g,OpenAIReview.RadicalQBoxTail.tent,
    tent,Nat.add_comm k]
  ring

/-- The exact primitive row has only an exponentially small signed boundary deficit. -/
theorem primitive_deficit_bound (d:ℕ) (hd:1≤d) :
    0≤OpenAIReview.RadicalQBoxTail.B d-primitiveResidual d logAtom ∧
      OpenAIReview.RadicalQBoxTail.B d-primitiveResidual d logAtom≤
        16*((d:ℝ)+1)*(1/2:ℝ)^d := by
  rw [primitiveResidual_eq_tail]
  exact OpenAIReview.RadicalQBoxTail.deficit_bound d hd

end OpenAIReview.RadicalQBox

#lint+ in OpenAIReview.RadicalQBox



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
  unless declarations>0 do throwError "Empty radical q-box audit."
  logInfo m!"Radical q-box audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-radical-qbox-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-radical-qbox-source-gate/axioms.json"
    (Json.mkObj [("scope",toJson "exact gcd cofactor grouping and literal logarithmic profile; field norm, determinant and source continuation remain paper-level"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr details)]).pretty
