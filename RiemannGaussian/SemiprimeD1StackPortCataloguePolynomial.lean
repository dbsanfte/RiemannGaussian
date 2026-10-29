/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueExecution
import RiemannGaussian.SemiprimeD1StackPortCatalogueLoopBounds
/-! # Uniform fixed-polynomial control bounds from actual original descriptors -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCataloguePolynomial
open SemiprimeD1StackPortCatalogueTransduction SemiprimeD1StackPortCatalogueLoop
open SemiprimeD1StackPortCatalogueLoopBounds
open SemiprimeD1EdgeCatalogueEncoding (Record vertex tape)
open SemiprimeD1StackEdgeCatalogueParse (wordMass)
open SemiprimeMacroGraph
/-- Actual parsed index together with the four retained source counters. -/
def dimension {r t digits:ℕ} (v:SubdividedVertex r t digits) : ℕ :=
  SemiprimeD1StackVertexArityOriginal.indexValue v+(r*t+1)+r+t+digits+1
/-- A finite descriptor cap, only used internally before actual original-input substitution. -/
def Bounded {r t digits:ℕ} (X:ℕ) (vs:List (SubdividedVertex r t digits)) : Prop :=
  ∀v∈vs,wordMass (vertex v)≤X ∧ dimension v≤X
/-- Actual arity is a consequence of the original parsed dimensions. -/
theorem arity_le {r t digits:ℕ} (v:SubdividedVertex r t digits) (X:ℕ) (hd:dimension v≤X) :
    subdividedArity v≤10*X^2 := by
  exact (original_arity_le v).trans (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left hd 2))
/-- Pure scalar bound for the actual retained per-record clock expression. -/
theorem recordTime_le {r t digits:ℕ} (v:SubdividedVertex r t digits) (X n f:ℕ)
    (hX:1≤X) (hm:wordMass (vertex v)≤X) (hd:dimension v≤X)
    (hn:n≤10*X^3) (hf:f≤X) :
    SemiprimeD1StackPortCatalogueScan.recordTime v n f≤10000*X^5 := by
  have ha:=arity_le v X hd
  have hl:=loopTime_le (vertex v) (subdividedArity v) n f 0
  have h2:X≤X^2:=Nat.le_pow (by omega)
  have h3:X^2≤X^3:=Nat.pow_le_pow_right hX (by omega)
  have h5:X^3≤X^5:=Nat.pow_le_pow_right hX (by omega)
  have hq:10*(n+f+0+2*subdividedArity v+wordMass (vertex v))+83≤403*X^3:=by
    nlinarith
  have hmul:subdividedArity v*(10*(n+f+0+2*subdividedArity v+wordMass (vertex v))+83)≤
      (10*X^2)*(403*X^3):=Nat.mul_le_mul ha hq
  have hr:SemiprimeD1StackVertexArityRecipes.recipeBudget
      (SemiprimeD1StackVertexArityOriginal.indexValue v) (r*t+1) r t digits≤100*X^2+100:=by
    unfold SemiprimeD1StackVertexArityRecipes.recipeBudget SemiprimeD1StackVertexArityRecipes.dimensionSum
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hd 2)) 100
  unfold SemiprimeD1StackPortCatalogueScan.recordTime
  nlinarith
/-- Every original parsed word mass is bounded by the actual acquired descriptor tape. -/
theorem mass_mem {r t digits:ℕ} (vs:List (SubdividedVertex r t digits))
    (v:SubdividedVertex r t digits) (hv:v∈vs) :
    wordMass (vertex v)≤(tape (vs.map vertex) []).length := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
    simp only [List.mem_cons] at hv
    change wordMass (vertex v)≤(SemiprimeD1EdgeCatalogueEncoding.record (vertex w) (tape (vs.map vertex) [])).length
    rw [SemiprimeD1StackEdgeCatalogueScan.record_length]
    rcases hv with he|hv
    · subst w;omega
    · have h:=ih hv;omega
/-- Every original factor occupies at least its five delimiters on the actual source tape. -/
theorem vertices_le_tape {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) :
    vs.length≤(tape (vs.map vertex) []).length := by
  induction vs with
  | nil => simp [tape]
  | cons v vs ih =>
    change vs.length+1≤(SemiprimeD1EdgeCatalogueEncoding.record (vertex v) (tape (vs.map vertex) [])).length
    rw [SemiprimeD1StackEdgeCatalogueScan.record_length]
    omega
/-- Actual parsed index is one of the five physically stored words. -/
theorem index_le_mass {r t digits:ℕ} (v:SubdividedVertex r t digits) :
    SemiprimeD1StackVertexArityOriginal.indexValue v≤wordMass (vertex v) := by
  unfold SemiprimeD1StackVertexArityOriginal.indexValue wordMass
  omega
/-- One concrete original dimension/tape size controls every actual parsed descriptor. -/
def size {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) : ℕ :=
  (tape (vs.map vertex) []).length+(r*t+1)+r+t+digits+1
/-- The original acquired source proves the descriptor invariant, rather than asking for it. -/
theorem original_bounded {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) : Bounded (size vs) vs := by
  intro v hv
  have hm:=mass_mem vs v hv
  have hi:=index_le_mass v
  constructor
  · unfold size;omega
  · unfold dimension size;omega
/-- All actual occurrence counts have the fixed-polynomial bound derived from the parsed descriptors. -/
theorem count_le {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) (X:ℕ)
    (hb:Bounded X vs) : count vs≤vs.length*(10*X^2) := by
  induction vs with
  | nil => simp [count]
  | cons v vs ih =>
    have ha:=arity_le v X (hb v (by simp)).2
    have hr:=ih (by intro w hw;exact hb w (by simp [hw]))
    simp only [count,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith
/-- Whole actual scan time, uniformly for all reached factor/occurrence counters. -/
theorem scanTime_le {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) (X f n:ℕ)
    (hX:1≤X) (hb:Bounded X vs) (hf:f+vs.length≤X) (hn:n+count vs≤10*X^3) :
    scanTime vs f n≤vs.length*(10000*X^5) := by
  induction vs generalizing f n with
  | nil => simp [scanTime]
  | cons v vs ih =>
    have hv:=hb v (by simp)
    have h0:=recordTime_le v X n f hX hv.1 hv.2 (by omega) (by simp only [List.length_cons] at hf;omega)
    have hbn:Bounded X vs:=by intro w hw;exact hb w (by simp [hw])
    have hfn:f+1+vs.length≤X:=by simp only [List.length_cons] at hf;omega
    have hnn:n+subdividedArity v+count vs≤10*X^3:=by
      simpa only [count,List.map_cons,List.sum_cons,Nat.add_assoc] using hn
    have hr:=ih (f+1) (n+subdividedArity v) hbn hfn hnn
    simp only [scanTime,List.length_cons]
    nlinarith
/-- Literal output bytes are polynomial in actual occurrence mass, never a completion catalogue. -/
theorem output_length_le {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) (X f n:ℕ)
    (_hX:1≤X) (hb:Bounded X vs) (hf:f+vs.length≤X) (hn:n+count vs≤10*X^3) :
    (output vs f n []).length≤count vs*(100*X^3) := by
  induction vs generalizing f n with
  | nil => simp [output,count]
  | cons v vs ih =>
    have hv:=hb v (by simp)
    have hbn:Bounded X vs:=by intro w hw;exact hb w (by simp [hw])
    have hfn:f+1+vs.length≤X:=by simp only [List.length_cons] at hf;omega
    have hnn:n+subdividedArity v+count vs≤10*X^3:=by
      simpa only [count,List.map_cons,List.sum_cons,Nat.add_assoc] using hn
    have hr:=ih (f+1) (n+subdividedArity v) hbn hfn hnn
    have hl:=records_length_le (vertex v) (subdividedArity v) n f 0
      (output vs (f+1) (n+subdividedArity v) [])
    have hc:subdividedArity v≤count (v::vs):=by simp only [count,List.map_cons,List.sum_cons];omega
    have h3:X≤X^3:=Nat.le_pow (by omega)
    have hq:2*(n+f+0+2*subdividedArity v+wordMass (vertex v))+8≤100*X^3:=by
      simp only [List.length_cons] at hf
      nlinarith only [hn,hc,hv.1,hf,h3,_hX]
    have hm:=Nat.mul_le_mul_left (subdividedArity v) hq
    change (records (vertex v) (subdividedArity v) n f 0
      (output vs (f+1) (n+subdividedArity v) [])).length≤_
    simp only [count,List.map_cons,List.sum_cons] at *
    nlinarith only [hl,hr,hm]
/-- Literal actual-family scan and byte bounds, with no resource premise at the original endpoint. -/
theorem original_resources {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) :
    scanTime vs 0 0≤10000*(size vs)^6 ∧
      (output vs 0 0 []).length≤1000*(size vs)^6 := by
  let X:=size vs
  have hX:1≤X:=by unfold X size;omega
  have hv:vs.length≤X:=(vertices_le_tape vs).trans (by unfold X size;omega)
  have hb:=original_bounded vs
  have hc:count vs≤10*X^3:=by
    have h:=count_le vs X hb
    have hm:=Nat.mul_le_mul_right (10*X^2) hv
    nlinarith only [h,hm]
  have hs:=scanTime_le vs X 0 0 hX hb (by omega) (by omega)
  have ho:=output_length_le vs X 0 0 hX hb (by omega) (by omega)
  have hm:=Nat.mul_le_mul_right (10000*X^5) hv
  have hn:=Nat.mul_le_mul_right (100*X^3) hc
  constructor <;> nlinarith only [hs,ho,hm,hn]
end RiemannGaussian.SemiprimeD1StackPortCataloguePolynomial
