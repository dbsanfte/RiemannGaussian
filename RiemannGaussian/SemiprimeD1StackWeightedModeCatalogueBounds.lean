/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueExecution
import RiemannGaussian.SemiprimeReportPolynomialGrowth
/-! # Same physical catalogue/enumeration clock, polynomial per feasible visit
Generated log sizes are bounded from the actual successful source trace.
Physical unary metadata sizes are charged, while coefficients/N stay binary
in the upstream caller. No native cost report is transported.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueBounds
open SemiprimeD1StackWeightedModeCatalogue SemiprimeD1StackWeightedModeCatalogueView
open SemiprimeD1StackWeightedModeCatalogueOrders SemiprimeD1StackWeightedModeCatalogueFinish
open SemiprimeD1StackWeightedModeCatalogueExecution
open SemiprimeD1StackWeightedModeView (unary unary_length vector history)
open SemiprimeD1StackWeightedModeResources (inputSize vector_length)
open SemiprimeReportPolynomialGrowth
local notation "ctl" => (Sum.inl :Control→Label)
attribute [local irreducible] acquisitionBudget timeBound
/-- Every initial physical metadata word fits the real total input bytes. -/
theorem initial_length (p t width:Nat) (k:Stack):
    ((initial (unary p) (unary t) (unary width)).data k).length ≤p+t+width:=by
  rcases k with k|k
  · cases k <;> simp only [initial,input,unary_length,List.length_nil] <;> omega
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> simp only [initial,input,unary_length,List.length_nil] <;> omega
    · cases k <;> simp only [initial,input,List.length_nil] <;> omega
/-- Both actual generated logs fit the SAME successful acquisition trace. -/
theorem log_lengths (p t width:Nat):
    (history (orderWeights (p*t) 0 (width-1)) []).length ≤p+t+width+acquisitionBudget p t width ∧
    (history (orderLabels (p*t) 0 (width-1)) []).length ≤p+t+width+acquisitionBudget p t width:=by
  obtain ⟨time,ht,hr⟩:=acquisition_trace p t width
  obtain ⟨finish,hf,ha⟩:=hr [] (initial (unary p) (unary t) (unary width)) ⟨rfl,rfl,rfl⟩
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program time (p+t+width)
    _ _ (initial_length p t width) hf
  have hw:=hd (aux .weightHistory)
  have hl:=hd (aux .labelHistory)
  rw [ha.2.1] at hw hl
  change (history (orderWeights (p*t) 0 (width-1)) []).length ≤p+t+width+time at hw
  change (history (orderLabels (p*t) 0 (width-1)) []).length ≤p+t+width+time at hl
  constructor <;> omega
/-- No output-size oracle is needed to pay either actual catalogue reversal. -/
theorem timeBound_le (p t width:Nat):timeBound p t width ≤
    5*acquisitionBudget p t width+4*(p+t+width)+
      SemiprimeD1StackWeightedModeBounds.runBound (weights p t width) width+10:=by
  obtain ⟨hw,hl⟩:=log_lengths p t width
  unfold timeBound
  omega
/-- A literal polynomial upper envelope for the paid multiplier and physical catalogue loops. -/
def acquisitionEnvelope (p t width:Nat):Nat:=
  5*p+5*(p*(2*t+3)+1)+5*width+17+1000*(width+1)*(p*t+1)*(width+p*t+2)
theorem acquisitionBudget_le (p t width:Nat):acquisitionBudget p t width ≤acquisitionEnvelope p t width:=by
  unfold acquisitionBudget acquisitionEnvelope
  have h:width-1 ≤width:=Nat.sub_le _ _
  gcongr
theorem acquisitionEnvelope_mono {p t width n:Nat} (hp:p ≤ n) (ht:t ≤ n) (hw:width ≤ n):
    acquisitionEnvelope p t width ≤acquisitionEnvelope n n n:=by
  unfold acquisitionEnvelope
  gcongr
/-- The actual generated weight-vector byte length is polynomial in real input metadata bytes. -/
theorem generated_bytes (p t width:Nat):
    inputSize (weights p t width) width ≤10*(p+t+width+1)^4:=by
  let n:=p+t+width
  let P:=width-1
  let ws:=weights p t width
  have hp:p ≤n:=by dsimp [n];omega
  have ht:t ≤n:=by dsimp [n];omega
  have hP:P ≤n:=by dsimp [P,n];omega
  have hw:width ≤n:=by dsimp [n];omega
  have hlen:ws.length=P*(p*t):=by
    dsimp [ws,weights,P]
    simp only [SemiprimeD1ModeCatalog.weights,List.length_map,SemiprimeD1ModeCatalog.catalog_length]
  have hsum:ws.sum ≤ws.length*P:=by
    have sum_bound (xs:List Nat) (h:∀w∈xs,w ≤P):xs.sum ≤xs.length*P:=by
      induction xs with
      | nil=>simp only [List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
      | cons x xs ih=>
        have hx:=h x (by simp)
        have hs:=ih (fun w hw=>h w (by simp [hw]))
        simp only [List.sum_cons,List.length_cons]
        nlinarith only [hx,hs]
    exact sum_bound ws (SemiprimeD1ModeCatalog.weights_le _ _)
  have hslots:p*t ≤n^2:=by simpa only [pow_two] using Nat.mul_le_mul hp ht
  have hdegree:ws.length ≤n^3:=by
    rw [hlen]
    have h:=Nat.mul_le_mul hP hslots
    convert h using 1;ring
  have hweight:ws.sum ≤n^4:=by
    have h:=hsum.trans (Nat.mul_le_mul hdegree hP)
    convert h using 1;ring
  have hN:1 ≤n+1:=by omega
  have h3:n^3 ≤(n+1)^4:=(Nat.pow_le_pow_left (by omega:n ≤n+1) 3).trans
    (Nat.pow_le_pow_right hN (by omega:3 ≤4))
  have h4:n^4 ≤(n+1)^4:=Nat.pow_le_pow_left (by omega) 4
  have h1:n+1 ≤(n+1)^4:=by simpa only [pow_one] using Nat.pow_le_pow_right hN (by omega:1 ≤4)
  change (vector ws).length+width+2 ≤10*(n+1)^4
  rw [vector_length]
  omega
/-- Fixed width polynomial for the same three-input physical source. -/
def polynomial (n:Nat):Nat:=
  5*acquisitionEnvelope n n n+4*n+10+10000*(10*(n+1)^4)^3
/-- Same actual source allowance is polynomial per actual feasible visit after real catalogue acquisition. -/
theorem timeBound_polynomial (p t width:Nat):
    timeBound p t width ≤polynomial (p+t+width)*
      SemiprimeD1WeightedTuples.visits (weights p t width) (width-1):=by
  let n:=p+t+width
  let v:=SemiprimeD1WeightedTuples.visits (weights p t width) (width-1)
  have hv:1 ≤v:=Nat.succ_le_of_lt (SemiprimeD1WeightedTuples.visits_positive _ _)
  have hf:5*acquisitionBudget p t width+4*n+10 ≤5*acquisitionEnvelope n n n+4*n+10:=by
    have h:acquisitionBudget p t width ≤acquisitionEnvelope n n n:=
      (acquisitionBudget_le p t width).trans (acquisitionEnvelope_mono (by dsimp [n];omega)
        (by dsimp [n];omega) (by dsimp [n];omega))
    omega
  have hfront:5*acquisitionBudget p t width+4*n+10 ≤(5*acquisitionEnvelope n n n+4*n+10)*v:=
    hf.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left _ hv)
  have hc:=SemiprimeD1StackWeightedModeResources.runBound_bytes (weights p t width) width
  have hbytes:=generated_bytes p t width
  have hpow:=Nat.pow_le_pow_left hbytes 3
  have hcore:SemiprimeD1StackWeightedModeBounds.runBound (weights p t width) width ≤
      10000*(10*(n+1)^4)^3*v:=
    hc.trans (Nat.mul_le_mul_right v (Nat.mul_le_mul_left 10000 hpow))
  have hall:=timeBound_le p t width
  change timeBound p t width ≤5*acquisitionBudget p t width+4*n+
    SemiprimeD1StackWeightedModeBounds.runBound (weights p t width) width+10 at hall
  change _ ≤polynomial n*v
  unfold polynomial
  calc
    _ ≤(5*acquisitionBudget p t width+4*n+10)+
        SemiprimeD1StackWeightedModeBounds.runBound (weights p t width) width:=by omega
    _ ≤(5*acquisitionEnvelope n n n+4*n+10)*v+10000*(10*(n+1)^4)^3*v:=
      Nat.add_le_add hfront hcore
    _= _:=by ring
/-- One own bound for the full actual finite program and actual generated weights. -/
def runBound (p t width:Nat):Nat:=polynomial (p+t+width)*
  SemiprimeD1WeightedTuples.visits (weights p t width) (width-1)
theorem source_run_bounded (p t width:Nat):∃time ≤runBound p t width,
    C.run program time (initial (unary p) (unary t) (unary width))=some (done p t width):=by
  obtain ⟨time,ht,hr⟩:=source_run p t width
  exact ⟨time,ht.trans (timeBound_polynomial p t width),hr⟩
/-- Fixed coefficient and degree are chosen before every input metadata triple. -/
theorem polynomial_monomial:∃A d:Nat,∀n,polynomial n ≤A*(n+1)^d:=by
  change Bound polynomial
  unfold polynomial acquisitionEnvelope
  boundArithmetic
/-- Existing feasible-menu cardinality bounds apply to this SAME physical program. -/
theorem runBound_le_leaves (p t width:Nat):
    runBound p t width ≤polynomial (p+t+width)*((weights p t width).length+1)*
      (SemiprimeD1WeightedTuples.tuples (weights p t width) (width-1)).length:=by
  have h:=Nat.mul_le_mul_left (polynomial (p+t+width))
    (SemiprimeD1WeightedTuples.visits_le (weights p t width) (width-1))
  simpa only [runBound,Nat.mul_assoc] using h
end RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueBounds
