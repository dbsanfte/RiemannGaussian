/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPointTerm
/-! # Actual nested physical rank-counter traversal for convolution
The runtime bounds are obtained from the same literal included pair procedure;
there is no supplied loop body, coefficient, route or execution-cost function.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetPointLoops
open SemiprimeD1StackJetPoint SemiprimeD1StackJetPointExecution SemiprimeD1StackJetPointTerm
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1JetAxes (Context)

/-- Declarative clean-state update at the physical inner counter register. -/
theorem resting_j_update (c : Cache) (i j acc word : List Bool) :
    Function.update (resting c i j acc) (aux .j) word=resting c i word acc := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl

/-- One real decrement selects the next pair index from the physical counter. -/
theorem inner_pop (c : Cache) (i acc : List Bool) (j : ℕ) :
    Runs program 1 .inner (resting c i (unary (j+1)) acc) .axesCopy (resting c i (unary j) acc) := by
  apply one_base program .inner .axesCopy (.pop (aux .j) .outer .axesCopy .axesCopy) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,resting,aux,unary,List.replicate_succ]
  · change Function.update (resting c i (unary (j+1)) acc) (aux .j) (unary (j+1)).tail=_
    rw [show (unary (j+1)).tail=unary j by rfl,resting_j_update]

/-- Real empty-inner-counter test returns to the outer loop. -/
theorem inner_empty (c : Cache) (i acc : List Bool) :
    Runs program 1 .inner (resting c i [] acc) .outer (resting c i [] acc) := by
  apply one_base program .inner .outer (.pop (aux .j) .outer .axesCopy .axesCopy) _ _ rfl
  · rfl
  · exact Function.update_eq_self_iff.mpr rfl

/-- Proof-side scalar value of the executed descending inner traversal. -/
def innerValue (ctx : Context) (a b : List (List Bool)) (k i : ℕ) : ℕ → List Bool → List Bool
  | 0,acc => acc
  | j+1,acc => innerValue ctx a b k i j (SemiprimeD1StackJetPointOrder.pairStep ctx a b k (i,j) acc)

/-- Concrete upper count for the same executed inner traversal. -/
def innerClock (ctx : Context) (c : Cache) (a b : List (List Bool)) (k i : ℕ) : ℕ → List Bool → ℕ
  | 0,_ => 1
  | j+1,acc => 1+pairBudget ctx c i j acc a b+
      innerClock ctx c a b k i j (SemiprimeD1StackJetPointOrder.pairStep ctx a b k (i,j) acc)

/-- Every inner-loop branch executes the actual closed pair controller.
All input/counter/work data are retained or consumed exactly as declared. -/
theorem inner_run (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (k i count : ℕ) (acc : List Bool)
    (ha : c.a=SemiprimeD1TensorTapeCodec.vectorBits a)
    (hb : c.b=SemiprimeD1TensorTapeCodec.vectorBits b)
    (haxes : c.axes=SemiprimeD1TensorTapeCodec.vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) :
    ∃ m ≤ innerClock ctx c a b k i count acc,
      Runs program m .inner (resting c (unary i) (unary count) acc) .outer
        (resting c (unary i) [] (innerValue ctx a b k i count acc)) := by
  induction count generalizing acc with
  | zero => exact ⟨1,le_rfl,inner_empty c (unary i) acc⟩
  | succ count ih =>
    have h1:=inner_pop c (unary i) acc count
    obtain ⟨mt,ht,h2⟩:=pair_run ctx hp c i count k acc a b ha hb haxes hwidth htarget
    obtain ⟨mi,hi,h3⟩:=ih (SemiprimeD1StackJetPointOrder.pairStep ctx a b k (i,count) acc)
    refine ⟨1+mt+mi,?_,?_⟩
    · change 1+mt+mi ≤ 1+pairBudget ctx c i count acc a b+
        innerClock ctx c a b k i count (SemiprimeD1StackJetPointOrder.pairStep ctx a b k (i,count) acc)
      omega
    · exact runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h1 h2) h3

/-- Declarative clean-state update at the physical outer counter register. -/
theorem resting_i_update (c : Cache) (i j acc word : List Bool) :
    Function.update (resting c i j acc) (aux .i) word=resting c word j acc := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl

/-- One actual outer decrement obtains the next physical row index. -/
theorem outer_pop (c : Cache) (acc : List Bool) (i : ℕ) :
    Runs program 1 .outer (resting c (unary (i+1)) [] acc) .innerInit (resting c (unary i) [] acc) := by
  apply one_base program .outer .innerInit (.pop (aux .i) .done .innerInit .innerInit) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,resting,aux,unary,List.replicate_succ]
  · change Function.update (resting c (unary (i+1)) [] acc) (aux .i) (unary (i+1)).tail=_
    rw [show (unary (i+1)).tail=unary i by rfl,resting_i_update]

/-- The actual empty-outer-counter branch reaches the literal final halt label. -/
theorem outer_empty (c : Cache) (acc : List Bool) :
    Runs program 1 .outer (resting c [] [] acc) .done (resting c [] [] acc) := by
  apply one_base program .outer .done (.pop (aux .i) .done .innerInit .innerInit) _ _ rfl
  · rfl
  · exact Function.update_eq_self_iff.mpr rfl

/-- Each physical row acquires a fresh inner counter by copying the retained rank. -/
theorem inner_init (c : Cache) (i acc : List Bool) :
    Runs program (5*c.rank.length+4) .innerInit (resting c i [] acc) .inner
      (resting c i c.rank acc) := by
  have h:=copy_call .rankJ .innerInit .inner (resting c i [] acc) rfl (by rfl) (by rfl)
  change Runs program (5*c.rank.length+4) .innerInit (resting c i [] acc) .inner
    (Function.update (resting c i [] acc) (aux .j) c.rank) at h
  rwa [resting_j_update] at h

/-- Proof-side value of the literal descending outer traversal. -/
def outerValue (ctx : Context) (a b : List (List Bool)) (k rank : ℕ) : ℕ → List Bool → List Bool
  | 0,acc => acc
  | i+1,acc => outerValue ctx a b k rank i (innerValue ctx a b k i rank acc)

/-- Concrete original-data upper count of the same outer traversal. -/
def outerClock (ctx : Context) (c : Cache) (a b : List (List Bool)) (k rank : ℕ) : ℕ → List Bool → ℕ
  | 0,_ => 1
  | i+1,acc => 1+(5*c.rank.length+4)+innerClock ctx c a b k i rank acc+
      outerClock ctx c a b k rank i (innerValue ctx a b k i rank acc)

/-- Actual closed outer traversal, retaining the real repeated rank-copy and
router/reader/arithmetic costs of every original index pair. -/
theorem outer_run (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (k rank count : ℕ) (acc : List Bool)
    (ha : c.a=SemiprimeD1TensorTapeCodec.vectorBits a)
    (hb : c.b=SemiprimeD1TensorTapeCodec.vectorBits b)
    (haxes : c.axes=SemiprimeD1TensorTapeCodec.vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) (hrank : c.rank=unary rank) :
    ∃ m ≤ outerClock ctx c a b k rank count acc,
      Runs program m .outer (resting c (unary count) [] acc) .done
        (resting c [] [] (outerValue ctx a b k rank count acc)) := by
  induction count generalizing acc with
  | zero => exact ⟨1,le_rfl,outer_empty c acc⟩
  | succ count ih =>
    have h1:=outer_pop c acc count
    have h2:=inner_init c (unary count) acc
    rw [hrank] at h2
    rw [show 5*(unary rank).length+4=5*c.rank.length+4 by rw [hrank]] at h2
    obtain ⟨mi,hi,h3⟩:=inner_run ctx hp c a b k count rank acc ha hb haxes hwidth htarget
    obtain ⟨mo,ho,h4⟩:=ih (innerValue ctx a b k count rank acc)
    refine ⟨1+(5*c.rank.length+4)+mi+mo,?_,?_⟩
    · change 1+(5*c.rank.length+4)+mi+mo ≤ 1+(5*c.rank.length+4)+innerClock ctx c a b k count rank acc+
        outerClock ctx c a b k rank count (innerValue ctx a b k count rank acc)
      omega
    · exact runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h1 h2) h3) h4

/-- Literal descending row specification of the physical inner counter. -/
def rowPairs (i count : ℕ) : List (ℕ×ℕ) :=
  (List.range count).reverse.map (fun j=>(i,j))
/-- Literal descending rows of the physical outer counter. -/
def outerPairs (rank count : ℕ) : List (ℕ×ℕ) :=
  (List.range count).reverse.flatMap (fun i=>rowPairs i rank)

/-- A recursive fold is compositional across actual sequential pair visits. -/
theorem accumulate_append (ctx : Context) (a b : List (List Bool)) (k : ℕ)
    (xs ys : List (ℕ×ℕ)) (acc : List Bool) :
    SemiprimeD1StackJetPointOrder.accumulate ctx a b k (xs++ys) acc=
      SemiprimeD1StackJetPointOrder.accumulate ctx a b k ys
        (SemiprimeD1StackJetPointOrder.accumulate ctx a b k xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons ij xs ih => exact ih _

/-- One actual inner decrement visits the last remaining original index. -/
theorem rowPairs_succ (i count : ℕ) : rowPairs i (count+1)=(i,count)::rowPairs i count := by
  simp [rowPairs,List.range_succ,List.reverse_append]

/-- One actual outer decrement visits one complete remaining original row. -/
theorem outerPairs_succ (rank count : ℕ) :
    outerPairs rank (count+1)=rowPairs count rank++outerPairs rank count := by
  simp [outerPairs,List.range_succ,List.reverse_append]

/-- Inner scalar specification is exactly the original pair fold in visit order. -/
theorem innerValue_eq (ctx : Context) (a b : List (List Bool)) (k i count : ℕ) (acc : List Bool) :
    innerValue ctx a b k i count acc=
      SemiprimeD1StackJetPointOrder.accumulate ctx a b k (rowPairs i count) acc := by
  induction count generalizing acc with
  | zero => rfl
  | succ count ih =>
    rw [innerValue,rowPairs_succ]
    exact ih _

/-- Outer scalar specification contains every original pair once in descending order. -/
theorem outerValue_eq (ctx : Context) (a b : List (List Bool)) (k rank count : ℕ) (acc : List Bool) :
    outerValue ctx a b k rank count acc=
      SemiprimeD1StackJetPointOrder.accumulate ctx a b k (outerPairs rank count) acc := by
  induction count generalizing acc with
  | zero => rfl
  | succ count ih => rw [outerValue,ih,innerValue_eq,outerPairs_succ,accumulate_append]

/-- Complete executed traversal denotes the exact frozen canonical coefficient. -/
theorem outerValue_original (ctx : Context) (a b : List (List Bool)) (k : ℕ) :
    outerValue ctx a b k ctx.rank ctx.rank []=(SemiprimeD1JetRingBits.mulAt ctx a b k).bits := by
  rw [outerValue_eq]
  exact SemiprimeD1StackJetPointOrder.descending_eq_original ctx a b k

end RiemannGaussian.SemiprimeD1StackJetPointLoops
