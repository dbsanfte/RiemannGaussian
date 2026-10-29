/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFiniteEnumerations
import RiemannGaussian.SemiprimeMacroGraph

/-! # Explicit constructor lists for the actual macro graph
No finite-type enumeration or classical inverse is used in the data path.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeMacroFiniteEnumerations
open SemiprimeFiniteEnumerations SemiprimeMacroGraph
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

/-- Explicit constructor data for `unit`. -/
def unit : FiniteEnumeration Unit := ⟨[()], by simp, by intro x; cases x; simp⟩
/-- Explicit constructor data for `boolean`. -/
def boolean : FiniteEnumeration Bool := ⟨[false,true], by simp, by intro x; cases x <;> simp⟩
/-- Explicit constructor data for `transforms`. -/
def transforms : FiniteEnumeration Transform := sum (fin 2) unit

/-- Explicit constructor data for `wordsCode`. -/
abbrev wordsCode (r t _digits : ℕ) := Fin 2 × Fin (r*t) ⊕ Transform × Fin r × Fin t ⊕ Transform × Fin r × Fin t ⊕ Transform × Fin t × Fin r ⊕ Fin (r*t) ⊕ Fin (r*t+1)
/-- Explicit constructor data for `wordsEquiv`. -/
def wordsEquiv (r t digits : ℕ) : wordsCode r t digits ≃ WordSignal r t where
  toFun := fun x => match x with
    | Sum.inl ((a,b)) => .input a b
    | Sum.inr (Sum.inl ((a,b,c))) => .first a b c
    | Sum.inr (Sum.inr (Sum.inl ((a,b,c)))) => .twiddle a b c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((a,b,c))))) => .second a b c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (a))))) => .product a
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a))))) => .carry a
  invFun := fun x => match x with
    | .input a b => Sum.inl ((a,b))
    | .first a b c => Sum.inr (Sum.inl ((a,b,c)))
    | .twiddle a b c => Sum.inr (Sum.inr (Sum.inl ((a,b,c))))
    | .second a b c => Sum.inr (Sum.inr (Sum.inr (Sum.inl ((a,b,c)))))
    | .product a => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (a)))))
    | .carry a => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a)))))
  left_inv := by intro x; rcases x with x | x | x | x | x | x <;> simp_all
  right_inv := by intro x; cases x <;> rfl
/-- Explicit constructor data for `words`. -/
def words (r t digits : ℕ) : FiniteEnumeration (WordSignal r t) :=
  transport (sum (prod (fin 2) (fin (r*t))) (sum (prod transforms (prod (fin r) (fin t))) (sum (prod transforms (prod (fin r) (fin t))) (sum (prod transforms (prod (fin t) (fin r))) (sum (fin (r*t)) (fin (r*t+1))))))) (wordsEquiv r t digits)

/-- Explicit constructor data for `flagsCode`. -/
abbrev flagsCode (_r _t digits : ℕ) := Fin 2 × Fin digits ⊕ Fin 2 × Fin (digits-1)
/-- Explicit constructor data for `flagsEquiv`. -/
def flagsEquiv (r t digits : ℕ) : flagsCode r t digits ≃ FlagSignal digits where
  toFun := fun x => match x with
    | Sum.inl ((a,b)) => .digit a b
    | Sum.inr ((a,b)) => .orOut a b
  invFun := fun x => match x with
    | .digit a b => Sum.inl ((a,b))
    | .orOut a b => Sum.inr ((a,b))
  left_inv := by intro x; rcases x with x | x <;> simp_all
  right_inv := by intro x; cases x <;> rfl
/-- Explicit constructor data for `flags`. -/
def flags (r t digits : ℕ) : FiniteEnumeration (FlagSignal digits) :=
  transport (sum (prod (fin 2) (fin digits)) (prod (fin 2) (fin (digits-1)))) (flagsEquiv r t digits)

/-- Explicit constructor data for `verticesCode`. -/
abbrev verticesCode (r t digits : ℕ) := Fin 2 × Fin (r*t) ⊕ Transform × Fin r ⊕ Transform × Fin r × Fin t ⊕ Transform × Fin t ⊕ Fin (r*t) ⊕ Unit ⊕ Fin (r*t) ⊕ Unit ⊕ Fin 2 × Fin (digits-1) ⊕ Fin 2
/-- Explicit constructor data for `verticesEquiv`. -/
def verticesEquiv (r t digits : ℕ) : verticesCode r t digits ≃ Vertex r t digits where
  toFun := fun x => match x with
    | Sum.inl ((a,b)) => .input a b
    | Sum.inr (Sum.inl ((a,b))) => .first a b
    | Sum.inr (Sum.inr (Sum.inl ((a,b,c)))) => .scale a b c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((a,b))))) => .second a b
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (a))))) => .product a
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (())))))) => .carryInitial
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (a))))))) => .carry a
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (())))))))) => .carryTerminal
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((a,b)))))))))) => .orGate a b
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a))))))))) => .inputCheck a
  invFun := fun x => match x with
    | .input a b => Sum.inl ((a,b))
    | .first a b => Sum.inr (Sum.inl ((a,b)))
    | .scale a b c => Sum.inr (Sum.inr (Sum.inl ((a,b,c))))
    | .second a b => Sum.inr (Sum.inr (Sum.inr (Sum.inl ((a,b)))))
    | .product a => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (a)))))
    | .carryInitial => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (()))))))
    | .carry a => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (a)))))))
    | .carryTerminal => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (()))))))))
    | .orGate a b => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((a,b))))))))))
    | .inputCheck a => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a)))))))))
  left_inv := by intro x; rcases x with x | x | x | x | x | x | x | x | x | x <;> simp_all
  right_inv := by intro x; cases x <;> rfl
/-- Explicit constructor data for `vertices`. -/
def vertices (r t digits : ℕ) : FiniteEnumeration (Vertex r t digits) :=
  transport (sum (prod (fin 2) (fin (r*t))) (sum (prod transforms (fin r)) (sum (prod transforms (prod (fin r) (fin t))) (sum (prod transforms (fin t)) (sum (fin (r*t)) (sum (unit) (sum (fin (r*t)) (sum (unit) (sum (prod (fin 2) (fin (digits-1))) (fin 2)))))))))) (verticesEquiv r t digits)

/-- Explicit constructor data for `bits`. -/
def bits (r t digits : ℕ) : FiniteEnumeration (BitSignal r t digits) :=
  sum (prod (words r t digits) (fin (r*t+1))) (flags r t digits)
/-- Explicit constructor data for `edges`. -/
def edges (r t digits : ℕ) : FiniteEnumeration (Edge r t digits) :=
  prod (bits r t digits) boolean
/-- Explicit constructor data for `subdividedVertices`. -/
def subdividedVertices (r t digits : ℕ) : FiniteEnumeration (SubdividedVertex r t digits) :=
  sum (vertices r t digits) (bits r t digits)
/-- Explicit constructor data for `incidences`. -/
def incidences (r t digits : ℕ) : FiniteEnumeration
    ((v : SubdividedVertex r t digits) × Fin (subdividedArity v)) :=
  sigma (subdividedVertices r t digits) (fun v => fin (subdividedArity v))

/-- Actual macro-graph source enumerations, retaining all ordered port constructors. -/
def source (r t digits palette Q : ℕ) [NeZero palette] :=
  sourceEnumerations (incidences r t digits) (edges r t digits)
    (subdividedVertices r t digits) palette Q

/-- Every source list is nodup, complete and has the exact actual finite size. -/
theorem edges_count (r t digits : ℕ) :
    (edges r t digits).values.length=Fintype.card (Edge r t digits) :=
  (edges r t digits).length_eq_card

#print axioms edges_count
end RiemannGaussian.SemiprimeMacroFiniteEnumerations
