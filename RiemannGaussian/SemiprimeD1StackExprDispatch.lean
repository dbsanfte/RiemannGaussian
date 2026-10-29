/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprWiring
/-! # Actual two-tag constructor dispatch -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackExprDispatch
open SemiprimeD1StackExpr SemiprimeD1StackExprWiring SemiprimeD1StackProcedureTrace
/-- The literal physical prefix for each finite operator. -/
def tags : Op→List Bool→List Bool
  | .add,rest=>false::true::rest
  | .sub,rest=>true::false::rest
  | .mul,rest=>true::true::rest
/-- Literal tags are read by two actual pop instructions. -/
theorem literal_tags (rest cached saved : List Bool) :
    Runs program 2 .eval (bank (false::false::rest) cached saved [] [] [] [] [])
      .literalCall (bank rest cached saved [] [] [] [] []) := by
  have h1 : Runs program 1 .eval (bank (false::false::rest) cached saved [] [] [] [] [])
      .secondLow (bank (false::rest) cached saved [] [] [] [] []) := by
    apply one_base program .eval .secondLow (.pop .code .bad .secondLow .secondHigh) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
    · simp [SemiprimeD1StackBytecode.execute]
  have h2 : Runs program 1 .secondLow (bank (false::rest) cached saved [] [] [] [] [])
      .literalCall (bank rest cached saved [] [] [] [] []) := by
    apply one_base program .secondLow .literalCall (.pop .code .bad .literalCall (.begin .add)) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
    · simp [SemiprimeD1StackBytecode.execute]
  exact runs_trans program 1 1 _ _ _ _ _ _ h1 h2

/-- Operator selection is obtained from physical tags, not a supplied opcode result. -/
theorem operator_tags (op : Op) (rest cached saved : List Bool) :
    Runs program 2 .eval (bank (tags op rest) cached saved [] [] [] [] [])
      (.begin op) (bank rest cached saved [] [] [] [] []) := by
  cases op with
  | add=>
    have h1 : Runs program 1 .eval (bank (tags .add rest) cached saved [] [] [] [] [])
        .secondLow (bank (true::rest) cached saved [] [] [] [] []) := by
      apply one_base program .eval .secondLow (.pop .code .bad .secondLow .secondHigh) _ _ rfl
      · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,tags]
      · simp [SemiprimeD1StackBytecode.execute,tags]
    have h2 : Runs program 1 .secondLow (bank (true::rest) cached saved [] [] [] [] [])
        (.begin .add) (bank rest cached saved [] [] [] [] []) := by
      apply one_base program .secondLow (.begin .add) (.pop .code .bad .literalCall (.begin .add)) _ _ rfl
      · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
      · simp [SemiprimeD1StackBytecode.execute]
    exact runs_trans program 1 1 _ _ _ _ _ _ h1 h2
  | sub=>
    have h1 : Runs program 1 .eval (bank (tags .sub rest) cached saved [] [] [] [] [])
        .secondHigh (bank (false::rest) cached saved [] [] [] [] []) := by
      apply one_base program .eval .secondHigh (.pop .code .bad .secondLow .secondHigh) _ _ rfl
      · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,tags]
      · simp [SemiprimeD1StackBytecode.execute,tags]
    have h2 : Runs program 1 .secondHigh (bank (false::rest) cached saved [] [] [] [] [])
        (.begin .sub) (bank rest cached saved [] [] [] [] []) := by
      apply one_base program .secondHigh (.begin .sub) (.pop .code .bad (.begin .sub) (.begin .mul)) _ _ rfl
      · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
      · simp [SemiprimeD1StackBytecode.execute]
    exact runs_trans program 1 1 _ _ _ _ _ _ h1 h2
  | mul=>
    have h1 : Runs program 1 .eval (bank (tags .mul rest) cached saved [] [] [] [] [])
        .secondHigh (bank (true::rest) cached saved [] [] [] [] []) := by
      apply one_base program .eval .secondHigh (.pop .code .bad .secondLow .secondHigh) _ _ rfl
      · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,tags]
      · simp [SemiprimeD1StackBytecode.execute,tags]
    have h2 : Runs program 1 .secondHigh (bank (true::rest) cached saved [] [] [] [] [])
        (.begin .mul) (bank rest cached saved [] [] [] [] []) := by
      apply one_base program .secondHigh (.begin .mul) (.pop .code .bad (.begin .sub) (.begin .mul)) _ _ rfl
      · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
      · simp [SemiprimeD1StackBytecode.execute]
    exact runs_trans program 1 1 _ _ _ _ _ _ h1 h2
end RiemannGaussian.SemiprimeD1StackExprDispatch
