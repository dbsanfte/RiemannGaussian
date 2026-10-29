/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionOriginal
/-! # Fixed complete physical order of the forty-eight acquired phase words -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersInventory
namespace P
export SemiprimeD1StackPhaseWorkingPrecision (Stack input metadataStack aux)
end P
namespace M
export SemiprimeD1StackPhaseWorkingPrecisionMetadata (Stack guardStack divStack aux)
end M
namespace G
export SemiprimeD1StackPhaseGeometryGuard (geometryStack aux)
end G
namespace Geo
export SemiprimeD1StackPhaseGeometry (subStack aux)
end Geo
/-- All four literal subtraction roles, including consumed work. -/
def subtraction : List SemiprimeD1StackAdder.Stack :=[.left,.right,.scratch,.output]
/-- All ten original and acquired geometry words. -/
def geometry : List SemiprimeD1StackPhaseGeometry.Aux :=
  [.exponent,.index,.counter,.center,.alpha,.sign,.zero,.order,.scan,.scratch]
/-- All seven original and acquired guard words. -/
def guards : List SemiprimeD1StackPhaseGeometryGuard.Aux :=[.levels,.left,.right,.limit,.valid,.scratch,.output]
/-- All six literal division roles. -/
def division : List SemiprimeD1StackUnaryDivmod.Stack :=[.input,.divisor,.copied,.scratch,.quotient,.remainder]
/-- All ten original and acquired bounded metadata words. -/
def metadata : List SemiprimeD1StackPhaseWorkingPrecisionMetadata.Aux :=
  [.edges,.precision,.multiplier,.multiplicand,.productScratch,.q,.r,.delta,.subtractWork,.copyScratch]
/-- All eleven binary work and output words, including both binary P and D. -/
def binary : List SemiprimeD1StackPhaseWorkingPrecision.Aux :=
  [.left,.right,.scratch,.output,.counter,.next,.todo,.zeroTodo,.shiftTodo,.copyScratch,.power]
/-- Literal fixed role order; all original, rejected and unused words are retained. -/
def roles : List P.Stack :=
  subtraction.map (P.metadataStack ∘ M.guardStack ∘ G.geometryStack ∘ Geo.subStack) ++
  geometry.map (P.metadataStack ∘ M.guardStack ∘ G.geometryStack ∘ Geo.aux) ++
  guards.map (P.metadataStack ∘ M.guardStack ∘ G.aux) ++
  division.map (P.metadataStack ∘ M.divStack) ++metadata.map (P.metadataStack ∘ M.aux) ++binary.map P.aux
/-- Exactly forty-eight serialized words, independent of every original input. -/
theorem roles_length : roles.length=48 :=by decide
/-- No physical role occurs twice in the fixed record order. -/
theorem roles_nodup : roles.Nodup :=by decide
/-- Every physical stopped phase role is serialized, with none omitted. -/
theorem roles_complete (k:P.Stack) : k∈roles :=by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp [roles,subtraction,geometry,guards,division,metadata,binary,P.metadataStack,M.guardStack,G.geometryStack,Geo.subStack,Geo.aux,G.aux,M.divStack,M.aux,P.aux,Function.comp_def]
        · cases k <;> simp [roles,subtraction,geometry,guards,division,metadata,binary,P.metadataStack,M.guardStack,G.geometryStack,Geo.subStack,Geo.aux,G.aux,M.divStack,M.aux,P.aux,Function.comp_def]
      · cases k <;> simp [roles,subtraction,geometry,guards,division,metadata,binary,P.metadataStack,M.guardStack,G.geometryStack,Geo.subStack,Geo.aux,G.aux,M.divStack,M.aux,P.aux,Function.comp_def]
    · rcases k with k|k
      · cases k <;> simp [roles,subtraction,geometry,guards,division,metadata,binary,P.metadataStack,M.guardStack,G.geometryStack,Geo.subStack,Geo.aux,G.aux,M.divStack,M.aux,P.aux,Function.comp_def]
      · cases k <;> simp [roles,subtraction,geometry,guards,division,metadata,binary,P.metadataStack,M.guardStack,G.geometryStack,Geo.subStack,Geo.aux,G.aux,M.divStack,M.aux,P.aux,Function.comp_def]
  · cases k <;> simp [roles,subtraction,geometry,guards,division,metadata,binary,P.metadataStack,M.guardStack,G.geometryStack,Geo.subStack,Geo.aux,G.aux,M.divStack,M.aux,P.aux,Function.comp_def]
/-- Fixed-position role selection lives entirely in finite program control. -/
def role (i:Fin 48) : P.Stack :=roles.get ⟨i.val,by simpa only [roles_length] using i.isLt⟩
/-- Fixed serialization visits the literal list in its declared order. -/
theorem role_get (i:Fin 48) : role i=roles[i.val] :=rfl
/-- The finite serialization index covers every stopped physical role. -/
theorem role_surjective : Function.Surjective role :=by
  intro k
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp (roles_complete k)
  refine ⟨⟨i.val,by simpa only [roles_length] using i.isLt⟩,?_⟩
  exact hi
/-- The five original operands are the only nonempty input words. -/
theorem input_only (a u edges:Nat) (t p:List Bool) (k:P.Stack) :
    P.input a u edges t p k=
      if k=P.metadataStack (M.guardStack (G.geometryStack (Geo.aux .exponent))) then List.replicate a true
      else if k=P.metadataStack (M.guardStack (G.aux .levels)) then List.replicate u true
      else if k=P.metadataStack (M.aux .edges) then List.replicate edges true
      else if k=P.metadataStack (M.guardStack (G.geometryStack (Geo.aux .index))) then t
      else if k=P.metadataStack (M.aux .precision) then p else [] :=by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersInventory
