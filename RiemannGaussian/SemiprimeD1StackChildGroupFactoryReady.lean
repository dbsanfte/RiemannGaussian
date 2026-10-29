/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactory
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectExecution
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesExecution
import RiemannGaussian.SemiprimeD1StackPacketInventoryExecution
/-! # Literal retained258-role child-factory ready source
All143 selector/occurrence/inventory allocations survive. Seven source inputs
alias their ACTUAL stopped producer tapes; all seven displaced input allocations
remain empty and counted. No producer is reacquired by this entry.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryReady
namespace S
export SemiprimeD1StackSourceIncidenceSelect (Stack environmentStack aux)
end S
namespace P
export SemiprimeD1StackSourceOccurrences (Stack)
end P
namespace I
export SemiprimeD1StackPacketInventory (Stack output packets)
end I
namespace G
export SemiprimeD1StackChildGroupFactoryRoles (Stack Aux aux)
end G
namespace W
export SemiprimeD1StackChildGroupFactoryWiring (Label entry)
end W
namespace Main
export SemiprimeD1StackChildGroupFactory (program Inputs input)
end Main
/-- All63 selector,21 occurrence,59 inventory and115 fresh source allocations. -/
abbrev Stack:=S.Stack⊕(P.Stack⊕(I.Stack⊕G.Stack))
/-- Entire stopped selector bank. -/
def selector:S.Stack→Stack:=Sum.inl
/-- Entire stopped occurrence bank. -/
def occurrence:P.Stack→Stack:=fun k=>.inr (.inl k)
/-- Entire stopped original sparse inventory bank. -/
def inventory:I.Stack→Stack:=fun k=>.inr (.inr (.inl k))
/-- Whole allocated115-role source bank, including seven unused input shadows. -/
def allocation:G.Stack→Stack:=fun k=>.inr (.inr (.inr k))
/-- Physical dictionary of ALL original old-vertex selected IDs. -/
def environment:Stack:=selector (S.environmentStack (SemiprimeD1StackSourceEnvironment.aux .dictionary))
/-- The exact retained acquired alphabet catalogue. -/
def catalogue:Stack:=selector (S.aux .catalogue)
/-- Actual retained unary owner count, including isolated owners. -/
def owners:Stack:=selector (S.aux .owners)
/-- Actual retained unary factor count, including empty factors. -/
def factors:Stack:=selector (S.aux .factors)
/-- Actual factor-major/local-slot occurrence pair stream. -/
def pairs:Stack:=occurrence .output
/-- Actual original chronological placement vector. -/
def placements:Stack:=inventory I.output
/-- Actual observed packet vector, including all source discovery order. -/
def packets:Stack:=inventory I.packets
/-- Exact seven source-input aliases. Context words remain in fresh counted allocations. -/
def factory:G.Stack→Stack
  | .inr (.inr (.inr (.inr (.inr .environment))))=>environment
  | .inr (.inr (.inr (.inr (.inr .catalogue))))=>catalogue
  | .inr (.inr (.inr (.inr (.inr .owners))))=>owners
  | .inr (.inr (.inr (.inr (.inr .factors))))=>factors
  | .inr (.inr (.inr (.inr (.inr .occurrences))))=>pairs
  | .inr (.inr (.inr (.inr (.inr .placements))))=>placements
  | .inr (.inr (.inr (.inr (.inr .packets))))=>packets
  | k=>allocation k
/-- Generic inverse view proves alias safety before original graph instantiation. -/
def recover:Stack→Option G.Stack
  | .inl k=>if k=S.environmentStack (SemiprimeD1StackSourceEnvironment.aux .dictionary) then some (G.aux .environment)
      else if k=S.aux .catalogue then some (G.aux .catalogue)
      else if k=S.aux .owners then some (G.aux .owners)
      else if k=S.aux .factors then some (G.aux .factors) else none
  | .inr (.inl k)=>if k=.output then some (G.aux .occurrences) else none
  | .inr (.inr (.inl k))=>if k=I.output then some (G.aux .placements)
      else if k=I.packets then some (G.aux .packets) else none
  | .inr (.inr (.inr k))=>some k
/-- Every real source role is recovered exactly; shadow allocations never alias it. -/
theorem recover_factory (k:G.Stack):recover (factory k)=some k:=by
  rcases k with k|k|k|k|k|k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases k <;> rfl
/-- Direct aliases are injective, including every complete callee/shadow role. -/
theorem factory_injective:Function.Injective factory:=by
  intro a b h
  have he:=congrArg recover h
  rw [recover_factory,recover_factory] at he
  exact Option.some.inj he
/-- The SAME actual literal source, with only fixed physical role renaming. -/
def program:W.Label→SemiprimeD1StackCalls.Instruction Stack W.Label:=
  fun pc=>SemiprimeD1StackValidationLink.instruction factory id (Main.program pc)
/-- Six honest actual order/group/header words; no decoded context, rank or precision. -/
structure Header where
  /-- Actual unary colour coordinate, distinct from the NEW jet axis. -/
  colourIndex:List Bool
  /-- Actual binary numeric group target. -/
  group:List Bool
  /-- Actual original unary-axis header. -/
  oldAxes:List Bool
  /-- Actual original binary precision, including weighted-root2ell. -/
  oldPrecision:List Bool
  /-- Actual acquired positive NEW jet-axis markers. -/
  jetAxis:List Bool
  /-- Actual NEW binary working precision, never equated with OLDp. -/
  newPrecision:List Bool
/-- Fresh source words contain ONLY the six actual header operands. -/
def privateInput (h:Header):G.Stack→List Bool
  | .inr (.inr (.inr (.inr (.inr .colourIndex))))=>h.colourIndex
  | .inr (.inr (.inr (.inr (.inr .group))))=>h.group
  | .inr (.inr (.inr (.inr (.inr .oldAxes))))=>h.oldAxes
  | .inr (.inr (.inr (.inr (.inr .oldPrecision))))=>h.oldPrecision
  | .inr (.inr (.inr (.inr (.inr .jetAxis))))=>h.jetAxis
  | .inr (.inr (.inr (.inr (.inr .newPrecision))))=>h.newPrecision
  | _=>[]
/-- Entire258-word physical bank; no cached role is projected away. -/
def data (s:S.Stack→List Bool) (p:P.Stack→List Bool) (i:I.Stack→List Bool)
    (fresh:G.Stack→List Bool):Stack→List Bool:=Sum.elim s (Sum.elim p (Sum.elim i fresh))
/-- Prepared entry retains all143 REAL stopped producer words and empty source-input shadows. -/
def initial (s:S.Stack→List Bool) (p:P.Stack→List Bool) (i:I.Stack→List Bool) (h:Header):
    SemiprimeD1StackCalls.State Stack W.Label:=⟨some W.entry,none,none,data s p i (privateInput h),[]⟩
/-- Actual source words are projections of the real retained tapes, never supplied getters in control. -/
def sourceInputs (s:S.Stack→List Bool) (p:P.Stack→List Bool) (i:I.Stack→List Bool) (h:Header):Main.Inputs:=
  ⟨s (S.environmentStack (SemiprimeD1StackSourceEnvironment.aux .dictionary)),s (S.aux .catalogue),
    s (S.aux .owners),s (S.aux .factors),p .output,i I.output,i I.packets,
    h.colourIndex,h.group,h.oldAxes,h.oldPrecision,h.jetAxis,h.newPrecision⟩
/-- Every actual aliased source operand agrees with its physical core initial value. -/
theorem initial_projection (s:S.Stack→List Bool) (p:P.Stack→List Bool) (i:I.Stack→List Bool)
    (h:Header) (k:G.Stack):
    (initial s p i h).data (factory k)=Main.input (sourceInputs s p i h) k:=by
  rcases k with k|k|k|k|k|k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases k <;> rfl
/-- The displaced source-input shadows stay physically empty at entry and remain counted. -/
theorem initial_shadows (s:S.Stack→List Bool) (p:P.Stack→List Bool) (i:I.Stack→List Bool)
    (h:Header):
    (initial s p i h).data (allocation (G.aux .environment))=[] ∧
    (initial s p i h).data (allocation (G.aux .catalogue))=[] ∧
    (initial s p i h).data (allocation (G.aux .owners))=[] ∧
    (initial s p i h).data (allocation (G.aux .factors))=[] ∧
    (initial s p i h).data (allocation (G.aux .occurrences))=[] ∧
    (initial s p i h).data (allocation (G.aux .placements))=[] ∧
    (initial s p i h).data (allocation (G.aux .packets))=[]:=⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
/-- Genuine fixed258-role ready machine; source acquisition remains caller work. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine environment
  (factory (G.aux .output)) W.entry program
/-- Every retained producer role, new source role and displaced shadow is counted. -/
theorem stack_card:Fintype.card Stack=258:=by
  rw [Fintype.card_sum,SemiprimeD1StackSourceIncidenceSelect.stack_card,Fintype.card_sum,
    SemiprimeD1StackSourceOccurrences.stack_card,Fintype.card_sum,SemiprimeD1StackPacketInventory.stack_card,
    SemiprimeD1StackChildGroupFactoryRoles.stack_card]
/-- Data and actual return alphabets are finite independently of inputs. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- No graph, predicate, permutation, order value or evaluator is in control. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryReady
