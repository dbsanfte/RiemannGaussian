/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointLoopView
/-! # Actual retained-source copies and complete forward endpoint catalogue
Both actual cached source tapes are copied, every pair is really parsed and
queried, and both chronological vector outputs are physically reversed once.
This prefix stops before packet buckets and derived port-order acquisition.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSource
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Loop
export SemiprimeD1StackChildGroupFactoryEndpointLoop (Row pairs placements Valid result timeBound source_trace)
end Loop
namespace View
export SemiprimeD1StackChildGroupFactoryEndpointLoopView
  (result_other result_oldHistory result_endpointHistory oldRecords selectedRecords)
end View
namespace Parse
export SemiprimeD1StackChildGroupFactoryEndpointParse (cleanRoles)
end Parse
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryEndpointCleanup (role)
end Cleanup
/-- The only initial acquisition operations are two paid copies of the actual retained source tapes. -/
def copied (before:Stack→List Bool) (rows:List Loop.Row):Stack→List Bool:=
  Function.update (Function.update before (aux .pairReader) (Loop.pairs rows))
    (aux .placementReader) (Loop.placements rows)
/-- Both actual endpoint catalogues and the full retained physical bank. -/
def result (before:Stack→List Bool) (rows:List Loop.Row):Stack→List Bool:=
  let out:=Loop.result rows (copied before rows)
  Function.update (Function.update (Function.update (Function.update out
    (aux .endpointHistory) []) (aux .endpoints) (View.selectedRecords rows++[false]))
    (aux .oldHistory) []) (aux .oldEndpoints) (View.oldRecords rows++[false])
/-- All own source clocks, including both copies, both real seed writes and both genuine reversals. -/
def timeBound (entries:List (List Bool×List Bool)) (rows:List Loop.Row):Nat:=
  (5*(Loop.pairs rows).length+4)+(5*(Loop.placements rows).length+4)+Loop.timeBound entries rows+
    (1+(2*(View.selectedRecords rows).length+3))+(1+(2*(View.oldRecords rows).length+3))
/-- Complete actual forward endpoint catalogue from retained actual source words, without a mask/edge getter input. -/
theorem source_trace (entries:List (List Bool×List Bool)) (rows:List Loop.Row) (before:Stack→List Bool)
    (hpair:before (aux .occurrences)=Loop.pairs rows) (hplacement:before (aux .placements)=Loop.placements rows)
    (hp:before (aux .pairReader)=[]) (hm:before (aux .placementReader)=[])
    (hclean:∀k∈Parse.cleanRoles,before k=[])
    (hside:before (aux .sideWord)=[]) (hr:before (aux .rowBuffer)=[])
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (hl:∀k,before (lookup k)=[])
    (hmap:before (aux .activationMap)=SemiprimeD1StackOwnerLookup.records entries [])
    (heh:before (aux .endpointHistory)=[]) (hoh:before (aux .oldHistory)=[])
    (heo:before (aux .endpoints)=[]) (hoo:before (aux .oldEndpoints)=[]) (hv:Loop.Valid entries rows):
    Runs program (timeBound entries rows) (.local 2 18) before (.local 6 17) (result before rows):=by
  simp only [aux] at heh hoh
  let c1:=Function.update before (aux .pairReader) (Loop.pairs rows)
  have h0:=copy_call 14 (.local 2 18) (.local 2 19) rfl before (Loop.pairs rows) [] hpair hp hc
  simp only [List.append_nil] at h0
  change Runs program _ _ before _ c1 at h0
  have h1:=copy_call 15 (.local 2 19) (.local 2 20) rfl c1 (Loop.placements rows) []
    (by simpa [c1,aux,copyStack,copyPorts] using hplacement) (by simpa [c1,aux,copyStack,copyPorts] using hm) (by simpa [c1,aux,copyStack,copyPorts] using hc)
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (copied before rows) at h1
  have h2:=Loop.source_trace entries rows (copied before rows) rfl rfl
    (by simpa [copied,Parse.cleanRoles,aux,field] using hclean)
    (by simpa [copied,aux] using hside) (by simpa [copied,aux] using hr)
    (by simpa [copied,aux] using hb) (by simpa [copied,aux] using hc)
    (by intro k;simpa [copied,aux,lookup] using hl k)
    (by simpa [copied,aux] using hmap) hv
  let out:=Loop.result rows (copied before rows)
  have hehist:out (aux .endpointHistory)=(View.selectedRecords rows).reverse:=by
    dsimp only [out]
    rw [View.result_endpointHistory]
    simp [copied,aux,heh]
  have hohist:out (aux .oldHistory)=(View.oldRecords rows).reverse:=by
    dsimp only [out]
    rw [View.result_oldHistory]
    simp [copied,aux,hoh]
  have heout:out (aux .endpoints)=[]:=by
    dsimp only [out]
    rw [View.result_other rows (copied before rows) (aux .endpoints)
      (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using heo
  have hoout:out (aux .oldEndpoints)=[]:=by
    dsimp only [out]
    rw [View.result_other rows (copied before rows) (aux .oldEndpoints)
      (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using hoo
  let b1:=Function.update out (aux .endpoints) [false]
  have h3:=push_run (.local 6 13) (.local 6 14) (aux .endpoints) false out rfl
  rw [heout] at h3
  have h4:=reverse_call 3 (.local 6 14) (.local 6 15) rfl b1 (View.selectedRecords rows).reverse [false]
    (by simpa [b1,aux,reverseStack,reversePorts] using hehist) (Function.update_self _ _ _)
  simp only [List.length_reverse,List.reverse_reverse] at h4
  change Runs program _ _ b1 _ (Function.update (Function.update b1 (aux .endpointHistory) [])
    (aux .endpoints) (View.selectedRecords rows++[false])) at h4
  let b2:=Function.update (Function.update out (aux .endpointHistory) []) (aux .endpoints) (View.selectedRecords rows++[false])
  have he2:Function.update (Function.update b1 (aux .endpointHistory) [])
      (aux .endpoints) (View.selectedRecords rows++[false])=b2:=by
    dsimp only [b1,b2]
    rw [Function.update_comm (by decide:aux .endpoints≠aux .endpointHistory),Function.update_idem]
  rw [he2] at h4
  let b3:=Function.update b2 (aux .oldEndpoints) [false]
  have hb2old:b2 (aux .oldEndpoints)=[]:=by simpa [b2,aux] using hoout
  have h5:=push_run (.local 6 15) (.local 6 16) (aux .oldEndpoints) false b2 rfl
  rw [hb2old] at h5
  have h6:=reverse_call 4 (.local 6 16) (.local 6 17) rfl b3 (View.oldRecords rows).reverse [false]
    (by simpa [b3,b2,aux,reverseStack,reversePorts] using hohist) (Function.update_self _ _ _)
  simp only [List.length_reverse,List.reverse_reverse] at h6
  change Runs program _ _ b3 _ (Function.update (Function.update b3 (aux .oldHistory) [])
    (aux .oldEndpoints) (View.oldRecords rows++[false])) at h6
  have he6:Function.update (Function.update b3 (aux .oldHistory) [])
      (aux .oldEndpoints) (View.oldRecords rows++[false])=result before rows:=by
    dsimp only [b3,b2,result]
    rw [Function.update_comm (by decide:aux .oldEndpoints≠aux .oldHistory),Function.update_idem]
  rw [he6] at h6
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 h6)))))
  simpa only [timeBound,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSource
