/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeStreams
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPackedRootInputs
/-! # Whole actual retained child-factory source with exact original ordered streams
The literal258-role ready program consumes only already acquired physical cache
words and six headers. Every original activation bit and exact native unary
scope/order row is produced in ALL original owner-first vertex order. The SAME
source clock covers every call, generated ordinal, frame, drain and real return.
This boundary supplies metadata; child table production, context installation,
recursive child production and the literal enclosing N-only caller stay open.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOriginal
open SemiprimeBitArithmetic (bitValue)
namespace R
export SemiprimeD1StackChildGroupFactoryReady (Stack Header factory initial sourceInputs program)
end R
namespace Res
export SemiprimeD1StackChildGroupFactoryReadyResources (source_run runBound size)
end Res
namespace Meaning
export SemiprimeD1StackChildGroupFactoryNativeInputs (CacheMeaning valid_original count_original)
end Meaning
namespace Root
export SemiprimeD1StackChildGroupFactoryPackedRootInputs (selectorWords occurrenceWords inventoryWords cache_original)
end Root
namespace N
export SemiprimeD1TensorNetwork (Network arity owner)
end N
namespace A
export SemiprimeD1StackChildGroupFactoryNativeActivation (originalIDs result_original)
end A
namespace Fld
export SemiprimeD1StackChildGroupFactoryNativeFields (source fields)
end Fld
namespace Streams
export SemiprimeD1StackChildGroupFactoryNativeStreams (scopeAt orderAt result_scopes result_orders)
end Streams
namespace C
export SemiprimeD1StackCalls (State run)
end C
namespace W
export SemiprimeD1StackChildGroupFactoryWiring (Label)
end W
namespace G
export SemiprimeD1StackChildGroupFactoryRoles (aux)
end G
/-- Exact native mask and both COMPLETE ordered scope/order streams at the real same-program halt. -/
theorem source_run_original (net:N.Network) (a:Nat)
    (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (header:R.Header)
    (hc:Meaning.CacheMeaning net a s p iv) (q:Fin a) (g:Fin 64)
    (hq:header.colourIndex=List.replicate q.val true) (hg:bitValue header.group=g.val):
    ∃t≤Res.runBound s p iv header,∃finish:C.State R.Stack W.Label,
      C.run R.program t (R.initial s p iv header)=some finish ∧
      finish.pc=none ∧ finish.flag=none ∧ finish.returned=none ∧ finish.frames=[] ∧
      finish.data (R.factory (G.aux .activation))=
        (SemiprimeD1ChildActivation.acquire net.leftCount net.rows.length 64 a (N.arity net.rows) (N.owner net.rows) q g).bits ∧
      finish.data (R.factory (G.aux .leftPorts))=SemiprimeD1TensorTapeCodec.vectorBits
        ((List.finRange (net.leftCount+net.rows.length)).map
          (Streams.scopeAt net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows) q g)) ∧
      finish.data (R.factory (G.aux .orders))=SemiprimeD1TensorTapeCodec.vectorBits
        ((List.finRange (net.leftCount+net.rows.length)).map
          (Streams.orderAt net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows) q g)) ∧
      (∀k,SemiprimeD1StackChildGroupFactoryReadyRetention.producer k=true→
        finish.data k=(R.initial s p iv header).data k) ∧
      (∀j:Fin 7,finish.data (SemiprimeD1StackChildGroupFactoryReady.allocation
        (G.aux (SemiprimeD1StackChildGroupFactoryReadyRetention.shadow j)))=[]):=by
  let input:=R.sourceInputs s p iv header
  have hv:=Meaning.valid_original net a s p iv header q hc hq
  have hcount:=Meaning.count_original net a s p iv header hc
  have hgroup:bitValue input.group=g.val:=hg
  obtain ⟨t,ht,finish,hr,hrel⟩:=Res.source_run s p iv header a q.val
    (A.originalIDs net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows))
    (Fld.source net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows)).state.packets
    (Fld.fields net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows)) hv
  have hstop:=SemiprimeD1StackChildGroupFactoryReadyExecution.stopped hrel
  refine ⟨t,ht,finish,hr,hstop.1,hstop.2.1,hstop.2.2.1,hstop.2.2.2,?_,?_,?_,?_,?_⟩
  · rw [hrel.1.1]
    exact A.result_original input net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows) q g _ _ hgroup
  · rw [hrel.1.1]
    exact Streams.result_scopes input net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows) q g hgroup hcount
  · rw [hrel.1.1]
    exact Streams.result_orders input net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows) q g hgroup hcount
  · intro k hk
    exact SemiprimeD1StackChildGroupFactoryReadyRetention.producer_retained s p iv header a q.val _ _ _ finish hrel k hk
  · intro j
    exact SemiprimeD1StackChildGroupFactoryReadyRetention.shadow_empty s p iv header a q.val _ _ _ finish hrel j
/-- The actual original-N reached root cache discharges ALL structural handoff obligations internally.
The displayed run begins at the honest ready cache, not an unimplemented enclosing N-only call. -/
theorem packed_root_source (bits:List Bool) (hN:0<bitValue bits) (header:R.Header)
    (q:Fin (SemiprimeD1StackRootSelectionAcquireEncoding.dimension bits)) (g:Fin 64)
    (hq:header.colourIndex=List.replicate q.val true) (hg:bitValue header.group=g.val):
    ∃t≤Res.runBound (Root.selectorWords bits hN) (Root.occurrenceWords bits hN) (Root.inventoryWords bits hN) header,
      ∃finish:C.State R.Stack W.Label,
      C.run R.program t (R.initial (Root.selectorWords bits hN) (Root.occurrenceWords bits hN) (Root.inventoryWords bits hN) header)=
        some finish ∧ finish.pc=none ∧ finish.frames=[]:=by
  obtain ⟨t,ht,finish,hr,hpc,_,_,hframes,_⟩:=source_run_original
    (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)
    (SemiprimeD1StackRootSelectionAcquireEncoding.dimension bits)
    (Root.selectorWords bits hN) (Root.occurrenceWords bits hN) (Root.inventoryWords bits hN) header
    (Root.cache_original bits hN) q g hq hg
  exact ⟨t,ht,finish,hr,hpc,hframes⟩
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOriginal
