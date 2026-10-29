/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyTrace
/-! # Actual retained258 entry through the complete core source
All115 actual core words are related at true halt and every physical word
outside the seven aliases/core work image retains its original bytes. This
executes the existing ready program with the EXACT core transition count.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyExecution
namespace R
export SemiprimeD1StackChildGroupFactoryReady
  (Stack factory factory_injective Header sourceInputs initial program initial_projection)
end R
namespace E
export SemiprimeD1StackChildGroupFactoryExecution (done timeBound source_run)
end E
namespace Main
export SemiprimeD1StackChildGroupFactory (input initial program)
end Main
namespace P
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
end P
open SemiprimeD1StackChildGroupFactoryReadyTrace
/-- Actual all258-role initial relation, including retained producers and all seven empty displaced inputs. -/
theorem initial_rel (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header):
    Rel R.factory (R.initial s p iv h).data (Main.initial (R.sourceInputs s p iv h)) (R.initial s p iv h):=by
  exact ⟨⟨R.initial_projection s p iv h,fun _ _=>rfl⟩,rfl,rfl,rfl,rfl⟩
/-- Whole ready source uses only actual retained producer/header bytes; no decoded output or clock operand. -/
theorem source_run (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header)
    (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hids:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (he:(R.sourceInputs s p iv h).environment=SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids)
    (hc:(R.sourceInputs s p iv h).catalogue=SemiprimeD1StackPacketRowsOriginal.catalogue a)
    (hi:(R.sourceInputs s p iv h).colourIndex=List.replicate coordinate true)
    (hlen:ids.length=(R.sourceInputs s p iv h).owners.length+(R.sourceInputs s p iv h).factors.length)
    (hpairs:(R.sourceInputs s p iv h).occurrences=SemiprimeD1StackChildGroupFactoryEndpointKeys.pairs fields)
    (hplacements:(R.sourceInputs s p iv h).placements=SemiprimeD1StackChildGroupFactoryEndpointKeys.placements fields)
    (hdom:∀f∈fields,SemiprimeBitArithmetic.bitValue f.owner < ids.length ∧
      SemiprimeBitArithmetic.bitValue f.factor < ids.length)
    (hpackets:(R.sourceInputs s p iv h).packets=SemiprimeD1TensorTapeCodec.vectorBits packets):
    ∃t≤E.timeBound (R.sourceInputs s p iv h) a coordinate ids packets fields,
      ∃finish,C.run R.program t (R.initial s p iv h)=some finish ∧
        Rel R.factory (R.initial s p iv h).data
          (E.done (R.sourceInputs s p iv h) a coordinate ids packets fields) finish:=by
  obtain ⟨t,ht,hr⟩:=E.source_run (R.sourceInputs s p iv h) a coordinate ids packets fields
    hids he hc hi hlen hpairs hplacements hdom hpackets
  obtain ⟨finish,hfinish,hrel⟩:=run_rel R.factory R.factory_injective (R.initial s p iv h).data
    Main.program R.program (fun _=>rfl) t (Main.initial (R.sourceInputs s p iv h))
    (E.done (R.sourceInputs s p iv h) a coordinate ids packets fields) (R.initial s p iv h)
    (initial_rel s p iv h) hr rfl
  exact ⟨t,ht,finish,hfinish,hrel⟩
/-- The actual transported final return sees EOF and genuinely halts with both flags clear. -/
theorem stopped {s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool}
    {p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool}
    {iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool} {h:R.Header}
    {a coordinate:Nat} {ids packets:List (List Bool)} {fields:List P.Fields}
    {finish:C.State R.Stack SemiprimeD1StackChildGroupFactoryWiring.Label}
    (hr:Rel R.factory (R.initial s p iv h).data
      (E.done (R.sourceInputs s p iv h) a coordinate ids packets fields) finish):
    finish.pc=none ∧ finish.flag=none ∧ finish.returned=none ∧ finish.frames=[]:=
  hr.2
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyExecution
