/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLookup
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationRows
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLog
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationCleanup
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationIncrement
/-! # Complete actual old-vertex activation iteration
One real lookup, true ID marker, real paired catalogue-row source, real
colour scan and equality, physical logging/cleanup, and actual binary increment.
All list/value arguments below describe the actual thirteen source words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationRow
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Lookup
export SemiprimeD1StackChildGroupFactoryActivationLookup (budget source_trace)
end Lookup
namespace Rows
export SemiprimeD1StackChildGroupFactoryActivationRows (budget source_trace)
end Rows
namespace Log
export SemiprimeD1StackChildGroupFactoryActivationLog (budget source_trace)
end Log
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryActivationCleanup (budget source_trace)
end Cleanup
namespace Increment
export SemiprimeD1StackChildGroupFactoryActivationIncrement (budget source_trace)
end Increment
/-- Sum of the same physical source-block clocks, including every cleanup and real return. -/
def timeBound (i:Inputs) (key selected unread:List Bool) (coordinate:Nat)
    (environment catalogue:List (List Bool×List Bool)) (colours:List (List Bool)):Nat:=
  Lookup.budget i key selected unread environment+Rows.budget i selected catalogue colours+
    Log.budget i key coordinate colours+Cleanup.budget i selected coordinate colours+Increment.budget key
/-- Whole literal activation iteration: no chosen ID, colour, flag or next key enters runtime control. -/
theorem source_trace (i:Inputs) (todo key hist map:List Bool) (coordinate:Nat)
    (environment catalogue:List (List Bool×List Bool)) (selected unread:List Bool)
    (colours:List (List Bool))
    (he:i.environment=SemiprimeD1StackOwnerLookup.records environment [])
    (hk:i.catalogue=SemiprimeD1StackOwnerLookup.records catalogue [])
    (hi:i.colourIndex=List.replicate coordinate true)
    (hget:SemiprimeD1StackOwnerLookup.result key environment []=(true::selected,unread))
    (hp:SemiprimeD1StackPacketRowsEncoding.present selected catalogue=true)
    (hr:SemiprimeD1StackPacketRowsAcquire.payload selected catalogue=SemiprimeD1PacketRows.serialize colours):
    ∃t≤timeBound i key selected unread coordinate environment catalogue colours,
      Runs program t (.local 0 4) (data i todo key hist map) (.local 0 3)
        (data i todo (SemiprimeBitArithmetic.addBits key [true] false).bits
          (active i coordinate colours::hist) (true::frame key (frame [active i coordinate colours] map))):=by
  obtain ⟨a,ha,h0⟩:=Lookup.source_trace i todo key hist map environment selected unread he hget
  obtain ⟨b,hb,h1⟩:=Rows.source_trace i todo key hist map coordinate catalogue selected colours hk hi hp hr
  obtain ⟨c,hc,h2⟩:=Log.source_trace i todo key hist map coordinate selected colours
  obtain ⟨d,hd,h3⟩:=Cleanup.source_trace i todo key hist map coordinate selected colours
  obtain ⟨e,he,h4⟩:=Increment.source_trace i todo key (active i coordinate colours::hist)
    (true::frame key (frame [active i coordinate colours] map))
  refine ⟨a+(b+(c+(d+e))),?_,join h0 (join h1 (join h2 (join h3 h4)))⟩
  dsimp only [timeBound]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationRow
