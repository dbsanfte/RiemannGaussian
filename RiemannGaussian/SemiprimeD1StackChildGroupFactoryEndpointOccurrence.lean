/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSide
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointCleanup
/-! # Whole actual paired-incidence endpoint acquisition
One real paired parse, the actual owner side BEFORE factor side, both actual
map lookups/conditional emissions, and all seven physical field drains.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOccurrence
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Parse
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields payload cleanRoles result timeBound source_trace)
end Parse
namespace Side
export SemiprimeD1StackChildGroupFactoryEndpointSide (result timeBound source_trace)
end Side
namespace Old
export SemiprimeD1StackChildGroupFactoryEndpointOldLog (vertex)
end Old
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryEndpointCleanup (role word pc result timeBound source_trace)
end Cleanup
open SemiprimeSourceHistogramKeyBits (frame)
/-- Complete physical bank after the real paired parse. -/
def parsedBank (before:Stack→List Bool) (f:Parse.Fields) (pairTail placementTail:List Bool):Stack→List Bool:=
  Parse.result before f pairTail placementTail
/-- The original owner side is acquired and logged before any factor side. -/
def ownerBank (flag:Bool) (before:Stack→List Bool) (f:Parse.Fields) (pairTail placementTail:List Bool):Stack→List Bool:=
  Side.result true flag (parsedBank before f pairTail placementTail) f.owner f.packet f.slot f.edge
/-- Both original side histories are retained after their real source calls. -/
def factorBank (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool):Stack→List Bool:=
  Side.result false factorFlag (ownerBank ownerFlag before f pairTail placementTail) f.factor f.packet f.slot f.edge
/-- Every field/private role is accounted for by the actual parser, side calls and seven real drains. -/
def result (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool):Stack→List Bool:=
  Cleanup.result (factorBank ownerFlag factorFlag before f pairTail placementTail)
/-- Same literal source-clock sum; flags here describe actual numeric map results only. -/
def timeBound (ownerFlag factorFlag:Bool) (f:Parse.Fields) (table ownerUnread factorUnread:List Bool)
    (entries:List (List Bool×List Bool)):Nat:=
  Parse.timeBound f+Side.timeBound true ownerFlag f.owner f.packet f.slot f.edge table ownerUnread entries+
    Side.timeBound false factorFlag f.factor f.packet f.slot f.edge table factorUnread entries+Cleanup.timeBound f
/-- Complete occurrence source advances both actual readers and preserves every other full-bank cache. -/
theorem source_trace (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail ownerUnread factorUnread:List Bool) (entries:List (List Bool×List Bool))
    (hpair:before (aux .pairReader)=true::frame f.owner (frame f.factor pairTail))
    (hplacement:before (aux .placementReader)=true::frame (Parse.payload f) placementTail)
    (hclean:∀k∈Parse.cleanRoles,before k=[])
    (hside:before (aux .sideWord)=[]) (hr:before (aux .rowBuffer)=[])
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (hl:∀k,before (lookup k)=[])
    (hm:before (aux .activationMap)=SemiprimeD1StackOwnerLookup.records entries [])
    (howner:SemiprimeD1StackOwnerLookup.result f.owner entries []=([ownerFlag],ownerUnread))
    (hfactor:SemiprimeD1StackOwnerLookup.result f.factor entries []=([factorFlag],factorUnread)):
    Runs program (timeBound ownerFlag factorFlag f (SemiprimeD1StackOwnerLookup.records entries [])
      ownerUnread factorUnread entries) (.local 2 20) before (.local 2 20)
      (result ownerFlag factorFlag before f pairTail placementTail):=by
  have h0:=Parse.source_trace before f pairTail placementTail hpair hplacement hclean
  change Runs program _ _ _ _ (parsedBank before f pairTail placementTail) at h0
  have ho:parsedBank before f pairTail placementTail (Old.vertex true)=f.owner:=rfl
  have hp:parsedBank before f pairTail placementTail (aux .packetKey)=f.packet:=rfl
  have hs:parsedBank before f pairTail placementTail (aux .slotWord)=f.slot:=rfl
  have he:parsedBank before f pairTail placementTail (aux .edgeWord)=f.edge:=rfl
  have hside':parsedBank before f pairTail placementTail (aux .sideWord)=[]:=by simpa [parsedBank,Parse.result,aux] using hside
  have hr':parsedBank before f pairTail placementTail (aux .rowBuffer)=[]:=by simpa [parsedBank,Parse.result,aux] using hr
  have hb':parsedBank before f pairTail placementTail (aux .frameBuffer)=[]:=by simpa [parsedBank,Parse.result,aux] using hb
  have hc':parsedBank before f pairTail placementTail (aux .copyScratch)=[]:=by simpa [parsedBank,Parse.result,aux] using hc
  have hl':∀k,parsedBank before f pairTail placementTail (lookup k)=[]:=by
    intro k;simpa [parsedBank,Parse.result,aux,lookup] using hl k
  have hm':parsedBank before f pairTail placementTail (aux .activationMap)=SemiprimeD1StackOwnerLookup.records entries []:=by
    simpa [parsedBank,Parse.result,aux] using hm
  have h1:=Side.source_trace true ownerFlag (parsedBank before f pairTail placementTail)
    f.owner f.packet f.slot f.edge ownerUnread entries ho hp hs he hside' hr' hb' hc' hl' hm' howner
  change Runs program _ _ _ _ (ownerBank ownerFlag before f pairTail placementTail) at h1
  have hfo:ownerBank ownerFlag before f pairTail placementTail (Old.vertex false)=f.factor:=by cases ownerFlag <;> rfl
  have hfp:ownerBank ownerFlag before f pairTail placementTail (aux .packetKey)=f.packet:=by cases ownerFlag <;> rfl
  have hfs:ownerBank ownerFlag before f pairTail placementTail (aux .slotWord)=f.slot:=by cases ownerFlag <;> rfl
  have hfe:ownerBank ownerFlag before f pairTail placementTail (aux .edgeWord)=f.edge:=by cases ownerFlag <;> rfl
  have hfside:ownerBank ownerFlag before f pairTail placementTail (aux .sideWord)=[]:=by
    cases ownerFlag <;> simpa [ownerBank,Side.result,aux] using hside'
  have hfr:ownerBank ownerFlag before f pairTail placementTail (aux .rowBuffer)=[]:=by
    cases ownerFlag <;> simpa [ownerBank,Side.result,aux] using hr'
  have hfb:ownerBank ownerFlag before f pairTail placementTail (aux .frameBuffer)=[]:=by
    cases ownerFlag <;> simpa [ownerBank,Side.result,aux] using hb'
  have hfc:ownerBank ownerFlag before f pairTail placementTail (aux .copyScratch)=[]:=by
    cases ownerFlag <;> simpa [ownerBank,Side.result,aux] using hc'
  have hfl:∀k,ownerBank ownerFlag before f pairTail placementTail (lookup k)=[]:=by
    intro k;cases ownerFlag <;> simpa [ownerBank,Side.result,aux,lookup] using hl' k
  have hfm:ownerBank ownerFlag before f pairTail placementTail (aux .activationMap)=SemiprimeD1StackOwnerLookup.records entries []:=by
    cases ownerFlag <;> simpa [ownerBank,Side.result,aux] using hm'
  have h2:=Side.source_trace false factorFlag (ownerBank ownerFlag before f pairTail placementTail)
    f.factor f.packet f.slot f.edge factorUnread entries hfo hfp hfs hfe hfside hfr hfb hfc hfl hfm hfactor
  change Runs program _ _ _ _ (factorBank ownerFlag factorFlag before f pairTail placementTail) at h2
  have hfields:∀j,factorBank ownerFlag factorFlag before f pairTail placementTail (Cleanup.role j)=Cleanup.word f j:=by
    intro j;fin_cases j <;> cases ownerFlag <;> cases factorFlag <;> rfl
  have h3:=Cleanup.source_trace (factorBank ownerFlag factorFlag before f pairTail placementTail) f hfields
  have hwhole:=join h0 (join h1 (join h2 h3))
  simpa only [timeBound,result,Cleanup.pc,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOccurrence
