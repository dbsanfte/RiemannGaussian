/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSearchBounds
/-! # Whole actual first-index query, including paid unread-byte early cleanup
The stopped search bank is bounded from its SAME actual literal source trace.
Cleanup pays all eleven unread/current fields, even after the first hit. The
bound uses actual input bytes/visit counts and no child runtime polynomial.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagQueryBounds
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackProcedureTrace
namespace Q
export SemiprimeD1StackChildGroupFactoryTagSource
  (copied searched result timeBound source_trace)
end Q
namespace Loop
export SemiprimeD1StackChildGroupFactoryTagLoop (source_trace timeBound)
end Loop
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end B
namespace P
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end P
namespace H
export SemiprimeD1StackChildGroupFactoryBucketHeader (cleanRoles)
end H
namespace Complete
export SemiprimeD1StackChildGroupFactoryTagComplete (copied timeBound)
end Complete
namespace Early
export SemiprimeD1StackChildGroupFactoryTagEarlyClear (timeBound)
end Early
/-- Only actual data/readiness obligations of the fixed source are bundled. -/
structure Ready (before:Stack→List Bool) (buckets:List B.Bucket) (target tag position:List Bool):Prop where
  buckets:before (aux .buckets)=B.records buckets
  outer:before (aux .outerReader)=[]
  header:∀k∈H.cleanRoles,before k=[]
  parser:∀k∈P.cleanRoles,before k=[]
  target:before (aux .vertexKey)=target
  tag:before (aux .tagWord)=tag
  position:before (aux .localPosition)=position
  candidate:before (aux .candidateTag)=[]
  answer:before (aux .answerPosition)=[]
  frame:before (aux .frameBuffer)=[]
  scratch:before (aux .copyScratch)=[]
  arithmetic:∀k,before (arithmetic k)=[]
/-- This SAME executed search bounds each physical stopped word, including unread suffixes. -/
theorem searched_word_le (before:Stack→List Bool) (buckets:List B.Bucket) (target tag position:List Bool)
    (hr:Ready before buckets target tag position) (cap:Nat) (hcap:∀k,(before k).length≤cap):
    ∀k,(Q.searched before buckets target tag position k).length≤
      cap+(B.records buckets).length+Loop.timeBound buckets target tag position:=by
  have hcopy:∀k,(Q.copied before buckets k).length≤cap+(B.records buckets).length:=by
    intro k
    by_cases hk:k=aux .outerReader
    · subst k;simp only [Q.copied,Function.update_self];omega
    · simpa only [Q.copied,Function.update_of_ne hk] using (hcap k).trans (Nat.le_add_right cap _)
  have hrun:=Loop.source_trace buckets (Q.copied before buckets) target tag position rfl
    (by simpa [Q.copied,H.cleanRoles,aux,field] using hr.header)
    (by simpa [Q.copied,P.cleanRoles,aux,field] using hr.parser)
    (by simpa [Q.copied,aux] using hr.target) (by simpa [Q.copied,aux] using hr.tag)
    (by simpa [Q.copied,aux] using hr.position) (by simpa [Q.copied,aux] using hr.candidate)
    (by simpa [Q.copied,aux] using hr.scratch)
    (by intro k;simpa [Q.copied,aux,arithmetic] using hr.arithmetic k)
  let start:C.State Stack Label:=⟨some (.local 11 28),none,none,Q.copied before buckets,[]⟩
  obtain ⟨finish,hf,hat⟩:=hrun [] start ⟨rfl,rfl,rfl⟩
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program (Loop.timeBound buckets target tag position)
    (cap+(B.records buckets).length) start finish hcopy hf
  rw [hat.2.1] at hd
  exact hd
/-- All eleven actual early-stop drains are paid from the acquired stopped bank. -/
theorem early_time (before:Stack→List Bool) (position:List Bool) (cap:Nat) (hcap:∀k,(before k).length≤cap):
    Early.timeBound (Complete.copied before position)≤11*(cap+1):=by
  have h0:=hcap (aux .outerReader)
  have h1:=hcap (aux .childReader)
  have h2:=hcap (aux .endpointReader)
  have h3:=hcap (aux .rowBuffer)
  have h4:=hcap (aux .ownerKey)
  have h5:=hcap (aux .sourceKey)
  have h6:=hcap (aux .slotWord)
  have h7:=hcap (aux .edgeWord)
  have h8:=hcap (aux .sideWord)
  have h9:=hcap (aux .globalPosition)
  have h10:=hcap (aux .candidateTag)
  simp only [aux] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [Early.timeBound,Complete.copied,aux]
  omega
/-- Both actual hit and actual missing paths include result copy, real logger and all local drains. -/
theorem complete_time (found:Bool) (before:Stack→List Bool) (position tag:List Bool) (cap:Nat)
    (hcap:∀k,(before k).length≤cap):
    Complete.timeBound found before position tag≤100*(cap+position.length+tag.length+1):=by
  have he:=early_time before position cap hcap
  have hl:=SemiprimeD1StackChildGroupFactoryOperationBounds.word_log_time position
  cases found <;> simp only [Complete.timeBound,Bool.false_eq_true,ite_false,ite_true,
    SemiprimeD1StackChildGroupFactoryTagAnswer.timeBound] <;> omega
/-- Whole real query clock, charging every unread byte left by its actual early stop. -/
theorem timeBound_le (before:Stack→List Bool) (buckets:List B.Bucket) (target tag position:List Bool)
    (hr:Ready before buckets target tag position) (cap L:Nat) (hcap:∀k,(before k).length≤cap)
    (hp:position.length+2*(buckets.flatMap (fun b=>b.children)).length≤L):
    Q.timeBound before buckets target tag position≤
      1000*(cap+(B.records buckets).length+Loop.timeBound buckets target tag position+L+tag.length+1):=by
  have hs:=searched_word_le before buckets target tag position hr cap hcap
  have hc:=complete_time (SemiprimeD1StackChildGroupFactoryTagLoop.found buckets target tag)
    (Q.searched before buckets target tag position)
    (SemiprimeD1StackChildGroupFactoryTagLoopView.finalPosition buckets target tag position) tag
    (cap+(B.records buckets).length+Loop.timeBound buckets target tag position) hs
  have hl:=SemiprimeD1StackChildGroupFactoryOrderBounds.outer_length buckets target tag position
  dsimp only [Q.timeBound]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagQueryBounds
