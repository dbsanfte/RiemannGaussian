/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataProducts
/-! # Complete physically acquired h/q/r/delta phase metadata, without binary-P advice -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataStages
open SemiprimeD1StackPhaseWorkingPrecisionMetadata SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives
open SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic SemiprimeD1StackPhaseWorkingPrecisionMetadataProducts
open SemiprimeD1StackProcedureTrace
/-- Complete bounded metadata for the NEXT actual binary shift/add stage. -/
def completed (a u M : Nat) (t : List Bool) : Counts :=
  {height:=height M u,q:=blocks a u M t,r:=M*(a+1),delta:=a-order a t}
/-- Actual q/r/delta program uses only the acquired h/i cache and original a/u/M. -/
theorem source_run (a u M : Nat) (t p : List Bool) (ha : order a t<a) (hu : order a t<u) :
    ∃q≤1000*(M+a+u+1)^2,Runs program q .qCopyU
      (context a u M t p (SemiprimeD1StackPhaseWorkingPrecisionMetadataHeight.heightCounts M u))
      .done (context a u M t p (completed a u M t)) :=by
  let c0:=SemiprimeD1StackPhaseWorkingPrecisionMetadataHeight.heightCounts M u
  have h0:=copy_context a u M t p 3 c0 .qCopyU (.subtractCopy false) rfl
  change Runs program (5*u+4) _ _ _ (context a u M t p (subCounts false c0 u 0)) at h0
  have h1:=copy_subtract false a u M t p c0 u hu.le
  let c1:=subCounts false c0 (u-order a t) 0
  have h2:=copy_context a u M t p 5 c1 .qCopyH (.product false) rfl
  let c2:Counts:={c1 with multiplier:=height M u}
  change Runs program (5*height M u+4) _ _ _ (context a u M t p c2) at h2
  obtain ⟨b,hb,h3⟩:=product_run false a u M t p c2 rfl
  let c3:=productCounts false c2
  have h4:=clear_multiplicity false a u M t p c3
  let c4:Counts:={c3 with multiplicand:=0}
  have h5:=copy_context a u M t p 6 c4 .rCopyM .rCopyA rfl
  let c5:Counts:={c4 with multiplier:=M}
  change Runs program (5*M+4) _ _ _ (context a u M t p c5) at h5
  have h6:=copy_context a u M t p 7 c5 .rCopyA .plusOne rfl
  let c6:Counts:={c5 with multiplicand:=a}
  change Runs program (5*a+4) _ _ _ (context a u M t p c6) at h6
  have h7:=plus_one a u M t p c6
  let c7:Counts:={c6 with multiplicand:=a+1}
  obtain ⟨d,hd,h8⟩:=product_run true a u M t p c7 rfl
  let c8:=productCounts true c7
  have h9:=clear_multiplicity true a u M t p c8
  let c9:Counts:={c8 with multiplicand:=0}
  have h10:=copy_context a u M t p 8 c9 .deltaCopyA (.subtractCopy true) rfl
  change Runs program (5*a+4) _ _ _ (context a u M t p (subCounts true c9 a 0)) at h10
  have h11:=copy_subtract true a u M t p c9 a ha.le
  have hh:=join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
  change Runs program ((5*u+4)+(7*order a t+5)+(5*height M u+4)+b+
    (u-order a t+1)+(5*M+4)+(5*a+4)+1+d+(a+1+1)+(5*a+4)+(7*order a t+5))
    .qCopyU _ .done (context a u M t p (completed a u M t)) at hh
  refine ⟨_,?_,hh⟩
  change b≤5*(height M u*(2*(u-order a t)+3)+1)+1 at hb
  change d≤5*(M*(2*(a+1)+3)+1)+1 at hd
  let I:=M+a+u+1
  have hI:1≤ I:=by dsimp [I];omega
  have hM:M≤ I:=by dsimp [I];omega
  have haI:a≤ I:=by dsimp [I];omega
  have huI:u≤ I:=by dsimp [I];omega
  have hiI:order a t≤ I:=ha.le.trans haI
  have hHeight:height M u≤4*I:=by have h:=height_le M u;dsimp [I];omega
  have hpart:2*(u-order a t)+3≤5*I:=by omega
  have hprod:height M u*(2*(u-order a t)+3)≤20*I^2:=by
    calc
      _≤(4*I)*(5*I):=Nat.mul_le_mul hHeight hpart
      _=_:=by ring
  have hpart2:2*(a+1)+3≤7*I:=by omega
  have hprod2:M*(2*(a+1)+3)≤7*I^2:=by
    calc
      _≤ I*(7*I):=Nat.mul_le_mul hM hpart2
      _=_:=by ring
  have hb':b≤100*I^2+6:=by omega
  have hd':d≤35*I^2+6:=by omega
  have hsq:I≤ I^2:=by nlinarith
  change _≤1000*I^2
  omega
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataStages
