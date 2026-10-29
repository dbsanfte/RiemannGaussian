/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsResources
/-! # Uniform whole-row charge includes retained source and growing actual heap/history -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
set_option exponentiation.threshold 4096
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsUniform
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsRows SemiprimeD1StackRootPhaseFreshRecordsResources
open SemiprimeSourceHistogramKeyBits (frame)
attribute [local irreducible] SemiprimeD1StackPhaseCacheFreshExecution.runBound
/-- Every allocated auxiliary address is bounded from the lengths of its actual seven data words. -/
theorem work_word (reader rec hp cn ref hist out:List Bool) (B:Nat)
    (h0:reader.length ≤ B) (h1:rec.length ≤ B) (h2:hp.length ≤ B) (h3:cn.length ≤ B)
    (h4:ref.length ≤ B) (h5:hist.length ≤ B) (h6:out.length ≤ B) (k:Aux) :
    (work reader rec hp cn ref hist out k).length ≤ B :=by
  cases k <;> first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact Nat.zero_le _
/-- Whole physical row has a cubic radius cap, including all345 cleanup words
and the growing immutable-input plus new-output heap banks. -/
theorem rowBound_le (root:R.Stack→List Bool) (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (i:Fin bs.length) (a u edges:Nat) (t tail hp:List Bool) (n:Nat) (hist:List Bool) (B:Nat)
    (hB:1 ≤ B) (hroot:∀k,(root k).length ≤ B)
    (hh:root R.heap=E.heap bs) (hc:root (R.aux .counter)=List.replicate bs.length true)
    (hb:bs[i.val]=SemiprimeD1StackPhaseCacheFreshComponents.phase a u edges t [false,true])
    (hresource:SemiprimeD1StackPhaseCacheFreshBounds.resource bs i a u edges t [false,true] [] ≤ B)
    (hi:i.val ≤ B) (hn:n ≤ B) (ht:tail.length ≤ 4*B^2+1)
    (hhp:hp.length ≤ 10^19*B^3) (hhist:hist.length ≤ 4*B^2) :
    rowBound root bs i a u edges t tail hp n hist ≤ 10^28*B^3 :=by
  let ptr:=List.replicate i.val true
  let got:=acquired root a u edges t ptr tail hp n hist
  let qdone:=stopped root a u edges t ptr
  let U:=10^20*B^3
  have b12:B ≤ B^2:=Nat.le_pow (by decide)
  have b23:B^2 ≤ B^3:=Nat.pow_le_pow_right hB (by decide)
  have b13:B ≤ B^3:=b12.trans b23
  have b3:1 ≤ B^3:=one_le_pow₀ hB
  have hU:B ≤ U:=by dsimp [U];omega
  have hq:∀k,(qdone k).length ≤ 10^15*B^2:=by
    intro k
    have he:(E.done bs i a u edges t [false,true] []).data=qdone:=by
      change SemiprimeD1StackPhaseCacheFreshComponents.completed _ _ _ _ _ _ _ _ _=_
      simp only [qdone,stopped,hh,hc,ptr]
    rw [←he]
    exact client_word bs i a u edges t B hB hresource hb k
  have hqU:∀k,(qdone k).length ≤ U:=by intro k;have h:=hq k;dsimp [U];omega
  have hrU:∀k,(root k).length ≤ U:=fun k=>(hroot k).trans hU
  have htail:tail.length ≤ U:=by dsimp [U];omega
  have hhpU:hp.length ≤ U:=by dsimp [U];omega
  have hnU:(List.replicate n true).length ≤ U:=by rw [List.length_replicate];omega
  have hhistU:hist.length ≤ U:=by dsimp [U];omega
  have hgot:∀k,(got k).length ≤ U:=view_word root qdone _ U hrU hqU
    (work_word tail [] hp (List.replicate n true) [] hist [] U htail (Nat.zero_le _) hhpU hnU
      (Nat.zero_le _) hhistU (Nat.zero_le _))
  have hrec: (record a u edges t).length ≤ 10^18*B^2:=row_record bs i a u edges t B hB hresource hb
  have hrecU:(record a u edges t).length ≤ U:=by dsimp [U];omega
  have hnewhp:(frame (record a u edges t) hp).length ≤ U:=by
    rw [SemiprimeSourceHistogramKeyBits.frame_length]
    dsimp [U]
    omega
  have hnewn:(List.replicate (n+1) true).length ≤ U:=by rw [List.length_replicate];dsimp [U];omega
  have hnewhist:(nextHistory n hist).length ≤ U:=by
    simp only [nextHistory,List.length_append,List.length_reverse,List.length_cons,
      SemiprimeSourceHistogramKeyBits.frame_length,List.length_replicate,List.length_nil]
    dsimp [U]
    omega
  have hlogged:∀k,(logged root a u edges t ptr tail hp n hist k).length ≤ U:=
    view_word root qdone _ U hrU hqU
      (work_word tail (record a u edges t) (frame (record a u edges t) hp) (List.replicate (n+1) true)
        (List.replicate n true) (nextHistory n hist) [] U htail hrecU hnewhp hnewn hnU hnewhist (Nat.zero_le _))
  have hm:=mass_le (logged root a u edges t ptr tail hp n hist) U hlogged
  have hs:=freshMass_le got U hgot
  have htime:=client_time bs i a u edges t B hB hresource
  unfold rowBound
  change 1000*(i.val+n+_+SemiprimeD1StackRootPhaseFreshRecordsSerialize.freshMass got+_+
    SemiprimeD1StackRootPhaseFreshRecordsCleanup.mass (logged root a u edges t ptr tail hp n hist)+1) ≤ _
  dsimp only [U] at hm hs
  omega
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsUniform
