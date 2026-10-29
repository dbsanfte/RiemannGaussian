/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankCalls
import RiemannGaussian.SemiprimeD1StackCachePhaseBankBinding
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateEncoding
/-! # Four actual input words and exact original-order phase-bank output ABI
Requests describe literal issued-reference and child-field pairs in proofs.
No request object, bank answer, phase, function or mode list inhabits runtime.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankEncoding
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackJetFoldWords (Modes modeTape)
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace O
export SemiprimeD1StackCachePhaseRootOriginal (rootSource rootDone rootSize)
end O
namespace R
export SemiprimeD1StackRootPhaseFreshRecords (heap aux)
export SemiprimeD1StackRootPhaseFreshRecordsEncoding (result)
end R
namespace A
export SemiprimeD1StackFreshBankRestoreOriginal (reference)
end A
/-- Actual issued-phase ordinal paired with actual per-phase nested recursive-child bytes, proof notation ONLY. -/
abbrev Request (bits:List Bool):=Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length×Modes
/-- Actual framed stream of acquired allocator-issued reference WORDS; no ordinal is encoded during runtime. -/
def references (bits:List Bool) (requests:List (Request bits)):List Bool:=vectorBits (requests.map (fun r=>A.reference bits r.1))
/-- Actual framed stream of the corresponding physically retained per-phase child tapes. -/
def children {bits:List Bool} (requests:List (Request bits)):List Bool:=vectorBits (requests.map (fun r=>modeTape r.2))
/-- Actual byte payload acquired by ONE real238-role source; this is a proof-side projection, never an operand. -/
def payload (bits:List Bool) (r:Request bits):List Bool:=
  (O.rootDone bits r.1 r.2).data (SemiprimeD1StackCachePhase.blockStack (SemiprimeD1StackCachePhase.Blocks.aux .output))
/-- Exact output vector in original physical reference/child-pair order, including repeats/rejections. -/
def result (bits:List Bool) (requests:List (Request bits)):List Bool:=vectorBits (requests.map (payload bits))
/-- Physical four-word prepared source; original-N acquisition/recursive child production are separate upstream tasks. -/
def source (bits:List Bool) (requests:List (Request bits)):C.State Stack Label:=
  initial (R.result bits R.heap) (R.result bits (R.aux .counter)) (references bits requests) (children requests)
/-- Literal stopped bank from its immutable physical heap/counter only; all other238-role words are empty. -/
def base (bits:List Bool):P.Stack→List Bool:=P.input (R.result bits R.heap) (R.result bits (R.aux .counter)) [] []
/-- Exact full246-role successful halt, with final true status physically written only after scratch's last use. -/
def done (bits:List Bool) (requests:List (Request bits)):C.State Stack Label:=
  ⟨none,none,none,Function.update (data (base bits)
    (words {references:=references bits requests,children:=children requests,output:=result bits requests})) status [true],[]⟩
/-- Literal tagged payload chunk, before the final outer false sentinel. -/
def chunk (word:List Bool):List Bool:=SemiprimeD1StackRecoveryCoordinateEncoding.chunk word
end RiemannGaussian.SemiprimeD1StackCachePhaseBankEncoding
