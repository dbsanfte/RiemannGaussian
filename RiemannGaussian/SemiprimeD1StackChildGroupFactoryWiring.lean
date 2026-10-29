/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles
/-! # Fixed literal primitive wiring for the complete child group factory
Pages/offsets and site labels are fixed finite program locations only. They do
not encode any acquired vertex, colour coordinate, jet dimension or answer.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactoryRoles
/-- All38 actual fixed copy operand pairs, determined before every input. -/
def copyPorts (site:Fin 38):Stack×Stack:=match site.val with
  | 0=>(aux .owners,aux .vertexTodo)
  | 1=>(aux .factors,aux .vertexTodo)
  | 2=>(aux .vertexKey,lookup (.inr .query))
  | 3=>(aux .environment,lookup (.inr .reader))
  | 4=>(lookup (.inr .output),aux .selectedID)
  | 5=>(aux .selectedID,aux .jointKey)
  | 6=>(aux .jointKey,rows (.inr .key))
  | 7=>(aux .catalogue,rows (.inr .catalogue))
  | 8=>(rows (.inr .leftOutput),aux .colourReader)
  | 9=>(aux .colourIndex,aux .colourCursor)
  | 10=>(aux .colourWord,arithmetic .left)
  | 11=>(aux .group,arithmetic .right)
  | 12=>(aux .vertexKey,arithmetic .left)
  | 13=>(arithmetic .output,aux .vertexKey)
  | 14=>(aux .occurrences,aux .pairReader)
  | 15=>(aux .placements,aux .placementReader)
  | 16=>(aux .ownerKey,lookup (.inr .query))
  | 17=>(aux .activationMap,lookup (.inr .reader))
  | 18=>(aux .factorKey,lookup (.inr .query))
  | 19=>(aux .packets,aux .packetReader)
  | 20=>(aux .endpoints,aux .endpointReader)
  | 21=>(aux .sourceKey,arithmetic .left)
  | 22=>(aux .packetKey,arithmetic .right)
  | 23=>(aux .globalPosition,arithmetic .left)
  | 24=>(arithmetic .output,aux .globalPosition)
  | 25=>(aux .portBank,ordinal .bank)
  | 26=>(aux .buckets,aux .outerReader)
  | 27=>(aux .ownerKey,arithmetic .left)
  | 28=>(aux .vertexKey,arithmetic .right)
  | 29=>(aux .oldEndpoints,aux .oldReader)
  | 30=>(aux .sideWord,aux .tagWord)
  | 31=>(aux .sideWord,aux .candidateTag)
  | 32=>(aux .tagWord,arithmetic .left)
  | 33=>(aux .candidateTag,arithmetic .right)
  | 34=>(aux .localPosition,arithmetic .left)
  | 35=>(arithmetic .output,aux .localPosition)
  | 36=>(aux .localPosition,aux .answerPosition)
  | 37=>(aux .orderBank,ordinal .bank)
  | _=>(aux .owners,aux .vertexTodo)
/-- All25 actual fixed frame operand pairs, determined before every input. -/
def framePorts (site:Fin 25):Stack×Stack:=match site.val with
  | 0=>(aux .selectedID,aux .jointKey)
  | 1=>(aux .flagScratch,aux .activationMap)
  | 2=>(aux .vertexKey,aux .activationMap)
  | 3=>(aux .sideWord,aux .rowBuffer)
  | 4=>(aux .edgeWord,aux .rowBuffer)
  | 5=>(aux .ownerKey,aux .rowBuffer)
  | 6=>(aux .rowBuffer,aux .frameBuffer)
  | 7=>(aux .slotWord,aux .rowBuffer)
  | 8=>(aux .packetKey,aux .rowBuffer)
  | 9=>(aux .factorKey,aux .rowBuffer)
  | 10=>(aux .globalPosition,aux .rowBuffer)
  | 11=>(aux .sourceKey,aux .rowBuffer)
  | 12=>(aux .globalPosition,aux .frameBuffer)
  | 13=>(ordinal .output,aux .rowBuffer)
  | 14=>(aux .jointKey,aux .rowBuffer)
  | 15=>(ordinal .output,aux .frameBuffer)
  | 16=>(aux .edgeWord,aux .tagWord)
  | 17=>(aux .edgeWord,aux .candidateTag)
  | 18=>(aux .answerPosition,aux .frameBuffer)
  | 19=>(aux .oldEndpoints,aux .output)
  | 20=>(aux .orders,aux .output)
  | 21=>(aux .leftPorts,aux .output)
  | 22=>(aux .buckets,aux .output)
  | 23=>(aux .endpoints,aux .output)
  | 24=>(aux .activation,aux .output)
  | _=>(aux .selectedID,aux .jointKey)
/-- All16 actual fixed reverse operand pairs, determined before every input. -/
def reversePorts (site:Fin 16):Stack×Stack:=match site.val with
  | 0=>(aux .activationHistory,aux .activation)
  | 1=>(aux .frameBuffer,aux .oldHistory)
  | 2=>(aux .frameBuffer,aux .endpointHistory)
  | 3=>(aux .endpointHistory,aux .endpoints)
  | 4=>(aux .oldHistory,aux .oldEndpoints)
  | 5=>(aux .frameBuffer,aux .bucketHistory)
  | 6=>(aux .frameBuffer,aux .portHistory)
  | 7=>(aux .bucketHistory,aux .jointKey)
  | 8=>(aux .portHistory,aux .portBank)
  | 9=>(aux .frameBuffer,aux .factorHistory)
  | 10=>(aux .factorHistory,aux .buckets)
  | 11=>(aux .frameBuffer,aux .vertexHistory)
  | 12=>(aux .frameBuffer,aux .orderHistory)
  | 13=>(aux .orderHistory,aux .orderBank)
  | 14=>(aux .vertexHistory,aux .leftPorts)
  | 15=>(aux .factorHistory,aux .orders)
  | _=>(aux .activationHistory,aux .activation)
/-- All21 actual fixed field operand pairs, determined before every input. -/
def fieldPorts (site:Fin 21):Stack×Stack:=match site.val with
  | 0=>(aux .colourReader,aux .colourWord)
  | 1=>(aux .pairReader,aux .ownerKey)
  | 2=>(aux .pairReader,aux .factorKey)
  | 3=>(aux .placementReader,aux .childReader)
  | 4=>(aux .childReader,aux .sourceKey)
  | 5=>(aux .childReader,aux .paddingKey)
  | 6=>(aux .childReader,aux .packetKey)
  | 7=>(aux .childReader,aux .slotWord)
  | 8=>(aux .childReader,aux .edgeWord)
  | 9=>(aux .childReader,aux .validWord)
  | 10=>(aux .packetReader,aux .packetKey)
  | 11=>(aux .endpointReader,aux .rowBuffer)
  | 12=>(aux .rowBuffer,aux .ownerKey)
  | 13=>(aux .rowBuffer,aux .sourceKey)
  | 14=>(aux .rowBuffer,aux .slotWord)
  | 15=>(aux .rowBuffer,aux .edgeWord)
  | 16=>(aux .rowBuffer,aux .sideWord)
  | 17=>(aux .outerReader,aux .childReader)
  | 18=>(aux .childReader,aux .endpointReader)
  | 19=>(aux .rowBuffer,aux .globalPosition)
  | 20=>(aux .oldReader,aux .rowBuffer)
  | _=>(aux .colourReader,aux .colourWord)
/-- Every actual preserving copy restores its disjoint scratch. -/
def copyStack (site:Fin 38) (k:Fin 3):Stack:=
  if k=0 then (copyPorts site).1 else if k=1 then (copyPorts site).2 else aux .copyScratch
/-- Each physical preserving field-frame appends to its actual destination. -/
def frameStack (site:Fin 25) (k:Fin 3):Stack:=
  if k=0 then (framePorts site).1 else if k=1 then (framePorts site).2 else aux .copyScratch
/-- Every genuine reversal consumes its actual source. -/
def reverseStack (site:Fin 16) (k:Fin 2):Stack:=
  if k=0 then (reversePorts site).1 else (reversePorts site).2
/-- Redirected actual parser input/output leave both unused allocations counted. -/
def fieldStack (site:Fin 21):F.Stack→Stack
  | .inl .input=>(fieldPorts site).1
  | .inl .output=>(fieldPorts site).2
  | .inl .scratch=>field (.inl .scratch)
  | .inr () =>field (.inr ())
/-- Finite literal location and included procedure labels, independent of all words. -/
inductive Label where
  | local (page:Fin 16) (offset:Fin 32)
  | clear (aborted:Bool) (part:Fin 115)
  | lookup (pc:L.Label) | rows (pc:R.Label) | add (pc:A.Label) | equal (pc:E.Label)
  | field (site:Fin 21) (pc:F.Label)
  | ordinal (pc:O.Label)
  | copy (site:Fin 38) (pc:Fin 9)
  | frame (site:Fin 25) (pc:Fin 11)
  | reverse (site:Fin 16) (pc:Fin 4)
  deriving Fintype
/-- Actual fixed source entry. -/
def entry:Label:=(.local 0 0)
/-- Actual fixed successful status stage, reached only after physical cleanup. -/
def accept:Label:=(.local 15 15)
/-- Actual fixed rejection status stage, reached only after physical cleanup. -/
def reject:Label:=(.local 15 16)
/-- Actual failure target before the complete physical cleanup. -/
def abort:Label:=(.local 15 14)
/-- Cleanup advances only a bounded fixed port label; no data counter is inspected. -/
def nextClear (aborted:Bool) (part:Fin 115):Label:=
  if h:part.val+1<115 then .clear aborted ⟨part.val+1,h⟩ else if aborted then reject else accept
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryWiring
