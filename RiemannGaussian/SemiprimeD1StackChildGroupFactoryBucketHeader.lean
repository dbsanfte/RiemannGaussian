/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFields
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketRecord
/-! # Actual nested-bucket header scan at both literal port/order source sites
All three actual header fields are physically parsed. The packet and actual
unary right-port tape are physically drained before scanning child endpoints.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketHeader
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryFields SemiprimeD1StackProcedureTrace
open SemiprimeD1StackChildGroupFactoryBucketRecord (payload)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Two literal location families, with no runtime classification or mode input. -/
def pc (search:Bool) (slot:Fin 14):Label:=if search then match slot.val with
  | 0=>(.local 11 28)
  | 1=>(.local 11 29)
  | 2=>(.local 11 30)
  | 3=>(.local 11 31)
  | 4=>(.local 12 0)
  | 5=>(.local 12 1)
  | 6=>(.local 12 2)
  | 7=>(.local 12 3)
  | 8=>(.local 12 4)
  | 9=>(.local 12 5)
  | 10=>(.local 12 6)
  | 11=>(.local 12 7)
  | 12=>(.local 12 8)
  | 13=>(.local 12 9)
  | _=>(.local 12 9)
else match slot.val with
  | 0=>(.local 9 7)
  | 1=>(.local 9 8)
  | 2=>(.local 9 9)
  | 3=>(.local 9 10)
  | 4=>(.local 9 11)
  | 5=>(.local 9 12)
  | 6=>(.local 9 13)
  | 7=>(.local 9 14)
  | 8=>(.local 9 15)
  | 9=>(.local 9 16)
  | 10=>(.local 9 17)
  | 11=>(.local 9 18)
  | 12=>(.local 9 19)
  | 13=>(.local 9 20)
  | _=>(.local 9 20)
/-- All actual header outputs and both actual Field private roles are physically empty. -/
def cleanRoles:List Stack:=[aux .childReader,aux .packetKey,aux .endpointReader,aux .paddingKey,
  field (.inl .scratch),field (.inr ())]
/-- Exact retained outer suffix and acquired actual nested endpoint vector. -/
def result (before:Stack→List Bool) (children tail:List Bool):Stack→List Bool:=
  Function.update (Function.update before (aux .outerReader) tail) (aux .endpointReader) children
/-- Four actual Field calls with validity pops, tag/EOF, and both real header drains. -/
def timeBound (packet children ports:List Bool):Nat:=
  8*((payload packet children ports).length+packet.length+children.length+ports.length)+packet.length+ports.length+36
/-- Exact actual header acquisition and paid disposal at either real caller site. -/
theorem source_trace (search:Bool) (before:Stack→List Bool) (packet children ports tail:List Bool)
    (hi:before (aux .outerReader)=true::frame (payload packet children ports) tail)
    (hz:∀k∈cleanRoles,before k=[]):
    Runs program (timeBound packet children ports) (pc search 0) before (pc search 13) (result before children tail):=by
  have hz0:before (aux .childReader)=[]:=hz _ (by simp [cleanRoles])
  have hz1:before (aux .packetKey)=[]:=hz _ (by simp [cleanRoles])
  have hz2:before (aux .endpointReader)=[]:=hz _ (by simp [cleanRoles])
  have hz3:before (aux .paddingKey)=[]:=hz _ (by simp [cleanRoles])
  have hz4:before (field (.inl .scratch))=[]:=hz _ (by simp [cleanRoles])
  have hz5:before (field (.inr ()))=[]:=hz _ (by simp [cleanRoles])
  simp only [aux,field,payload] at hi hz0 hz1 hz2 hz3 hz4 hz5
  let b0:=before
  let b1:Stack→List Bool:=Function.update b0 (aux .outerReader) (frame (payload packet children ports) tail)
  have h0a:=pop_run (pc search 0) abort (pc search 1) (pc search 2) (aux .outerReader) b0
      (true::frame (payload packet children ports) tail) (by cases search <;> rfl) (by simp [b0,aux,payload,hi])
  have h0:Runs program 1 (pc search 0) b0 (pc search 2) b1:=by
    simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h0a
  let b2:Stack→List Bool:=Function.update (Function.update b1 (aux .outerReader) tail) (aux .childReader) (payload packet children ports)
  have h1:Runs program (8*((payload packet children ports)).length+8) (pc search 2) b1 (pc search 4) b2:=
    field_read 17 (pc search 2) (pc search 3) (pc search 4) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b1 (payload packet children ports) tail (by simp [b0,b1,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,aux,fieldStack,fieldPorts,payload,hz0]) (by simp [b0,b1,aux,field,payload,hz4]) (by simp [b0,b1,aux,field,payload,hz5])
  let b3:Stack→List Bool:=Function.update (Function.update b2 (aux .childReader) (frame children (frame ports []))) (aux .packetKey) packet
  have h2:Runs program (8*(packet).length+8) (pc search 4) b2 (pc search 6) b3:=
    field_read 6 (pc search 4) (pc search 5) (pc search 6) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b2 packet (frame children (frame ports [])) (by simp [b0,b1,b2,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,aux,fieldStack,fieldPorts,payload,hz1]) (by simp [b0,b1,b2,aux,field,payload,hz4]) (by simp [b0,b1,b2,aux,field,payload,hz5])
  let b4:Stack→List Bool:=Function.update (Function.update b3 (aux .childReader) (frame ports [])) (aux .endpointReader) children
  have h3:Runs program (8*(children).length+8) (pc search 6) b3 (pc search 8) b4:=
    field_read 18 (pc search 6) (pc search 7) (pc search 8) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b3 children (frame ports []) (by simp [b0,b1,b2,b3,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,aux,fieldStack,fieldPorts,payload,hz2]) (by simp [b0,b1,b2,b3,aux,field,payload,hz4]) (by simp [b0,b1,b2,b3,aux,field,payload,hz5])
  let b5:Stack→List Bool:=Function.update (Function.update b4 (aux .childReader) []) (aux .paddingKey) ports
  have h4:Runs program (8*(ports).length+8) (pc search 8) b4 (pc search 10) b5:=
    field_read 5 (pc search 8) (pc search 9) (pc search 10) abort abort
      (by cases search <;> rfl) (by cases search <;> rfl)
      b4 ports [] (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload]) (by simp [b0,b1,b2,b3,b4,aux,fieldStack,fieldPorts,payload,hz3]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz4]) (by simp [b0,b1,b2,b3,b4,aux,field,payload,hz5])
  have h5a:=peek_run (pc search 10) (pc search 11) abort abort (aux .childReader) b5 []
      (by cases search <;> rfl) (by simp [b0,b1,b2,b3,b4,b5,aux,payload])
  have h5:Runs program 1 (pc search 10) b5 (pc search 11) b5:=by
    simpa only [List.head?_nil,SemiprimeD1StackBytecode.choose] using h5a
  let b6:Stack→List Bool:=Function.update b5 (aux .packetKey) []
  have h6:Runs program (packet.length+1) (pc search 11) b5 (pc search 12) b6:=
    drain_loop (pc search 11) (pc search 12) (aux .packetKey) (by cases search <;> rfl) b5 packet (by simp [b0,b1,b2,b3,b4,b5,aux,payload])
  let b7:Stack→List Bool:=Function.update b6 (aux .paddingKey) []
  have h7:Runs program (ports.length+1) (pc search 12) b6 (pc search 13) b7:=
    drain_loop (pc search 12) (pc search 13) (aux .paddingKey) (by cases search <;> rfl) b6 ports (by simp [b0,b1,b2,b3,b4,b5,b6,aux,payload])
  have hout:b7=result before children tail:=by
    funext k
    rcases k with k|k|k|k|k|k
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,result]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,payload,hz0,hz1,hz3,result]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (h7)))))))
  rw [hout] at hwhole
  have ht:(1)+((8*((payload packet children ports)).length+8))+((8*(packet).length+8))+((8*(children).length+8))+((8*(ports).length+8))+(1)+((packet.length+1))+((ports.length+1))=timeBound packet children ports:=by dsimp only [timeBound];omega
  simpa only [←ht,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketHeader
