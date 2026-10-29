/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireEncoding
import RiemannGaussian.SemiprimeD1StackPacketModeAcquirePrimitives
/-! # Actual packet fields acquire the real catalogue packet-count operand
Empty raw packet keys still have actual vector entries and are counted once.
Every field byte, parser-valid pop, payload drain and count push is paid.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquireCount
open SemiprimeD1StackPacketModeAcquire SemiprimeD1StackPacketModeAcquireEncoding
open SemiprimeD1StackPacketModeAcquirePrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl"=>Label.local
/-- Full actual counting boundary; the natural count only describes physically pushed true markers. -/
def words (original order precision reader:List Bool) (count:Nat):Words:=
  {modes:=M.input (List.replicate count true) [] precision,packets:=original,order:=order,reader:=reader}
/-- One real vector entry parses and drains its raw field, then pushes exactly one packet marker. -/
theorem row_run (original order precision word:List Bool) (rest:List (List Bool)) (count:Nat) :
    Runs program (9*word.length+11) (ctl .packetTag)
      (bank (words original order precision (vectorBits (word::rest)) count)) (ctl .packetTag)
      (bank (words original order precision (vectorBits rest) (count+1))) :=by
  let w0:=words original order precision (vectorBits (word::rest)) count
  let w1:=words original order precision (frame word (vectorBits rest)) count
  have h0:=pop_run .packetTag (ctl .abort) (ctl .packetEnd) (ctl .field) (aux .reader)
    (bank w0) (true::frame word (vectorBits rest)) rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [update_reader] at h0
  have h1:=field_call .field .valid rfl (bank w1) word (vectorBits rest) rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (Function.update (bank w1)
    (aux .reader) (vectorBits rest)) (aux .payload) word) (aux .valid) [true]) at h1
  rw [update_reader,update_payload,update_valid] at h1
  let w2:Words:={w1 with reader:=vectorBits rest,payload:=word,valid:=[true]}
  have h2:=pop_run .valid (ctl .abort) (ctl .abort) (ctl .clearPayload) (aux .valid)
    (bank w2) [true] rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h2
  rw [update_valid] at h2
  let w3:Words:={w2 with valid:=[]}
  have h3:=drain_loop .clearPayload (ctl .countPacket) (aux .payload) rfl (bank w3) word rfl
  rw [update_payload] at h3
  change Runs program _ _ _ _ (bank (words original order precision (vectorBits rest) count)) at h3
  have h4:=push_run .countPacket (ctl .packetTag) packetCount true
    (bank (words original order precision (vectorBits rest) count)) rfl
  rw [show packetCount=modeStack packetRole from rfl,update_mode] at h4
  dsimp only [words] at h4
  rw [input_packet] at h4
  change Runs program 1 _ _ _ (bank (words original order precision (vectorBits rest) (count+1))) at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  convert h using 1
  omega
/-- The actual final false vector tag and actual EOF peek are both executed. -/
theorem nil_run (original order precision:List Bool) (count:Nat) :
    Runs program 2 (ctl .packetTag) (bank (words original order precision [false] count))
      (ctl .copyOrder) (bank (words original order precision [] count)) :=by
  have h0:=pop_run .packetTag (ctl .abort) (ctl .packetEnd) (ctl .field) (aux .reader)
    (bank (words original order precision [false] count)) [false] rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [update_reader] at h0
  have h1:=peek_run .packetEnd (ctl .copyOrder) (ctl .abort) (ctl .abort) (aux .reader)
    (bank (words original order precision [] count)) [] rfl rfl
  exact join h0 h1
/-- Exact actually executed packet-parser loop clock. -/
def countTime (packets:List (List Bool)):Nat:=(packets.map (fun word=>9*word.length+11)).sum+2
/-- Actual complete count loop preserves the original packets/order/WIDTH and acquires the real unary packet count. -/
theorem count_run (packets:List (List Bool)) (original order precision:List Bool) (count:Nat) :
    Runs program (countTime packets) (ctl .packetTag)
      (bank (words original order precision (vectorBits packets) count)) (ctl .copyOrder)
      (bank (words original order precision [] (count+packets.length))) :=by
  induction packets generalizing count with
  | nil=>simpa only [countTime,vectorBits,List.map_nil,List.sum_nil,List.length_nil,Nat.add_zero,Nat.zero_add] using
      nil_run original order precision count
  | cons word packets ih=>
    have h0:=row_run original order precision word packets count
    have h1:=ih (count+1)
    have h:=join h0 h1
    have he:count+1+packets.length=count+(word::packets).length:=by simp only [List.length_cons];omega
    rw [he] at h
    convert h using 1
    simp only [countTime,List.map_cons,List.sum_cons]
    omega
/-- First physical input copy is preserving, and every actual copied vector byte is charged. -/
theorem copy_input_run (packets order precision:List Bool) :
    Runs program (5*packets.length+4) (ctl .start) (initial packets order precision).data
      (ctl .packetTag) (bank (words packets order precision packets 0)) :=by
  rw [initial_bank]
  have h:=copy_call .packets .start .packetTag rfl
    (bank {modes:=M.input [] [] precision,packets:=packets,order:=order}) packets [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank _ ) (aux .reader) (packets++[])) at h
  rw [List.append_nil,update_reader] at h
  exact h
/-- Packet-vector acquisition and all real parser/count steps form one paid source prefix. -/
theorem source_count_run (packets:List (List Bool)) (order precision:List Bool) :
    Runs program (5*(vectorBits packets).length+4+countTime packets) (ctl .start)
      (initial (vectorBits packets) order precision).data (ctl .copyOrder)
      (bank (words (vectorBits packets) order precision [] packets.length)) :=by
  have h0:=copy_input_run (vectorBits packets) order precision
  have h1:=count_run packets (vectorBits packets) order precision 0
  simpa only [Nat.zero_add] using join h0 h1
end RiemannGaussian.SemiprimeD1StackPacketModeAcquireCount
