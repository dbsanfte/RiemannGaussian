/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireEncoding
import RiemannGaussian.SemiprimeD1StackPacketModeAcquirePrimitives
/-! # Physically consumed tile words and two actual marker pushes per byte
Doubling never inserts a computed natural result. It consumes the old real
tile word into a real reverse cursor and pushes two true markers for each byte.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquireDouble
open SemiprimeD1StackPacketModeAcquire SemiprimeD1StackPacketModeAcquireEncoding
open SemiprimeD1StackPacketModeAcquirePrimitives SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Actual whole44-role tile-loop boundary, with the untouched original fields retained. -/
def words (original order precision packets todo tiles scan:List Bool):Words:=
  {modes:=M.input packets tiles precision,packets:=original,order:=order,todo:=todo,tileScan:=scan}
/-- One actual true push changes exactly the next source's physical tile input. -/
theorem push_tile (pc next:Control) (hc:program (ctl pc)=.base (.push tileCount true (ctl next)))
    (original order precision packets todo scan:List Bool) (tiles:Nat) :
    Runs program 1 (ctl pc)
      (bank (words original order precision packets todo (List.replicate tiles true) scan)) (ctl next)
      (bank (words original order precision packets todo (List.replicate (tiles+1) true) scan)) :=by
  have h:=push_run pc (ctl next) tileCount true
    (bank (words original order precision packets todo (List.replicate tiles true) scan)) hc
  rw [show tileCount=modeStack tileRole from rfl,update_mode] at h
  dsimp only [words] at h
  rw [input_tile] at h
  exact h
/-- Every actual old tile byte is consumed and replaced by two true markers; EOF is charged too. -/
theorem fill_run (original order precision packets todo:List Bool) (count current:Nat) :
    Runs program (3*count+1) (ctl .tilePop)
      (bank (words original order precision packets todo (List.replicate current true) (List.replicate count true)))
      (ctl .orderLoop)
      (bank (words original order precision packets todo (List.replicate (current+2*count) true) [])) :=by
  induction count generalizing current with
  | zero=>
    have h:=pop_run .tilePop (ctl .orderLoop) (ctl .abort) (ctl .tilePushOne) (aux .tileScan)
      (bank (words original order precision packets todo (List.replicate current true) [])) [] rfl rfl
    rw [update_tileScan] at h
    exact h
  | succ count ih=>
    have h0:=pop_run .tilePop (ctl .orderLoop) (ctl .abort) (ctl .tilePushOne) (aux .tileScan)
      (bank (words original order precision packets todo (List.replicate current true) (List.replicate (count+1) true)))
      (true::List.replicate count true) rfl rfl
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
    rw [update_tileScan] at h0
    have h1:=push_tile .tilePushOne .tilePushTwo rfl original order precision packets todo
      (List.replicate count true) current
    have h2:=push_tile .tilePushTwo .tilePop rfl original order precision packets todo
      (List.replicate count true) (current+1)
    have h3:=ih (current+2)
    have h:=join (join (join h0 h1) h2) h3
    have he:current+2+2*count=current+2*(count+1):=by omega
    rw [he] at h
    convert h using 1
    omega
/-- A whole actual doubling includes reversal, its genuine call/return and every byte-loop transition. -/
theorem double_run (original order precision packets todo:List Bool) (tiles:Nat) :
    Runs program (5*tiles+4) (ctl .reverseTiles)
      (bank (words original order precision packets todo (List.replicate tiles true) [])) (ctl .orderLoop)
      (bank (words original order precision packets todo (List.replicate (2*tiles) true) [])) :=by
  have h0:=reverse_call .reverseTiles .tilePop rfl
    (bank (words original order precision packets todo (List.replicate tiles true) []))
    (List.replicate tiles true) [] rfl rfl
  simp only [List.length_replicate,List.reverse_replicate,List.append_nil] at h0
  change Runs program (2*tiles+3) _ _ _ (Function.update (Function.update
    (bank (words original order precision packets todo (List.replicate tiles true) [])) tileCount [])
      (aux .tileScan) (List.replicate tiles true)) at h0
  rw [show tileCount=modeStack tileRole from rfl,update_mode] at h0
  dsimp only [words] at h0
  rw [input_tile,update_tileScan] at h0
  have h1:=fill_run original order precision packets todo tiles 0
  simp only [Nat.zero_add] at h1
  have h:=join h0 h1
  change Runs program _ (ctl .reverseTiles)
    (bank (words original order precision packets todo (List.replicate tiles true) [])) (ctl .orderLoop)
    (bank (words original order precision packets todo (List.replicate (2*tiles) true) [])) at h
  convert h using 1
  omega
end RiemannGaussian.SemiprimeD1StackPacketModeAcquireDouble
