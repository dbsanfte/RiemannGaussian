/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroBitNetwork

/-!
# Concrete producer/consumer macro graph

The port constructors below are the actual ordered word roles of the compiler,
not an arbitrary enumeration of endpoint fibres. Source and target axis
permutations are explicit finite equivalences.
-/
namespace RiemannGaussian.SemiprimeMacroGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open SemiprimeMacroBitNetwork SemiprimeBooleanNetwork

/-- The two forward transforms and the inverse transform. -/
abbrev Transform := Fin 2 ⊕ Unit

/-- Literal source ordering `j=j1+r*j2`. -/
def inputIndex (r t : ℕ) : (Fin r×Fin t) ≃ Fin (r*t) :=
  (Equiv.prodComm (Fin r) (Fin t)).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm t r)))

/-- Literal output ordering `k=k2+t*k1`. -/
def outputIndex (r t : ℕ) : (Fin r×Fin t) ≃ Fin (r*t) := finProdFinEquiv

/-- Actual word-producing signals of the full three-transform compiler. -/
inductive WordSignal (r t : ℕ)
  | input : Fin 2→Fin (r*t)→WordSignal r t
  | first : Transform→Fin r→Fin t→WordSignal r t
  | twiddle : Transform→Fin r→Fin t→WordSignal r t
  | second : Transform→Fin t→Fin r→WordSignal r t
  | product : Fin (r*t)→WordSignal r t
  | carry : Fin (r*t+1)→WordSignal r t
  deriving DecidableEq,Fintype

/-- Actual local word roles at every arithmetic vertex, retaining ordered
input/output positions instead of enumerating a cardinality fibre. -/
inductive WordPort (r t : ℕ)
  | inputOut : Fin 2→Fin (r*t)→WordPort r t
  | firstIn : Transform→Fin r→Fin t→WordPort r t
  | firstOut : Transform→Fin r→Fin t→WordPort r t
  | scaleIn : Transform→Fin r→Fin t→WordPort r t
  | scaleOut : Transform→Fin r→Fin t→WordPort r t
  | secondIn : Transform→Fin t→Fin r→WordPort r t
  | secondOut : Transform→Fin t→Fin r→WordPort r t
  | productIn : Fin 2→Fin (r*t)→WordPort r t
  | productOut : Fin (r*t)→WordPort r t
  | carryInitial : WordPort r t
  | carryCoefficient : Fin (r*t)→WordPort r t
  | carryPrevious : Fin (r*t)→WordPort r t
  | carryOut : Fin (r*t)→WordPort r t
  | carryTerminal : WordPort r t
  deriving DecidableEq,Fintype

/-- The actual unique producer role of each word signal. -/
def producer {r t : ℕ} : WordSignal r t→WordPort r t
  | .input side i => .inputOut side i
  | .first transform j₁ k₂ => .firstOut transform j₁ k₂
  | .twiddle transform j₁ k₂ => .scaleOut transform j₁ k₂
  | .second transform k₂ k₁ => .secondOut transform k₂ k₁
  | .product k => .productOut k
  | .carry k => if h : k.val=0 then .carryInitial else
      .carryOut ⟨k.val-1,by have := k.isLt;omega⟩

/-- The actual unique consumer role of each word signal. -/
def consumer {r t : ℕ} : WordSignal r t→WordPort r t
  | .input side i =>
      let axes := (inputIndex r t).symm i
      .firstIn (.inl side) axes.1 axes.2
  | .first transform j₁ k₂ => .scaleIn transform j₁ k₂
  | .twiddle transform j₁ k₂ => .secondIn transform k₂ j₁
  | .second (.inl side) k₂ k₁ => .productIn side (outputIndex r t (k₁,k₂))
  | .second (.inr _) k₂ k₁ => .carryCoefficient (outputIndex r t (k₁,k₂))
  | .product k =>
      let axes := (inputIndex r t).symm k
      .firstIn (.inr ()) axes.1 axes.2
  | .carry k => if h : k.val<r*t then .carryPrevious ⟨k.val,h⟩ else .carryTerminal

/-- Every concrete vertex word role identifies its precise signal and host
side: false is the producer, true the consumer. -/
def portSignal {r t : ℕ} : WordPort r t→WordSignal r t×Bool
  | .inputOut side i => (.input side i,false)
  | .firstIn (.inl side) j₁ j₂ => (.input side (inputIndex r t (j₁,j₂)),true)
  | .firstIn (.inr _) j₁ j₂ => (.product (inputIndex r t (j₁,j₂)),true)
  | .firstOut transform j₁ k₂ => (.first transform j₁ k₂,false)
  | .scaleIn transform j₁ k₂ => (.first transform j₁ k₂,true)
  | .scaleOut transform j₁ k₂ => (.twiddle transform j₁ k₂,false)
  | .secondIn transform k₂ j₁ => (.twiddle transform j₁ k₂,true)
  | .secondOut transform k₂ k₁ => (.second transform k₂ k₁,false)
  | .productIn side k =>
      let axes := (outputIndex r t).symm k
      (.second (.inl side) axes.2 axes.1,true)
  | .productOut k => (.product k,false)
  | .carryInitial => (.carry ⟨0,by omega⟩,false)
  | .carryCoefficient k =>
      let axes := (outputIndex r t).symm k
      (.second (.inr ()) axes.2 axes.1,true)
  | .carryPrevious k => (.carry ⟨k.val,by have := k.isLt;omega⟩,true)
  | .carryOut k => (.carry ⟨k.val+1,by have := k.isLt;omega⟩,false)
  | .carryTerminal => (.carry ⟨r*t,by omega⟩,true)

/-- The concrete producer/consumer endpoint function. -/
def endpoint {r t : ℕ} (e : WordSignal r t×Bool) : WordPort r t :=
  if e.2 then consumer e.1 else producer e.1

/-- Producer roles recover the same signal, including initial/noninitial carries. -/
theorem port_producer {r t : ℕ} (signal : WordSignal r t) :
    portSignal (producer signal)=(signal,false) := by
  cases signal with
  | input side i => rfl
  | first transform j₁ k₂ => rfl
  | twiddle transform j₁ k₂ => rfl
  | second transform k₂ k₁ => rfl
  | product k => rfl
  | carry k =>
    simp only [producer]
    split_ifs with h
    · simp only [portSignal,Prod.mk.injEq,and_true,WordSignal.carry.injEq]
      apply Fin.ext
      exact h.symm
    · simp only [portSignal,Prod.mk.injEq,and_true,WordSignal.carry.injEq]
      apply Fin.ext
      change k.val-1+1=k.val
      omega

/-- Consumer roles recover the same signal through both actual axis permutations. -/
theorem port_consumer {r t : ℕ} (signal : WordSignal r t) :
    portSignal (consumer signal)=(signal,true) := by
  cases signal with
  | input side i => simp [consumer,portSignal]
  | first transform j₁ k₂ => rfl
  | twiddle transform j₁ k₂ => rfl
  | second transform k₂ k₁ =>
    cases transform with
    | inl side => simp [consumer,portSignal]
    | inr u => cases u; simp [consumer,portSignal]
  | product k => simp [consumer,portSignal]
  | carry k =>
    simp only [consumer]
    split_ifs with h
    · rfl
    · simp only [portSignal,Prod.mk.injEq,and_true,WordSignal.carry.injEq]
      apply Fin.ext
      change r*t=k.val
      have := k.isLt
      omega

/-- Every real vertex word role is hit by exactly its indicated endpoint. -/
theorem endpoint_port {r t : ℕ} (port : WordPort r t) : endpoint (portSignal port)=port := by
  cases port with
  | firstIn transform j₁ j₂ => cases transform <;> simp [portSignal,endpoint,consumer]
  | productIn side k => simp [portSignal,endpoint,consumer]
  | carryCoefficient k => simp [portSignal,endpoint,consumer]
  | carryInitial => simp [portSignal,endpoint,producer]
  | carryPrevious k => simp [portSignal,endpoint,consumer,k.isLt]
  | carryOut k =>
    simp only [portSignal,endpoint,Bool.false_eq_true,↓reduceIte,producer]
    rw [dite_eq_right (by omega)]
    congr
  | carryTerminal => simp [portSignal,endpoint,consumer]
  | _ => rfl

/-- Exact concrete endpoint bijection for every word role of the full compiler.
It proves ownership, not just equality of two cardinalities. -/
def wordEndpointEquiv (r t : ℕ) : (WordSignal r t×Bool) ≃ WordPort r t where
  toFun := endpoint
  invFun := portSignal
  left_inv e := by
    rcases e with ⟨signal,side⟩
    cases side
    · exact port_producer signal
    · exact port_consumer signal
  right_inv := endpoint_port

/-- Actual digit flags and non-initial OR outputs. -/
inductive FlagSignal (digits : ℕ)
  | digit : Fin 2→Fin digits→FlagSignal digits
  | orOut : Fin 2→Fin (digits-1)→FlagSignal digits
  deriving DecidableEq,Fintype

/-- Ordered one-bit roles of actual source, OR and terminal check vertices. -/
inductive FlagPort (digits : ℕ)
  | digitOut : Fin 2→Fin digits→FlagPort digits
  | orPrevious : Fin 2→Fin (digits-1)→FlagPort digits
  | orNew : Fin 2→Fin (digits-1)→FlagPort digits
  | orOut : Fin 2→Fin (digits-1)→FlagPort digits
  | terminal : Fin 2→FlagPort digits
  deriving DecidableEq,Fintype

/-- Actual flag producers, with no hidden copying. -/
def flagProducer {digits : ℕ} : FlagSignal digits→FlagPort digits
  | .digit side i => .digitOut side i
  | .orOut side i => .orOut side i

/-- Actual single consumers of every source/OR flag, including digits=1. -/
def flagConsumer {digits : ℕ} (hdigits : 0<digits) : FlagSignal digits→FlagPort digits
  | .digit side i => if hi : i.val=0 then
      if hd : digits=1 then .terminal side else .orPrevious side ⟨0,by omega⟩
      else .orNew side ⟨i.val-1,by have := i.isLt;omega⟩
  | .orOut side i => if hi : i.val+1<digits-1 then
      .orPrevious side ⟨i.val+1,hi⟩ else .terminal side

/-- Each literal flag port identifies the corresponding signal and endpoint. -/
def flagPortSignal {digits : ℕ} (hdigits : 0<digits) : FlagPort digits→FlagSignal digits×Bool
  | .digitOut side i => (.digit side i,false)
  | .orPrevious side i => if hi : i.val=0 then (.digit side ⟨0,hdigits⟩,true)
      else (.orOut side ⟨i.val-1,by have := i.isLt;omega⟩,true)
  | .orNew side i => (.digit side ⟨i.val+1,by have := i.isLt;omega⟩,true)
  | .orOut side i => (.orOut side i,false)
  | .terminal side => if hd : digits=1 then (.digit side ⟨0,hdigits⟩,true)
      else (.orOut side ⟨digits-2,by omega⟩,true)

/-- The exact producer/consumer flag endpoint function. -/
def flagEndpoint {digits : ℕ} (hdigits : 0<digits) (e : FlagSignal digits×Bool) : FlagPort digits :=
  if e.2 then flagConsumer hdigits e.1 else flagProducer e.1

/-- Producer-side identification is literal. -/
theorem flag_port_producer {digits : ℕ} (hdigits : 0<digits) (signal : FlagSignal digits) :
    flagPortSignal hdigits (flagProducer signal)=(signal,false) := by
  cases signal <;> rfl

/-- Every flag consumer identifies exactly its source, including both chain ends. -/
theorem flag_port_consumer {digits : ℕ} (hdigits : 0<digits) (signal : FlagSignal digits) :
    flagPortSignal hdigits (flagConsumer hdigits signal)=(signal,true) := by
  cases signal with
  | digit side i =>
    simp only [flagConsumer]
    split_ifs with hi hd
    · simp only [flagPortSignal,hd,↓reduceDIte,Prod.mk.injEq,and_true,FlagSignal.digit.injEq,
        true_and]
      apply Fin.ext
      exact hi.symm
    · simp only [flagPortSignal,↓reduceDIte,Prod.mk.injEq,and_true,FlagSignal.digit.injEq,
        true_and]
      apply Fin.ext
      exact hi.symm
    · simp only [flagPortSignal,Prod.mk.injEq,and_true,FlagSignal.digit.injEq,true_and]
      apply Fin.ext
      change i.val-1+1=i.val
      omega
  | orOut side i =>
    simp only [flagConsumer]
    split_ifs with hi
    · simp only [flagPortSignal]
      rw [dite_eq_right (by omega)]
      simp only [Prod.mk.injEq,and_true,FlagSignal.orOut.injEq,true_and]
      apply Fin.ext
      change i.val+1-1=i.val
      omega
    · simp only [flagPortSignal]
      rw [dite_eq_right (by have := i.isLt;omega)]
      simp only [Prod.mk.injEq,and_true,FlagSignal.orOut.injEq,true_and]
      apply Fin.ext
      change digits-2=i.val
      have := i.isLt
      omega

/-- Every actual flag vertex port is reached by the identified endpoint. -/
theorem flag_endpoint_port {digits : ℕ} (hdigits : 0<digits) (port : FlagPort digits) :
    flagEndpoint hdigits (flagPortSignal hdigits port)=port := by
  cases port with
  | digitOut side i => rfl
  | orOut side i => rfl
  | orPrevious side i =>
    simp only [flagPortSignal]
    split_ifs with hi
    · simp only [flagEndpoint,↓reduceIte,flagConsumer,↓reduceDIte]
      rw [dite_eq_right (by have := i.isLt;omega)]
      congr <;> exact hi.symm
    · simp only [flagEndpoint,↓reduceIte,flagConsumer]
      rw [dite_eq_left (by have := i.isLt;omega)]
      congr
      omega
  | orNew side i =>
    simp only [flagPortSignal,flagEndpoint,↓reduceIte,flagConsumer]
    rw [dite_eq_right (by omega)]
    congr
  | terminal side =>
    simp only [flagPortSignal]
    split_ifs with hd
    · simp [flagEndpoint,flagConsumer,hd]
    · simp only [flagEndpoint,↓reduceIte,flagConsumer]
      rw [dite_eq_right (by omega)]

/-- Exact ownership bijection of the entire actual one-bit flag wiring. -/
def flagEndpointEquiv (digits : ℕ) (hdigits : 0<digits) :
    (FlagSignal digits×Bool) ≃ FlagPort digits where
  toFun := flagEndpoint hdigits
  invFun := flagPortSignal hdigits
  left_inv e := by
    rcases e with ⟨signal,side⟩
    cases side
    · exact flag_port_producer hdigits signal
    · exact flag_port_consumer hdigits signal
  right_inv := flag_endpoint_port hdigits

/-- Every actual physical word bit and one-bit flag signal. -/
abbrev BitSignal (r t digits : ℕ) := (WordSignal r t×Fin (r*t+1)) ⊕ FlagSignal digits

/-- Every actual arithmetic word-bit role and one-bit flag vertex role. -/
abbrev BitPort (r t digits : ℕ) := (WordPort r t×Fin (r*t+1)) ⊕ FlagPort digits

/-- Actual complete physical bit endpoint map, preserving each bit position. -/
def bitEndpoint {r t digits : ℕ} (hdigits : 0<digits) :
    (BitSignal r t digits×Bool)→BitPort r t digits
  | (.inl (signal,bit),side) => .inl (endpoint (signal,side),bit)
  | (.inr signal,side) => .inr (flagEndpoint hdigits (signal,side))

/-- Identify the signal and endpoint of every complete physical bit port. -/
def bitPortSignal {r t digits : ℕ} (hdigits : 0<digits) :
    BitPort r t digits→BitSignal r t digits×Bool
  | .inl (port,bit) => (.inl ((portSignal port).1,bit),(portSignal port).2)
  | .inr port => (.inr (flagPortSignal hdigits port).1,(flagPortSignal hdigits port).2)

/-- Exact complete graph endpoint bijection: not a signal-only cardinality count. -/
def bitEndpointEquiv (r t digits : ℕ) (hdigits : 0<digits) :
    (BitSignal r t digits×Bool) ≃ BitPort r t digits where
  toFun := bitEndpoint hdigits
  invFun := bitPortSignal hdigits
  left_inv e := by
    rcases e with ⟨signal,side⟩
    cases signal with
    | inl signal =>
      rcases signal with ⟨signal,bit⟩
      have he := (wordEndpointEquiv r t).left_inv (signal,side)
      simpa only [bitEndpoint,bitPortSignal,wordEndpointEquiv] using congrArg
        (fun e : WordSignal r t×Bool => ((Sum.inl (e.1,bit) : BitSignal r t digits),e.2)) he
    | inr signal =>
      have he := (flagEndpointEquiv digits hdigits).left_inv (signal,side)
      simpa only [bitEndpoint,bitPortSignal,flagEndpointEquiv] using congrArg
        (fun e : FlagSignal digits×Bool => ((Sum.inr e.1 : BitSignal r t digits),e.2)) he
  right_inv port := by
    cases port with
    | inl port =>
      rcases port with ⟨port,bit⟩
      have he := (wordEndpointEquiv r t).right_inv port
      simpa only [bitEndpoint,bitPortSignal,Prod.eta,wordEndpointEquiv] using congrArg
        (fun p : WordPort r t => (Sum.inl (p,bit) : BitPort r t digits)) he
    | inr port =>
      have he := (flagEndpointEquiv digits hdigits).right_inv port
      simpa only [bitEndpoint,bitPortSignal,Prod.eta,flagEndpointEquiv] using congrArg
        (fun p : FlagPort digits => (Sum.inr p : BitPort r t digits)) he

/-- Explicit sum decomposition of the actual word tags, used only to count
these already-wired signal constructors. -/
def wordSignalSumEquiv (r t : ℕ) : WordSignal r t ≃
    ((Fin 2×Fin (r*t)) ⊕ (Transform×Fin r×Fin t) ⊕
      (Transform×Fin r×Fin t) ⊕ (Transform×Fin t×Fin r) ⊕ Fin (r*t) ⊕ Fin (r*t+1)) where
  toFun
    | .input side i => .inl (side,i)
    | .first tr j k => .inr (.inl (tr,j,k))
    | .twiddle tr j k => .inr (.inr (.inl (tr,j,k)))
    | .second tr k j => .inr (.inr (.inr (.inl (tr,k,j))))
    | .product k => .inr (.inr (.inr (.inr (.inl k))))
    | .carry k => .inr (.inr (.inr (.inr (.inr k))))
  invFun
    | .inl (side,i) => .input side i
    | .inr (.inl (tr,j,k)) => .first tr j k
    | .inr (.inr (.inl (tr,j,k))) => .twiddle tr j k
    | .inr (.inr (.inr (.inl (tr,k,j)))) => .second tr k j
    | .inr (.inr (.inr (.inr (.inl k)))) => .product k
    | .inr (.inr (.inr (.inr (.inr k)))) => .carry k
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨a,b⟩|⟨tr,j,k⟩|⟨tr,j,k⟩|⟨tr,k,j⟩|k|k <;> rfl

/-- Explicit decomposition of actual flag tags. -/
def flagSignalSumEquiv (digits : ℕ) : FlagSignal digits ≃
    ((Fin 2×Fin digits) ⊕ (Fin 2×Fin (digits-1))) where
  toFun
    | .digit side i => .inl (side,i)
    | .orOut side i => .inr (side,i)
  invFun
    | .inl (side,i) => .digit side i
    | .inr (side,i) => .orOut side i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨side,i⟩|⟨side,i⟩ <;> rfl

/-- Count of the actual, explicitly wired word signals. -/
theorem word_signal_card (r t : ℕ) : Fintype.card (WordSignal r t)=13*(r*t)+1 := by
  rw [Fintype.card_congr (wordSignalSumEquiv r t)]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Transform,Fintype.card_unit]
  ring

/-- Count of the actual flag signals; the one-digit boundary case is included. -/
theorem flag_signal_card (digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (FlagSignal digits)=4*digits-2 := by
  rw [Fintype.card_congr (flagSignalSumEquiv digits)]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

/-- Actual wired bit signals have the compiler's exact source count. -/
theorem bit_signal_card (r t digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (BitSignal r t digits)=(13*(r*t)+1)*(r*t+1)+4*digits-2 := by
  change Fintype.card ((WordSignal r t×Fin (r*t+1)) ⊕ FlagSignal digits)=_
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,word_signal_card,flag_signal_card digits hdigits]
  omega

/-- Every actual physical bit port is one of precisely two endpoints per signal. -/
theorem bit_port_card (r t digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (BitPort r t digits)=2*((13*(r*t)+1)*(r*t+1)+4*digits-2) := by
  rw [←Fintype.card_congr (bitEndpointEquiv r t digits hdigits),Fintype.card_prod,
    Fintype.card_bool,bit_signal_card r t digits hdigits]
  omega

/-- The complete actual original vertex family, including shared input
word/flag vertices and all terminal checks. -/
inductive Vertex (r t digits : ℕ)
  | input : Fin 2→Fin (r*t)→Vertex r t digits
  | first : Transform→Fin r→Vertex r t digits
  | scale : Transform→Fin r→Fin t→Vertex r t digits
  | second : Transform→Fin t→Vertex r t digits
  | product : Fin (r*t)→Vertex r t digits
  | carryInitial : Vertex r t digits
  | carry : Fin (r*t)→Vertex r t digits
  | carryTerminal : Vertex r t digits
  | orGate : Fin 2→Fin (digits-1)→Vertex r t digits
  | inputCheck : Fin 2→Vertex r t digits
  deriving DecidableEq,Fintype

/-- Actual vertex owning each arithmetic word role. -/
def wordOwner {r t digits : ℕ} : WordPort r t→Vertex r t digits
  | .inputOut side i => .input side i
  | .firstIn tr j₁ _ => .first tr j₁
  | .firstOut tr j₁ _ => .first tr j₁
  | .scaleIn tr j₁ k₂ => .scale tr j₁ k₂
  | .scaleOut tr j₁ k₂ => .scale tr j₁ k₂
  | .secondIn tr k₂ _ => .second tr k₂
  | .secondOut tr k₂ _ => .second tr k₂
  | .productIn _ k => .product k
  | .productOut k => .product k
  | .carryInitial => .carryInitial
  | .carryCoefficient k => .carry k
  | .carryPrevious k => .carry k
  | .carryOut k => .carry k
  | .carryTerminal => .carryTerminal

/-- Actual source/OR/check vertex owning each one-bit flag role. -/
def flagOwner {r t digits : ℕ} (hcap : digits≤r*t) : FlagPort digits→Vertex r t digits
  | .digitOut side i => .input side ⟨i.val,by have := i.isLt;omega⟩
  | .orPrevious side i => .orGate side i
  | .orNew side i => .orGate side i
  | .orOut side i => .orGate side i
  | .terminal side => .inputCheck side

/-- Actual owner of every physical ordered word-bit or flag role. -/
def owner {r t digits : ℕ} (hcap : digits≤r*t) : BitPort r t digits→Vertex r t digits
  | .inl (port,_) => wordOwner port
  | .inr port => flagOwner hcap port

/-- A concrete acyclic stage rank, used to rule out self-loop/repeated-scope edges. -/
def vertexRank {r t digits : ℕ} : Vertex r t digits→ℕ
  | .input _ _ => 0
  | .first (.inl _) _ => 2
  | .first (.inr _) _ => 6
  | .scale (.inl _) _ _ => 3
  | .scale (.inr _) _ _ => 7
  | .second (.inl _) _ => 4
  | .second (.inr _) _ => 8
  | .product _ => 5
  | .carryInitial => 0
  | .carry k => 9+k.val
  | .carryTerminal => 9+r*t
  | .orGate _ i => 1+i.val
  | .inputCheck _ => digits

/-- Every actual word signal goes from an earlier to a later vertex. -/
theorem word_rank_increases {r t digits : ℕ} (signal : WordSignal r t) :
    vertexRank (wordOwner (digits:=digits) (producer signal))<
      vertexRank (wordOwner (digits:=digits) (consumer signal)) := by
  cases signal with
  | input side i => simp [producer,consumer,wordOwner,vertexRank]
  | first tr j k => cases tr <;> simp [producer,consumer,wordOwner,vertexRank]
  | twiddle tr j k => cases tr <;> simp [producer,consumer,wordOwner,vertexRank]
  | second tr k j =>
    cases tr with
    | inl side => simp [producer,consumer,wordOwner,vertexRank]
    | inr u => cases u; simp [producer,consumer,wordOwner,vertexRank]; omega
  | product k => simp [producer,consumer,wordOwner,vertexRank]
  | carry k =>
    simp only [producer,consumer]
    split_ifs <;> simp only [wordOwner,vertexRank] <;> have hk := k.isLt <;> omega

/-- Every flag edge also goes strictly forward, including the one-digit case. -/
theorem flag_rank_increases {r t digits : ℕ} (hdigits : 0<digits) (hcap : digits≤r*t)
    (signal : FlagSignal digits) :
    vertexRank (flagOwner hcap (flagProducer signal))<
      vertexRank (flagOwner hcap (flagConsumer hdigits signal)) := by
  cases signal with
  | digit side i =>
    simp only [flagProducer,flagConsumer]
    split_ifs <;> simp only [flagOwner,vertexRank] <;> have hi := i.isLt <;> omega
  | orOut side i =>
    simp only [flagProducer,flagConsumer]
    split_ifs <;> simp only [flagOwner,vertexRank] <;> have hi := i.isLt <;> omega

/-- The complete actual bit graph has distinct earlier/later endpoint owners. -/
theorem endpoint_rank_increases {r t digits : ℕ} (hdigits : 0<digits) (hcap : digits≤r*t)
    (signal : BitSignal r t digits) :
    vertexRank (owner hcap (bitEndpoint hdigits (signal,false)))<
      vertexRank (owner hcap (bitEndpoint hdigits (signal,true))) := by
  cases signal with
  | inl signal =>
    rcases signal with ⟨signal,bit⟩
    exact word_rank_increases signal
  | inr signal => exact flag_rank_increases hdigits hcap signal

/-- No original vertex reads the same signal at both its endpoints. -/
theorem endpoint_owners_ne {r t digits : ℕ} (hdigits : 0<digits) (hcap : digits≤r*t)
    (signal : BitSignal r t digits) :
    owner hcap (bitEndpoint hdigits (signal,false))≠
      owner hcap (bitEndpoint hdigits (signal,true)) := by
  intro he
  have hr := endpoint_rank_increases hdigits hcap signal
  rw [he] at hr
  exact Nat.lt_irrefl _ hr

/-- No repeated scope variable: two concrete ports at the same original
vertex with the same signal are the same port. -/
theorem scope_signal_injective {r t digits : ℕ} (hdigits : 0<digits) (hcap : digits≤r*t)
    (p q : BitPort r t digits) (howner : owner hcap p=owner hcap q)
    (hsignal : (bitPortSignal hdigits p).1=(bitPortSignal hdigits q).1) : p=q := by
  let e := bitPortSignal hdigits p
  let f := bitPortSignal hdigits q
  have hp : bitEndpoint hdigits e=p := (bitEndpointEquiv r t digits hdigits).right_inv p
  have hq : bitEndpoint hdigits f=q := (bitEndpointEquiv r t digits hdigits).right_inv q
  have hs : e.1=f.1 := hsignal
  have hown : owner hcap (bitEndpoint hdigits e)=owner hcap (bitEndpoint hdigits f) := by rw [hp,hq];exact howner
  have heq : e=f := by
    rcases e with ⟨signal,b⟩
    rcases f with ⟨other,c⟩
    dsimp only at hs
    subst other
    cases b <;> cases c
    · rfl
    · exact False.elim ((endpoint_owners_ne hdigits hcap signal) hown)
    · exact False.elim ((endpoint_owners_ne hdigits hcap signal) hown.symm)
    · rfl
  rw [←hp,←hq,heq]

/-- Every post-subdivision edge is one original signal's selected host half. -/
abbrev Edge (r t digits : ℕ) := BitSignal r t digits×Bool

/-- Original actual role ports plus the two explicit equality-vertex ports. -/
abbrev SubdividedPort (r t digits : ℕ) := BitPort r t digits ⊕ (BitSignal r t digits×Bool)

/-- Original vertices and one actual equality vertex per original signal. -/
abbrev SubdividedVertex (r t digits : ℕ) := Vertex r t digits ⊕ BitSignal r t digits

/-- Literal host ownership in the actual bipartite subdivided graph. -/
def subdividedOwner {r t digits : ℕ} (hcap : digits≤r*t) :
    SubdividedPort r t digits→SubdividedVertex r t digits
  | .inl port => .inl (owner hcap port)
  | .inr (signal,_) => .inr signal

/-- Each new edge has one original host and its equality-vertex host. -/
def subdividedEndpoint {r t digits : ℕ} (hdigits : 0<digits) :
    (Edge r t digits×Bool)→SubdividedPort r t digits
  | (edge,false) => .inl (bitEndpoint hdigits edge)
  | (edge,true) => .inr edge

/-- Actual inverse from a subdivided vertex port to its edge and endpoint side. -/
def subdividedPortEdge {r t digits : ℕ} (hdigits : 0<digits) :
    SubdividedPort r t digits→Edge r t digits×Bool
  | .inl port => (bitPortSignal hdigits port,false)
  | .inr edge => (edge,true)

/-- The actual whole subdivided graph endpoint map is bijective. -/
def subdividedEndpointEquiv (r t digits : ℕ) (hdigits : 0<digits) :
    (Edge r t digits×Bool) ≃ SubdividedPort r t digits where
  toFun := subdividedEndpoint hdigits
  invFun := subdividedPortEdge hdigits
  left_inv e := by
    rcases e with ⟨edge,side⟩
    cases side
    · exact congrArg (fun e : Edge r t digits => (e,false))
        ((bitEndpointEquiv r t digits hdigits).left_inv edge)
    · rfl
  right_inv port := by
    cases port with
    | inl port => exact congrArg Sum.inl ((bitEndpointEquiv r t digits hdigits).right_inv port)
    | inr edge => rfl

/-- Every actual edge joins opposite original/equality sides, so there are no self loops. -/
theorem subdivided_bipartite {r t digits : ℕ} (hdigits : 0<digits) (hcap : digits≤r*t)
    (edge : Edge r t digits) :
    subdividedOwner hcap (subdividedEndpoint hdigits (edge,false))≠
      subdividedOwner hcap (subdividedEndpoint hdigits (edge,true)) := by
  simp [subdividedEndpoint,subdividedOwner]

/-- Actual post-subdivision scopes have no repeated edge variable. -/
theorem subdivided_scope_injective {r t digits : ℕ} (hdigits : 0<digits) (hcap : digits≤r*t)
    (p q : SubdividedPort r t digits)
    (howner : subdividedOwner hcap p=subdividedOwner hcap q)
    (hedge : (subdividedPortEdge hdigits p).1=(subdividedPortEdge hdigits q).1) : p=q := by
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      apply congrArg Sum.inl
      exact (bitEndpointEquiv r t digits hdigits).symm.injective hedge
    | inr edge => cases howner
  | inr edge =>
    cases q with
    | inl q => cases howner
    | inr other => exact congrArg Sum.inr hedge

/-- Every actual edge occurs in exactly two concrete local tensor ports. -/
theorem edge_occurrence_two {r t digits : ℕ} (hdigits : 0<digits) (edge : Edge r t digits) :
    (∑ port : SubdividedPort r t digits,
      if (subdividedPortEdge hdigits port).1=edge then (1 : ℕ) else 0)=2 := by
  classical
  rw [←Equiv.sum_comp (subdividedEndpointEquiv r t digits hdigits)]
  change (∑ e : Edge r t digits×Bool,
    if (subdividedPortEdge hdigits (subdividedEndpoint hdigits e)).1=edge then (1 : ℕ) else 0)=2
  have he : ∀ e : Edge r t digits×Bool,
      subdividedPortEdge hdigits (subdividedEndpoint hdigits e)=e :=
    (subdividedEndpointEquiv r t digits hdigits).left_inv
  simp only [he]
  rw [Fintype.sum_prod_type]
  have hh (a : Edge r t digits) : (∑ b : Bool,if a=edge then (1 : ℕ) else 0)=
      if a=edge then 2 else 0 := by by_cases ha : a=edge <;> simp [ha]
  simp_rw [hh]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- Exact actual post-subdivision edge count. -/
theorem edge_card (r t digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (Edge r t digits)=2*((13*(r*t)+1)*(r*t+1)+4*digits-2) := by
  rw [Fintype.card_prod,Fintype.card_bool,bit_signal_card r t digits hdigits]
  omega

/-- Exact actual port count follows from the proved endpoint ownership bijection. -/
theorem subdivided_port_card (r t digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (SubdividedPort r t digits)=4*((13*(r*t)+1)*(r*t+1)+4*digits-2) := by
  rw [←Fintype.card_congr (subdividedEndpointEquiv r t digits hdigits),Fintype.card_prod,
    Fintype.card_bool,edge_card r t digits hdigits]
  omega

/-- Explicit decomposition of the actual original vertex constructors. -/
def vertexSumEquiv (r t digits : ℕ) : Vertex r t digits ≃
    ((Fin 2×Fin (r*t)) ⊕ (Transform×Fin r) ⊕ (Transform×Fin r×Fin t) ⊕
      (Transform×Fin t) ⊕ Fin (r*t) ⊕ Unit ⊕ Fin (r*t) ⊕ Unit ⊕
        (Fin 2×Fin (digits-1)) ⊕ Fin 2) where
  toFun
    | .input side i => .inl (side,i)
    | .first tr j => .inr (.inl (tr,j))
    | .scale tr j k => .inr (.inr (.inl (tr,j,k)))
    | .second tr k => .inr (.inr (.inr (.inl (tr,k))))
    | .product k => .inr (.inr (.inr (.inr (.inl k))))
    | .carryInitial => .inr (.inr (.inr (.inr (.inr (.inl ())))))
    | .carry k => .inr (.inr (.inr (.inr (.inr (.inr (.inl k))))))
    | .carryTerminal => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))
    | .orGate side i => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (side,i)))))))))
    | .inputCheck side => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (side)))))))))
  invFun
    | .inl (side,i) => .input side i
    | .inr (.inl (tr,j)) => .first tr j
    | .inr (.inr (.inl (tr,j,k))) => .scale tr j k
    | .inr (.inr (.inr (.inl (tr,k)))) => .second tr k
    | .inr (.inr (.inr (.inr (.inl k)))) => .product k
    | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .carryInitial
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl k)))))) => .carry k
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))) => .carryTerminal
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (side,i))))))))) => .orGate side i
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (side))))))))) => .inputCheck side
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨side,i⟩|⟨tr,j⟩|⟨tr,j,k⟩|⟨tr,k⟩|k|u|k|u|⟨side,i⟩|side
    all_goals rfl

/-- Exact count of the actual original vertices (before equality subdivision). -/
theorem vertex_card (r t digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (Vertex r t digits)=7*(r*t)+3*(r+t)+2*digits+2 := by
  rw [Fintype.card_congr (vertexSumEquiv r t digits)]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Transform,Fintype.card_unit]
  have hd : 2*(digits-1)+2=2*digits := by omega
  nlinarith

/-- Exact original-plus-equality vertex count of the actual subdivided graph. -/
theorem subdivided_vertex_card (r t digits : ℕ) (hdigits : 0<digits) :
    Fintype.card (SubdividedVertex r t digits)=
      7*(r*t)+3*(r+t)+2*digits+2+((13*(r*t)+1)*(r*t+1)+4*digits-2) := by
  rw [Fintype.card_sum,vertex_card r t digits hdigits,bit_signal_card r t digits hdigits]

/-- Literal zero extension is a bijection onto the larger physical words
whose checked integer value fits the smaller active width. This handles the
compiler's `(n+1)`-bit carry words constrained below `2^n`, and source digits. -/
def boundedWordEquiv (small large : ℕ) (hwidth : small≤large) :
    BitVec small ≃ {word : BitVec large // decode word<2^small} where
  toFun word :=
    ⟨encode large (decode word),by
      have hw : decode word<2^large := lt_of_lt_of_le word.isLt
        (Nat.pow_le_pow_right (by omega) hwidth)
      rw [decode_encode hw]
      exact word.isLt⟩
  invFun word := encode small (decode word.val)
  left_inv word := by
    apply BitVec.eq_of_toNat_eq
    have hw : decode word<2^large := lt_of_lt_of_le word.isLt
      (Nat.pow_le_pow_right (by omega) hwidth)
    change decode (encode small (decode (encode large (decode word))))=decode word
    rw [decode_encode hw]
    exact decode_encode (show decode word<2^small from word.isLt)
  right_inv word := by
    apply Subtype.ext
    apply BitVec.eq_of_toNat_eq
    have hw : decode word.val<2^large := word.val.isLt
    change decode (encode large (decode (encode small (decode word.val))))=decode word.val
    rw [decode_encode word.property,decode_encode hw]

/-- Exact physical carry-width bridge: no accepted top carry bit is free. -/
def physicalCarryEquiv (n : ℕ) :
    BitVec n ≃ {word : BitVec (n+1) // decode word<2^n} :=
  boundedWordEquiv n (n+1) (by omega)

/-- Split the actual post-subdivision edge assignment into its two host halves. -/
def edgeAssignmentEquiv (r t digits : ℕ) :
    (Edge r t digits→Bool) ≃ ((BitSignal r t digits→Bool)×(BitSignal r t digits→Bool)) where
  toFun assignment := (fun signal => assignment (signal,false),fun signal => assignment (signal,true))
  invFun halves edge := if edge.2 then halves.2 edge.1 else halves.1 edge.1
  left_inv assignment := by funext edge;rcases edge with ⟨signal,side⟩;cases side <;> rfl
  right_inv halves := by rcases halves with ⟨a,b⟩;rfl

/-- The actual original role-port assignment supplied by shared signal bits. -/
def originalAssignment {r t digits : ℕ} (hdigits : 0<digits) (assignment : BitSignal r t digits→Bool)
    (port : BitPort r t digits) : Bool := assignment (bitPortSignal hdigits port).1

/-- The actual original-vertex port assignment after equality subdivision. -/
def subdividedAssignment {r t digits : ℕ} (hdigits : 0<digits) (assignment : Edge r t digits→Bool)
    (port : BitPort r t digits) : Bool := assignment (bitPortSignal hdigits port)

/-- All actual equality vertices force the two host halves to agree. -/
def equalitiesHold {r t digits : ℕ} (assignment : Edge r t digits→Bool) : Prop :=
  ∀ signal,assignment (signal,false)=assignment (signal,true)

/-- Concrete graph subdivision preserves the accepted assignment count for
ANY predicates on its actual original role ports. The graph endpoint relation
is constructed above, not assumed correct by this theorem. -/
theorem graph_subdivision_count {r t digits : ℕ} (hdigits : 0<digits)
    (accepted : (BitPort r t digits→Bool)→Prop) :
    (∑ assignment : Edge r t digits→Bool,
      if equalitiesHold assignment ∧ accepted (subdividedAssignment hdigits assignment)
        then (1 : ℕ) else 0)=
      ∑ assignment : BitSignal r t digits→Bool,
        if accepted (originalAssignment hdigits assignment) then 1 else 0 := by
  classical
  rw [←Equiv.sum_comp (edgeAssignmentEquiv r t digits).symm]
  change (∑ halves : (BitSignal r t digits→Bool)×(BitSignal r t digits→Bool),
    if equalitiesHold ((edgeAssignmentEquiv r t digits).symm halves) ∧
      accepted (subdividedAssignment hdigits ((edgeAssignmentEquiv r t digits).symm halves))
      then (1 : ℕ) else 0)=_
  rw [Fintype.sum_prod_type]
  have he : ∀ a b : BitSignal r t digits→Bool,
      (if equalitiesHold ((edgeAssignmentEquiv r t digits).symm (a,b)) ∧
        accepted (subdividedAssignment hdigits ((edgeAssignmentEquiv r t digits).symm (a,b)))
        then (1 : ℕ) else 0)=
      if b=a then (if accepted (originalAssignment hdigits a) then 1 else 0) else 0 := by
    intro a b
    by_cases hab : b=a
    · subst b
      have hx : subdividedAssignment hdigits ((edgeAssignmentEquiv r t digits).symm (a,a))=
          originalAssignment hdigits a := by
        funext port
        simp only [subdividedAssignment,originalAssignment,edgeAssignmentEquiv,Equiv.coe_fn_symm_mk]
        split_ifs <;> rfl
      have hh : equalitiesHold ((edgeAssignmentEquiv r t digits).symm (a,a)) := by intro signal;rfl
      rw [hx,ite_eq_left rfl]
      simp [hh]
    · have hh : ¬equalitiesHold ((edgeAssignmentEquiv r t digits).symm (a,b)) := by
        intro h
        apply hab
        funext signal
        exact (h signal).symm
      simp [hab,hh]
  simp_rw [he]
  simp

/-- The actual ordered local port blocks at every vertex: all input words
first, all output words next; source flags follow the source word. -/
abbrev LocalSlot {r t digits : ℕ} : Vertex r t digits→Type
  | .input _ i => Fin (r*t+1) ⊕ {j : Fin digits // j.val=i.val}
  | .first _ _ => (Fin t×Fin (r*t+1)) ⊕ (Fin t×Fin (r*t+1))
  | .scale _ _ _ => Fin (r*t+1) ⊕ Fin (r*t+1)
  | .second _ _ => (Fin r×Fin (r*t+1)) ⊕ (Fin r×Fin (r*t+1))
  | .product _ => (Fin 2×Fin (r*t+1)) ⊕ Fin (r*t+1)
  | .carryInitial => Fin (r*t+1)
  | .carry _ => (Fin 2×Fin (r*t+1)) ⊕ Fin (r*t+1)
  | .carryTerminal => Fin (r*t+1)
  | .orGate _ _ => Fin 3
  | .inputCheck _ => Fin 1

/-- Every actual physical bit port has an owner and literal ordered block slot. -/
def structuredPort {r t digits : ℕ} (hcap : digits≤r*t) :
    BitPort r t digits→(v : Vertex r t digits)×LocalSlot v
  | .inl (.inputOut side i,bit) => ⟨.input side i,.inl bit⟩
  | .inl (.firstIn tr j k,bit) => ⟨.first tr j,.inl (k,bit)⟩
  | .inl (.firstOut tr j k,bit) => ⟨.first tr j,.inr (k,bit)⟩
  | .inl (.scaleIn tr j k,bit) => ⟨.scale tr j k,.inl bit⟩
  | .inl (.scaleOut tr j k,bit) => ⟨.scale tr j k,.inr bit⟩
  | .inl (.secondIn tr k j,bit) => ⟨.second tr k,.inl (j,bit)⟩
  | .inl (.secondOut tr k j,bit) => ⟨.second tr k,.inr (j,bit)⟩
  | .inl (.productIn side k,bit) => ⟨.product k,.inl (side,bit)⟩
  | .inl (.productOut k,bit) => ⟨.product k,.inr bit⟩
  | .inl (.carryInitial,bit) => ⟨.carryInitial,bit⟩
  | .inl (.carryCoefficient k,bit) => ⟨.carry k,.inl (0,bit)⟩
  | .inl (.carryPrevious k,bit) => ⟨.carry k,.inl (1,bit)⟩
  | .inl (.carryOut k,bit) => ⟨.carry k,.inr bit⟩
  | .inl (.carryTerminal,bit) => ⟨.carryTerminal,bit⟩
  | .inr (.digitOut side j) => ⟨.input side ⟨j.val,by have := j.isLt;omega⟩,.inr ⟨j,rfl⟩⟩
  | .inr (.orPrevious side i) => ⟨.orGate side i,0⟩
  | .inr (.orNew side i) => ⟨.orGate side i,1⟩
  | .inr (.orOut side i) => ⟨.orGate side i,2⟩
  | .inr (.terminal side) => ⟨.inputCheck side,0⟩

/-- Every ordered block slot reconstructs its literal graph role. -/
def unstructuredPort {r t digits : ℕ} : ((v : Vertex r t digits)×LocalSlot v)→BitPort r t digits
  | ⟨.input side i,.inl bit⟩ => .inl (.inputOut side i,bit)
  | ⟨.input side _,.inr j⟩ => .inr (.digitOut side j.val)
  | ⟨.first tr j,.inl (k,bit)⟩ => .inl (.firstIn tr j k,bit)
  | ⟨.first tr j,.inr (k,bit)⟩ => .inl (.firstOut tr j k,bit)
  | ⟨.scale tr j k,.inl bit⟩ => .inl (.scaleIn tr j k,bit)
  | ⟨.scale tr j k,.inr bit⟩ => .inl (.scaleOut tr j k,bit)
  | ⟨.second tr k,.inl (j,bit)⟩ => .inl (.secondIn tr k j,bit)
  | ⟨.second tr k,.inr (j,bit)⟩ => .inl (.secondOut tr k j,bit)
  | ⟨.product k,.inl (side,bit)⟩ => .inl (.productIn side k,bit)
  | ⟨.product k,.inr bit⟩ => .inl (.productOut k,bit)
  | ⟨.carryInitial,bit⟩ => .inl (.carryInitial,bit)
  | ⟨.carry k,.inl (side,bit)⟩ =>
      if side.val=0 then .inl (.carryCoefficient k,bit) else .inl (.carryPrevious k,bit)
  | ⟨.carry k,.inr bit⟩ => .inl (.carryOut k,bit)
  | ⟨.carryTerminal,bit⟩ => .inl (.carryTerminal,bit)
  | ⟨.orGate side i,slot⟩ =>
      if slot.val=0 then .inr (.orPrevious side i)
      else if slot.val=1 then .inr (.orNew side i) else .inr (.orOut side i)
  | ⟨.inputCheck side,_⟩ => .inr (.terminal side)

/-- Concrete owner/block-slot bijection, not an arbitrary enumeration of fibres. -/
def structuredPortEquiv (r t digits : ℕ) (hcap : digits≤r*t) :
    BitPort r t digits ≃ ((v : Vertex r t digits)×LocalSlot v) where
  toFun := structuredPort hcap
  invFun := unstructuredPort
  left_inv port := by
    cases port with
    | inl port => rcases port with ⟨port,bit⟩;cases port <;> rfl
    | inr port => cases port <;> rfl
  right_inv port := by
    rcases port with ⟨vertex,slot⟩
    cases vertex with
    | input side i =>
      cases slot with
      | inl bit => rfl
      | inr j =>
        rcases i with ⟨i,hi⟩
        rcases j with ⟨⟨j,hj⟩,he⟩
        dsimp only at he
        subst j
        rfl
    | first tr j => rcases slot with ⟨k,bit⟩|⟨k,bit⟩ <;> rfl
    | scale tr j k => cases slot <;> rfl
    | second tr k => rcases slot with ⟨j,bit⟩|⟨j,bit⟩ <;> rfl
    | product k => rcases slot with ⟨side,bit⟩|bit <;> rfl
    | carryInitial => rfl
    | carry k =>
      cases slot with
      | inl p => rcases p with ⟨side,bit⟩;fin_cases side <;> rfl
      | inr bit => rfl
    | carryTerminal => rfl
    | orGate side i => fin_cases slot <;> rfl
    | inputCheck side => fin_cases slot;rfl

/-- The structured port's owner is exactly the already-proved graph owner. -/
theorem structuredPort_owner {r t digits : ℕ} (hcap : digits≤r*t) (port : BitPort r t digits) :
    (structuredPort hcap port).1=owner hcap port := by
  cases port with
  | inl port => rcases port with ⟨port,bit⟩;cases port <;> rfl
  | inr port => cases port <;> rfl

/-- The optional source flag slot has its literal zero/one size and ordering. -/
def sourceFlagSlotEquiv {digits n : ℕ} (i : Fin n) :
    {j : Fin digits // j.val=i.val} ≃ Fin (if i.val<digits then 1 else 0) where
  toFun j := ⟨0,by have hj := j.val.isLt;have he := j.property;rw [ite_eq_left (by omega)];omega⟩
  invFun slot := by
    have hi : i.val<digits := by
      by_contra hn
      have hs := slot.isLt
      simp only [ite_eq_right hn] at hs
      omega
    exact ⟨⟨i.val,hi⟩,rfl⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    exact j.property.symm
  right_inv slot := by
    apply Fin.ext
    change 0=slot.val
    have hs := slot.isLt
    split_ifs at hs <;> omega

/-- Exact ordered physical port arity of each actual compiler vertex. -/
def arity {r t digits : ℕ} : Vertex r t digits→ℕ
  | .input _ i => (r*t+1)+(if i.val<digits then 1 else 0)
  | .first _ _ => t*(r*t+1)+t*(r*t+1)
  | .scale _ _ _ => (r*t+1)+(r*t+1)
  | .second _ _ => r*(r*t+1)+r*(r*t+1)
  | .product _ => 2*(r*t+1)+(r*t+1)
  | .carryInitial => r*t+1
  | .carry _ => 2*(r*t+1)+(r*t+1)
  | .carryTerminal => r*t+1
  | .orGate _ _ => 3
  | .inputCheck _ => 1

/-- Explicit input-before-output, word-before-bit flattening at every vertex.
Only the standard sum/product finite-index bijections are used. -/
def localSlotFinEquiv {r t digits : ℕ} : (v : Vertex r t digits)→LocalSlot v ≃ Fin (arity v)
  | .input _ i =>
      (Equiv.sumCongr (Equiv.refl _) (sourceFlagSlotEquiv i)).trans finSumFinEquiv
  | .first _ _ =>
      (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv
  | .scale _ _ _ => finSumFinEquiv
  | .second _ _ =>
      (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv
  | .product _ => (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv
  | .carryInitial => Equiv.refl _
  | .carry _ => (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv
  | .carryTerminal => Equiv.refl _
  | .orGate _ _ => Equiv.refl _
  | .inputCheck _ => Equiv.refl _

/-- Every actual physical graph role is bijective to its exact ordered vertex
port `Fin arity`. No arbitrary fibre enumeration or graph-correctness premise. -/
def orderedPortEquiv (r t digits : ℕ) (hcap : digits≤r*t) :
    BitPort r t digits ≃ ((v : Vertex r t digits)×Fin (arity v)) :=
  (structuredPortEquiv r t digits hcap).trans
    (Equiv.sigmaCongrRight (fun v => localSlotFinEquiv v))

/-- The requested full producer/consumer endpoint bijection to actual ordered
compiler ports, including digit flags sharing source vertices. -/
def orderedEndpointEquiv (r t digits : ℕ) (hdigits : 0<digits) (hcap : digits≤r*t) :
    (BitSignal r t digits×Bool) ≃ ((v : Vertex r t digits)×Fin (arity v)) :=
  (bitEndpointEquiv r t digits hdigits).trans (orderedPortEquiv r t digits hcap)

/-- Ordered-port conversion preserves the concrete endpoint owner exactly. -/
theorem orderedPort_owner {r t digits : ℕ} (hcap : digits≤r*t) (port : BitPort r t digits) :
    ((orderedPortEquiv r t digits hcap) port).1=owner hcap port :=
  structuredPort_owner hcap port

/-- The actual sum of local arities follows from the concrete ordered endpoint
bijection, rather than merely from a signal-cardinality analogy. -/
theorem total_arity (r t digits : ℕ) (hdigits : 0<digits) (hcap : digits≤r*t) :
    (∑ v : Vertex r t digits,arity v)=2*((13*(r*t)+1)*(r*t+1)+4*digits-2) := by
  have he := Fintype.card_congr (orderedPortEquiv r t digits hcap)
  rw [bit_port_card r t digits hdigits,Fintype.card_sigma] at he
  simpa only [Fintype.card_fin] using he.symm

/-- Exact first-stage physical arity, with bundled t outputs. -/
theorem first_arity {r t digits : ℕ} (tr : Transform) (j : Fin r) :
    arity (Vertex.first (r:=r) (t:=t) (digits:=digits) tr j)=2*t*(r*t+1) := by simp only [arity];ring

/-- Exact second-stage physical arity, with bundled r outputs. -/
theorem second_arity {r t digits : ℕ} (tr : Transform) (k : Fin t) :
    arity (Vertex.second (r:=r) (t:=t) (digits:=digits) tr k)=2*r*(r*t+1) := by simp only [arity];ring

/-- Exact carry arity includes all three physical `(n+1)`-bit words. -/
theorem carry_arity {r t digits : ℕ} (k : Fin (r*t)) :
    arity (Vertex.carry (r:=r) (t:=t) (digits:=digits) k)=3*(r*t+1) := by simp only [arity];ring

/-- Every actual original vertex has the small-port macro bound, including
source/flag/check vertices rather than just arithmetic-stage examples. -/
theorem arity_bound {r t digits : ℕ} (v : Vertex r t digits) :
    arity v≤(2*(r+t)+3)*(r*t+1) := by
  cases v <;> simp only [arity]
  all_goals first | (split_ifs <;> ring_nf <;> omega) | (ring_nf;omega)

/-- Exact 0/1 ordering of the two equality ports. -/
def boolSlotEquiv : Bool ≃ Fin 2 where
  toFun side := if side then 1 else 0
  invFun slot := decide (slot.val=1)
  left_inv side := by cases side <;> rfl
  right_inv slot := by fin_cases slot <;> rfl

/-- Original physical arities and literal two-port equality vertices. -/
def subdividedArity {r t digits : ℕ} : SubdividedVertex r t digits→ℕ
  | .inl vertex => arity vertex
  | .inr _ => 2

/-- Explicit sum-to-dependent-local-port ordering for original/equality sides. -/
def subdivisionSlotEquiv (r t digits : ℕ) :
    (((v : Vertex r t digits)×Fin (arity v)) ⊕ (BitSignal r t digits×Fin 2)) ≃
      ((v : SubdividedVertex r t digits)×Fin (subdividedArity v)) where
  toFun
    | .inl ⟨v,slot⟩ => ⟨.inl v,slot⟩
    | .inr (signal,slot) => ⟨.inr signal,slot⟩
  invFun
    | ⟨.inl v,slot⟩ => .inl ⟨v,slot⟩
    | ⟨.inr signal,slot⟩ => .inr (signal,slot)
  left_inv p := by rcases p with ⟨v,slot⟩|⟨signal,slot⟩ <;> rfl
  right_inv p := by rcases p with ⟨v,slot⟩;cases v <;> rfl

/-- Complete actual ordered local ports after equality subdivision. -/
def subdividedOrderedPortEquiv (r t digits : ℕ) (hcap : digits≤r*t) :
    SubdividedPort r t digits ≃
      ((v : SubdividedVertex r t digits)×Fin (subdividedArity v)) :=
  (Equiv.sumCongr (orderedPortEquiv r t digits hcap)
    (Equiv.prodCongr (Equiv.refl _) boolSlotEquiv)).trans (subdivisionSlotEquiv r t digits)

/-- Full actual post-subdivision producer/consumer endpoint bijection to
ordered local `Fin arity` ports. -/
def subdividedOrderedEndpointEquiv (r t digits : ℕ) (hdigits : 0<digits) (hcap : digits≤r*t) :
    (Edge r t digits×Bool) ≃
      ((v : SubdividedVertex r t digits)×Fin (subdividedArity v)) :=
  (subdividedEndpointEquiv r t digits hdigits).trans (subdividedOrderedPortEquiv r t digits hcap)

/-- Exact actual post-subdivision sum of vertex arities. -/
theorem subdivided_total_arity (r t digits : ℕ) (hdigits : 0<digits) (hcap : digits≤r*t) :
    (∑ v : SubdividedVertex r t digits,subdividedArity v)=
      4*((13*(r*t)+1)*(r*t+1)+4*digits-2) := by
  have he := Fintype.card_congr (subdividedOrderedPortEquiv r t digits hcap)
  rw [subdivided_port_card r t digits hdigits,Fintype.card_sigma] at he
  simpa only [Fintype.card_fin] using he.symm

/-- The equality graph retains the proved macro small-port scope bound. -/
theorem subdivided_arity_bound {r t digits : ℕ} (v : SubdividedVertex r t digits) :
    subdividedArity v≤(2*(r+t)+3)*(r*t+1) := by
  cases v with
  | inl vertex => exact arity_bound vertex
  | inr signal => simp only [subdividedArity];ring_nf;omega

/-- Literal Python first-DFT input word-major/bit-minor port offset. -/
theorem first_input_offset {r t digits : ℕ} (hcap : digits≤r*t) (tr : Transform)
    (j : Fin r) (k : Fin t) (bit : Fin (r*t+1)) :
    ((orderedPortEquiv r t digits hcap) (.inl (.firstIn tr j k,bit))).2.val=
      k.val*(r*t+1)+bit.val := by
  change bit.val+(r*t+1)*k.val=k.val*(r*t+1)+bit.val
  ring

/-- Literal Python first-DFT output offset after its t input words. -/
theorem first_output_offset {r t digits : ℕ} (hcap : digits≤r*t) (tr : Transform)
    (j : Fin r) (k : Fin t) (bit : Fin (r*t+1)) :
    ((orderedPortEquiv r t digits hcap) (.inl (.firstOut tr j k,bit))).2.val=
      (t+k.val)*(r*t+1)+bit.val := by
  change t*(r*t+1)+(bit.val+(r*t+1)*k.val)=(t+k.val)*(r*t+1)+bit.val
  ring

/-- Literal Python second-DFT input offset. -/
theorem second_input_offset {r t digits : ℕ} (hcap : digits≤r*t) (tr : Transform)
    (k : Fin t) (j : Fin r) (bit : Fin (r*t+1)) :
    ((orderedPortEquiv r t digits hcap) (.inl (.secondIn tr k j,bit))).2.val=
      j.val*(r*t+1)+bit.val := by
  change bit.val+(r*t+1)*j.val=j.val*(r*t+1)+bit.val
  ring

/-- Literal Python second-DFT output offset after its r input words. -/
theorem second_output_offset {r t digits : ℕ} (hcap : digits≤r*t) (tr : Transform)
    (k : Fin t) (j : Fin r) (bit : Fin (r*t+1)) :
    ((orderedPortEquiv r t digits hcap) (.inl (.secondOut tr k j,bit))).2.val=
      (r+j.val)*(r*t+1)+bit.val := by
  change r*(r*t+1)+(bit.val+(r*t+1)*j.val)=(r+j.val)*(r*t+1)+bit.val
  ring

/-- Literal product input order: left word before right word. -/
theorem product_input_offset {r t digits : ℕ} (hcap : digits≤r*t) (side : Fin 2)
    (k : Fin (r*t)) (bit : Fin (r*t+1)) :
    ((orderedPortEquiv r t digits hcap) (.inl (.productIn side k,bit))).2.val=
      side.val*(r*t+1)+bit.val := by
  change bit.val+(r*t+1)*side.val=side.val*(r*t+1)+bit.val
  ring

/-- Literal INTEGER-carry input order: coefficient, then previous carry. -/
theorem carry_previous_offset {r t digits : ℕ} (hcap : digits≤r*t)
    (k : Fin (r*t)) (bit : Fin (r*t+1)) :
    ((orderedPortEquiv r t digits hcap) (.inl (.carryPrevious k,bit))).2.val=
      (r*t+1)+bit.val := by
  change bit.val+(r*t+1)*1=(r*t+1)+bit.val
  ring

/-- Literal carry-output offset after its two physical input words. -/
theorem carry_output_offset {r t digits : ℕ} (hcap : digits≤r*t)
    (k : Fin (r*t)) (bit : Fin (r*t+1)) :
    ((orderedPortEquiv r t digits hcap) (.inl (.carryOut k,bit))).2.val=
      2*(r*t+1)+bit.val := rfl

/-- The one-bit input flag follows the full physical source word. -/
theorem source_flag_offset {r t digits : ℕ} (hcap : digits≤r*t)
    (side : Fin 2) (j : Fin digits) :
    ((orderedPortEquiv r t digits hcap) (.inr (.digitOut side j))).2.val=r*t+1 := by
  change (r*t+1)+0=r*t+1
  omega

/-- Ordered-port conversion preserves actual original/equality ownership. -/
theorem subdivided_ordered_owner {r t digits : ℕ} (hcap : digits≤r*t)
    (port : SubdividedPort r t digits) :
    ((subdividedOrderedPortEquiv r t digits hcap) port).1=subdividedOwner hcap port := by
  cases port with
  | inl port => exact congrArg Sum.inl (orderedPort_owner hcap port)
  | inr edge => rfl

/-- The actual edge variable read at an ordered local tensor input port. -/
def orderedEdgeAt {r t digits : ℕ} (hdigits : 0<digits) (hcap : digits≤r*t)
    (port : (v : SubdividedVertex r t digits)×Fin (subdividedArity v)) : Edge r t digits :=
  (subdividedPortEdge hdigits ((subdividedOrderedPortEquiv r t digits hcap).symm port)).1

/-- Concrete ordered tensor scopes have no repeated variable indices. -/
theorem ordered_scope_injective {r t digits : ℕ} (hdigits : 0<digits) (hcap : digits≤r*t)
    (vertex : SubdividedVertex r t digits) :
    Function.Injective (fun slot : Fin (subdividedArity vertex) => orderedEdgeAt hdigits hcap ⟨vertex,slot⟩) := by
  intro a b he
  let p := (subdividedOrderedPortEquiv r t digits hcap).symm ⟨vertex,a⟩
  let q := (subdividedOrderedPortEquiv r t digits hcap).symm ⟨vertex,b⟩
  have hp : subdividedOwner hcap p=vertex := by
    have ho := subdivided_ordered_owner hcap p
    have hv := congrArg Sigma.fst ((subdividedOrderedPortEquiv r t digits hcap).apply_symm_apply ⟨vertex,a⟩)
    exact ho.symm.trans hv
  have hq : subdividedOwner hcap q=vertex := by
    have ho := subdivided_ordered_owner hcap q
    have hv := congrArg Sigma.fst ((subdividedOrderedPortEquiv r t digits hcap).apply_symm_apply ⟨vertex,b⟩)
    exact ho.symm.trans hv
  have hports : p=q := subdivided_scope_injective hdigits hcap p q (hp.trans hq.symm) he
  have hv := congrArg (subdividedOrderedPortEquiv r t digits hcap) hports
  change (subdividedOrderedPortEquiv r t digits hcap)
      ((subdividedOrderedPortEquiv r t digits hcap).symm ⟨vertex,a⟩)=
    (subdividedOrderedPortEquiv r t digits hcap)
      ((subdividedOrderedPortEquiv r t digits hcap).symm ⟨vertex,b⟩) at hv
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at hv
  apply Fin.ext
  exact congrArg (fun port : (v : SubdividedVertex r t digits)×Fin (subdividedArity v) => port.2.val) hv

/-- Exactly two ordered local tensor ports use every actual edge variable. -/
theorem ordered_edge_occurrence_two {r t digits : ℕ} (hdigits : 0<digits) (hcap : digits≤r*t)
    (edge : Edge r t digits) :
    (∑ vertex : SubdividedVertex r t digits,∑ slot : Fin (subdividedArity vertex),
      if orderedEdgeAt hdigits hcap ⟨vertex,slot⟩=edge then (1 : ℕ) else 0)=2 := by
  classical
  rw [←Fintype.sum_sigma (fun port : (v : SubdividedVertex r t digits)×Fin (subdividedArity v) =>
    if orderedEdgeAt hdigits hcap port=edge then (1 : ℕ) else 0)]
  rw [←Equiv.sum_comp (subdividedOrderedPortEquiv r t digits hcap)]
  have he : ∀ port : SubdividedPort r t digits,
      orderedEdgeAt hdigits hcap ((subdividedOrderedPortEquiv r t digits hcap) port)=
        (subdividedPortEdge hdigits port).1 := by
    intro port
    unfold orderedEdgeAt
    rw [Equiv.symm_apply_apply]
  simp_rw [he]
  exact edge_occurrence_two hdigits edge

end RiemannGaussian.SemiprimeMacroGraph
