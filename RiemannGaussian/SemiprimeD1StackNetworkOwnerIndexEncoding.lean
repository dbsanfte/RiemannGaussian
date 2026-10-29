/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndex
import RiemannGaussian.SemiprimeD1OrdinalBankSpec
import RiemannGaussian.SemiprimeD1StackOwnerLookupOriginal
import RiemannGaussian.SemiprimeD1StackOwnerFibre
import RiemannGaussian.SemiprimeD1TensorNetworkLayout
/-! # Exact fixed-width owner counter and original physical owner-row encoding
These are mathematical invariants for the literal source. No list, ordinal,
lookup, power or getter below is a runtime operand or an executed opcode.
Port keys preserve the actual UNARY record ABI; owner payloads remain BINARY.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexEncoding
open SemiprimeBitArithmetic (bitValue bitNat)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeSourceHistogramKeyBits (frame)
namespace O
export SemiprimeD1OrdinalBankSpec (idAt)
end O
/-- Actual n+1-bit padded owner counter, including the final post-owner value n. -/
def ownerWord (n v:Nat) :List Bool :=O.idAt (n+1) v
/-- Every processed/final counter retains EXACTLY its paid original n+1 physical bits. -/
theorem ownerWord_length (n v:Nat) (hv:v≤n) :(ownerWord n v).length=n+1 :=
  SemiprimeD1OrdinalBankSpec.id_length (n+1) v (by omega)
/-- BINARY owner payload represents its exact original zero-based owner ordinal. -/
theorem ownerWord_value (n v:Nat) (hv:v≤n) :bitValue (ownerWord n v)=v :=
  SemiprimeD1OrdinalBankSpec.id_value (n+1) v (by omega)
/-- Actual source zero allocation is the literal n+1 false cells, not a compact-word convention. -/
theorem ownerWord_zero (n:Nat) :ownerWord n 0=List.replicate (n+1) false :=by
  apply SemiprimeD1StackAssignmentOrder.word_value_injective
  · rw [ownerWord_length n 0 (by omega),List.length_replicate]
  · rw [ownerWord_value n 0 (by omega),SemiprimeD1OrdinalBankSpec.zero_value]
/-- No actual owner counter wraps, even at the retained final value n. -/
theorem ownerWord_no_overflow (n v:Nat) (hv:v≤n) :
    SemiprimeD1StackIncrement.overflow (ownerWord n v)=false :=
  SemiprimeD1OrdinalBankSpec.no_overflow (n+1) (ownerWord n v)
    (SemiprimeD1OrdinalBankSpec.id_mem (n+1) v (by omega))
/-- Actual fixed-width wrapped successor is the exact next original owner word. -/
theorem ownerWord_succ (n v:Nat) (hv:v<n) :
    SemiprimeD1StackIncrement.wrapped (ownerWord n v)=ownerWord n (v+1) :=by
  apply SemiprimeD1StackAssignmentOrder.word_value_injective
  · rw [SemiprimeD1StackIncrement.wrapped_length,ownerWord_length n v (by omega),ownerWord_length n (v+1) (by omega)]
  · rw [SemiprimeD1StackAssignmentOrder.wrapped_value_step _ (ownerWord_no_overflow n v (by omega)),
      ownerWord_value n v (by omega),ownerWord_value n (v+1) (by omega)]
/-- Padded actual owner words identify exact owner ordinals without a compactness premise. -/
theorem ownerWord_eq_iff (n v w:Nat) (hv:v≤n) (hw:w≤n) :ownerWord n v=ownerWord n w ↔ v=w :=by
  constructor
  · intro h
    have hh:=congrArg bitValue h
    simpa only [ownerWord_value n v hv,ownerWord_value n w hw] using hh
  · intro h;cases h;rfl
/-- A UNARY physical port's numeric key is power-minus-one, never the port ordinal itself. -/
theorem key_value (p:Nat) :bitValue (unary p)+1=2^p :=by
  induction p with
  | zero=>rfl
  | succ p ih=>
    simp only [unary,List.replicate_succ,bitValue,bitNat,ite_true,pow_succ] at ih ⊢
    omega
/-- Actual numeric key comparison between UNARY original ports is exact ordinal equality. -/
theorem key_value_eq_iff (p q:Nat) :bitValue (unary p)=bitValue (unary q) ↔ p=q :=by
  constructor
  · intro h
    induction p generalizing q with
    | zero=>
      cases q with
      | zero=>rfl
      | succ q=>
        change 0=1+2*bitValue (unary q) at h
        omega
    | succ p ih=>
      cases q with
      | zero=>
        change 1+2*bitValue (unary p)=0 at h
        omega
      | succ q=>
        have ht:bitValue (unary p)=bitValue (unary q):=by
          change 1+2*bitValue (unary p)=1+2*bitValue (unary q) at h
          omega
        exact congrArg Nat.succ (ih q ht)
  · intro h;cases h;rfl
/-- Literal unary port key payload includes the zero-port EMPTY field. -/
theorem key_length (p:Nat) :(unary p).length=p :=List.length_replicate
/-- Exact port→binary-owner pairs for one actual owner vertex, preserving its port order. -/
def portPairs (n owner:Nat) (ports:List Nat) :List (List Bool×List Bool) :=
  ports.map (fun p=>(unary p,ownerWord n owner))
/-- Exact original left-vertex/port order; table entries are physically parsed by the source separately. -/
def ownerPairs (n:Nat) :Nat→List SemiprimeD1LeafCounter.Vertex→List (List Bool×List Bool)
  | _,[]=>[]
  | start,v::vertices=>portPairs n start v.ports++ownerPairs n (start+1) vertices
/-- Appending physical port fields appends their owner pairs without a key or owner permutation. -/
theorem portPairs_append (n owner:Nat) (p q:List Nat) :
    portPairs n owner (p++q)=portPairs n owner p++portPairs n owner q :=by
  exact List.map_append
/-- Exact one-vertex row prefix before the subsequent owner records. -/
theorem ownerPairs_cons (n start:Nat) (v:SemiprimeD1LeafCounter.Vertex) (vertices:List SemiprimeD1LeafCounter.Vertex) :
    ownerPairs n start (v::vertices)=portPairs n start v.ports++ownerPairs n (start+1) vertices :=rfl
/-- The owner successor is the actual number of preceding left vertices, not a port count. -/
theorem ownerPairs_append (n start:Nat) (xs ys:List SemiprimeD1LeafCounter.Vertex) :
    ownerPairs n start (xs++ys)=ownerPairs n start xs++ownerPairs n (start+xs.length) ys :=by
  induction xs generalizing start with
  | nil=>simp only [List.nil_append,ownerPairs,List.length_nil,Nat.add_zero]
  | cons v xs ih=>
    simp only [List.cons_append,ownerPairs,ih,List.length_cons,List.append_assoc]
    rw [show start+1+xs.length=start+(xs.length+1) by omega]
/-- All keys in a row are the literal existing portTape UNARY fields. -/
theorem portPairs_keys (n owner:Nat) (ports:List Nat) :
    (portPairs n owner ports).map Prod.fst=ports.map unary :=by
  simp only [portPairs,List.map_map,Function.comp_def]
/-- Owner payload is repeated once per actual local port, with no supplied local arity. -/
theorem portPairs_values (n owner:Nat) (ports:List Nat) :
    (portPairs n owner ports).map Prod.snd=List.replicate ports.length (ownerWord n owner) :=by
  simp only [portPairs,List.map_map,Function.comp_def,List.map_const']
/-- Exact pair bytes written by two real preserving Frames and one actual true constructor push. -/
def pairBytes (pair:List Bool×List Bool) :List Bool :=true::frame pair.1 (frame pair.2 [])
/-- Chronological actual row bytes BEFORE the final false record-vector terminator. -/
def payload (rows:List (List Bool×List Bool)) :List Bool :=
  rows.foldr (fun pair tail=>pairBytes pair++tail) []
/-- Pair framing preserves an arbitrary physical row/record suffix literally. -/
theorem pairBytes_append (key value tail:List Bool) :
    pairBytes (key,value)++tail=true::frame key (frame value tail) :=by
  unfold pairBytes
  rw [List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,SemiprimeD1TensorTapeCodec.frame_append,List.nil_append]
/-- Every actual pair charges both key and binary-owner words plus all three constructors/delimiters. -/
theorem pairBytes_length (key value:List Bool) :
    (pairBytes (key,value)).length=2*key.length+2*value.length+3 :=by
  simp only [pairBytes,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
/-- Literal row-byte payload concatenation, used before the one final real history reverse. -/
theorem payload_append (xs ys:List (List Bool×List Bool)) :payload (xs++ys)=payload xs++payload ys :=by
  induction xs with
  | nil=>rfl
  | cons row xs ih=>
    change pairBytes row++payload (xs++ys)=(pairBytes row++payload xs)++payload ys
    rw [ih,List.append_assoc]
/-- Exact old OwnerLookup.records ABI for arbitrary following rows and physical tail. -/
theorem records_append (xs ys:List (List Bool×List Bool)) (tail:List Bool) :
    SemiprimeD1StackOwnerLookup.records (xs++ys) tail=
      payload xs++SemiprimeD1StackOwnerLookup.records ys tail :=by
  induction xs with
  | nil=>rfl
  | cons row xs ih=>
    rcases row with ⟨key,value⟩
    change true::frame key (frame value (SemiprimeD1StackOwnerLookup.records (xs++ys) tail))=
      (pairBytes (key,value)++payload xs)++SemiprimeD1StackOwnerLookup.records ys tail
    rw [List.append_assoc,pairBytes_append,ih]
/-- The source's final false push and real reverse complete EXACTLY the old catalogue format. -/
theorem records_payload (rows:List (List Bool×List Bool)) (tail:List Bool) :
    SemiprimeD1StackOwnerLookup.records rows tail=payload rows++false::tail :=by
  simpa only [List.append_nil,SemiprimeD1StackOwnerLookup.records] using records_append rows [] tail
/-- A vertex's rows append to the complete subsequent original owner catalogue in exact order. -/
theorem vertex_records (n start:Nat) (v:SemiprimeD1LeafCounter.Vertex) (vertices:List SemiprimeD1LeafCounter.Vertex) (tail:List Bool) :
    SemiprimeD1StackOwnerLookup.records (ownerPairs n start (v::vertices)) tail=
      payload (portPairs n start v.ports)++SemiprimeD1StackOwnerLookup.records (ownerPairs n (start+1) vertices) tail :=by
  exact records_append _ _ _
/-- Membership records the exact original left-vertex position and literal local port. -/
theorem mem_ownerPairs (n start:Nat) (vertices:List SemiprimeD1LeafCounter.Vertex) (key value:List Bool) :
    (key,value)∈ownerPairs n start vertices ↔
      ∃j:Fin vertices.length,∃p,p∈vertices[j.val].ports ∧ key=unary p ∧ value=ownerWord n (start+j.val) :=by
  induction vertices generalizing start with
  | nil=>
    constructor
    · intro h;cases h
    · rintro ⟨j,_⟩;exact Fin.elim0 j
  | cons vertex vertices ih=>
    rw [ownerPairs,List.mem_append]
    constructor
    · intro h
      rcases h with h|h
      · obtain ⟨p,hp,he⟩:=List.mem_map.mp h
        refine ⟨0,p,hp,(congrArg Prod.fst he).symm,?_⟩
        simpa only [Fin.val_zero,Nat.add_zero] using (congrArg Prod.snd he).symm
      · obtain ⟨j,p,hp,hk,hv⟩:=(ih (start+1)).mp h
        refine ⟨⟨j.val+1,by simpa only [List.length_cons] using Nat.succ_lt_succ j.isLt⟩,p,hp,hk,?_⟩
        exact hv.trans (congrArg (ownerWord n) (by dsimp only;omega))
    · rintro ⟨⟨j,hj⟩,p,hp,hk,hv⟩
      cases j with
      | zero=>
        apply Or.inl
        refine List.mem_map.mpr ⟨p,hp,?_⟩
        apply Prod.ext
        · exact hk.symm
        · simpa only [Nat.add_zero] using hv.symm
      | succ j=>
        apply Or.inr
        apply (ih (start+1)).mpr
        refine ⟨⟨j,by simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ hj⟩,p,hp,hk,?_⟩
        exact hv.trans (congrArg (ownerWord n) (by dsimp only;omega))
/-- Original network well-formedness licenses every global UNARY-port lookup to its UNIQUE left owner.
This is a semantic bridge only; the runtime index must still be physically acquired. -/
theorem original_lookup (net:SemiprimeD1TensorNetwork.Network) (hw:SemiprimeD1TensorNetwork.WellFormed net)
    (p:Fin (SemiprimeD1TensorNetwork.scope net.rows)) (tail:List Bool) :
    (SemiprimeD1StackOwnerLookup.result (unary p.val) (ownerPairs net.leftCount 0 net.left.toList) tail).1=
      ownerWord net.leftCount (SemiprimeD1TensorNetworkLayout.leftGroup net.rows p).val :=by
  let target:=SemiprimeD1TensorNetworkLayout.leftGroup net.rows p
  apply SemiprimeD1StackOwnerLookupOriginal.result_value
  · refine ⟨unary p.val,?_,rfl⟩
    apply (mem_ownerPairs _ _ _ _ _).mpr
    refine ⟨⟨target.val,by simpa only [Vector.length_toList] using target.isLt⟩,p.val,?_,rfl,?_⟩
    · rw [Vector.getElem_toList,hw.1 target]
      exact (SemiprimeD1TensorNetworkLayout.leftGroup_mem net.rows target p).mpr rfl
    · simp only [Nat.zero_add]
      rfl
  · intro key payload hmem hmatch
    obtain ⟨j,port,hport,hkey,hvalue⟩:=(mem_ownerPairs _ _ _ _ _).mp hmem
    have hportEq:port=p.val:=(key_value_eq_iff port p.val).mp (by rw [←hkey];exact hmatch)
    let owner:Fin net.leftCount:=⟨j.val,by simpa only [Vector.length_toList] using j.isLt⟩
    have hm:p.val∈SemiprimeD1TensorNetwork.leftPorts net.rows owner:=by
      rw [←hw.1 owner]
      rw [hportEq,Vector.getElem_toList] at hport
      exact hport
    have he:target=owner:=(SemiprimeD1TensorNetworkLayout.leftGroup_mem net.rows owner p).mp hm
    rw [hvalue]
    exact congrArg (ownerWord net.leftCount) (by simpa only [Nat.zero_add] using (congrArg Fin.val he).symm)
/-- Physical owner-fibre filtering preserves literal pair-stream concatenation. -/
theorem fibre_values_append (query:List Bool) (xs ys:List (List Bool×List Bool)) :
    SemiprimeD1StackOwnerFibre.values query (xs++ys)=
      SemiprimeD1StackOwnerFibre.values query xs++SemiprimeD1StackOwnerFibre.values query ys :=by
  induction xs with
  | nil=>rfl
  | cons row xs ih=>
    rcases row with ⟨key,value⟩
    by_cases h:bitValue key=bitValue query
    · simp only [List.cons_append,SemiprimeD1StackOwnerFibre.values,h,ite_true,ih]
    · simp only [List.cons_append,SemiprimeD1StackOwnerFibre.values,h,ite_false,ih]
/-- A vertex emits its binary owner once for EACH matching actual unary port occurrence. -/
theorem fibre_portPairs (n owner p:Nat) (ports:List Nat) :
    SemiprimeD1StackOwnerFibre.values (unary p) (portPairs n owner ports)=
      List.replicate (ports.count p) (ownerWord n owner) :=by
  induction ports with
  | nil=>rfl
  | cons q ports ih=>
    simp only [portPairs] at ih
    by_cases h:q=p
    · subst q
      simp [portPairs,SemiprimeD1StackOwnerFibre.values,ih,List.replicate_succ]
    · simp [portPairs,SemiprimeD1StackOwnerFibre.values,key_value_eq_iff,h,ih]
/-- A physically indexed left-prefix with no matching port yields an EMPTY owner fibre. -/
theorem fibre_empty (n start p:Nat) (vertices:List SemiprimeD1LeafCounter.Vertex)
    (hno:∀v∈vertices,p∉v.ports) :
    SemiprimeD1StackOwnerFibre.values (unary p) (ownerPairs n start vertices)=[] :=by
  induction vertices generalizing start with
  | nil=>rfl
  | cons v vertices ih=>
    have hcount:v.ports.count p=0:=List.count_eq_zero.mpr (hno v (by simp))
    have ht:=ih (start+1) (fun w hw=>hno w (List.mem_cons_of_mem v hw))
    rw [ownerPairs,fibre_values_append,fibre_portPairs,hcount,List.replicate_zero,List.nil_append,ht]
/-- A UNIQUE left-vertex port occurrence gives exactly one actual binary owner payload. -/
theorem fibre_unique (n start p:Nat) (vertices:List SemiprimeD1LeafCounter.Vertex) (target:Fin vertices.length)
    (hnodup:∀v∈vertices,v.ports.Nodup)
    (howner:∀j:Fin vertices.length,p∈vertices[j.val].ports ↔j.val=target.val) :
    SemiprimeD1StackOwnerFibre.values (unary p) (ownerPairs n start vertices)=
      [ownerWord n (start+target.val)] :=by
  induction vertices generalizing start with
  | nil=>exact Fin.elim0 target
  | cons v vertices ih=>
    rcases target with ⟨target,htarget⟩
    cases target with
    | zero=>
      have hm:p∈v.ports:=(howner ⟨0,by simp⟩).mpr rfl
      have hc:v.ports.count p=1:=List.count_eq_one_of_mem (hnodup v (by simp)) hm
      have hno:∀w∈vertices,p∉w.ports:=by
        intro w hw hp
        obtain ⟨j,hj,he⟩:=List.mem_iff_getElem.mp hw
        have hf:((⟨j+1,by simpa only [List.length_cons] using Nat.succ_lt_succ hj⟩:Fin (v::vertices).length).val)=0:=
          (howner ⟨j+1,by simpa only [List.length_cons] using Nat.succ_lt_succ hj⟩).mp (by change p∈vertices[j].ports;rw [he];exact hp)
        dsimp only at hf
        omega
      rw [ownerPairs,fibre_values_append,fibre_portPairs,hc,fibre_empty n (start+1) p vertices hno,List.append_nil]
      rfl
    | succ target=>
      have hm:p∉v.ports:=by
        intro h
        have he:((⟨0,by simp⟩:Fin (v::vertices).length).val)=target+1:=(howner ⟨0,by simp⟩).mp h
        dsimp only at he
        omega
      have hc:v.ports.count p=0:=List.count_eq_zero.mpr hm
      have hj:target<vertices.length:=by simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ htarget
      have ho:∀j:Fin vertices.length,p∈vertices[j.val].ports ↔j.val=target:=by
        intro j
        have h:=howner ⟨j.val+1,by simpa only [List.length_cons] using Nat.succ_lt_succ j.isLt⟩
        dsimp only at h
        constructor
        · intro hp;have he:=h.mp hp;omega
        · intro he;exact h.mpr (by omega)
      have ht:=ih (start+1) ⟨target,hj⟩ (fun w hw=>hnodup w (List.mem_cons_of_mem v hw)) ho
      rw [ownerPairs,fibre_values_append,fibre_portPairs,hc,List.replicate_zero,List.nil_append]
      simpa only [show start+(target+1)=start+1+target by omega] using ht
/-- Original well-formed literal network data gives the EXACT SINGLETON global-port owner fibre. -/
theorem original_fibre (net:SemiprimeD1TensorNetwork.Network) (hw:SemiprimeD1TensorNetwork.WellFormed net)
    (p:Fin (SemiprimeD1TensorNetwork.scope net.rows)) :
    SemiprimeD1StackOwnerFibre.values (unary p.val) (ownerPairs net.leftCount 0 net.left.toList)=
      [ownerWord net.leftCount (SemiprimeD1TensorNetworkLayout.leftGroup net.rows p).val] :=by
  let target:=SemiprimeD1TensorNetworkLayout.leftGroup net.rows p
  have h:=fibre_unique net.leftCount 0 p.val net.left.toList
    ⟨target.val,by simpa only [Vector.length_toList] using target.isLt⟩
  dsimp only at h
  simp only [Nat.zero_add] at h
  apply h
  · intro v hv
    apply SemiprimeD1TensorNetworkLayout.vertex_ports_nodup net hw v
    exact List.mem_append_left _ hv
  · intro j
    let owner:Fin net.leftCount:=⟨j.val,by simpa only [Vector.length_toList] using j.isLt⟩
    rw [Vector.getElem_toList,hw.1 owner,SemiprimeD1TensorNetworkLayout.leftGroup_mem]
    constructor
    · intro he
      exact (congrArg Fin.val he).symm
    · intro he
      exact Fin.ext he.symm
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexEncoding
