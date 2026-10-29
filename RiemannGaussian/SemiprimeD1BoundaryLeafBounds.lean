/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsTableBounds
import RiemannGaussian.SemiprimeD1BoundaryLeafCanonical

/-! # Retained native boundary leaf work -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeafBounds
open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryRecords (Entry Tensor size tableEntries)
open SemiprimeD1BoundaryRecordsReduction (GoodEntries)
open SemiprimeD1BoundaryRecordsGroupBounds
open SemiprimeD1BoundaryRecordsContractBounds
open SemiprimeD1BoundaryRecordsAttachBounds
open SemiprimeD1BoundaryRecordsSeedBounds
open SemiprimeD1BoundaryRecordsTableBounds
open SemiprimeD1JetAxes (Context)

/-- A join restores the real original assignment address. -/
theorem attach_keys (ctx : Context) (source target : List Nat) (K : Nat)
    (acc table : List Entry) (hg : GoodEntries ctx acc) (hk : Keys K acc) :
    Keys K (SemiprimeD1BoundaryRecords.attach ctx source target acc table).value := by
  have hp:=requests_properties ctx source target K acc hg hk
  unfold SemiprimeD1BoundaryRecords.attach
  intro e he
  apply lookupFuel_keys ctx _ _ _ K (by omega) ?_ e
    ((SemiprimeD1BoundaryRecordsSort.sort_perm _).mem_iff.mp he)
  intro e he
  exact (hp e ((SemiprimeD1BoundaryRecordsSort.sort_perm _).mem_iff.mp he)).2.2

/-- Conservative literal-storage acquisition factor for one vertex. -/
def vertexBudget (ctx : Context) (ports : List Nat) (K W : Nat) (v : Vertex) : Nat :=
  tableBudget ctx v.ports.length*(SemiprimeD1TensorTables.storage v.table+1)+
  attachBudget ctx ports v.ports K (recordBudget ctx v.ports.length) W*
    (SemiprimeD1TensorTables.storage v.table+1)+v.ports.length+5

/-- Conservative sum of literal-storage vertex factors. -/
def verticesBudget (ctx : Context) (ports : List Nat) (K W : Nat) (vs : List Vertex) : Nat :=
  (vs.map (vertexBudget ctx ports K W)).sum+1

/-- Each literal vertex is acquired once; repeated joins keep the same N
accumulator records and never scan the N-by-table Cartesian product. -/
theorem multiplyVertices_clock (ctx : Context) (ports : List Nat) (K W : Nat)
    (vs : List Vertex) (acc : List Entry) (hvs : SemiprimeD1LeafCounter.Good ctx vs)
    (hg : GoodEntries ctx acc) (hk : Keys K acc) (hn : acc.length≤2^W) :
    (multiplyVertices ctx ports vs acc).clock≤ verticesBudget ctx ports K W vs*(2^W+1) := by
  induction vs generalizing acc with
  | nil => simp only [multiplyVertices,verticesBudget,List.map_nil,List.sum_nil,Nat.zero_add,Nat.one_mul]; omega
  | cons v vs ih =>
    have hv:=hvs v List.mem_cons_self
    obtain ⟨htg,htk,htn⟩:=table_properties ctx v.table hv
    have ht:=table_clock ctx v.table hv
    have ha:=attach_clock_pow ctx ports v.ports K (recordBudget ctx v.ports.length) W acc
      (tableEntries v.table).value hg hk
      (fun e he => size_le ctx v.ports.length e (htg e he) (htk e he))
      (fun e he => (htg e he).1.le) hn
    have hgood:=SemiprimeD1BoundaryRecordsCanonical.attach_good ctx ports v.ports acc (tableEntries v.table).value
    have hkeys:=attach_keys ctx ports v.ports K acc (tableEntries v.table).value hg hk
    have hlength:=SemiprimeD1BoundaryRecordsCanonical.attach_length ctx ports v.ports acc (tableEntries v.table).value
    have tail:=ih _ (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) hgood hkeys
      (by rw [hlength]; exact hn)
    have ha' : (SemiprimeD1BoundaryRecords.attach ctx ports v.ports acc (tableEntries v.table).value).clock≤
        attachBudget ctx ports v.ports K (recordBudget ctx v.ports.length) W*
          (SemiprimeD1TensorTables.storage v.table+1)*(2^W+1) := by
      apply ha.trans
      have hh : 2^W+(tableEntries v.table).value.length+1≤
          (SemiprimeD1TensorTables.storage v.table+1)*(2^W+1) := by nlinarith
      exact (Nat.mul_le_mul_left _ hh).trans_eq (by ring)
    have ht':=ht.trans (Nat.le_mul_of_pos_right _ (by omega : 0<2^W+1))
    have hm : v.ports.length+5≤(v.ports.length+5)*(2^W+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    simp only [multiplyVertices,verticesBudget,List.map_cons,List.sum_cons]
    change _≤(vertexBudget ctx ports K W v+
      (vs.map (vertexBudget ctx ports K W)).sum+1)*(2^W+1)
    rw [show vertexBudget ctx ports K W v =
      tableBudget ctx v.ports.length*(SemiprimeD1TensorTables.storage v.table+1)+
      attachBudget ctx ports v.ports K (recordBudget ctx v.ports.length) W*
        (SemiprimeD1TensorTables.storage v.table+1)+v.ports.length+5 from rfl]
    change _≤((vs.map (vertexBudget ctx ports K W)).sum+1)*(2^W+1) at tail
    nlinarith only [ht',ha',tail,hm]

/-- Exact literal table cardinality, not a storage oracle. -/
theorem table_length {n : Nat} (t : SemiprimeD1TensorTables.Table n) :
    (tableEntries t).value.length=2^n := by
  induction t with
  | leaf ws => rfl
  | fork l r ihl ihr => simp only [tableEntries,List.length_append,List.length_map,ihl,ihr,pow_succ]; omega

/-- Sharp per-vertex polynomial with literal table acquisition charged once. -/
def vertexPolynomial (ctx : Context) (ports : List Nat) (K W : Nat) (v : Vertex) : Nat :=
  tableBudget ctx v.ports.length*(ctx.rank*(3*ctx.precision+4)+3)+
  2*attachBudget ctx ports v.ports K (recordBudget ctx v.ports.length) W+v.ports.length+5

/-- Sum of sharp per-vertex polynomial factors. -/
def verticesPolynomial (ctx : Context) (ports : List Nat) (K W : Nat) (vs : List Vertex) : Nat :=
  (vs.map (vertexPolynomial ctx ports K W)).sum+1

/-- Sharp literal-vertex bound: setup and table count each contribute only one
catalogue. No stored-input exponential is multiplied by the accumulator size. -/
theorem multiplyVertices_clock_sharp (ctx : Context) (ports : List Nat) (K W : Nat)
    (vs : List Vertex) (acc : List Entry) (hvs : SemiprimeD1LeafCounter.Good ctx vs)
    (hdeg : ∀v∈vs,v.ports.length≤ W)
    (hg : GoodEntries ctx acc) (hk : Keys K acc) (hn : acc.length≤2^W) :
    (multiplyVertices ctx ports vs acc).clock≤ verticesPolynomial ctx ports K W vs*(2^W+1) := by
  induction vs generalizing acc with
  | nil => simp only [multiplyVertices,verticesPolynomial,List.map_nil,List.sum_nil,Nat.zero_add,Nat.one_mul]; omega
  | cons v vs ih =>
    have hv:=hvs v List.mem_cons_self
    have hd:=hdeg v List.mem_cons_self
    have hpow : (2:Nat)^v.ports.length≤2^W := Nat.pow_le_pow_right (by omega) hd
    obtain ⟨htg,htk,_⟩:=table_properties ctx v.table hv
    have ht:=table_clock ctx v.table hv
    have hstorage:=SemiprimeD1TensorTables.storage_bound ctx v.table hv
    have ht' : (tableEntries v.table).clock≤
        (tableBudget ctx v.ports.length*(ctx.rank*(3*ctx.precision+4)+3))*(2^W+1) := by
      apply ht.trans
      calc
        _ ≤ tableBudget ctx v.ports.length*((ctx.rank*(3*ctx.precision+4)+3)*2^v.ports.length) := Nat.mul_le_mul_left _ hstorage
        _ ≤ tableBudget ctx v.ports.length*((ctx.rank*(3*ctx.precision+4)+3)*(2^W+1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
        _ = _ := by ring
    have ha:=attach_clock_pow ctx ports v.ports K (recordBudget ctx v.ports.length) W acc
      (tableEntries v.table).value hg hk
      (fun e he => size_le ctx v.ports.length e (htg e he) (htk e he))
      (fun e he => (htg e he).1.le) hn
    have htable : (tableEntries v.table).value.length≤2^W := by rw [table_length]; exact hpow
    have ha' : (SemiprimeD1BoundaryRecords.attach ctx ports v.ports acc (tableEntries v.table).value).clock≤
        (2*attachBudget ctx ports v.ports K (recordBudget ctx v.ports.length) W)*(2^W+1) := by
      apply ha.trans
      have hh : 2^W+(tableEntries v.table).value.length+1≤2*(2^W+1) := by omega
      exact (Nat.mul_le_mul_left _ hh).trans_eq (by ring)
    have hgood:=SemiprimeD1BoundaryRecordsCanonical.attach_good ctx ports v.ports acc (tableEntries v.table).value
    have hkeys:=attach_keys ctx ports v.ports K acc (tableEntries v.table).value hg hk
    have hlength:=SemiprimeD1BoundaryRecordsCanonical.attach_length ctx ports v.ports acc (tableEntries v.table).value
    have tail:=ih _ (fun x hx => hvs x (List.mem_cons_of_mem _ hx))
      (fun x hx => hdeg x (List.mem_cons_of_mem _ hx)) hgood hkeys (by rw [hlength]; exact hn)
    have hm : v.ports.length+5≤(v.ports.length+5)*(2^W+1) := Nat.le_mul_of_pos_right _ (by omega)
    simp only [multiplyVertices,verticesPolynomial,List.map_cons,List.sum_cons]
    change _≤(vertexPolynomial ctx ports K W v+
      (vs.map (vertexPolynomial ctx ports K W)).sum+1)*(2^W+1)
    rw [show vertexPolynomial ctx ports K W v =
      tableBudget ctx v.ports.length*(ctx.rank*(3*ctx.precision+4)+3)+
      2*attachBudget ctx ports v.ports K (recordBudget ctx v.ports.length) W+v.ports.length+5 from rfl]
    change _≤((vs.map (vertexPolynomial ctx ports K W)).sum+1)*(2^W+1) at tail
    nlinarith only [ht',ha',tail,hm]

theorem multiplyVertices_length (ctx : Context) (ports : List Nat) (vs : List Vertex) (acc : List Entry) :
    (multiplyVertices ctx ports vs acc).value.length=acc.length := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v vs ih =>
    simp only [multiplyVertices]
    rw [ih,SemiprimeD1BoundaryRecordsCanonical.attach_length]

theorem multiplyVertices_keys (ctx : Context) (ports : List Nat) (K : Nat)
    (vs : List Vertex) (acc : List Entry) (hg : GoodEntries ctx acc) (hk : Keys K acc) :
    Keys K (multiplyVertices ctx ports vs acc).value := by
  induction vs generalizing acc with
  | nil => exact hk
  | cons v vs ih =>
    exact ih _ (SemiprimeD1BoundaryRecordsCanonical.attach_good ctx _ _ _ _)
      (attach_keys ctx _ _ K _ _ hg hk)

/-- Complete class contraction polynomial in actual port metadata. -/
def bucketPolynomial (ctx : Context) (g : SemiprimeD1BoundaryPlan.Graph) (vs : List Vertex)
    (colours : List Nat) (c W : Nat) : Nat :=
  let ports:=classPorts g colours c
  seedBudget ctx ports.1.length+
  verticesPolynomial ctx ports.1 ports.1.length W (classVertices vs colours c)+
  contractBudget ctx ports.1 ports.2 ports.1.length W+
  (g.vertices+g.edges.length+colours.length+1)^3+3

/-- The actual class incident-address bound pays its complete contraction.
The input hypotheses are intrinsic canonical literal data and measured local
widths, rather than a precomputed boundary table or entry-evaluation oracle. -/
theorem bucket_clock (ctx : Context) (g : SemiprimeD1BoundaryPlan.Graph) (vs : List Vertex)
    (colours : List Nat) (c W : Nat)
    (hg : SemiprimeD1LeafCounter.Good ctx (classVertices vs colours c))
    (hd : ∀v∈classVertices vs colours c,v.ports.length≤ W)
    (hw : (classPorts g colours c).1.length≤ W) :
    (bucket ctx g vs colours c).clock≤ bucketPolynomial ctx g vs colours c W*(2^W+1) := by
  let ports:=classPorts g colours c
  let selected:=classVertices vs colours c
  let init:=SemiprimeD1BoundaryRecords.seed ctx ports.1.length
  let products:=multiplyVertices ctx ports.1 selected init.value
  have hpow : (2:Nat)^ports.1.length≤2^W := Nat.pow_le_pow_right (by omega) hw
  have hi:=seed_clock ctx ports.1.length
  have hi' : init.clock≤ seedBudget ctx ports.1.length*(2^W+1) :=
    hi.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hpow 1))
  have hgood:=SemiprimeD1BoundaryRecordsCanonical.seed_good ctx ports.1.length
  have hkey:=seed_keys ctx ports.1.length
  have hn : init.value.length≤2^W := by rw [seed_length]; exact hpow
  have hm:=multiplyVertices_clock_sharp ctx ports.1 ports.1.length W selected init.value hg hd hgood hkey hn
  have hmg:=SemiprimeD1BoundaryLeafCanonical.multiplyVertices_good ctx ports.1 selected init.value hgood
  have hmk:=multiplyVertices_keys ctx ports.1 ports.1.length selected init.value hgood hkey
  have hmn : products.value.length≤2^W := by rw [multiplyVertices_length]; exact hn
  have hc:=contract_clock_pow ctx ports.1 ports.2 ports.1.length W products.value hmg hmk hmn
  change init.clock+products.clock+(SemiprimeD1BoundaryRecords.contract ctx ports.1 ports.2 products.value).clock+
    (g.vertices+g.edges.length+colours.length+1)^3+3≤_
  unfold bucketPolynomial
  change _≤(seedBudget ctx ports.1.length+verticesPolynomial ctx ports.1 ports.1.length W selected+
    contractBudget ctx ports.1 ports.2 ports.1.length W+(g.vertices+g.edges.length+colours.length+1)^3+3)*(2^W+1)
  have hp : (g.vertices+g.edges.length+colours.length+1)^3+3≤
      ((g.vertices+g.edges.length+colours.length+1)^3+3)*(2^W+1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith only [hi',hm,hc,hp]

/-- Grouping never allocates an additional address record. -/
theorem group_length (ctx : Context) : (es : List Entry) →
    (SemiprimeD1BoundaryRecords.group ctx es).value.length≤ es.length
  | [] => by simp [SemiprimeD1BoundaryRecords.group]
  | [a] => by simp [SemiprimeD1BoundaryRecords.group]
  | a::b::rest => by
    rw [SemiprimeD1BoundaryRecords.group]
    split
    · exact (group_length ctx _).trans (by simp)
    · simpa only [List.length_cons] using Nat.add_le_add_right (group_length ctx (b::rest)) 1
termination_by es => es.length

theorem contract_length (ctx : Context) (source target : List Nat) (es : List Entry) :
    (SemiprimeD1BoundaryRecords.contract ctx source target es).value.length≤ es.length := by
  apply (group_length ctx _).trans
  rw [SemiprimeD1BoundaryRecordsSort.sort_length,SemiprimeD1BoundaryRecordsCanonical.rekey_length]

theorem contract_keys (ctx : Context) (source target : List Nat) (es : List Entry) :
    Keys target.length (SemiprimeD1BoundaryRecords.contract ctx source target es).value := by
  apply group_keys
  intro e he
  exact rekey_keys source target es e ((SemiprimeD1BoundaryRecordsSort.sort_perm _).mem_iff.mp he)

/-- Complete consecutive-merge polynomial in actual port metadata. -/
def mergePolynomial (ctx : Context) (left right : Tensor) (W : Nat) : Nat :=
  let ports:=unionPorts left.ports right.ports
  let target:=remainingPorts left.ports right.ports
  seedBudget ctx ports.length+
  2*attachBudget ctx ports left.ports ports.length (recordBudget ctx left.ports.length) W+
  2*attachBudget ctx ports right.ports ports.length (recordBudget ctx right.ports.length) W+
  contractBudget ctx ports target ports.length W+
  (left.ports.length+right.ports.length+1)^4+7

/-- A real consecutive merge pays two full joins and a contraction, each
linear in the measured union catalogue. Both tables stay explicit. -/
theorem merge_clock (ctx : Context) (left right : Tensor) (W : Nat)
    (hlg : GoodEntries ctx left.entries) (hrg : GoodEntries ctx right.entries)
    (hlk : Keys left.ports.length left.entries) (hrk : Keys right.ports.length right.entries)
    (hln : left.entries.length≤2^W) (hrn : right.entries.length≤2^W)
    (hw : (unionPorts left.ports right.ports).length≤ W) :
    (SemiprimeD1BoundaryLeaf.merge ctx left right).clock≤ mergePolynomial ctx left right W*(2^W+1) := by
  let ports:=unionPorts left.ports right.ports
  let target:=remainingPorts left.ports right.ports
  let init:=SemiprimeD1BoundaryRecords.seed ctx ports.length
  let first:=SemiprimeD1BoundaryRecords.attach ctx ports left.ports init.value left.entries
  let second:=SemiprimeD1BoundaryRecords.attach ctx ports right.ports first.value right.entries
  have hpow : (2:Nat)^ports.length≤2^W := Nat.pow_le_pow_right (by omega) hw
  have hi:=seed_clock ctx ports.length
  have hi' : init.clock≤ seedBudget ctx ports.length*(2^W+1) :=
    hi.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hpow 1))
  have hig:=SemiprimeD1BoundaryRecordsCanonical.seed_good ctx ports.length
  have hik:=seed_keys ctx ports.length
  have hin : init.value.length≤2^W := by rw [seed_length]; exact hpow
  have hf:=attach_clock_pow ctx ports left.ports ports.length (recordBudget ctx left.ports.length) W init.value left.entries hig hik
    (fun e he => size_le ctx _ e (hlg e he) (hlk e he)) (fun e he => (hlg e he).1.le) hin
  have hfg:=SemiprimeD1BoundaryRecordsCanonical.attach_good ctx ports left.ports init.value left.entries
  have hfk:=attach_keys ctx ports left.ports ports.length init.value left.entries hig hik
  have hfn : first.value.length≤2^W := by rw [SemiprimeD1BoundaryRecordsCanonical.attach_length]; exact hin
  have hs:=attach_clock_pow ctx ports right.ports ports.length (recordBudget ctx right.ports.length) W first.value right.entries hfg hfk
    (fun e he => size_le ctx _ e (hrg e he) (hrk e he)) (fun e he => (hrg e he).1.le) hfn
  have hsg:=SemiprimeD1BoundaryRecordsCanonical.attach_good ctx ports right.ports first.value right.entries
  have hsk:=attach_keys ctx ports right.ports ports.length first.value right.entries hfg hfk
  have hsn : second.value.length≤2^W := by rw [SemiprimeD1BoundaryRecordsCanonical.attach_length]; exact hfn
  have hc:=contract_clock_pow ctx ports target ports.length W second.value hsg hsk hsn
  have hf' : first.clock≤(2*attachBudget ctx ports left.ports ports.length (recordBudget ctx left.ports.length) W)*(2^W+1) := by
    apply hf.trans
    have hh : 2^W+left.entries.length+1≤2*(2^W+1) := by omega
    exact (Nat.mul_le_mul_left _ hh).trans_eq (by ring)
  have hs' : second.clock≤(2*attachBudget ctx ports right.ports ports.length (recordBudget ctx right.ports.length) W)*(2^W+1) := by
    apply hs.trans
    have hh : 2^W+right.entries.length+1≤2*(2^W+1) := by omega
    exact (Nat.mul_le_mul_left _ hh).trans_eq (by ring)
  have hm : (left.ports.length+right.ports.length+1)^4+7≤
      ((left.ports.length+right.ports.length+1)^4+7)*(2^W+1) := Nat.le_mul_of_pos_right _ (by omega)
  change init.clock+first.clock+second.clock+(SemiprimeD1BoundaryRecords.contract ctx ports target second.value).clock+
    (left.ports.length+right.ports.length+1)^4+7≤_
  change _≤(seedBudget ctx ports.length+
    2*attachBudget ctx ports left.ports ports.length (recordBudget ctx left.ports.length) W+
    2*attachBudget ctx ports right.ports ports.length (recordBudget ctx right.ports.length) W+
    contractBudget ctx ports target ports.length W+(left.ports.length+right.ports.length+1)^4+7)*(2^W+1)
  nlinarith only [hi',hf',hs',hc,hm]

/-- Intrinsic complete canonical tensor, with the actual address-count bound. -/
def Ready (ctx : Context) (W : Nat) (t : Tensor) : Prop :=
  GoodEntries ctx t.entries ∧ Keys t.ports.length t.entries ∧ t.entries.length≤2^W

theorem bucket_ready (ctx : Context) (g : SemiprimeD1BoundaryPlan.Graph) (vs : List Vertex)
    (colours : List Nat) (c W : Nat) (hw : (classPorts g colours c).1.length≤ W) :
    Ready ctx W (bucket ctx g vs colours c).value := by
  refine ⟨SemiprimeD1BoundaryLeafCanonical.bucket_good ctx g vs colours c,?_,?_⟩
  · exact contract_keys ctx _ _ _
  · apply (contract_length ctx _ _ _).trans
    rw [multiplyVertices_length,seed_length]
    exact Nat.pow_le_pow_right (by omega) hw

theorem merge_ready (ctx : Context) (left right : Tensor) (W : Nat)
    (hw : (unionPorts left.ports right.ports).length≤ W) :
    Ready ctx W (SemiprimeD1BoundaryLeaf.merge ctx left right).value := by
  refine ⟨SemiprimeD1BoundaryLeafCanonical.merge_good ctx left right,?_,?_⟩
  · exact contract_keys ctx _ _ _
  · apply (contract_length ctx _ _ _).trans
    rw [SemiprimeD1BoundaryRecordsCanonical.attach_length,
      SemiprimeD1BoundaryRecordsCanonical.attach_length,seed_length]
    exact Nat.pow_le_pow_right (by omega) hw

/-- Exact maximum of actual consecutive-merge union dimensions. -/
def mergeWidth (ctx : Context) : Tensor → List Tensor → Nat
  | _,[] => 0
  | first,next::rest => max (unionPorts first.ports next.ports).length
      (mergeWidth ctx (SemiprimeD1BoundaryLeaf.merge ctx first next).value rest)

/-- Sum of the explicit polynomial per-merge factors; no record payloads occur. -/
def mergeChainPolynomial (ctx : Context) (W : Nat) : Tensor → List Tensor → Nat
  | _,[] => 1
  | first,next::rest => mergePolynomial ctx first next W+
      mergeChainPolynomial ctx W (SemiprimeD1BoundaryLeaf.merge ctx first next).value rest+3

theorem mergeAll_clock (ctx : Context) (W : Nat) (first : Tensor) (rest : List Tensor)
    (hfirst : Ready ctx W first) (hrest : ∀t∈rest,Ready ctx W t)
    (hw : mergeWidth ctx first rest≤ W) :
    (mergeAll ctx first rest).clock≤ mergeChainPolynomial ctx W first rest*(2^W+1) := by
  induction rest generalizing first with
  | nil => simp only [mergeAll,mergeChainPolynomial,Nat.one_mul]; exact Nat.le_add_left 1 (2^W)
  | cons next rest ih =>
    have hn:=hrest next List.mem_cons_self
    have hdim : (unionPorts first.ports next.ports).length≤ W := (Nat.le_max_left _ _).trans hw
    have htail : mergeWidth ctx (SemiprimeD1BoundaryLeaf.merge ctx first next).value rest≤ W :=
      (Nat.le_max_right _ _).trans hw
    have hm:=merge_clock ctx first next W hfirst.1 hn.1 hfirst.2.1 hn.2.1 hfirst.2.2 hn.2.2 hdim
    have ht:=ih _ (merge_ready ctx first next W hdim)
      (fun t ht => hrest t (List.mem_cons_of_mem _ ht)) htail
    have hpad : 3≤3*(2^W+1) := by nlinarith [Nat.zero_le (2^W)]
    simp only [mergeAll,mergeChainPolynomial]
    nlinarith only [hm,ht,hpad]

end RiemannGaussian.SemiprimeD1BoundaryLeafBounds
