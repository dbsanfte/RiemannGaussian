/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryPlan
import RiemannGaussian.SemiprimeD1LeafCounterBounds

/-! # Sequential records for boundary contraction

Requests are sorted by the required tensor address. One forward merge attaches
the stored value, preserving a table cursor for repeated equal requests. A
second sort restores assignment order. Thus no exponentially long tensor is
rescanned for each request. Every result carries its own executed list-work
report. Coefficient operations are the existing full canonical jet routines.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryPlan (Work)
open SemiprimeD1JetAxes (Context)
/-- Complete jet words and the retained report from the existing bit operations. -/
abbrev JetRun := SemiprimeD1JetRingBits.Run

/-- A concrete keyed full-jet value, never an evaluator closure. -/
structure Entry where
  /-- Boolean address in the explicitly retained port order. -/
  key : List Bool
  /-- Complete current-context dense coefficient vector. -/
  words : List (List Bool)
  deriving Repr

/-- A finite explicit boundary table with its ordered global edge identifiers. -/
structure Tensor where
  /-- Actual boundary port order. -/
  ports : List Nat
  /-- Lexicographically ordered literal entries. -/
  entries : List Entry
  deriving Repr

/-- Physical record length, including every key/coefficient delimiter. -/
def size (e : Entry) : Nat := e.key.length+(e.words.map List.length).sum+e.words.length+2

/-- Lexicographic comparison, with false before true and exact EOF handling. -/
def compareKey : List Bool → List Bool → Work Ordering
  | [],[] => ⟨.eq,1⟩
  | [],_::_ => ⟨.lt,1⟩
  | _::_,[] => ⟨.gt,1⟩
  | a::as,b::bs =>
    if a==b then
      let tail:=compareKey as bs
      ⟨tail.value,tail.clock+3⟩
    else ⟨if a then .gt else .lt,3⟩

/-- Paid copy of all record bytes. -/
def copyEntries (es : List Entry) : Work (List Entry) :=
  ⟨es,(es.map (fun e => 3*size e+3)).sum+1⟩

/-- One stable sequential merge, with an explicit decreasing record budget. -/
def mergeFuel : Nat → List Entry → List Entry → Work (List Entry)
  | 0,xs,ys =>
    let out:=copyEntries (xs++ys)
    ⟨out.value,out.clock+xs.length+1⟩
  | _+1,[],ys => copyEntries ys
  | _+1,xs,[] => copyEntries xs
  | n+1,x::xs,y::ys =>
    let cmp:=compareKey x.key y.key
    if cmp.value==.gt then
      let tail:=mergeFuel n (x::xs) ys
      ⟨y::tail.value,cmp.clock+tail.clock+3*size y+5⟩
    else
      let tail:=mergeFuel n xs (y::ys)
      ⟨x::tail.value,cmp.clock+tail.clock+3*size x+5⟩

/-- Merge visits each input record at most once, apart from repeated head reads. -/
def merge (xs ys : List Entry) : Work (List Entry) :=
  mergeFuel (xs.length+ys.length) xs ys

/-- One bottom-up pass, pairing adjacent sorted runs. -/
def mergePass : List (List Entry) → Work (List (List Entry))
  | [] => ⟨[],1⟩
  | [xs] => ⟨[xs],1⟩
  | xs::ys::rest =>
    let head:=merge xs ys
    let tail:=mergePass rest
    ⟨head.value::tail.value,head.clock+tail.clock+3⟩

/-- Logarithmically many sequential merge passes; each pass halves run count. -/
def sortPasses : Nat → List (List Entry) → Work (List Entry)
  | _,[] => ⟨[],1⟩
  | _,[xs] => ⟨xs,1⟩
  | 0,runs =>
    let out:=copyEntries runs.flatten
    ⟨out.value,out.clock+runs.length+1⟩
  | n+1,runs =>
    let pass:=mergePass runs
    let tail:=sortPasses n pass.value
    ⟨tail.value,pass.clock+tail.clock+3⟩

/-- Closed merge sort, with `size N+1` actual passes as a safe integer budget. -/
def sort (es : List Entry) : Work (List Entry) :=
  let out:=sortPasses (Nat.size es.length+1) (es.map (fun e => [e]))
  ⟨out.value,out.clock+3*es.length+1⟩

/-- Sequential finite address lookup in a metadata port list. -/
def findPort (p : Nat) : List Nat → Work Nat
  | [] => ⟨0,1⟩
  | q::qs =>
    if p=q then ⟨0,3*(Nat.size p+Nat.size q+1)⟩ else
      let tail:=findPort p qs
      ⟨tail.value+1,tail.clock+3*(Nat.size p+Nat.size q+1)⟩

/-- Paid list bit read, defaulting to false at actual EOF. -/
def readBit : List Bool → Nat → Work Bool
  | [],_ => ⟨false,1⟩
  | b::_,0 => ⟨b,3⟩
  | _::bs,i+1 => let tail:=readBit bs i; ⟨tail.value,tail.clock+3⟩

/-- Acquire one local address from the actual source address and port lists. -/
def project (bits : List Bool) (source : List Nat) : List Nat → Work (List Bool)
  | [] => ⟨[],1⟩
  | p::ps =>
    let index:=findPort p source
    let bit:=readBit bits index.value
    let tail:=project bits source ps
    ⟨bit.value::tail.value,index.clock+bit.clock+tail.clock+3⟩

/-- False-first local assignments; only the current load is enumerated. -/
def assignments : Nat → Work (List (List Bool))
  | 0 => ⟨[[]],2⟩
  | n+1 =>
    let tail:=assignments n
    let low:=tail.value.map (false::·)
    let high:=tail.value.map (true::·)
    ⟨low++high,tail.clock+(tail.value.length+1)*(6*n+15)+3⟩

/-- Serialize the actual ordered local table once, with its full leaf payloads. -/
def tableEntries : {n : Nat} → SemiprimeD1TensorTables.Table n → Work (List Entry)
  | _,.leaf ws =>
    let copied:=SemiprimeD1JetAxes.copyVector ws
    ⟨[⟨[],copied.1⟩],copied.2+3⟩
  | _,.fork low high =>
    let left:=tableEntries low
    let right:=tableEntries high
    let lo:=left.value.map (fun e => {e with key:=false::e.key})
    let hi:=right.value.map (fun e => {e with key:=true::e.key})
    ⟨lo++hi,left.clock+right.clock+
      (left.value.map (fun e => 3*size e+5)).sum+
      (right.value.map (fun e => 3*size e+5)).sum+left.value.length+3⟩

/-- A request carries its return address and the full current accumulator. -/
structure Request where
  /-- Required local lookup address. -/
  key : List Bool
  /-- Original assignment address, restored after the sequential lookup. -/
  route : List Bool
  /-- Full accumulator to multiply by the actual looked-up tensor value. -/
  words : List (List Bool)
  deriving Repr

/-- Pack a request into an ordinary sortable record without losing its route.
The first word is metadata; coefficient arithmetic sees only the tail. -/
def Request.pack (r : Request) : Entry := ⟨r.key,r.route::r.words⟩

/-- Recover the literal route and coefficient tail after sorting. -/
def Request.unpack (r : Entry) : Request := ⟨r.key,r.words.headD [],r.words.tail⟩

/-- Generate one request per actual accumulator, preserving full original ports. -/
def requests (source target : List Nat) : List Entry → Work (List Entry)
  | [] => ⟨[],1⟩
  | e::es =>
    let address:=project e.key source target
    let tail:=requests source target es
    let r:Request:=⟨address.value,e.key,e.words⟩
    ⟨r.pack::tail.value,address.clock+tail.clock+3*size e+7⟩

/-- One forward sorted request/table merge. Equal requests reuse the current
table record; the table cursor never moves backwards. Missing means ring zero. -/
def lookupFuel (ctx : Context) : Nat → List Entry → List Entry → Work (List Entry)
  | 0,rs,_ => ⟨rs,1⟩
  | _+1,[],_ => ⟨[],1⟩
  | n+1,r::rs,[] =>
    let request:=Request.unpack r
    let zero:=SemiprimeD1JetRingBits.mul ctx request.words []
    let tail:=lookupFuel ctx n rs []
    ⟨⟨request.route,zero.words⟩::tail.value,
      zero.clock+tail.clock+3*size r+7⟩
  | n+1,r::rs,t::ts =>
    let cmp:=compareKey r.key t.key
    match cmp.value with
    | .gt =>
      let tail:=lookupFuel ctx n (r::rs) ts
      ⟨tail.value,cmp.clock+tail.clock+size t+3⟩
    | .lt =>
      let request:=Request.unpack r
      let zero:=SemiprimeD1JetRingBits.mul ctx request.words []
      let tail:=lookupFuel ctx n rs (t::ts)
      ⟨⟨request.route,zero.words⟩::tail.value,
        cmp.clock+zero.clock+tail.clock+3*size r+7⟩
    | .eq =>
      let request:=Request.unpack r
      let product:=SemiprimeD1JetRingBits.mul ctx request.words t.words
      let tail:=lookupFuel ctx n rs (t::ts)
      ⟨⟨request.route,product.words⟩::tail.value,
        cmp.clock+product.clock+tail.clock+3*size r+3*size t+7⟩

/-- Two sorts and one monotone join attach each actual local tensor value. -/
def attach (ctx : Context) (source target : List Nat) (acc table : List Entry) :
    Work (List Entry) :=
  let req:=requests source target acc
  let ordered:=sort req.value
  let joined:=lookupFuel ctx (ordered.value.length+table.length+1) ordered.value table
  let restored:=sort joined.value
  ⟨restored.value,req.clock+ordered.clock+joined.clock+restored.clock+7⟩

/-- Change to the new boundary key, retaining the whole coefficient payload. -/
def rekey (source target : List Nat) : List Entry → Work (List Entry)
  | [] => ⟨[],1⟩
  | e::es =>
    let key:=project e.key source target
    let tail:=rekey source target es
    ⟨⟨key.value,e.words⟩::tail.value,key.clock+tail.clock+3*size e+5⟩

/-- Fold one sorted equal-key run by actual canonical full-jet additions. -/
def group (ctx : Context) : List Entry → Work (List Entry)
  | [] => ⟨[],1⟩
  | [e] => ⟨[e],3*size e+3⟩
  | a::b::rest =>
    let cmp:=compareKey a.key b.key
    if cmp.value==.eq then
      let sum:=SemiprimeD1JetRingBits.add ctx a.words b.words
      let tail:=group ctx (⟨a.key,sum.words⟩::rest)
      ⟨tail.value,cmp.clock+sum.clock+tail.clock+3*size a+3*size b+7⟩
    else
      let tail:=group ctx (b::rest)
      ⟨a::tail.value,cmp.clock+tail.clock+3*size a+3⟩
termination_by es => es.length

/-- Explicit address sort/group contraction, never a random-access update. -/
def contract (ctx : Context) (source target : List Nat) (es : List Entry) :
    Work (List Entry) :=
  let keyed:=rekey source target es
  let ordered:=sort keyed.value
  let out:=group ctx ordered.value
  ⟨out.value,keyed.clock+ordered.clock+out.clock+5⟩

/-- Initialize each actual assignment with the canonical current ring unit. -/
def seed (ctx : Context) (n : Nat) : Work (List Entry) :=
  let assignments:=assignments n
  let unit:=SemiprimeD1JetAffineCoefficient.one ctx
  let es:=assignments.value.map (fun bits => (⟨bits,unit.words⟩:Entry))
  ⟨es,assignments.clock+unit.clock+
    (es.map (fun e => 3*size e+3)).sum+3⟩

/-- Proof-side exact-key value; this function is never a runtime operand. -/
noncomputable def value (ctx : Context) (es : List Entry) (bits : List Bool) :
    SemiprimeD1JetInterpretation.Carrier ctx :=
  SemiprimeD1JetInterpretation.interpret ctx
    (((es.find? (fun e => e.key==bits)).map Entry.words).getD [])

end RiemannGaussian.SemiprimeD1BoundaryRecords
