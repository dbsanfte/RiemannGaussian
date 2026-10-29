/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueFields
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueParse
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueFields
open SemiprimeD1StackProcedureTrace (Runs runs_trans one_base)
open SemiprimeSourceHistogramKeyBits (frame)
/-- The next literal caller position after an actually validated field. -/
def nextField (part:Fin 7) : Label :=
  if h:part.val<5 then .local (.field ⟨part.val+1,by omega⟩)
  else if part=5 then .local .bankTag else .local (.record 0)
/-- Actual reader role for a statically selected field. -/
def readerRole (part:Fin 7) : Aux := if part=6 then .readerIds else .readerEdges
/-- One framed payload is parsed and its real validity byte is consumed. -/
theorem read_field (s:S.Stack→List Bool) (w:RecipeWork→List Bool)
    (f:Fin 7→List Bool) (a:Aux→List Bool) (part:Fin 7) (word tail:List Bool)
    (hi:a (readerRole part)=frame word tail) (ho:f part=[])
    (hs:a .fieldScratch=[]) (hv:a .valid=[]) :
    Runs program (8*word.length+8) (.local (.field part)) (data s w f a)
      (nextField part) (data s w (Function.update f part word)
        (Function.update a (readerRole part) tail)) := by
  let a':=Function.update a (readerRole part) tail
  let f':=Function.update f part word
  have hn:readerRole part≠.valid:=by unfold readerRole;split <;> decide
  have hv':a' .valid=[]:=by simp only [a',Function.update_of_ne hn.symm,hv]
  have hf:=field_call part (data s w f a) word tail
    (by by_cases h:part=6 <;> simpa only [fieldReader,readerRole,h,ite_true,ite_false,data_aux] using hi) ho hs hv
  have he:Function.update (Function.update (Function.update (data s w f a)
      (fieldReader part) tail) (cache part) word) (aux .valid) [true]=
      data s w f' (Function.update a' .valid [true]):=by
    simp only [fieldReader,readerRole,←show aux (if part=6 then Aux.readerIds else Aux.readerEdges)=
      (if part=6 then aux .readerIds else aux .readerEdges) by split <;> rfl,
      update_aux,update_cache,a',f']
  rw [he] at hf
  have hp:Runs program 1 (.local (.valid part))
      (data s w f' (Function.update a' .valid [true])) (nextField part) (data s w f' a'):=by
    apply one_base program _ _ (.pop (aux .valid) (.local .abort) (.local .abort) (nextField part)) _ _ rfl
    · simp only [SemiprimeD1StackBytecode.execute,data_aux,Function.update_same,SemiprimeD1StackBytecode.choose,List.head?_cons]
    · simp only [SemiprimeD1StackBytecode.execute,data_aux,Function.update_same,update_aux,
        Function.update_idem]
      simp only [List.tail_cons]
      rw [←hv',Function.update_eq_self]
  simpa only [show 8*word.length+8=(8*word.length+7)+1 by omega,a',f'] using
    runs_trans program _ _ _ _ _ _ _ _ hf hp
/-- Prefix of the seven physically acquired fields; unread caches are actually empty. -/
def parsed (p:Fin 7→List Bool) (n:Nat) (i:Fin 7) : List Bool := if i.val<n then p i else []
/-- Remaining literal six-field edge tape, retaining its actual following edge suffix. -/
def edgeRest (p:Fin 7→List Bool) (n:Nat) (tail:List Bool) : List Bool :=
  ((List.ofFn (fun i:Fin 6=>p ⟨i.val,by omega⟩)).drop n).foldr frame tail
/-- The bytes at every actual parser boundary, including the still unread ID vector tag. -/
def parseAux (p:Fin 7→List Bool) (n:Nat) (edges ids collector:List Bool) : Aux→List Bool
  | .readerEdges=>edgeRest p n edges
  | .readerIds=>true::frame (p 6) ids
  | .reversed=>collector
  | _=>[]
/-- The reader consumes the next actual edge field, including a legitimately empty half word. -/
theorem edgeRest_step (p:Fin 7→List Bool) (n:Nat) (hn:n<6) (tail:List Bool) :
    edgeRest p n tail=frame (p ⟨n,by omega⟩) (edgeRest p (n+1) tail) := by
  unfold edgeRest
  rw [List.drop_eq_getElem_cons (by simpa using hn)]
  simp only [List.getElem_ofFn,List.foldr_cons]
/-- All six edge fields are consumed; the following actual edge bytes are retained. -/
theorem edgeRest_end (p:Fin 7→List Bool) (tail:List Bool) : edgeRest p 6 tail=tail := by
  simp [edgeRest]
/-- The cache after a physical field read equals the next exact prefix cache. -/
theorem parsed_step (p:Fin 7→List Bool) (n:Nat) (hn:n<7) :
    Function.update (parsed p n) ⟨n,hn⟩ (p ⟨n,hn⟩)=parsed p (n+1) := by
  funext i
  by_cases h:i=⟨n,hn⟩
  · subst i;simp [parsed]
  · have hi:i.val≠n:=by intro he;apply h;exact Fin.ext he
    simp only [Function.update_of_ne h,parsed]
    split <;> split <;> simp_all <;> omega
/-- Static six-field parser boundary; the bank tag is read only after field six. -/
def stagePC (n:Nat) : Label :=
  if h:n<6 then .local (.field ⟨n,by omega⟩) else .local .bankTag
/-- Actual cost of the first n physical edge-field parser and validity calls. -/
def edgeTime (p:Fin 7→List Bool) : Nat→Nat
  | 0=>0
  | n+1=>edgeTime p n+(8*(p ⟨n%7,Nat.mod_lt _ (by omega)⟩).length+8)
/-- A real field call advances both byte readers and the exact parsed prefix. -/
theorem edge_step (s:S.Stack→List Bool) (w:RecipeWork→List Bool)
    (p:Fin 7→List Bool) (n:Nat) (hn:n<6) (edges ids collector:List Bool) :
    Runs program (8*(p ⟨n,by omega⟩).length+8) (stagePC n)
      (data s w (parsed p n) (parseAux p n edges ids collector))
      (stagePC (n+1)) (data s w (parsed p (n+1)) (parseAux p (n+1) edges ids collector)) := by
  let part:Fin 7:=⟨n,by omega⟩
  have hp:part≠6:=by intro h;have:=congrArg Fin.val h;dsimp [part] at this;omega
  have hr:=read_field s w (parsed p n) (parseAux p n edges ids collector)
    part (p part) (edgeRest p (n+1) edges)
    (by simpa only [readerRole,hp,ite_false,parseAux] using edgeRest_step p n hn edges)
    (by simp [parsed,part]) rfl rfl
  have ha:Function.update (parseAux p n edges ids collector) (readerRole part)
      (edgeRest p (n+1) edges)=parseAux p (n+1) edges ids collector:=by
    funext k;cases k <;> simp [readerRole,hp,parseAux]
  have hpc:nextField part=stagePC (n+1):=by
    unfold nextField stagePC
    by_cases h:n<5
    · simp only [part,h,dite_eq_left,show n+1<6 by omega]
    · have he:n=5:=by omega
      subst n;rfl
  rw [ha,parsed_step p n (by omega),hpc] at hr
  simpa only [stagePC,dite_eq_left hn,part] using hr
/-- Exact physical trace reading all first n edge fields; no parsed word is supplied to control. -/
theorem edge_prefix (s:S.Stack→List Bool) (w:RecipeWork→List Bool)
    (p:Fin 7→List Bool) (n:Nat) (hn:n≤6) (edges ids collector:List Bool) :
    Runs program (edgeTime p n) (stagePC 0)
      (data s w (parsed p 0) (parseAux p 0 edges ids collector))
      (stagePC n) (data s w (parsed p n) (parseAux p n edges ids collector)) := by
  induction n with
  | zero=>exact SemiprimeD1StackProcedureTrace.runs_refl program _ _
  | succ n ih=>
    have hlt:n<6:=by omega
    have hmod:n%7=n:=Nat.mod_eq_of_lt (by omega)
    have ht:=runs_trans program _ _ _ _ _ _ _ _ (ih (by omega))
      (edge_step s w p n hlt edges ids collector)
    simpa only [edgeTime,hmod] using ht
/-- After this wire's actual seven payloads are acquired, both reader suffixes are retained. -/
def rowAux (edges ids collector:List Bool) : Aux→List Bool
  | .readerEdges=>edges | .readerIds=>ids | .reversed=>collector | _=>[]
/-- The complete actual seven-field cache contains precisely the parsed bytes. -/
theorem parsed_all (p:Fin 7→List Bool) : parsed p 7=p := by
  funext i;unfold parsed;exact ite_eq_left i.isLt
/-- Consume the next actual ID-vector tag and parse its actual binary payload. -/
theorem bank_read (s:S.Stack→List Bool) (w:RecipeWork→List Bool)
    (p:Fin 7→List Bool) (edges ids collector:List Bool) :
    Runs program (8*(p 6).length+9) (.local .bankTag)
      (data s w (parsed p 6) (parseAux p 6 edges ids collector))
      (.local (.record 0)) (data s w p (rowAux edges ids collector)) := by
  let a:=Function.update (parseAux p 6 edges ids collector) .readerIds (frame (p 6) ids)
  have htag:Runs program 1 (.local .bankTag)
      (data s w (parsed p 6) (parseAux p 6 edges ids collector))
      (.local (.field 6)) (data s w (parsed p 6) a):=by
    apply one_base program _ _ (.pop (aux .readerIds) (.local .abort) (.local .abort) (.local (.field 6))) _ _ rfl
    · rfl
    · change Function.update _ (aux .readerIds) _=_
      exact update_aux _ _ _ _ _ _
  have hf:=read_field s w (parsed p 6) a 6 (p 6) ids
    (by simp only [a,readerRole,ite_true,Function.update_same])
    (by simp [parsed]) (by rfl) (by rfl)
  have ha:Function.update a (readerRole 6) ids=rowAux edges ids collector:=by
    funext k;cases k <;> simp [a,readerRole,parseAux,rowAux,edgeRest_end]
  have hc:Function.update (parsed p 6) 6 (p 6)=p:=by
    calc
      _=parsed p 7:=by simpa only [show (⟨6,by omega⟩:Fin 7)=6 by decide] using parsed_step p 6 (by omega)
      _=p:=parsed_all p
  rw [ha,hc] at hf
  have hnext:nextField (6:Fin 7)=.local (.record 0):=by simp [nextField]
  rw [hnext] at hf
  simpa only [show 1+(8*(p 6).length+8)=8*(p 6).length+9 by omega] using
    runs_trans program _ _ _ _ _ _ _ _ htag hf
/-- The actual edge-tape EOF peek preserves an empty half as a valid first field. -/
theorem edge_peek (s:S.Stack→List Bool) (w:RecipeWork→List Bool)
    (p:Fin 7→List Bool) (edges ids collector:List Bool) :
    Runs program 1 (.local .parse)
      (data s w (parsed p 0) (parseAux p 0 edges ids collector))
      (stagePC 0) (data s w (parsed p 0) (parseAux p 0 edges ids collector)) := by
  apply one_base program _ _ (.peek (aux .readerEdges) (.local .finalTag)
    (.local (.field 0)) (.local (.field 0))) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose _ _ _ (edgeRest p 0 edges).head?)=_
    rw [edgeRest_step p 0 (by omega)]
    rw [show (⟨0,by omega⟩:Fin 7)=0 by decide]
    cases p 0 <;> simp only [frame,List.head?_cons,SemiprimeD1StackBytecode.choose,stagePC,
      show (0:Nat)<6 by omega,dite_eq_left,show (⟨0,by omega⟩:Fin 7)=0 by decide]
  · rfl
/-- Exact same-source trace physically acquiring one complete original edge and its next ID.
The seven payloads describe existing bytes; none are machine instructions or supplied answers. -/
theorem row_read (s:S.Stack→List Bool) (w:RecipeWork→List Bool)
    (p:Fin 7→List Bool) (edges ids collector:List Bool) :
    Runs program (1+edgeTime p 6+(8*(p 6).length+9)) (.local .parse)
      (data s w (parsed p 0) (parseAux p 0 edges ids collector))
      (.local (.record 0)) (data s w p (rowAux edges ids collector)) := by
  have h6:=edge_prefix s w p 6 (by omega) edges ids collector
  have hstart:=runs_trans program _ _ _ _ _ _ _ _ (edge_peek s w p edges ids collector) h6
  exact runs_trans program _ _ _ _ _ _ _ _ hstart (bank_read s w p edges ids collector)
/-- The six physical parser costs are bounded by their actual acquired payload lengths. -/
theorem edgeTime_bound (p:Fin 7→List Bool) (cap n:Nat)
    (hp:∀i,(p i).length≤cap) : edgeTime p n≤8*n*(cap+1) := by
  induction n with
  | zero=>simp only [edgeTime,Nat.mul_zero,Nat.zero_mul,Nat.le_refl]
  | succ n ih=>
    have h:=hp ⟨n%7,Nat.mod_lt _ (by omega)⟩
    simp only [edgeTime]
    nlinarith
/-- The actual complete seven-field parser has a linear byte bound, with no external clock. -/
theorem row_read_bound (p:Fin 7→List Bool) (cap:Nat) (hp:∀i,(p i).length≤cap) :
    1+edgeTime p 6+(8*(p 6).length+9)≤56*(cap+1)+2 := by
  have h:=edgeTime_bound p cap 6 hp
  have hi:=hp 6
  omega
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueParse
