/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeFieldBounds
import RiemannGaussian.SemiprimeD1StackRename

/-! # Literal finite-bytecode field parser
The frozen parser's six finite register settings become fixed control labels.
The final valid flag is physically pushed onto a fourth Boolean stack. Every
parser transition executes a literal stack instruction or static jump; there
is no opaque parser opcode or input-dependent label catalogue.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
namespace F
export SemiprimeD1TensorTapeFieldMachine (Stack PC Registers Alphabet program)
end F
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B

/-- Four fixed Boolean stacks; the extra stack receives the actual validity bit. -/
abbrev Stack := F.Stack⊕Unit
/-- Fixed finite parser-state labels plus terminal flag-write/halt labels. -/
abbrev Label := (F.PC×F.Registers)⊕(F.Registers⊕Unit)

/-- Enter one fixed parser state/register pair. -/
def active (pc:F.PC) (v:F.Registers) : Label := .inl (pc,v)
/-- Enter the actual physical validity-bit write. -/
def terminal (v:F.Registers) : Label := .inr (.inl v)
/-- The unique final literal halt label. -/
def stop : Label := .inr (.inr ())

/-- Explicit literal instruction table; finite register functions are evaluated
only on the fixed label, never on a dynamic word or native counter. -/
def code : Label→B.Instruction Stack Label
  | .inl (.tagPop,_) => .pop (.inl .input)
      (active .tagBranch (none,false))
      (active .tagBranch (some false,true))
      (active .tagBranch (some true,false))
  | .inl (.tagBranch,v) => .jump (active (if v.1==some true then .dataPop else .reversePop) v)
  | .inl (.dataPop,_) => .pop (.inl .input)
      (active .dataBranch (none,false))
      (active .dataBranch (some false,false))
      (active .dataBranch (some true,false))
  | .inl (.dataBranch,v) => .jump (active (if v.1.isSome then .dataPush else .reversePop) v)
  | .inl (.dataPush,v) => .push (.inl .scratch) (v.1.getD false) (active .tagPop v)
  | .inl (.reversePop,v) => .pop (.inl .scratch)
      (active .reverseBranch (none,v.2))
      (active .reverseBranch (some false,v.2))
      (active .reverseBranch (some true,v.2))
  | .inl (.reverseBranch,v) => .jump (if v.1.isSome then active .reversePush v else terminal v)
  | .inl (.reversePush,v) => .push (.inl .output) (v.1.getD false) (active .reversePop v)
  | .inr (.inl v) => .push (.inr ()) v.2 stop
  | .inr (.inr _) => .halt

/-- Actual source configuration encoded entirely by fixed labels and physical stacks. -/
def Rel (source:Turing.TM2.Cfg F.Alphabet F.PC F.Registers)
    (aux:Unit→List Bool) (target:B.State Stack Label) : Prop :=
  target.pc=some (match source.l with | none=>terminal source.var | some pc=>active pc source.var) ∧
    target.store=Sum.elim source.stk aux

/-- Literal pop dispatch preserves the finite-register tag for every actual top bit. -/
theorem choose_active (pc:F.PC) (flag:Option Bool→Bool) (top:Option Bool) :
    SemiprimeD1StackBytecode.choose (active pc (none,flag none))
      (active pc (some false,flag (some false))) (active pc (some true,flag (some true))) top=
      active pc (top,flag top) := by
  cases top with
  | none => rfl
  | some bit => cases bit <;> rfl

/-- The tag pop's three literal finite outcomes encode its actual register update. -/
theorem choose_tag (top:Option Bool) :
    SemiprimeD1StackBytecode.choose (active .tagBranch (none,false))
      (active .tagBranch (some false,true)) (active .tagBranch (some true,false)) top=
      active .tagBranch (top,top==some false) := by
  cases top with
  | none => rfl
  | some bit => cases bit <;> rfl

/-- Data/reverse pops preserve their fixed second register bit. -/
theorem choose_plain (pc:F.PC) (valid:Bool) (top:Option Bool) :
    SemiprimeD1StackBytecode.choose (active pc (none,valid))
      (active pc (some false,valid)) (active pc (some true,valid)) top=
      active pc (top,valid) := by
  cases top with
  | none => rfl
  | some bit => cases bit <;> rfl

/-- One original parser transition is one actually executed literal bytecode transition. -/
theorem execute_rel (pc:F.PC) (v:F.Registers) (store:F.Stack→List Bool)
    (aux:Unit→List Bool) (target:B.State Stack Label)
    (h:Rel ⟨some pc,v,store⟩ aux target) :
    Rel (Turing.TM2.stepAux (F.program pc) v store) aux
      (B.execute (code (active pc v)) target) := by
  rcases h with ⟨_,hs⟩
  rcases v with ⟨bit,valid⟩
  cases pc <;> cases bit with
  | none => cases valid <;> simp only [Rel,code,F.program,B.execute,Turing.TM2.stepAux,
      hs,Sum.elim_inl,SemiprimeD1StackRename.payload_update,active,terminal,and_self,and_true] <;>
      first | rfl | exact congrArg some (choose_tag _) | exact congrArg some (choose_plain _ _ _) | simp
  | some bit => cases bit <;> cases valid <;> simp only [Rel,code,F.program,B.execute,Turing.TM2.stepAux,
      hs,Sum.elim_inl,SemiprimeD1StackRename.payload_update,active,terminal,and_self,and_true] <;>
      first | rfl | exact congrArg some (choose_tag _) | exact congrArg some (choose_plain _ _ _) | simp
/-- Actual one-step correspondence, retaining arbitrary auxiliary flag-stack tail. -/
theorem step_rel (source out:Turing.TM2.Cfg F.Alphabet F.PC F.Registers)
    (aux:Unit→List Bool) (target:B.State Stack Label) (h:Rel source aux target)
    (hs:SemiprimeD1TensorTapeFieldMachine.step source=some out) :
    ∃finish,B.step code target=some finish ∧ Rel out aux finish := by
  cases source with
  | mk pc v store =>
    cases pc with
    | none => simp [SemiprimeD1TensorTapeFieldMachine.step,Turing.TM2.step] at hs
    | some pc =>
      have he:out=Turing.TM2.stepAux (F.program pc) v store:=by
        exact (Option.some.inj hs).symm
      subst out
      refine ⟨B.execute (code (active pc v)) target,?_,execute_rel pc v store aux target h⟩
      have hp:target.pc=some (active pc v):=h.1
      simp only [B.step,SemiprimeD1StackBytecode.step,hp,Option.map_some]

/-- Every actual parser path executes the literal compiled instructions, step for step. -/
theorem executes_rel {fuel:ℕ} {source out:Turing.TM2.Cfg F.Alphabet F.PC F.Registers}
    (path:SemiprimeD1TensorTapeFieldMachine.Executes fuel source out)
    (aux:Unit→List Bool) (target:B.State Stack Label) (h:Rel source aux target) :
    ∃finish,B.run code fuel target=some finish ∧ Rel out aux finish := by
  induction path generalizing target with
  | refl c => exact ⟨target,rfl,h⟩
  | @next fuel source mid out hs path ih =>
    obtain ⟨next,hnext,hrel⟩:=step_rel source mid aux target h hs
    obtain ⟨finish,hfinish,hout⟩:=ih next hrel
    refine ⟨finish,?_,hout⟩
    rw [show fuel+1=1+fuel by omega,SemiprimeD1StackCopy.run_add]
    change (B.step code target).bind (B.run code fuel)=some finish
    rw [hnext,Option.bind_some,hfinish]

/-- Physical initial input plus an arbitrary existing validity-bit stack tail. -/
def initial (xs extra:List Bool) : B.State Stack Label :=
  ⟨some (active .tagPop (none,false)),none,
    Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents xs [] []) (fun _=>extra)⟩

/-- Actual computed outputs, including physically written validity and exact unconsumed suffix. -/
def final (xs extra:List Bool) : B.State Stack Label :=
  ⟨none,none,Sum.elim
    (SemiprimeD1TensorTapeFieldMachine.contents (SemiprimeSourceHistogramKeyBits.split xs).rest []
      (SemiprimeSourceHistogramKeyBits.split xs).first)
    (fun _=>(SemiprimeSourceHistogramKeyBits.split xs).valid::extra)⟩

/-- Terminal finite-register information is written by an actual push and halt. -/
theorem terminal_run (v:F.Registers) (store:F.Stack→List Bool) (extra:List Bool)
    (target:B.State Stack Label)
    (h:Rel (⟨none,v,store⟩:Turing.TM2.Cfg F.Alphabet F.PC F.Registers) (fun _=>extra) target) :
    B.run code 2 target=some (⟨none,none,Sum.elim store (fun _=>v.2::extra)⟩:B.State Stack Label) := by
  have hp:target.pc=some (terminal v):=h.1
  have hs:target.store=Sum.elim store (fun _=>extra):=h.2
  simp only [B.run,SemiprimeD1StackBytecode.run,Function.iterate_succ_apply,
    Function.iterate_zero_apply,Option.bind_some,B.step,SemiprimeD1StackBytecode.step,hp,
    Option.map_some,code,terminal,B.execute,SemiprimeD1StackBytecode.execute,stop,hs]
  congr 2
  funext k
  cases k <;> simp [Function.update]

/-- Complete compiled parser, including malformed input and final physical flag write. -/
theorem parse_run (xs extra:List Bool) :
    B.run code (SemiprimeD1TensorTapeFieldExecution.fieldSteps xs+2) (initial xs extra)=
      some (final xs extra) := by
  have path:=SemiprimeD1TensorTapeFieldExecution.parse_exec xs (none,false) [] []
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.reverse_nil,List.nil_append,List.append_nil] at path
  have h:Rel (SemiprimeD1TensorTapeFieldMachine.config (some .tagPop) (none,false) xs [] [])
      (fun _=>extra) (initial xs extra):=⟨rfl,rfl⟩
  obtain ⟨finish,hfinish,hrel⟩:=executes_rel path (fun _=>extra) (initial xs extra) h
  rw [SemiprimeD1StackCopy.run_add,hfinish,Option.bind_some]
  exact terminal_run _ _ extra finish hrel

/-- One fixed finite Boolean-stack machine after eliminating all parser registers into labels. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine (.inl .input) (.inl .output)
  (active .tagPop (none,false)) code

/-- Concrete true machine-time bound for the compiled parser, without a parser opcode. -/
def parseInTime (xs extra:List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackBytecode.configuration (initial xs extra))
      (some (SemiprimeD1StackBytecode.configuration (final xs extra))) (4*xs.length+8) := by
  apply SemiprimeD1StackBytecode.evalsCorrect (.inl .input) (.inl .output) (active .tagPop (none,false)) code
  refine ⟨⟨SemiprimeD1TensorTapeFieldExecution.fieldSteps xs+2,parse_run xs extra⟩,?_⟩
  have h:=SemiprimeD1TensorTapeFieldExecution.fieldSteps_le xs
  change SemiprimeD1TensorTapeFieldExecution.fieldSteps xs+2 ≤ 4*xs.length+8
  omega
/-- The compiled program uses exactly four fixed Boolean stacks. -/
theorem stack_card : Fintype.card Stack=4 := by decide

/-- All 55 register/syntax/terminal labels are fixed before the input tape. -/
theorem label_card : Fintype.card Label=55 := by decide

/-- Actual framed-field bytecode execution, including the physically written true flag. -/
theorem framed_run (word tail extra:List Bool) :
    B.run code (8*word.length+6) (initial (SemiprimeSourceHistogramKeyBits.frame word tail) extra)=
      some (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word)
        (fun _=>true::extra)⟩:B.State Stack Label) := by
  have h:=parse_run (SemiprimeSourceHistogramKeyBits.frame word tail) extra
  have hs:=SemiprimeSourceHistogramKeyBits.split_frame word tail
  simpa only [SemiprimeD1TensorTapeFieldBounds.fieldSteps_frame,final,hs.1,hs.2.1,hs.2.2] using h

/-- A real framed parser machine certificate, independent of the unconsumed tail length. -/
def framedInTime (word tail extra:List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackBytecode.configuration (initial (SemiprimeSourceHistogramKeyBits.frame word tail) extra))
      (some (SemiprimeD1StackBytecode.configuration
        (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word)
          (fun _=>true::extra)⟩:B.State Stack Label))) (8*word.length+6) := by
  apply SemiprimeD1StackBytecode.evalsCorrect (.inl .input) (.inl .output) (active .tagPop (none,false)) code
  exact ⟨⟨8*word.length+6,framed_run word tail extra⟩,le_refl _⟩

/-- Every reached bytecode stack is bounded from actual initial payload and executed steps. -/
theorem prefix_bound (xs extra:List Bool) (fuel:ℕ) (out:B.State Stack Label)
    (hr:B.run code fuel (initial xs extra)=some out) :
    ∀k,(out.store k).length ≤ xs.length+extra.length+fuel := by
  apply SemiprimeD1StackCopy.run_bound code fuel (xs.length+extra.length) _ out ?_ hr
  intro k
  cases k with
  | inl k => cases k <;> simp [initial,SemiprimeD1TensorTapeFieldMachine.contents]
  | inr k => cases k; simp [initial]

/-- All actual target-machine prefixes have a linear total stack-cell bound. -/
theorem machine_prefix_cells (xs extra:List Bool) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel]
      (some (SemiprimeD1StackBytecode.configuration (initial xs extra)))=some cfg) :
    (cfg.stk (.inl (.input:F.Stack))).length+(cfg.stk (.inl (.scratch:F.Stack))).length+
      (cfg.stk (.inl (.output:F.Stack))).length+(cfg.stk (.inr ())).length ≤
      4*(xs.length+extra.length+fuel) := by
  have he:=SemiprimeD1StackBytecode.run_correct (.inl (.input:F.Stack)) (.inl (.output:F.Stack))
    (active .tagPop (none,false)) code fuel (initial xs extra)
  change (B.run code fuel (initial xs extra)).map SemiprimeD1StackBytecode.configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel]
      (some (SemiprimeD1StackBytecode.configuration (initial xs extra))) at he
  cases hc:B.run code fuel (initial xs extra) with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:SemiprimeD1StackBytecode.configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    have h:=prefix_bound xs extra fuel out hc
    have h0:=h (.inl (.input:F.Stack))
    have h1:=h (.inl (.scratch:F.Stack))
    have h2:=h (.inl (.output:F.Stack))
    have h3:=h (.inr ())
    change (out.store (.inl (.input:F.Stack))).length+(out.store (.inl (.scratch:F.Stack))).length+
      (out.store (.inl (.output:F.Stack))).length+(out.store (.inr ())).length ≤ _
    omega
end RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
