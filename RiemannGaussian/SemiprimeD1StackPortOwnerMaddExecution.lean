import RiemannGaussian.SemiprimeD1StackPortOwnerMadd
import RiemannGaussian.SemiprimeD1StackProcedureFragments
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerMaddExecution
open SemiprimeD1StackPortOwnerMadd
open SemiprimeD1StackProcedureFragments (Runs included_call)
open SemiprimeD1StackUnaryDivmod (unary)
/-- The actual preserving copy executes inside the routing procedure. -/
theorem copy_call (offset:Bool) (store:Stack→List Bool)
    (hs:store (.inr .copyScratch)=[]) (pc next:Label)
    (hc:program pc=.call (.inr (.inl (offset,0))) next) :
    Runs program (5*(store (if offset then .inl .c else .inl .a)).length+4) pc store next
      (Function.update store (if offset then .inr .output else .inr .multiplier)
        (store (if offset then .inl .c else .inl .a)++store (if offset then .inr .output else .inr .multiplier))) := by
  apply included_call program (copyStack offset) (fun p=>.inr (.inl (offset,p))) (copyStack_injective offset)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc
    (5*(store (if offset then .inl .c else .inl .a)).length+3)
    (SemiprimeD1StackCopy.state 0 none (store (if offset then .inl .c else .inl .a))
      (store (if offset then .inr .output else .inr .multiplier)) [])
    (SemiprimeD1StackCopy.done (store (if offset then .inl .c else .inl .a))
      (store (if offset then .inl .c else .inl .a)++store (if offset then .inr .output else .inr .multiplier)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · constructor
    · intro k;fin_cases k <;> cases offset <;> simp [copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hs]
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> cases offset <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,Function.update,hs]
    · intro k hk
      have hn:k≠(if offset then .inr .output else .inr .multiplier):=by
        intro he;exact hk 1 (by cases offset <;> simpa [copyStack] using he.symm)
      exact Function.update_of_ne hn _ _
/-- The actual product has no result or cost answer operand. -/
theorem product_call (store:Stack→List Bool) (a b:ℕ)
    (ha:store (.inr .multiplier)=unary a) (hb:store (.inl .b)=unary b)
    (hs:store (.inr .productScratch)=[]) (ho:store (.inr .output)=[]) :
    ∃ time ≤ 5*(a*(2*b+3)+1)+1,Runs program time (.inl .product) store (.inl .offset)
      (Function.update (Function.update store (.inr .multiplier) []) (.inr .output) (unary (a*b))) := by
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackUnaryProduct.product_run a b
  refine ⟨time+1,by omega,?_⟩
  apply included_call program productStack (fun p=>.inr (.inr p)) productStack_injective P.code P.entry
    (fun _=>rfl) (.inl .product) (.inl .offset) rfl time
    (⟨some P.entry,none,SemiprimeD1StackUnaryProduct.contents (unary a) (unary b) [] []⟩:B.State P.Stack P.Label)
    (⟨none,none,SemiprimeD1StackUnaryProduct.contents [] (unary b) [] (unary (a*b))⟩:B.State P.Stack P.Label)
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> simp [productStack,SemiprimeD1StackUnaryProduct.contents,ha,hb,hs,ho]
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> simp [productStack,SemiprimeD1StackUnaryProduct.contents,Function.update,hb,hs]
    · intro k hk
      have h0:k≠(.inr .multiplier:Stack):=by intro he;exact hk .multiplier he.symm
      have h1:k≠(.inr .output:Stack):=by intro he;exact hk .product he.symm
      simp [Function.update,h0,h1]
/-- Exact physical endpoint-slot arithmetic, preserving every acquired operand. -/
theorem madd_run (a b c:ℕ) :
    ∃ time ≤ 5*a+5*c+5*(a*(2*b+3)+1)+9,
      Runs program time (.inl .start) (data (unary a) (unary b) (unary c) [] [] [] [])
        (.inl .halt) (data (unary a) (unary b) (unary c) [] [] [] (unary (a*b+c))) := by
  let s0:=data (unary a) (unary b) (unary c) [] [] [] []
  let s1:=data (unary a) (unary b) (unary c) (unary a) [] [] []
  let s2:=data (unary a) (unary b) (unary c) [] [] [] (unary (a*b))
  have h01:Runs program (5*a+4) (.inl .start) s0 (.inl .product) s1 := by
    have h:=copy_call false s0 rfl (.inl .start) (.inl .product) rfl
    change Runs program (5*(unary a).length+4) (.inl .start) s0 (.inl .product)
      (Function.update s0 (.inr .multiplier) (unary a++[])) at h
    have he:Function.update s0 (.inr .multiplier) (unary a++[]) = s1 := by
      funext k;rcases k with k|k <;> cases k <;> simp [s0,s1,data,Function.update]
    rw [he] at h
    simpa only [unary,List.length_replicate] using h
  obtain ⟨t,ht,h12⟩:=product_call s1 a b rfl rfl rfl rfl
  have h12':Runs program t (.inl .product) s1 (.inl .offset) s2 := by
    have he:Function.update (Function.update s1 (.inr .multiplier) []) (.inr .output) (unary (a*b)) = s2 := by
      funext k;rcases k with k|k <;> cases k <;> simp [s1,s2,data,Function.update]
    rw [he] at h12
    exact h12
  have h23:Runs program (5*c+4) (.inl .offset) s2 (.inl .halt)
      (data (unary a) (unary b) (unary c) [] [] [] (unary (a*b+c))) := by
    have h:=copy_call true s2 rfl (.inl .offset) (.inl .halt) rfl
    have he:Function.update s2 (.inr .output) (unary c++unary (a*b)) =
        data (unary a) (unary b) (unary c) [] [] [] (unary (a*b+c)) := by
      funext k;rcases k with k|k <;> cases k <;> simp [s2,data,Function.update,←SemiprimeD1StackUnaryDivmod.unary_add,Nat.add_comm]
    change Runs program (5*(unary c).length+4) (.inl .offset) s2 (.inl .halt)
      (Function.update s2 (.inr .output) (unary c++unary (a*b))) at h
    rw [he] at h
    simpa only [unary,List.length_replicate] using h
  refine ⟨(5*a+4)+t+(5*c+4),by omega,?_⟩
  exact (h01.trans h12').trans h23
/-- Literal acquired-operand entry, internal to the original endpoint supplier. -/
def initial (a b c:ℕ) : C.State Stack Label :=
  ⟨some (.inl .start),none,none,data (unary a) (unary b) (unary c) [] [] [] [],[]⟩
/-- Every work stack is cleared; only the actual slot and original counters remain. -/
def done (a b c:ℕ) : C.State Stack Label :=
  ⟨none,none,none,data (unary a) (unary b) (unary c) [] [] [] (unary (a*b+c)),[]⟩
/-- Whole real nested execution, including its final halt. -/
theorem source_run (a b c:ℕ) :
    ∃ time ≤ 5*a+5*c+5*(a*(2*b+3)+1)+10,
      C.run program time (initial a b c)=some (done a b c) := by
  obtain ⟨t,ht,h⟩:=madd_run a b c
  obtain ⟨finish,hr,hout⟩:=h [] (initial a b c) ⟨rfl,rfl,rfl⟩
  refine ⟨t+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done a b c)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,
    SemiprimeD1StackCalls.execute,hdata,hframes,done]
end RiemannGaussian.SemiprimeD1StackPortOwnerMaddExecution
