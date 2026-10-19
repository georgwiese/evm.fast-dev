import InitECandidate.Solver.Mpt.AccountBalanceStoreFrame
import InitECandidate.Solver.Input.LoopInvariant
import InitECandidate.Solver.Input.GlobalEffectsAtoms
import InitECandidate.Solver.Input.GlobalEffectsLoop

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem balance_body_output_safe : Input.LocalPrefix (ofString "acct_out") balanceLoopBody := by
  rw [balance_body_shape]
  exact .dec _ _ _ (by decide) (.dec _ _ _ (by decide) (.seq (.store _ _) (.assign _ _ (by decide))))

/-- The entire actual original balance loop preserves every ordinary word
outside its account object. Only real continuing iterations invoke the
body frame; index progress, byte limits and retained locals are derived. -/
theorem balance_loop_window (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer header payload flag index : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (fieldCell : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (output : Output out) (small : payload.toNat≤32) (bounded : index.toNat≤payload.toNat)
    (normal : evaluateHOLFiniteState source balanceLoop=(none,post)) :
    Rlp.Slices.Window source post out.toNat (out.toNat+56) := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    ∃ i : BitVec 64,current.locals.lookup (ofString "i")=some (.val (.word i)) ∧
      current.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag) ∧
      current.locals.lookup (ofString "acct_out")=some (.val (.word out)) ∧ i.toNat≤payload.toNat ∧
      Rlp.Slices.Window source current out.toNat (out.toNat+56)
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) (.cmp .lower (localVar "i") (field "f1" 2))=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) balanceLoopBody=(none,target) → invariant target := by
    intro current codeEq valid word observed nonzero clock target bodyRun
    obtain ⟨i,currentIndex,currentField,currentOutput,currentBound,currentWindow⟩ := valid
    have limitRead := payload_read current "f1" pointer header payload flag currentField
    simp only [eval] at limitRead
    have read : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address))
        (.cmp .lower (localVar "i") (field "f1" 2))=some (.val (.word (if i.toNat<payload.toNat then 1#64 else 0#64))) := by
      simp [evalHOLFinite,evalHOLExact,localVar,toExact,currentIndex,limitRead,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
    have active : i.toNat<payload.toNat := by
      by_contra inactive
      rw [if_neg inactive] at read
      have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using observed.symm.trans read
      exact nonzero zero
    have bodyWindow := balance_body_window (decClockHOLFinite current) target out pointer header payload flag i currentOutput currentField currentIndex output small active bodyRun
    have nextIndex := balance_body_advances (decClockHOLFinite current) target i currentIndex bodyRun
    have nextField := balance_body_safe.summary_full (decClockHOLFinite current)
    have nextOutput := balance_body_output_safe.summary_full (decClockHOLFinite current)
    unfold Input.LocalSummary at nextField nextOutput
    rw [bodyRun] at nextField nextOutput
    have number : (i+1#64).toNat=i.toNat+1 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat+1<2^64; omega)]
      rfl
    exact ⟨i+1#64,nextIndex,(nextField.1 rfl).trans currentField,(nextOutput.1 rfl).trans currentOutput,
      by rw [number]; omega,Rlp.Slices.Window.trans source current target out.toNat (out.toNat+56) currentWindow bodyWindow⟩
  have initial : invariant source := ⟨index,indexCell,fieldCell,outputCell,bounded,Rlp.Slices.Window.refl source _ _⟩
  rw [balance_loop_shape] at normal
  obtain ⟨finalIndex,finalCell,finalField,finalOutput,finalBound,window⟩ :=
    Input.loop_invariant source.code (ofString "f1") (.cmp .lower (localVar "i") (field "f1" 2)) balanceLoopBody balance_body_safe invariant step source post rfl initial normal
  exact window

theorem balance_loop_saved (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notPosition : ofString name≠ofString "pos") (notAddress : ofString name≠ofString "lp") (notIndex : ofString name≠ofString "i")
    (normal : evaluateHOLFiniteState source balanceLoop=(none,post)) :
    post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  have safe : Input.LocalPrefix (ofString name) balanceLoop := by
    rw [balance_loop_shape,balance_body_shape]
    exact .loop _ (.dec _ _ _ notPosition (.dec _ _ _ notAddress (.seq (.store _ _) (.assign _ _ notIndex))))
  have summary := safe.summary_full source
  unfold Input.LocalSummary at summary
  rw [normal] at summary
  exact summary.1 rfl

theorem balance_loop_globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code balanceLoop := by
  rw [balance_loop_shape,balance_body_shape]
  unfold balanceStore increment
  repeat first
    | apply Input.GlobalEffects.loop
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_body_output_safe
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_loop_window
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_loop_saved
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_loop_globals
