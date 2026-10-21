import InitECandidate.Solver.Mpt.CompactToNibblesProgram
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.ByteStoreLocal

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem odd_quiet (code) : Input.QuietClock.Preserves code oddGuard :=
  Input.QuietClock.conditional code oddTest oddWrite .skip
    (Input.QuietClock.sequence code _ _ (Input.QuietClock.store_byte code _ _) (Input.QuietClock.assign code _ _))
    (Input.QuietClock.skip code)

/-- Actual normal optional first-nibble writing yields a genuine0/1 k and
retains the original pointer, length and allocated output words. A failed
byte store cannot supply these continuation facts. -/
theorem odd_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length out odd : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (oddCell : source.locals.lookup (ofString "odd")=some (.val (.word odd)))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source oddGuard=(none,target)) :
    ∃ k : BitVec 64,(k=0#64 ∨ k=1#64) ∧ target.locals.lookup (ofString "k")=some (.val (.word k)) ∧
      target.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧
      target.locals.lookup (ofString "n")=some (.val (.word length)) ∧ target.locals.lookup (ofString "out")=some (.val (.word out)) := by
  by_cases zero : odd=0#64
  · have skipped : evaluateHOLFiniteState source oddGuard=(none,source):=by
      simp [oddGuard,oddTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,oddCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    have same : target=source:=(congrArg Prod.snd (normal.symm.trans skipped))
    rw [same]
    exact ⟨0#64,Or.inl rfl,kCell,pointerCell,lengthCell,outCell⟩
  · have taken : evaluateHOLFiniteState source oddGuard=evaluateHOLFiniteState source oddWrite:=by
      simp [oddGuard,oddTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,oddCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [taken] at normal
    obtain ⟨middle,storeRun,assignRun⟩:=Input.sequence_none source target _ _ normal
    have same:=Input.assign_none middle target "k" (.const 1#64) 1#64 rfl assignRun
    have kept (name : MlS) : middle.locals.lookup name=source.locals.lookup name:=by
      have info:=Input.byte_store_local name (localVar "out") (.op .and [localVar "c0",.const 15#64]) source
      unfold Input.LocalSummary at info
      rw [storeRun] at info
      exact info.1 rfl
    rw [same]
    exact ⟨1#64,Or.inr rfl,bind_lookup_same _ _ _,
      (bind_lookup_other middle "k" "p" 1#64 (by decide)).trans ((kept _).trans pointerCell),
      (bind_lookup_other middle "k" "n" 1#64 (by decide)).trans ((kept _).trans lengthCell),
      (bind_lookup_other middle "k" "out" 1#64 (by decide)).trans ((kept _).trans outCell)⟩

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.odd_quiet
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.odd_normal
