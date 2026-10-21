import InitECandidate.Solver.Input.RootBoundaryScratchFrame
import InitECandidate.Solver.Mpt.WitnessStepPrefixTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Follow either original step body through its genuine caught parser.
The actual decoded item and protected scratch frame retain both original
databases at the same real suffix, with every scalar global unchanged. -/
theorem step_parsed_suffix (kind : Mpt.WitnessStep.Kind) (input : Guest.InputBlob)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length cursor limit : BitVec 64)
    (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (fits : pointer.toNat+length.toNat<2^64) (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (Mpt.WitnessStep.body kind)=(outcome,post)) :
    source.clock-post.clock≤60*length.toNat+45 ∨ ∃ ready inner answer,
      RootBoundary input ready ∧ Mpt.WitnessStep.parsed kind pointer length answer ∧
      Rlp.Validation.Arena ready cursor limit ∧ Rlp.Validation.Above source ready cursor.toNat ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧ OriginalCode.Installed ready.code ∧
      (∀ key,ready.globals.lookup key=source.globals.lookup key) ∧
      ready.locals.lookup (ofString "it")=some answer ∧
      ready.locals.lookup (ofString "db")=some (.val (.word db)) ∧
      ready.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧ ready.locals.lookup (ofString "n")=some (.val (.word length)) ∧
      ready.clock≤source.clock ∧ source.clock-ready.clock≤60*length.toNat+44 ∧
      evaluateHOLFiniteState ready (Mpt.WitnessStep.afterRlp kind)=(outcome,inner) ∧
      post=QueryBranch.restore source "it" (QueryBranch.restore (Mpt.WitnessStep.tupleEntry source) "e" inner) := by
  rcases Mpt.WitnessStep.parsed_suffix_trace kind source post db pointer length cursor limit dbCell pointerCell lengthCell arena fits installed outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨ready,inner,answer,parsed,nextArena,above,domain,endian,codeEq,heapEq,globalCells,itemCell,nextDb,nextPointer,nextLength,forward,price,continued,endpoint⟩:=reached
    have dbEq : ready.locals.lookup (ofString "db")=source.locals.lookup (ofString "db"):=nextDb.trans dbCell.symm
    have nextBoundary:=boundary.scratch_frame input source ready cursor below heapEq domain endian dbEq above
    have nextInstalled : OriginalCode.Installed ready.code:=by rw [codeEq]; exact installed
    exact Or.inr ⟨ready,inner,answer,nextBoundary,parsed,nextArena,above,domain,endian,codeEq,nextInstalled,globalCells,itemCell,nextDb,nextPointer,nextLength,forward,price,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.step_parsed_suffix
