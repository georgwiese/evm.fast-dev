import InitECandidate.Solver.Input.RootBoundaryScratchFrame
import InitECandidate.Solver.Mpt.WitnessStepPrefixNormal

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Genuine complete step returns reach the actual parsed suffix with both
original databases intact. All parser data and frames follow from that run. -/
theorem step_parsed_normal (kind : Mpt.WitnessStep.Kind) (input : Guest.InputBlob)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length cursor limit : BitVec 64)
    (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (fits : pointer.toNat+length.toNat<2^64) (installed : OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (Mpt.WitnessStep.body kind)=(some (.returned value),post)) :
    ∃ ready inner answer,RootBoundary input ready ∧ Mpt.WitnessStep.parsed kind pointer length answer ∧
      Rlp.Validation.Arena ready cursor limit ∧ Rlp.Validation.Above source ready cursor.toNat ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧ OriginalCode.Installed ready.code ∧
      (∀ key,ready.globals.lookup key=source.globals.lookup key) ∧
      ready.locals.lookup (ofString "it")=some answer ∧
      ready.locals.lookup (ofString "db")=some (.val (.word db)) ∧
      ready.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧ ready.locals.lookup (ofString "n")=some (.val (.word length)) ∧
      evaluateHOLFiniteState ready (Mpt.WitnessStep.afterRlp kind)=(some (.returned value),inner) ∧
      post=QueryBranch.restore source "it" (QueryBranch.restore (Mpt.WitnessStep.tupleEntry source) "e" inner) := by
  obtain ⟨ready,inner,answer,parsed,nextArena,above,domain,endian,codeEq,globals,itemCell,nextDb,nextPointer,nextLength,forward,price,continued,endpoint⟩:=
    Mpt.WitnessStep.parsed_suffix_normal kind source post db pointer length cursor limit dbCell pointerCell lengthCell arena fits installed value normal
  have dbEq : ready.locals.lookup (ofString "db")=source.locals.lookup (ofString "db"):=nextDb.trans dbCell.symm
  have nextBoundary:=boundary.scratch_frame input source ready cursor below (globals _) domain endian dbEq above
  have nextInstalled : OriginalCode.Installed ready.code:=by rw [codeEq]; exact installed
  exact ⟨ready,inner,answer,nextBoundary,parsed,nextArena,above,domain,endian,codeEq,nextInstalled,globals,itemCell,nextDb,nextPointer,nextLength,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.step_parsed_normal
