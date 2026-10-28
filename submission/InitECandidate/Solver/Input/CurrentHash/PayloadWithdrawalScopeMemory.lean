import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalAllocationMemory
import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalScopeCost

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete actual withdrawal/final payload phase protects earlier caller
metadata on this same normal return, through both lexical declarations and
its real assigned allocation, loop, list and releases. -/
theorem State.withdrawal_memory {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (saved : SavedCursor source "m2" ch base)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source withdrawalScope=(some (.returned value),post)) : post.memory query=source.memory query := by
  have entry := data.withdrawal_data
  let firstState := bind source "wd" (withdrawalPointer input blob)
  let secondState := bind firstState "nwd" (BitVec.ofNat 64 (withdrawalCount input))
  have next : State input firstState blob record array ch cursor chunk out zeros length start size := data.bound "wd" (withdrawalPointer input blob) (by decide)
  have finalState : State input secondState blob record array ch cursor chunk out zeros length start size := next.bound "nwd" (BitVec.ofNat 64 (withdrawalCount input)) (by decide)
  have savedFirst : SavedCursor firstState "m2" ch base := saved.of_lookup
    ((bind_lookup_other source "wd" "m2" (withdrawalPointer input blob) (by decide)).trans saved.binding)
  have savedSecond : SavedCursor secondState "m2" ch base := savedFirst.of_lookup
    ((bind_lookup_other firstState "nwd" "m2" (BitVec.ofNat 64 (withdrawalCount input)) (by decide)).trans savedFirst.binding)
  have pointer : secondState.locals.lookup (ofString "wd")=some (.val (.word (withdrawalPointer input blob))) :=
    (bind_lookup_other firstState "nwd" "wd" (BitVec.ofNat 64 (withdrawalCount input)) (by decide)).trans (bind_lookup_same source "wd" (withdrawalPointer input blob))
  have count : secondState.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 (withdrawalCount input)))) := bind_lookup_same firstState "nwd" (BitVec.ofNat 64 (withdrawalCount input))
  let output := evaluateHOLFiniteState secondState afterNwd
  have inner := ScalarScope.declare_execute firstState output.2 "nwd" (fieldExpression 56) (BitVec.ofNat 64 (withdrawalCount input)) afterNwd output.1 next.withdrawal_data.2.1 rfl
  have innerRun : evaluateHOLFiniteState firstState afterWd=(output.1,restore firstState "nwd" output.2) := by
    rw [withdrawal_shapes.2.1]
    exact inner
  have whole := ScalarScope.declare_execute source (restore firstState "nwd" output.2) "wd" (fieldExpression 48) (withdrawalPointer input blob) afterWd output.1 entry.1 innerRun
  rw [←withdrawal_shapes.1] at whole
  have resultEq : some (.returned value)=output.1 := congrArg Prod.fst (actual.symm.trans whole)
  have memoryEq := congrArg (fun observed : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>observed.2.memory query) (actual.symm.trans whole)
  change post.memory query=output.2.memory query at memoryEq
  have returned : evaluateHOLFiniteState secondState afterNwd=(some (.returned value),output.2) := Prod.ext resultEq.symm rfl
  have frame := finalState.withdrawal_after_nwd_memory (post:=output.2) savedSecond (withdrawalPointer input blob) (withdrawalCount input) entry.2.2.1 pointer count entry.2.2.2
    query before chunkAway outAway value returned
  change output.2.memory query=source.memory query at frame
  exact memoryEq.trans frame

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.withdrawal_memory
