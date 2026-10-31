import InitECandidate.Solver.Mpt.CurrentWitnessStepPrefix
import InitECandidate.Solver.Mpt.WitnessResolveCost

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Price the actual parsed resolver suffix with its real current database.
No query readability, future lookup result or allocation success is assumed. -/
theorem resolve_suffix_cost (data : CurrentTable.NodeBuild.Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length : BitVec 64) (answer : ValueHOL 64) (database : CurrentTable.NodeLookup.Database source data)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (parsed : Rlp.Item.Valid pointer length.toNat answer)
    (itemCell : source.locals.lookup (ofString "it")=some answer)
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (Mpt.WitnessStep.afterRlp .resolve)).2.clock≤268 := by
  obtain ⟨header,payload,flag,answerEq,small,positive,extent,binary,listHeader⟩:=parsed
  rw [answerEq] at itemCell
  exact Mpt.WitnessResolve.suffix_cost data source pointer header payload flag database dbCell itemCell installed

/-- Every actual outcome of the unchanged current resolver is bounded by
its real parser allowance and fixed-depth Patricia lookup/constructor tail.
The physical database is below the persistent cap and survives scratch work.
The incoming query may be arbitrary, unaligned or unreadable. -/
theorem resolve_body_cost (data : CurrentTable.NodeBuild.Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length : BitVec 64) (database : CurrentTable.NodeLookup.Database source data)
    (tableBefore : (CurrentTable.New.endPointer data.table data.cap).toNat≤2952790016)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (live : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source (Mpt.WitnessStep.body .resolve)).2.clock≤60*length.toNat+281 := by
  let output:=evaluateHOLFiniteState source (Mpt.WitnessStep.body .resolve)
  rcases Mpt.CurrentWitnessStep.parsed_suffix_trace .resolve source output.2 data.table pointer length dbCell pointerCell lengthCell live fits output.1 rfl with stopped|reached
  · exact stopped.trans (by omega)
  · obtain ⟨ready,inner,answer,parsed,readyLive,frame,itemCell,nextDb,nextPointer,nextLength,forward,price,continued,endpoint⟩:=reached
    have domain:=MemoryMetadata.domain frame.metadata
    have endian:=MemoryMetadata.endian frame.metadata
    have currentDatabase:=database.of_before 2952790016 tableBefore domain endian
      (fun query earlier=>frame.outside query (Or.inl earlier))
    have tail:=resolve_suffix_cost data ready pointer length answer currentDatabase nextDb parsed itemCell readyLive.code
    rw [continued] at tail
    change ready.clock-inner.clock≤268 at tail
    have clock:=evaluateHOLFiniteState_clock_le ready (Mpt.WitnessStep.afterRlp .resolve)
    rw [continued] at clock
    change inner.clock≤ready.clock at clock
    have finalClock : output.2.clock=inner.clock:=by rw [endpoint]; rfl
    change source.clock-output.2.clock≤60*length.toNat+281
    rw [finalClock]
    omega

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.resolve_suffix_cost
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.resolve_body_cost
