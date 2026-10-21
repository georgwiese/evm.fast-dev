import InitECandidate.Solver.Input.WitnessStepParsedSuffix
import InitECandidate.Solver.Mpt.WitnessResolveCost

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem RootBoundary.resolve_suffix_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length : BitVec 64) (answer : ValueHOL 64) (boundary : RootBoundary input source)
    (parsed : Rlp.Item.Valid pointer length.toNat answer)
    (itemCell : source.locals.lookup (ofString "it")=some answer)
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (Mpt.WitnessStep.afterRlp .resolve)).2.clock≤6*WitnessConstructors.nodeCount input+7 := by
  obtain ⟨header,payload,flag,answerEq,small,positive,extent,binary,listHeader⟩:=parsed
  rw [answerEq] at itemCell
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,heapCell,arena,aligned,nodeBefore,codeBefore⟩:=boundary
  exact Mpt.WitnessResolve.suffix_cost source _ nodes 2713717584#64 pointer header payload flag _ 1024 _ nodeDatabase nodeCell itemCell installed

/-- Complete original _resolve_step236 at the actual main-constructed
database: all outcomes, real caught RLP parsing, arbitrary table query and
original hashed-node allocation. This is a source-clock bound. -/
theorem resolve_body_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (fits : pointer.toNat+length.toNat<2^64) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (Mpt.WitnessStep.body .resolve)).2.clock≤60*length.toNat+6*WitnessConstructors.nodeCount input+51 := by
  have originalBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩:=boundary
  let output:=evaluateHOLFiniteState source (Mpt.WitnessStep.body .resolve)
  rcases step_parsed_suffix .resolve input source output.2 nodes pointer length cursor limit originalBoundary nodeCell pointerCell lengthCell arena below fits installed output.1 rfl with stopped|reached
  · exact stopped.trans (by omega)
  · obtain ⟨ready,inner,answer,nextBoundary,parsed,nextArena,above,domain,endian,codeEq,nextInstalled,globalCells,itemCell,nextDb,nextPointer,nextLength,forward,price,continued,endpoint⟩:=reached
    have tail:=nextBoundary.resolve_suffix_cost input ready pointer length answer parsed itemCell nextInstalled
    rw [continued] at tail
    change ready.clock-inner.clock≤6*WitnessConstructors.nodeCount input+7 at tail
    have clock:=evaluateHOLFiniteState_clock_le ready (Mpt.WitnessStep.afterRlp .resolve)
    rw [continued] at clock
    change inner.clock≤ready.clock at clock
    have finalClock : output.2.clock=inner.clock:=by rw [endpoint]; rfl
    change source.clock-output.2.clock≤60*length.toNat+6*WitnessConstructors.nodeCount input+51
    rw [finalClock]
    omega

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.RootBoundary.resolve_suffix_cost
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.resolve_body_cost
