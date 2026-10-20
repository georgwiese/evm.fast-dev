import InitECandidate.Solver.Input.BswapExecution
import InitECandidate.Solver.Input.MemoryWordCalls
import InitECandidate.Solver.GasBudget.Be64Normal

namespace InitECandidate.Solver.Input.MemoryWordCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open GasBudget.MemoryWriter

def fastTail : ProgHOL 64 := .seq (.store (localVar "p") (localVar "w")) (.return (.const 0#64))
def fastPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer word : BitVec 64) :=
  restore source "w" (emptyLocalsHOLFinite {source with memory := StoreWord.put source.memory pointer word,clock := source.clock - 1})
def slowFirst (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) :=
  {source with memory := GasBudget.Be32Stores.written source.memory source.be pointer (value >>> 32) GasBudget.Be32Stores.clauses,clock := source.clock - 1}
def slowPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) :=
  let first := slowFirst source pointer value
  {first with memory := GasBudget.Be32Stores.written first.memory first.be (pointer + 4#64) value GasBudget.Be32Stores.clauses,clock := source.clock - 2}

private theorem fast_scope_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64) (memory : WordWrites.Memory) :
    restore source "w" (emptyLocalsHOLFinite {QueryBranch.bind {source with clock := source.clock - 1} "w" word with memory := memory}) =
      restore source "w" (emptyLocalsHOLFinite {source with clock := source.clock - 1,memory := memory}) := rfl

theorem be64_fast_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (v : source.locals.lookup (ofString "v") = some (.val (.word value))) (mapped : source.memaddrs pointer) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (fast .be64) =
      (some (.returned (.val (.word 0#64))),fastPost source pointer (BswapExecution.result value)) := by
  let word := BswapExecution.result value
  let ready := QueryBranch.bind {source with clock := source.clock - 1} "w" word
  have readyP : ready.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "w" ≠ ofString "p" from by decide,p]
  have readyW : ready.locals.lookup (ofString "w") = some (.val (.word word)) := by
    simp [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "v"] = some [.val (.word value)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,v]
  have called := BswapExecution.call_execute source value "w" [localVar "v"] fastTail args installed enough
  have stored := StoreWord.execute ready (localVar "p") (localVar "w") pointer word
    (by simp [QueryBranch.eval,evalHOLExact,localVar,readyP]) (by simp [QueryBranch.eval,evalHOLExact,localVar,readyW]) mapped
  let target := {ready with memory := StoreWord.put ready.memory pointer word}
  have finish : evaluateHOLFiniteState ready fastTail = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite target) := by
    rw [fastTail,StateSteps.next_sequence ready target _ _ stored (Nat.le_refl _)]
    exact BuildEntry.zero_return target
  have shape : fast .be64 = .decCall (ofString "w") .one (ofString "bswap64") [localVar "v"] fastTail := by
    simp only [fast,Kind.body,Kind.signature,Kind.original,Guest.guestFn_st_be64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,fastTail,localVar]
  rw [shape,called,finish]
  have frame := fast_scope_frame source word (StoreWord.put source.memory pointer word)
  exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => ((some (.returned (.val (.word 0#64))) : Option (PanSemResultExact 64)),state)) frame

theorem be64_slow_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (v : source.locals.lookup (ofString "v") = some (.val (.word value)))
    (mapped : BytesMapped source pointer 8) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source (slow .be64) =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (slowPost source pointer value)) := by
  have firstArgsRead : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) firstArgs =
      some [.val (.word pointer),.val (.word (value >>> 32))] := by
    simp [firstArgs,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,p,v,wordShiftHOL]
  have firstMapped : BytesMapped source pointer 4 := by simpa only [BitVec.add_zero] using mapped.subrange 0 4 (by decide)
  have firstRun := be32_execute source pointer (value >>> 32) firstArgs installed firstArgsRead (be32_mapped firstMapped) (by omega)
  let first := slowFirst source pointer value
  have secondArgsRead : evalListHOLFinite first (h := fun query => Classical.propDecidable (first.memaddrs query)) secondArgs =
      some [.val (.word (pointer + 4#64)),.val (.word value)] := by
    simp [secondArgs,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,first,slowFirst,p,v,valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondRun := be32_execute first (pointer + 4#64) value secondArgs installed secondArgsRead (be32_mapped (mapped.subrange 4 4 (by decide)))
    (by change 1 ≤ source.clock - 1; omega)
  have firstClock : first.clock ≤ source.clock := Nat.sub_le _ _
  have subtract : source.clock - 1 - 1 = source.clock - 2 := by omega
  have secondActual : evaluateHOLFiniteState first (.call (some (none,none)) (ofString "st_be32") secondArgs) = (none,slowPost source pointer value) := by
    simpa only [first,slowFirst,slowPost,subtract] using secondRun
  rw [be64_slow_shape,StateSteps.next_sequence source first _ _ firstRun firstClock,be64SlowTail,
    StateSteps.next_sequence first (slowPost source pointer value) _ _ secondActual (by change source.clock - 2 ≤ source.clock - 1; omega)]
  exact BuildEntry.zero_return (slowPost source pointer value)

end InitECandidate.Solver.Input.MemoryWordCalls

#print axioms InitECandidate.Solver.Input.MemoryWordCalls.be64_fast_execute
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.be64_slow_execute
