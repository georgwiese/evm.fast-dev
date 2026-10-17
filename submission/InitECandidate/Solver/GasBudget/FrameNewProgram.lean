import InitECandidate.Solver.Arenas.Calls
import InitECandidate.Solver.Arenas.Marks
import InitECandidate.Solver.WitnessRadix.ZeroCall
import InitECandidate.Solver.GasBudget.Frame
import InitECandidate.Solver.MutableTable.ZeroWords

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

abbrev size : Nat := 280

def clear : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [localVar "e", .const 280#64]
def program (continuation : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "stack_mark") .one (ofString "scratch_mark") []
    (.decCall (ofString "mem_mark") .one (ofString "frame_mem_mark") []
      (.decCall (ofString "e") .one (ofString "scratch_alloc") [.const 280#64]
        (.seq clear continuation)))
def body : ProgHOL 64 := match Guest.guestFn_frame_new with | .function fn => progToHOL fn.body | _ => .skip
def afterZero : ProgHOL 64 := match body with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.decCall _ _ _ _ (.seq _ rest))) => rest
  | _ => .skip

theorem actual_prefix : body = program afterZero := by
  simp only [body, afterZero, Guest.guestFn_frame_new, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, program, clear, localVar]

structure Code (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  scratchMark : source.code.lookup (ofString "scratch_mark") = some ([], Arenas.markBody .down, .one)
  memoryMark : source.code.lookup (ofString "frame_mem_mark") = some ([], Arenas.markBody .up, .one)
  scratch : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one)
  zero : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one)

noncomputable def markedScratch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  bind {source with clock := source.clock - 1} "stack_mark" scratch
noncomputable def markedMemory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64) :=
  bind {markedScratch source scratch with clock := (markedScratch source scratch).clock - 1} "mem_mark" memory
noncomputable def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64) :=
  bind (Arenas.post {markedMemory source scratch memory with clock := (markedMemory source scratch memory).clock - 1}
    .down scratch 280#64) "e" (Arenas.rounded .down scratch 280#64)
noncomputable def zeroed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64) :=
  {allocated source scratch memory with
    memory := WitnessRadix.Zero.finalMemory source.memory (Arenas.rounded .down scratch 280#64) size
    clock := (allocated source scratch memory).clock - (WitnessRadix.Zero.price size + 1)}
noncomputable def closeScope (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "stack_mark" (restore (markedScratch source scratch) "mem_mark"
    (restore (markedMemory source scratch memory) "e" target))

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.actual_prefix
