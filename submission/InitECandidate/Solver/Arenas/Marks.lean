import InitECandidate.Solver.Arenas.Program
import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def markName : Direction → String | .up => "frame_mem_mark" | .down => "scratch_mark"
def markBody : Direction → ProgHOL 64
  | .up => match Guest.Software.guestFn_frame_mem_mark with | .function fn => progToHOL fn.body | _ => .skip
  | .down => match Guest.Software.guestFn_scratch_mark with | .function fn => progToHOL fn.body | _ => .skip

theorem mark_body (direction : Direction) : markBody direction = .return (pointerExpression direction) := by
  cases direction <;>
    simp only [markBody, Guest.Software.guestFn_frame_mem_mark, Guest.Software.guestFn_scratch_mark, progToHOL, expToHOL,
      pointerExpression, pointerName]

theorem mark_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (direction : Direction) (pointer : BitVec 64)
    (stored : source.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer))) :
    evaluateHOLFiniteState source (markBody direction) =
      (some (.returned (.val (.word pointer))), emptyLocalsHOLFinite source) := by
  rw [mark_body, evaluateHOLFiniteState_return]
  simp [pointerExpression, evalHOLExact, toExact, stored, shapeOfHOLExact, sizeOfShapeWithContextHOL]

/-- Both real mark calls return the current arena cursor without changing
memory or globals. The sole clock consumed is the caller's call clock. -/
theorem mark_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (direction : Direction)
    (name : String) (pointer : BitVec 64) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString (markName direction)) = some ([], markBody direction, .one))
    (stored : source.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer)))
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source
      (.decCall (ofString name) .one (ofString (markName direction)) [] continuation) =
      (let output := evaluateHOLFiniteState (bind {source with clock := source.clock - 1} name pointer) continuation
       (output.1, restore source name output.2)) := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString (markName direction)) [] =
      some (markBody direction, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup source.code.lookup
    (ofString (markName direction)) [] (markBody direction) (fun _ => none) .one raw
  let entry := callEntryStateHOLFinite source callee
  have run := mark_execute entry direction pointer stored
  have args : evalListHOLFinite source
      (h := fun address => Classical.propDecidable (source.memaddrs address)) [] = some [] := rfl
  have actual := Input.CallNormal.pure_return_execute source (emptyLocalsHOLFinite entry) name
    (ofString (markName direction)) [] [] (markBody direction) continuation callee pointer 0 args called enough run rfl
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.mark_body
#print axioms InitECandidate.Solver.Arenas.mark_execute
#print axioms InitECandidate.Solver.Arenas.mark_call
