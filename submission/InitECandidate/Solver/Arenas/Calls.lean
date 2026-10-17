import InitECandidate.Solver.Arenas.Execution
import InitECandidate.Solver.Arenas.Arithmetic
import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def functionName : Direction → String | .up => "frame_mem_alloc" | .down => "scratch_alloc"
def formals : List (MlS × ShapeHOL) := [(ofString "n", .one)]
def Room : Direction → BitVec 64 → BitVec 64 → BitVec 64 → Prop
  | .up, pointer, limit, amount => pointer.toNat + amount.toNat ≤ limit.toNat
  | .down, pointer, limit, amount => limit.toNat + amount.toNat ≤ pointer.toNat

theorem room_guards (direction : Direction) (pointer limit amount : BitVec 64)
    (aligned : limit.toNat % 8 = 0) (room : Room direction pointer limit amount) :
    (¬ distance direction pointer limit < amount) ∧
      (¬ outside direction (rounded direction pointer amount) limit) := by
  cases direction with
  | up => exact ⟨(upward_guards pointer limit amount aligned room).1,
      (upward_guards pointer limit amount aligned room).2.1⟩
  | down => exact ⟨(downward_guards pointer limit amount aligned room).1,
      (downward_guards pointer limit amount aligned room).2.1⟩

/-- Actual scoped allocator call with derived successful guards and body.
Its own cursor update is exact; caller locals surround the continuation with
ordinary lexical restoration, and no memory/FFI cell is changed. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (direction : Direction)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (pointer limit amount : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      arguments = some [.val (.word amount)])
    (code : source.code.lookup (ofString (functionName direction)) = some (formals, body direction, .one))
    (pointerGlobal : source.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString (limitName direction)) = some (.val (.word limit)))
    (aligned : limit.toNat % 8 = 0) (room : Room direction pointer limit amount) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source
      (.decCall (ofString name) .one (ofString (functionName direction)) arguments continuation) =
      (let output := evaluateHOLFiniteState
        (bind (post {source with clock := source.clock - 1} direction pointer amount) name
          (resultWord direction pointer amount)) continuation
       (output.1, restore source name output.2)) := by
  classical
  obtain ⟨callee, called, amountLocal⟩ := Input.CallNormal.unary_environment source.code.lookup
    (ofString (functionName direction)) "n" (body direction) amount code
  let entry := callEntryStateHOLFinite source callee
  have guards := room_guards direction pointer limit amount aligned room
  obtain ⟨target, run, frame⟩ := execute entry direction pointer limit amount amountLocal pointerGlobal limitGlobal guards.1 guards.2
  have actual := Input.CallNormal.return_execute source target name .one (ofString (functionName direction))
    arguments [.val (.word amount)] (body direction) continuation callee .one
    (.val (.word (resultWord direction pointer amount))) args called enough run
    (by simp [shapeOfHOLExact, shapeEqHOL])
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with locals := source.locals}) frame
  have nextEq : Input.CallNormal.continuationEntry source target name (.val (.word (resultWord direction pointer amount))) =
      bind (post {source with clock := source.clock - 1} direction pointer amount) name
        (resultWord direction pointer amount) := by
    change setVarHOLFinite (ofString name) (.val (.word (resultWord direction pointer amount)))
      {target with locals := source.locals} = _
    exact congrArg (fun state : PanSemStateFiniteExact 64 F =>
      setVarHOLFinite (ofString name) (.val (.word (resultWord direction pointer amount))) state) callerFrame
  rw [nextEq] at actual
  exact actual

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.room_guards
#print axioms InitECandidate.Solver.Arenas.call_execute
