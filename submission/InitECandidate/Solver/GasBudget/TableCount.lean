import InitECandidate.Solver.Input.PureAssignReturn

namespace InitECandidate.Solver.GasBudget.TableCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def expression : ExpHOL 64 := .load .one (addConst (localVar "t") 24#64)
def body : ProgHOL 64 := match Guest.guestFn_htab_count with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "t", .one)]

theorem body_shape : body = .return expression := by
  simp only [body, Guest.guestFn_htab_count, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    expression, localVar, addConst]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table count : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (mapped : source.memaddrs (table + 24#64)) (cell : source.memory (table + 24#64) = .word count) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word count))), emptyLocalsHOLFinite source) := by
  rw [body_shape, evaluateHOLFiniteState_return]
  simp [expression, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, tableLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, isWfShapeExactHOL, memLoadHOLExact, mapped, cell,
    shapeOfHOLExact, sizeOfShapeWithContextHOL]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (table count : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word table)])
    (code : source.code.lookup (ofString "htab_count") = some (formals, body, .one))
    (mapped : source.memaddrs (table + 24#64)) (cell : source.memory (table + 24#64) = .word count)
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_count") arguments continuation) =
      (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1} name count) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, tableLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "htab_count") "t" body table code
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry table count tableLocal mapped cell
  have actual := Input.CallNormal.pure_return_execute source (emptyLocalsHOLFinite entry) name (ofString "htab_count")
    arguments [.val (.word table)] body continuation callee count 0 args called enough run rfl
  simpa only [Nat.sub_zero] using actual

theorem call_assign (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (table count old : BitVec 64)
    (present : source.locals.lookup (ofString name) = some (.val (.word old)))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word table)])
    (code : source.code.lookup (ofString "htab_count") = some (formals, body, .one))
    (mapped : source.memaddrs (table + 24#64)) (cell : source.memory (table + 24#64) = .word count)
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (some (.local, ofString name), none)) (ofString "htab_count") arguments) =
      (none, WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1} name count) := by
  obtain ⟨callee, called, tableLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "htab_count") "t" body table code
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry table count tableLocal mapped cell
  have actual := Input.CallNormal.pure_assign_execute source (emptyLocalsHOLFinite entry) name old (ofString "htab_count")
    arguments [.val (.word table)] body callee count 0 present args called enough run rfl
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.GasBudget.TableCount

#print axioms InitECandidate.Solver.GasBudget.TableCount.body_shape
#print axioms InitECandidate.Solver.GasBudget.TableCount.execute
#print axioms InitECandidate.Solver.GasBudget.TableCount.call_execute
#print axioms InitECandidate.Solver.GasBudget.TableCount.call_assign
