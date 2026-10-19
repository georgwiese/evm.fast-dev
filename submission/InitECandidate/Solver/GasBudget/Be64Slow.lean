import InitECandidate.Solver.GasBudget.MemoryWriterBytes
import InitECandidate.Solver.GasBudget.MemoryWriterPrice
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.GasBudget.MemoryWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def firstArgs : List (ExpHOL 64) := [localVar "p", .shift .lsr (localVar "v") (.const 32#64)]
def secondArgs : List (ExpHOL 64) := [.op .add [localVar "p", .const 4#64], localVar "v"]
def be64SlowTail : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "st_be32") secondArgs) (.return (.const 0#64))

theorem be64_slow_shape : slow .be64 = .seq (.call (some (none, none)) (ofString "st_be32") firstArgs) be64SlowTail := by
  simp only [slow, Kind.body, Kind.signature, Kind.original, Guest.guestFn_st_be64, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, firstArgs, secondArgs, be64SlowTail, localVar]

set_option maxHeartbeats 1000000 in
theorem be64_slow_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (valueLocal : source.locals.lookup (ofString "v") = some (.val (.word value)))
    (mapped : BytesMapped source pointer 8)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (slow .be64) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ 2 ≤ source.clock ∧ post.clock = source.clock - 2 ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} ∧
      (∀ query, BytesAway pointer query 8 → post.memory query = source.memory query) := by
  rw [be64_slow_shape] at normal
  have safe : Input.LocalPrefix (ofString "p") (.call (some (none, none)) (ofString "st_be32") firstArgs) := .call none _ _ (by simp)
  obtain ⟨first, firstRun, tailRun, retained⟩ := safe.normal_continue source post be64SlowTail returned normal
  have readFirst : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) firstArgs =
      some [.val (.word pointer), .val (.word (value >>> (32 : Nat)))] := by
    simp [firstArgs, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, pointerLocal, valueLocal, wordShiftHOL]
  have firstMapped : BytesMapped source pointer 4 := by intro offset inside; exact mapped offset (by omega)
  obtain ⟨firstFits, firstEq⟩ := Be32Stores.call_normal source first pointer (value >>> (32 : Nat)) firstArgs installed readFirst (be32_mapped firstMapped) firstRun
  have safeSecond : Input.LocalPrefix (ofString "p") (.call (some (none, none)) (ofString "st_be32") secondArgs) := .call none _ _ (by simp)
  obtain ⟨second, secondRun, returnRun, retainedAgain⟩ := safeSecond.normal_continue first post (.return (.const 0#64)) returned tailRun
  have firstInstalled : Input.OriginalCode.Installed first.code := by rw [firstEq]; exact installed
  have firstP : first.locals.lookup (ofString "p") = some (.val (.word pointer)) := by rw [firstEq]; exact pointerLocal
  have firstV : first.locals.lookup (ofString "v") = some (.val (.word value)) := by rw [firstEq]; exact valueLocal
  have readSecond : evalListHOLFinite first (h := fun address => Classical.propDecidable (first.memaddrs address)) secondArgs =
      some [.val (.word (pointer + 4#64)), .val (.word value)] := by
    simp [secondArgs, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, firstP, firstV, valueIsWord, valueWord, wordOpHOL, wordOp]
  have secondMapped : BytesMapped first (pointer + 4#64) 4 := by
    have region := mapped.subrange 4 4 (by decide)
    rw [firstEq]
    exact region
  obtain ⟨secondFits, secondEq⟩ := Be32Stores.call_normal first second (pointer + 4#64) value secondArgs firstInstalled readSecond (be32_mapped secondMapped) secondRun
  obtain ⟨readReturn, postEq⟩ := Input.return_normal second post (.const 0#64) returned returnRun
  have result : returned = .val (.word 0#64) := (Option.some.inj readReturn).symm
  have funded : 2 ≤ source.clock := by rw [firstEq] at secondFits; change 1 ≤ source.clock - 1 at secondFits; omega
  refine ⟨result, funded, ?_, ?_, ?_⟩
  · rw [postEq, secondEq, firstEq]
    change source.clock - 1 - 1 = source.clock - 2
    omega
  · rw [postEq, secondEq, firstEq]
    rfl
  · intro query away
    have awayFirst : BytesAway pointer query 4 := by intro offset inside; exact away offset (by omega)
    have awaySecond : BytesAway (pointer + 4#64) query 4 := away.subrange 4 4 (by decide)
    rw [postEq, secondEq]
    change Be32Stores.written first.memory first.be (pointer + 4#64) value Be32Stores.clauses query = _
    rw [Be32Stores.written_away _ _ _ _ _ _ (be32_away awaySecond), firstEq]
    exact Be32Stores.written_away _ _ _ _ _ _ (be32_away awayFirst)

end InitECandidate.Solver.GasBudget.MemoryWriter

#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be64_slow_shape
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be64_slow_normal
