import InitECandidate.Solver.MutableTable.GrowProgram
import InitECandidate.Solver.MutableTable.MemoryModelRehashFrame

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure LoopLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (count index : Nat) : Prop where
  table : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0)))
  stride : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind))))
  keys : source.locals.lookup (ofString "keys") = some (.val (.word (cell old .keys 0)))
  vals : source.locals.lookup (ofString "vals") = some (.val (.word (cell old .values 0)))
  order : source.locals.lookup (ofString "order") = some (.val (.word (cell old .order 0)))
  countLocal : source.locals.lookup (ofString "nitems") = some (.val (.word (BitVec.ofNat 64 count)))
  indexLocal : source.locals.lookup (ofString "k") = some (.val (.word (BitVec.ofNat 64 index)))

theorem capacity_signed_small (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) : plan.capacity < 2 ^ 63 := by
  have high := valid.upper .values
  change plan.base .values + 8 * plan.capacity ≤ 33806089496 at high
  omega

/-- Original growth uses signed comparison. Its natural interpretation is
derived under the physical array extent bound, rather than changing the AST. -/
theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (valid : Valid kind old) (count index : Nat) (countBound : count ≤ old.capacity) (indexBound : index ≤ count)
    (locals : LoopLocals source kind old count index) :
    @evalHOLFinite 64 Guest.HostMemory _ source (fun address => Classical.propDecidable (source.memaddrs address)) Grow.loopTest =
      some (.val (.word (if index < count then 1#64 else 0#64))) := by
  have capHigh := capacity_signed_small kind old valid
  have countSmall : count < 2 ^ 64 := by omega
  have indexSmall : index < 2 ^ 64 := by omega
  have countSign : count < 2 ^ 63 := by omega
  have indexSign : index < 2 ^ 63 := by omega
  norm_num only [Nat.reducePow] at countSmall indexSmall countSign indexSign
  by_cases active : index < count <;>
    simp [Grow.loopTest, localVar, evalHOLFinite, evalHOLExact, toExact, locals.indexLocal, locals.countLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt countSmall, Nat.mod_eq_of_lt indexSmall, countSign, indexSign, active]

theorem index_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (count index : Nat) (locals : LoopLocals source kind old count index) (slot : BitVec 64)
    (mapped : source.memaddrs (cell old .order 0 + BitVec.ofNat 64 index * 8#64))
    (stored : source.memory (cell old .order 0 + BitVec.ofNat 64 index * 8#64) = .word slot) :
    eval source Grow.indexRead = some (.val (.word slot)) := by
  simp [eval, Grow.indexRead, Grow.times, localVar, evalHOLExact, evalListHOLExact, toExact, locals.order, locals.indexLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, memLoadHOLExact, isWfShapeExactHOL, mapped, stored]

theorem insert_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (count index : Nat) (locals : LoopLocals source kind old count index) (slot value : BitVec 64)
    (iLocal : source.locals.lookup (ofString "i") = some (.val (.word slot)))
    (mapped : source.memaddrs (cell old .values 0 + slot * 8#64))
    (stored : source.memory (cell old .values 0 + slot * 8#64) = .word value) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "t", Grow.keyAddress, Grow.valueRead] =
      some (TableCall.values (cell old .header 0) (cell old .keys 0 + slot * BitVec.ofNat 64 (NaturalLayout.stride kind)) value) := by
  simp [TableCall.values, Grow.keyAddress, Grow.valueRead, Grow.times, localVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact,
    locals.table, locals.keys, locals.vals, locals.stride, iLocal, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
    memLoadHOLExact, isWfShapeExactHOL, mapped, stored]

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.capacity_signed_small
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.condition_read
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.index_read
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.insert_arguments
