import InitECandidate.Solver.MutableTable.CopyStageState
import InitECandidate.Solver.MutableTable.MemoryModelReads

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure CoreLocals {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old : Plan) : Prop where
  table : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0)))
  cap : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 old.capacity)))
  stride : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind))))

theorem stage_lookup_other {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool)
    (query : String) (different : ofString (name pool) ≠ ofString query) :
    (stageState source kind old next pool).locals.lookup (ofString query) = source.locals.lookup (ofString query) := by
  unfold stageState
  split <;> exact bind_lookup_other _ (name pool) query _ different

theorem stage_lookup_same {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool) :
    (stageState source kind old next pool).locals.lookup (ofString (name pool)) = some (.val (.word (cell next pool 0))) := by
  unfold stageState
  split <;> simpa only [cell, Nat.add_zero, copied, CopyGeneral.callState, allocated, PersistentAlloc.nextState] using bind_lookup_same
    {source with globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (next.base pool + size kind next pool)))), clock := source.clock - 1}
    (name pool) (BitVec.ofNat 64 (next.base pool))

theorem CoreLocals.stage {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool)
    (locals : CoreLocals source kind old) : CoreLocals (stageState source kind old next pool) kind old := by
  constructor
  · exact (stage_lookup_other source kind old next pool "t" (by cases pool <;> decide)).trans locals.table
  · exact (stage_lookup_other source kind old next pool "cap" (by cases pool <;> decide)).trans locals.cap
  · exact (stage_lookup_other source kind old next pool "stride" (by cases pool <;> decide)).trans locals.stride

theorem stage_new_header {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool)
    (prior : pool ≠ .header → source.locals.lookup (ofString "n") = some (.val (.word (cell next .header 0)))) :
    (stageState source kind old next pool).locals.lookup (ofString "n") = some (.val (.word (cell next .header 0))) := by
  by_cases header : pool = .header
  · subst pool
    exact stage_lookup_same source kind old next .header
  · exact (stage_lookup_other source kind old next pool "n" (by cases pool <;> first | exact False.elim (header rfl) | decide)).trans (prior header)

theorem amount_read {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old : Plan)
    (locals : CoreLocals source kind old) (pool : Pool) :
    eval source (amountExpression pool) = some (.val (.word (BitVec.ofNat 64 (amount kind old.capacity pool)))) := by
  cases pool <;> simp [eval, amountExpression, amount, localVar, evalHOLExact, evalListHOLExact, toExact,
    locals.cap, locals.stride, valueIsWord, valueWord, panOpHOL, ← BitVec.ofNat_mul, Nat.mul_comm]

theorem source_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (valid : Valid kind old) (domain : source.memaddrs = InitE.ordinaryDomain) (count : BitVec 64)
    (header : MemoryModel.Header source.memory kind old count) (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (pool : Pool) : eval source (sourceExpression pool) = some (.val (.word (cell old pool 0))) := by
  cases pool with
  | header => simp [eval, sourceExpression, localVar, evalHOLExact, toExact, tableLocal]
  | keys => exact header.read source kind old valid domain count tableLocal 32 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  | values => exact header.read source kind old valid domain count tableLocal 40 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  | used => exact header.read source kind old valid domain count tableLocal 48 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  | order => exact header.read source kind old valid domain count tableLocal 56 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  | position => exact header.read source kind old valid domain count tableLocal 64 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_lookup_other
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_lookup_same
#print axioms InitECandidate.Solver.MutableTable.TableCopy.CoreLocals.stage
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_new_header
#print axioms InitECandidate.Solver.MutableTable.TableCopy.amount_read
#print axioms InitECandidate.Solver.MutableTable.TableCopy.source_read
