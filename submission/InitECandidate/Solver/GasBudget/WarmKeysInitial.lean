import InitECandidate.Solver.GasBudget.WarmKeysInvariant
import InitECandidate.Solver.MutableTable.TableRuntime.Normal

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem initial_price : TableRuntime.price 16 + 1 = 10 := by decide

/-- The actual constructor's checked memory result establishes the empty
warming table, rather than assuming its header or used/order arrays. -/
theorem initial_table (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat)
    (environment : Environment source) (valid : Valid .storage (fresh .storage start 16)) :
    Table (TableRuntime.callState source "ak" .storage start 16) (fresh .storage start 16) [] (freshEnd .storage start 16) start := by
  refine ⟨valid, by simp [fresh], TableRuntime.caller_header source "ak" .storage start 16 valid,
    TableRuntime.caller_model source "ak" .storage start 16 valid (Or.inr (by decide)) environment.domain environment.little,
    ⟨4, rfl, by decide⟩, ?_, valid.upper .position, ?_, ?_, ?_⟩
  · simp [TableRuntime.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · have aligned := valid.aligned .header
    change start % 8 = 0 at aligned
    simpa [freshEnd, stride, KeyHash.keySize, rounded, Nat.add_mod] using aligned
  · intro pool
    exact (fresh_bounds .storage start 16 pool).2
  · intro pool
    exact (fresh_bounds .storage start 16 pool).1

theorem initial_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor start total : Nat)
    (keys : source.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 start))))
    (count : source.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 total)))) :
    Locals (bind (TableRuntime.callState source "ak" .storage cursor 16) "i" 0#64) (cell (fresh .storage cursor 16) .header 0) start total 0 := by
  let constructed := TableRuntime.callState source "ak" .storage cursor 16
  have table : constructed.locals.lookup (ofString "ak") = some (.val (.word (cell (fresh .storage cursor 16) .header 0))) := bind_lookup_same _ _ _
  have keys' : constructed.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 start))) :=
    (bind_lookup_other _ "ak" "al_keys" _ (by decide)).trans keys
  have count' : constructed.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 total))) :=
    (bind_lookup_other _ "ak" "nkeys" _ (by decide)).trans count
  exact ⟨(bind_lookup_other _ "i" "ak" _ (by decide)).trans table,
    (bind_lookup_other _ "i" "al_keys" _ (by decide)).trans keys',
    (bind_lookup_other _ "i" "nkeys" _ (by decide)).trans count', bind_lookup_same _ _ _⟩

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.initial_price
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.initial_table
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.initial_locals
