import InitECandidate.Solver.MutableTable.GrowRuntime.Header
import InitECandidate.Solver.MutableTable.GrowRuntime.Stores
import InitECandidate.Solver.MutableTable.GrowRuntime.Frames

set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure ArrayLocals {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : Plan) : Prop where
  keys : source.locals.lookup (ofString "nkeys") = some (.val (.word (cell plan .keys 0)))
  vals : source.locals.lookup (ofString "nvals") = some (.val (.word (cell plan .values 0)))
  used : source.locals.lookup (ofString "nused") = some (.val (.word (cell plan .used 0)))
  order : source.locals.lookup (ofString "norder") = some (.val (.word (cell plan .order 0)))
  position : source.locals.lookup (ofString "norder_pos") = some (.val (.word (cell plan .position 0)))

theorem allocated_arrays {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (table start capacity : Nat) :
    ArrayLocals (allocatedState source kind start capacity) (relocated kind table start capacity) := by
  have names : ([ofString "nkeys", ofString "nvals", ofString "nused", ofString "norder", ofString "norder_pos"] : List MlS).Nodup := by decide
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true, List.nodup_nil] at names
  rcases names with ⟨⟨neq0, neq1, neq2, neq3⟩, ⟨neq4, neq5, neq6⟩, ⟨neq7, neq8⟩, neq9⟩
  constructor <;> simp only [allocatedState, orderState, usedState, valueState, keyState, PersistentAlloc.nextState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, cell, relocated, Nat.add_zero, beq_iff_eq, ↓reduceIte, neq0, Ne.symm neq0, neq1, Ne.symm neq1, neq2, Ne.symm neq2, neq3, Ne.symm neq3, neq4, Ne.symm neq4, neq5, Ne.symm neq5, neq6, Ne.symm neq6, neq7, Ne.symm neq7, neq8, Ne.symm neq8, neq9, Ne.symm neq9]

theorem allocated_other {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) (name : String)
    (away : ∀ saved ∈ (["nkeys", "nvals", "nused", "norder", "norder_pos"] : List String), ofString saved ≠ ofString name) :
    (allocatedState source kind start capacity).locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
  exact (bind_lookup_other _ "norder_pos" name _ (away "norder_pos" (by simp))).trans ((bind_lookup_other _ "norder" name _ (away "norder" (by simp))).trans ((bind_lookup_other _ "nused" name _ (away "nused" (by simp))).trans ((bind_lookup_other _ "nvals" name _ (away "nvals" (by simp))).trans ((bind_lookup_other _ "nkeys" name _ (away "nkeys" (by simp))).trans (rfl)))))

theorem header_amount (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (count : Nat) :
    AmountLocals (headerState source kind old count) kind (2 * old.capacity) := by
  refine ⟨bind_lookup_same _ _ _,
    (bind_lookup_other _ "ncap" "stride" _ (by decide)).trans ((bind_lookup_other _ "nitems" "stride" _ (by decide)).trans ((bind_lookup_other _ "order" "stride" _ (by decide)).trans ((bind_lookup_other _ "vals" "stride" _ (by decide)).trans ((bind_lookup_other _ "keys" "stride" _ (by decide)).trans (bind_lookup_same _ _ _)))))⟩

def preparedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (start count : Nat) :=
  let allocated := allocatedState (headerState source kind old count) kind start (2 * old.capacity)
  WitnessRadix.QueryBranch.bind {allocated with
    memory := (resetMemory source.memory (relocated kind (old.base .header) start (2 * old.capacity)))
    clock := allocated.clock - (Zero.price (2 * old.capacity) + 1)} "k" 0#64

set_option maxHeartbeats 1000000 in
theorem prepared_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (start count : Nat)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0)))) :
    LoopLocals (preparedState source kind old start count) kind old count 0 := by
  have names : ([ofString "t", ofString "cap", ofString "stride", ofString "keys", ofString "vals", ofString "order", ofString "nitems", ofString "ncap", ofString "nkeys", ofString "nvals", ofString "nused", ofString "norder", ofString "norder_pos", ofString "k"] : List MlS).Nodup := by decide
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true, List.nodup_nil] at names
  rcases names with ⟨⟨neq0, neq1, neq2, neq3, neq4, neq5, neq6, neq7, neq8, neq9, neq10, neq11, neq12⟩, ⟨neq13, neq14, neq15, neq16, neq17, neq18, neq19, neq20, neq21, neq22, neq23, neq24⟩, ⟨neq25, neq26, neq27, neq28, neq29, neq30, neq31, neq32, neq33, neq34, neq35⟩, ⟨neq36, neq37, neq38, neq39, neq40, neq41, neq42, neq43, neq44, neq45⟩, ⟨neq46, neq47, neq48, neq49, neq50, neq51, neq52, neq53, neq54⟩, ⟨neq55, neq56, neq57, neq58, neq59, neq60, neq61, neq62⟩, ⟨neq63, neq64, neq65, neq66, neq67, neq68, neq69⟩, ⟨neq70, neq71, neq72, neq73, neq74, neq75⟩, ⟨neq76, neq77, neq78, neq79, neq80⟩, ⟨neq81, neq82, neq83, neq84⟩, ⟨neq85, neq86, neq87⟩, ⟨neq88, neq89⟩, neq90⟩
  constructor <;> simp only [allocatedState, orderState, usedState, valueState, keyState, PersistentAlloc.nextState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, cell, relocated, Nat.add_zero, beq_iff_eq, ↓reduceIte, preparedState, headerState, tableLocal, neq0, Ne.symm neq0, neq1, Ne.symm neq1, neq2, Ne.symm neq2, neq3, Ne.symm neq3, neq4, Ne.symm neq4, neq5, Ne.symm neq5, neq6, Ne.symm neq6, neq7, Ne.symm neq7, neq8, Ne.symm neq8, neq9, Ne.symm neq9, neq10, Ne.symm neq10, neq11, Ne.symm neq11, neq12, Ne.symm neq12, neq13, Ne.symm neq13, neq14, Ne.symm neq14, neq15, Ne.symm neq15, neq16, Ne.symm neq16, neq17, Ne.symm neq17, neq18, Ne.symm neq18, neq19, Ne.symm neq19, neq20, Ne.symm neq20, neq21, Ne.symm neq21, neq22, Ne.symm neq22, neq23, Ne.symm neq23, neq24, Ne.symm neq24, neq25, Ne.symm neq25, neq26, Ne.symm neq26, neq27, Ne.symm neq27, neq28, Ne.symm neq28, neq29, Ne.symm neq29, neq30, Ne.symm neq30, neq31, Ne.symm neq31, neq32, Ne.symm neq32, neq33, Ne.symm neq33, neq34, Ne.symm neq34, neq35, Ne.symm neq35, neq36, Ne.symm neq36, neq37, Ne.symm neq37, neq38, Ne.symm neq38, neq39, Ne.symm neq39, neq40, Ne.symm neq40, neq41, Ne.symm neq41, neq42, Ne.symm neq42, neq43, Ne.symm neq43, neq44, Ne.symm neq44, neq45, Ne.symm neq45, neq46, Ne.symm neq46, neq47, Ne.symm neq47, neq48, Ne.symm neq48, neq49, Ne.symm neq49, neq50, Ne.symm neq50, neq51, Ne.symm neq51, neq52, Ne.symm neq52, neq53, Ne.symm neq53, neq54, Ne.symm neq54, neq55, Ne.symm neq55, neq56, Ne.symm neq56, neq57, Ne.symm neq57, neq58, Ne.symm neq58, neq59, Ne.symm neq59, neq60, Ne.symm neq60, neq61, Ne.symm neq61, neq62, Ne.symm neq62, neq63, Ne.symm neq63, neq64, Ne.symm neq64, neq65, Ne.symm neq65, neq66, Ne.symm neq66, neq67, Ne.symm neq67, neq68, Ne.symm neq68, neq69, Ne.symm neq69, neq70, Ne.symm neq70, neq71, Ne.symm neq71, neq72, Ne.symm neq72, neq73, Ne.symm neq73, neq74, Ne.symm neq74, neq75, Ne.symm neq75, neq76, Ne.symm neq76, neq77, Ne.symm neq77, neq78, Ne.symm neq78, neq79, Ne.symm neq79, neq80, Ne.symm neq80, neq81, Ne.symm neq81, neq82, Ne.symm neq82, neq83, Ne.symm neq83, neq84, Ne.symm neq84, neq85, Ne.symm neq85, neq86, Ne.symm neq86, neq87, Ne.symm neq87, neq88, Ne.symm neq88, neq89, Ne.symm neq89, neq90, Ne.symm neq90]

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.allocated_arrays
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.allocated_other
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.header_amount
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.prepared_locals
