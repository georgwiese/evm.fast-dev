import InitECandidate.Solver.MutableTable.TableRuntime.Initial

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

structure Locals {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (table : BitVec 64) (capacity : Nat) : Prop where
  tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table))
  capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity)))
  strideLocal : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind))))

theorem Locals.allocated {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (table : BitVec 64) (capacity : Nat)
    (locals : Locals source kind table capacity) (name : String) (pointer next : Nat)
    (notTable : ofString name ≠ ofString "t") (notCap : ofString name ≠ ofString "cap") (notStride : ofString name ≠ ofString "stride") :
    Locals (PersistentAlloc.nextState source name pointer next) kind table capacity := by
  unfold PersistentAlloc.nextState
  exact ⟨(bind_lookup_other _ name "t" _ notTable).trans locals.tableLocal,
    (bind_lookup_other _ name "cap" _ notCap).trans locals.capLocal,
    (bind_lookup_other _ name "stride" _ notStride).trans locals.strideLocal⟩

theorem read_capacity {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (table : BitVec 64) (capacity : Nat)
    (locals : Locals source kind table capacity) : eval source (localVar "cap") = some (.val (.word (BitVec.ofNat 64 capacity))) := by
  simp [eval, localVar, evalHOLExact, toExact, locals.capLocal]

theorem read_scale {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (table : BitVec 64) (capacity factor : Nat)
    (locals : Locals source kind table capacity) :
    eval source (TableNew.capacityTimes (.const (BitVec.ofNat 64 factor))) = some (.val (.word (BitVec.ofNat 64 (factor * capacity)))) := by
  simp [eval, TableNew.capacityTimes, localVar, evalHOLExact, evalListHOLExact, toExact, locals.capLocal,
    valueIsWord, valueWord, panOpHOL, ← BitVec.ofNat_mul, Nat.mul_comm capacity factor]

theorem read_key_amount {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (table : BitVec 64) (capacity : Nat)
    (locals : Locals source kind table capacity) :
    eval source (TableNew.capacityTimes (localVar "stride")) = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind * capacity)))) := by
  simp [eval, TableNew.capacityTimes, localVar, evalHOLExact, evalListHOLExact, toExact, locals.capLocal, locals.strideLocal,
    valueIsWord, valueWord, panOpHOL, ← BitVec.ofNat_mul, Nat.mul_comm capacity (NaturalLayout.stride kind)]

theorem initial_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity)))) :
    Locals (initialState source kind start capacity) kind (BitVec.ofNat 64 start) capacity := by
  let allocated := PersistentAlloc.nextState source "t" start (start + 72)
  refine ⟨?_, ?_, bind_lookup_same _ _ _⟩
  · exact (bind_lookup_other allocated "stride" "t" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact (bind_lookup_other allocated "stride" "cap" _ (by decide)).trans
      ((bind_lookup_other _ "t" "cap" _ (by decide)).trans capLocal)

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.Locals.allocated
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.read_capacity
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.read_scale
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.read_key_amount
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.initial_locals
