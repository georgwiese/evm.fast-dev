import InitECandidate.Solver.WitnessRadix.TableInitial

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

structure Locals {F : Type} (source : PanSemStateFiniteExact 64 F) (table : BitVec 64) (capacity : Nat) : Prop where
  tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table))
  capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity)))
  strideLocal : source.locals.lookup (ofString "stride") = some (.val (.word 32#64))

theorem locals_allocated {F : Type} (source : PanSemStateFiniteExact 64 F) (table : BitVec 64) (capacity : Nat)
    (locals : Locals source table capacity) (name : String) (pointer next : Nat)
    (notTable : ofString name ≠ ofString "t") (notCap : ofString name ≠ ofString "cap")
    (notStride : ofString name ≠ ofString "stride") :
    Locals (PersistentAlloc.nextState source name pointer next) table capacity := by
  unfold PersistentAlloc.nextState
  exact ⟨(bind_lookup_other _ name "t" _ notTable).trans locals.tableLocal,
    (bind_lookup_other _ name "cap" _ notCap).trans locals.capLocal,
    (bind_lookup_other _ name "stride" _ notStride).trans locals.strideLocal⟩

theorem read_capacity {F : Type} (source : PanSemStateFiniteExact 64 F) (table : BitVec 64) (capacity : Nat)
    (locals : Locals source table capacity) : eval source (localVar "cap") = some (.val (.word (BitVec.ofNat 64 capacity))) := by
  simp [eval, localVar, evalHOLExact, toExact, locals.capLocal]

theorem read_scale {F : Type} (source : PanSemStateFiniteExact 64 F) (table : BitVec 64) (capacity factor : Nat)
    (locals : Locals source table capacity) :
    eval source (capacityTimes (.const (BitVec.ofNat 64 factor))) = some (.val (.word (BitVec.ofNat 64 (factor * capacity)))) := by
  simp [eval, capacityTimes, localVar, evalHOLExact, evalListHOLExact, toExact, locals.capLocal,
    valueIsWord, valueWord, panOpHOL, ← BitVec.ofNat_mul, Nat.mul_comm capacity factor]

theorem read_key_amount {F : Type} (source : PanSemStateFiniteExact 64 F) (table : BitVec 64) (capacity : Nat)
    (locals : Locals source table capacity) :
    eval source (capacityTimes (localVar "stride")) = some (.val (.word (BitVec.ofNat 64 (32 * capacity)))) := by
  simp [eval, capacityTimes, localVar, evalHOLExact, evalListHOLExact, toExact, locals.capLocal, locals.strideLocal,
    valueIsWord, valueWord, panOpHOL, ← BitVec.ofNat_mul, Nat.mul_comm capacity 32]

theorem allocated_heap {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (pointer next : Nat) :
    (PersistentAlloc.nextState source name pointer next).globals.lookup (ofString "heap_ptr") =
      some (.val (.word (BitVec.ofNat 64 next))) := by
  simp [PersistentAlloc.nextState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.locals_allocated
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.read_scale
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.read_key_amount
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.allocated_heap
