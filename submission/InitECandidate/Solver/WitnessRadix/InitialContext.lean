import InitECandidate.Solver.WitnessRadix.ConstructionInvariant
import InitECandidate.Solver.WitnessRadix.BuildInitialState

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open SplitScope

def initialContext (layout : Layout) (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64)) : SplitContext :=
  { src := layout.primary, dst := layout.backup, keys := layout.keys
    node := branchAddress layout.keys layout.count 0, depth := 0#64, dest := cell layout .header 24
    pendingStart := cell layout .primary (8 * layout.count)
    pendingCount := cell layout .backup (8 * layout.count)
    pendingNode := cell layout .vals (8 * layout.count)
    keyFor := keyFor, input := input, position := 0, start := 0, limit := layout.count }

def initialState {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) : PanSemStateFiniteExact 64 F :=
  BuildEntry.entered source layout.table (BitVec.ofNat 64 layout.count) layout.keys layout.vals layout.primary layout.backup

theorem initial_layout (layout : Layout) (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64))
    (length : input.length = layout.count) (ordinals : ∀ ordinal ∈ input, ordinal.toNat < layout.count) :
    ContextAt layout (initialContext layout keyFor input) 0 0 (.header, 24) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ordinals⟩
  change 0 + input.length ≤ layout.count
  omega

theorem initial_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64)) (length : input.length = layout.count) :
    SplitCount.TaskLocals (initialState source layout) (initialContext layout keyFor input) := by
  constructor
  all_goals simp [initialState, initialContext, BuildEntry.entered, BuildEntry.initialValues,
    QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString,
    branchAddress, cell, base, byteAddress, length, BitVec.ofNat_mul, Nat.mul_comm]

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.initial_layout
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.initial_locals
