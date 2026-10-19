import InitECandidate.Solver.Mpt.WsAccountWorldAgreement
import InitECandidate.Solver.GasBudget.JournalProtectedFrame
import InitECandidate.Solver.WitnessRadix.Keccak256EnvironmentFields
import InitECandidate.Solver.Rlp.ValidationArena

namespace InitECandidate.Solver.Mpt.StateWorldFrame
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString

theorem hash_environment (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad : BitVec 64)
    (environment : Keccak256.Environment source stp pad) (domain : target.memaddrs = source.memaddrs) (code : target.code = source.code)
    (oracle : target.ffi.oracle = source.ffi.oracle) (globals : Journal.OtherGlobals source target) : Keccak256.Environment target stp pad := {
  domain := domain.trans environment.domain
  stateGlobal := (globals _ (by decide) (by decide)).trans environment.stateGlobal
  scratchGlobal := (globals _ (by decide) (by decide)).trans environment.scratchGlobal
  zeroCode := by rw [code]; exact environment.zeroCode
  copyCode := by rw [code]; exact environment.copyCode
  hashCode := ⟨by rw [code]; exact environment.hashCode.block,by rw [code]; exact environment.hashCode.perm,oracle.trans environment.hashCode.oracleEq⟩ }

theorem scratch_arena (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (domain : target.memaddrs = source.memaddrs) (globals : Journal.OtherGlobals source target) : Rlp.Validation.Arena target cursor limit :=
  ⟨domain.trans arena.domain,(globals _ (by decide) (by decide)).trans arena.cursorGlobal,(globals _ (by decide) (by decide)).trans arena.limitGlobal,
    arena.ordered,arena.aligned,arena.lower,arena.upper⟩

/-- Immutable witness ownership survives actual state/journal mutations.
The tables' current floors and original journal reservation place every
witness word inside the already-proved protected memory frame. -/
theorem witness_world {ι κ : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root nibs : BitVec 64)
    (cutoff frozenEnd valueLimit cursor base cap : Nat) (objects : ι → TableFamily.Object) (next : κ → TableFamily.Object)
    (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit) (family : TableFamily.Model source cursor objects)
    (afterWorld : frozenEnd ≤ cursor) (floors : ∀ index,frozenEnd ≤ (objects index).floor) (journalAfter : frozenEnd ≤ base)
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be) (globals : Journal.OtherGlobals source target)
    (frame : ∀ query : BitVec 64,cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
      TableFamily.Outside next query ∧ target.memory query = source.memory query) : Nonempty (WsAccountLeaf.World target ws root nibs cutoff frozenEnd valueLimit) := by
  apply Nonempty.intro
  apply WsAccountLeaf.World.of_agreement source target ws root nibs cutoff frozenEnd valueLimit world domain endian
    (globals _ (by decide) (by decide)) (globals _ (by decide) (by decide))
  intro query needed
  have bounds := world.footprint query needed
  have outside : TableFamily.Outside objects query := by
    intro index
    exact TableFamily.outside_floor source (objects index).kind (objects index).plan (objects index).slots cursor (objects index).floor (family.tables index) query
      (Nat.lt_of_lt_of_le bounds.2 (floors index))
  exact (frame query bounds.1 (by omega) outside (Or.inl (by omega))).2

end InitECandidate.Solver.Mpt.StateWorldFrame

#print axioms InitECandidate.Solver.Mpt.StateWorldFrame.hash_environment
#print axioms InitECandidate.Solver.Mpt.StateWorldFrame.scratch_arena
#print axioms InitECandidate.Solver.Mpt.StateWorldFrame.witness_world
