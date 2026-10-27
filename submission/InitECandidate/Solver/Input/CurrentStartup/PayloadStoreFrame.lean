import InitECandidate.Solver.Input.CurrentStartup.PayloadExtra

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- An observed scalar store to a real payload field preserves copied
input and all retained context. Actual mapping/value success is extracted
from the continuing store, and separation from the derived record geometry. -/
theorem Context.op_store (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) (length offset : Nat) (destination : ExpHOL 64) (operation : BinOp) (arguments : List (ExpHOL 64))
    (context : Context input source pointer record length) (inside : offset < 136)
    (read : eval source destination = some (.val (.word (record + BitVec.ofNat 64 offset))))
    (actual : evaluateHOLFiniteState source (.store destination (.op operation arguments)) = (none, target)) : Context input target pointer record length := by
  have encoded : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have number : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; have := context.recordRoom; omega), encoded]
  have image := Blob.HeapInput.op_store_separate source target input pointer (record + BitVec.ofNat 64 offset)
    destination operation arguments context.image context.aligned (by have := context.room; omega)
    (Or.inr (by rw [number]; have := context.recordLower; omega)) read actual
  obtain ⟨value, memory, evaluated, stored, targetEq⟩ := store_at_normal source target destination (.op operation arguments) _ read actual
  have fields : target = {source with memory := target.memory, clock := target.clock} := by rw [targetEq]
  rw [fields] at image ⊢
  exact Context.memory_clock input source pointer record length target.clock target.memory context image

end InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.Context.op_store
