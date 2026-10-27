import InitECandidate.Solver.Input.CurrentStartup.PayloadExtra
import InitECandidate.Solver.Input.PayloadWordStore

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

/-- A known scalar payload-field value can be stored using the actual derived
record geometry. This retains the complete context and exact old-word frame. -/
theorem Context.field_store (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) (length offset : Nat) (expression : ExpHOL 64) (word : BitVec 64)
    (context : Context input source pointer record length) (inside : offset ≤ 128) (aligned : offset % 8 = 0)
    (read : eval source expression = some (.val (.word word))) :
    evaluateHOLFiniteState source (.store (Scalar.plus (localVar "pl") offset) expression) =
      (none, Payload.fieldStored source record offset word) ∧
    Context input (Payload.fieldStored source record offset word) pointer record length ∧
    (Payload.fieldStored source record offset word).memory (record + BitVec.ofNat 64 offset) = .word word ∧
    (∀ query, query ≠ record + BitVec.ofNat 64 offset →
      (Payload.fieldStored source record offset word).memory query = source.memory query) := by
  obtain ⟨run, image, cell, frame⟩ := Payload.field_store source input pointer record context.image context.pl context.domain
    context.aligned context.recordAligned (by have := context.lower; omega) context.recordLower (by have := context.recordRoom; omega)
    offset inside aligned expression word read
  exact ⟨run, Context.memory_clock input source pointer record length source.clock _ context image, cell, frame⟩

end InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.Context.op_store

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace.Context.field_store
