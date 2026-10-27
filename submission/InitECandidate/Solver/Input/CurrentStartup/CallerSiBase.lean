import InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
import InitECandidate.Solver.Input.Witness.Fields

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A later field of the actual96-byte stateless record is distinct from its
base. The proof uses the real allocation bounds and64-bit address semantics. -/
theorem Context.si_ne_offset (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length offset : Nat)
    (context : Context input source pointer statelessRecord record gasWord length)
    (positive : 0 < offset) (inside : offset ≤ 88) :
    statelessRecord ≠ statelessRecord + BitVec.ofNat 64 offset := by
  have encoded : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have number : (statelessRecord + BitVec.ofNat 64 offset).toNat = statelessRecord.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; have := context.statelessRoom; omega), encoded]
  intro same
  have natural := congrArg BitVec.toNat same
  rw [number] at natural
  omega

/-- A genuine later scalar field write retains the payload-pointer cell at
si+0, alongside the shared input/gas/heap context. -/
theorem Context.store_base (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length offset : Nat) (expression : ExpHOL 64) (word : BitVec 64)
    (context : Context input source pointer statelessRecord record gasWord length)
    (positive : 0 < offset) (inside : offset ≤ 88) (aligned : offset % 8 = 0)
    (read : eval source expression = some (.val (.word word))) :
    let target := {source with memory := WitnessRadix.StoreWord.put source.memory (statelessRecord + BitVec.ofNat 64 offset) word}
    evaluateHOLFiniteState source (.store (Scalar.plus (localVar "si") offset) expression) = (none, target) ∧
      Context input target pointer statelessRecord record gasWord length ∧ target.memory statelessRecord = source.memory statelessRecord := by
  obtain ⟨run, targetContext⟩ := context.stateless_store input source pointer statelessRecord record gasWord length offset expression word inside aligned read
  exact ⟨run, targetContext, by
    simp [WitnessRadix.StoreWord.put, context.si_ne_offset input source pointer statelessRecord record gasWord length offset positive inside]⟩

end InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.Context.si_ne_offset
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.Context.store_base
