import InitECandidate.Solver.MutableTable.KeyHash
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.AlignedMapped

namespace InitECandidate.Solver.MutableTable.KeyCompare
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def values (kind : KeyHash.Kind) (a b : BitVec 64) : List (ValueHOL 64) := MemeqByteRuntime.values a b (KeyHash.keySize kind)

/-- Uniform actual comparator caller for every original table key width.
Mapped byte regions derive every read for both alignments. No equality,
collision distribution or successful comparator run is assumed. -/
theorem call_of_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (a b : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind a b))
    (known : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (aFits : a.toNat + KeyHash.keySize kind < 2 ^ 64) (bFits : b.toNat + KeyHash.keySize kind < 2 ^ 64)
    (leftMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (little : source.be = false) (enough : MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ (spent : Nat) (answer : BitVec 64), spent ≤ MemeqByteRuntime.price (KeyHash.keySize kind) ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "memeq") arguments continuation) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - (spent + 1)} name answer) continuation
         (output.1, restore source name output.2)) := by
  classical
  cases kind with
  | account => exact MemeqSized.call_of_mapped source .address a b name arguments continuation args known aFits bFits leftMapped rightMapped enough
  | storage => exact MemeqSized.call_of_mapped source .storage a b name arguments continuation args known aFits bFits leftMapped rightMapped enough
  | indexedAccount =>
    exact MemeqByteRuntime.other_call_of_mapped source a b 28 name arguments continuation args known
      (by decide) (by decide) (by decide) (by decide) aFits bFits leftMapped rightMapped enough
  | indexedStorage =>
    exact MemeqByteRuntime.other_call_of_mapped source a b 60 name arguments continuation args known
      (by decide) (by decide) (by decide) (by decide) aFits bFits leftMapped rightMapped enough
  | word =>
    obtain ⟨callee, called, aLocal, bLocal, lengthLocal⟩ := MemeqByteRuntime.environment source.code.lookup a b 32 known
    let entry := callEntryStateHOLFinite source callee
    let left := KeyHash.observedKey source a
    let right := KeyHash.observedKey source b
    have leftView := MemoryBytes.byteView_of_fields source entry rfl rfl rfl a left (KeyHash.observed_view source a leftMapped)
    have rightView := MemoryBytes.byteView_of_fields source entry rfl rfl rfl b right (KeyHash.observed_view source b rightMapped)
    obtain ⟨spent, spentBound, bodyRun⟩ := Memeq32.memory_execute entry a b left right aLocal bLocal lengthLocal leftView rightView
      aFits bFits little (by change 4 ≤ source.clock - 1; change 5 ≤ source.clock at enough; omega)
    let answer : BitVec 64 := if left = right then 1#64 else 0#64
    have answerBound : answer = 0#64 ∨ answer = 1#64 := by dsimp only [answer]; split <;> simp
    have frame : emptyLocalsHOLFinite (restore entry "i" (emptyLocalsHOLFinite {entry with clock := entry.clock - spent})) =
        emptyLocalsHOLFinite {source with clock := source.clock - 1 - spent} := rfl
    have actual := Input.CallNormal.pure_return_execute source _ name (ofString "memeq") arguments _ Memeq32.body continuation callee
      answer spent args called (by change 5 ≤ source.clock at enough; omega) bodyRun frame
    have clocks : source.clock - 1 - spent = source.clock - (spent + 1) := by omega
    exact ⟨spent, answer, spentBound, answerBound, by simpa only [clocks] using actual⟩

end InitECandidate.Solver.MutableTable.KeyCompare

#print axioms InitECandidate.Solver.MutableTable.KeyCompare.call_of_mapped
