import InitECandidate.Solver.Input.MainInputCopy

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def inputCursor (input : Guest.InputBlob) := PersistentAlloc.rounded inputPointer (inputAmount input)

theorem input_cursor_bounds (input : Guest.InputBlob) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes) :
    2713731432 + input.length % 2 ^ 64 + 8 ≤ (inputCursor input).toNat ∧
      (inputCursor input).toNat ≤ 2847949152 ∧ (inputCursor input).toNat % 8 = 0 := by
  have small : input.length % 2 ^ 64 ≤ 134217712 := bounded
  have amount : (inputAmount input).toNat = input.length % 2 ^ 64 + 8 := by
    unfold inputAmount
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have room : inputPointer.toNat + (inputAmount input).toNat ≤ 33806089496 := by
    rw [amount]
    change 2713731432 + input.length % 2 ^ 64 + 8 ≤ _
    omega
  have guards := PersistentAlloc.guards inputPointer (inputAmount input) room
  have number := PersistentAlloc.rounded_nat inputPointer (inputAmount input) (by rw [amount]; change 2713731432 + (input.length % 2 ^ 64 + 8) + 7 < _; omega)
  change (inputCursor input).toNat = _ at number
  rw [amount] at number
  change (inputCursor input).toNat = (2713731432 + (input.length % 2 ^ 64 + 8) + 7) / 8 * 8 at number
  refine ⟨?_,?_,guards.2.2.2.2⟩
  · have lower := guards.2.2.1
    rw [amount] at lower
    exact lower
  · omega

theorem InputCopied.other_global (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input source current) (key : MlS) (different : key ≠ ofString "heap_ptr") :
    current.globals.lookup key = source.globals.lookup key := by
  rw [copied.globals]
  simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm different]

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.input_cursor_bounds
#print axioms InitECandidate.Solver.Input.Main.InputCopied.other_global
