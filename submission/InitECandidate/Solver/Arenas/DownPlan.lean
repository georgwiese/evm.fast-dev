import InitECandidate.Solver.Arenas.Prefix

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem rounded_down_padded (pointer amount padded : BitVec 64)
    (pointerAligned : pointer.toNat % 8 = 0) (paddedAligned : padded.toNat % 8 = 0)
    (covers : amount.toNat ≤ padded.toNat) (padding : padded.toNat < amount.toNat + 8)
    (funded : padded.toNat ≤ pointer.toNat) :
    rounded .down pointer amount = pointer - padded := by
  have amountFunded : amount ≤ pointer := by change amount.toNat ≤ pointer.toNat; omega
  have paddedFunded : padded ≤ pointer := funded
  apply BitVec.eq_of_toNat_eq
  rw [rounded_down_nat pointer amount amountFunded, BitVec.toNat_sub_of_le paddedFunded]
  omega

theorem cursor_number (scratch : BitVec 64) (consumed : Nat) (funded : consumed ≤ scratch.toNat) :
    (scratch - BitVec.ofNat 64 consumed).toNat = scratch.toNat - consumed := by
  have small : consumed < 2 ^ 64 := Nat.lt_of_le_of_lt funded scratch.isLt
  have number : (BitVec.ofNat 64 consumed).toNat = consumed := by change consumed % (2 ^ 64) = consumed; exact Nat.mod_eq_of_lt small
  have affordable : BitVec.ofNat 64 consumed ≤ scratch := by change (BitVec.ofNat 64 consumed).toNat ≤ scratch.toNat; rw [number]; exact funded
  rw [BitVec.toNat_sub_of_le affordable, number]

/-- Natural constant-plan form, including the real four-byte allocation that
consumes eight aligned scratch bytes. -/
theorem rounded_decrement (scratch : BitVec 64) (before amount padded : Nat)
    (aligned : scratch.toNat % 8 = 0) (beforeAligned : before % 8 = 0) (paddedAligned : padded % 8 = 0)
    (covers : amount ≤ padded) (padding : padded < amount + 8)
    (room : before + padded ≤ scratch.toNat) :
    rounded .down (scratch - BitVec.ofNat 64 before) (BitVec.ofNat 64 amount) =
      scratch - BitVec.ofNat 64 (before + padded) := by
  have beforeSmall : before < 2 ^ 64 := by have bound := scratch.isLt; omega
  have amountSmall : amount < 2 ^ 64 := by have bound := scratch.isLt; omega
  have paddedSmall : padded < 2 ^ 64 := by have bound := scratch.isLt; omega
  have pointerNum := cursor_number scratch before (by omega)
  have amountNum : (BitVec.ofNat 64 amount).toNat = amount := by change amount % (2 ^ 64) = amount; exact Nat.mod_eq_of_lt amountSmall
  have paddedNum : (BitVec.ofNat 64 padded).toNat = padded := by change padded % (2 ^ 64) = padded; exact Nat.mod_eq_of_lt paddedSmall
  have rounded := rounded_down_padded (scratch - BitVec.ofNat 64 before) (BitVec.ofNat 64 amount) (BitVec.ofNat 64 padded)
    (by rw [pointerNum]; omega) (by rw [paddedNum]; exact paddedAligned)
    (by rw [amountNum, paddedNum]; exact covers) (by rw [amountNum, paddedNum]; exact padding)
    (by rw [paddedNum, pointerNum]; omega)
  rw [rounded, BitVec.sub_sub, ← BitVec.ofNat_add]

namespace Prefix
noncomputable def expectedState {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (cursor : BitVec 64) :=
  WitnessRadix.QueryBranch.bind {source with
    globals := source.globals.update (ofString "scratch_ptr", .val (.word cursor))
    clock := source.clock - 1} name cursor

/-- Arena-prefix allocation using a proved expected next cursor. All real
allocation/guard execution remains supplied by the checked arena constructor. -/
theorem allocate_expected {F : Type} (source entered : PanSemStateFiniteExact 64 F)
    (name : String) (expression : ExpHOL 64) (rest : List WitnessRadix.ProgramPrefix.Action)
    (restoreRest : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F)
    (pointer limit amount nextCursor : BitVec 64)
    (read : eval source expression = some (.val (.word amount)))
    (code : source.code.lookup (ofString "scratch_alloc") = some (formals, body .down, .one))
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit)))
    (aligned : limit.toNat % 8 = 0) (room : limit.toNat + amount.toNat ≤ pointer.toNat)
    (rounding : rounded .down pointer amount = nextCursor) (enough : 1 ≤ source.clock)
    (next : Executes .down (expectedState source name nextCursor) rest entered restoreRest) :
    Executes .down source (.allocate name expression :: rest) entered
      (fun target => restore source name (restoreRest target)) := by
  apply Executes.allocate (direction := .down) pointer limit amount read code pointerGlobal limitGlobal aligned room enough
  simpa only [resultWord, post, pointerName, rounding, expectedState] using next
end Prefix

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.rounded_down_padded
#print axioms InitECandidate.Solver.Arenas.cursor_number
#print axioms InitECandidate.Solver.Arenas.rounded_decrement
#print axioms InitECandidate.Solver.Arenas.Prefix.allocate_expected
