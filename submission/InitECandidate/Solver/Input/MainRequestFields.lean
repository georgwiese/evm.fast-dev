import InitECandidate.Solver.Input.MainRequestSetup
import InitECandidate.Solver.Input.RequestFromHeader

namespace InitECandidate.Solver.Input.Main.RequestPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem ready_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (clock : Nat) :
    (ready source input clock).clock = clock - 1 := rfl

theorem ready_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (clock : Nat) :
    (ready source input clock).locals.lookup (ofString "np") = some (.val (.word (inputPointer + 18#64))) ∧
    (ready source input clock).locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)))) := by
  constructor
  · exact (bind_lookup_other (Request.positioned (current source input clock) input inputPointer (cursor input) (Guest.GasLimit.le32 input 6)) "nlen" "np" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact bind_lookup_same _ _ _

theorem ready_si (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (clock : Nat) :
    (ready source input clock).locals.lookup (ofString "si") = some (.val (.word (cursor input))) := by
  exact (bind_lookup_other (Request.positioned (current source input clock) input inputPointer (cursor input) (Guest.GasLimit.le32 input 6)) "nlen" "si" _ (by decide)).trans
    ((bind_lookup_other (Request.chained (current source input clock) input (cursor input) (Guest.GasLimit.le32 input 6)) "np" "si" _ (by decide)).trans (bind_lookup_same _ _ _))

/-- Exact original request-prefix fields relative to the actual decoder
callee entry; outer guards/stores cost <=4 and the SI allocation costs1. -/
theorem ready_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (paid : Nat) (bound : paid ≤ 4) :
    Request.ReadyFrame source (ready source input (source.clock - paid)) (cursor input) := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [ready_clock]
    omega

end InitECandidate.Solver.Input.Main.RequestPrefix

#print axioms InitECandidate.Solver.Input.Main.RequestPrefix.ready_clock
#print axioms InitECandidate.Solver.Input.Main.RequestPrefix.ready_bindings
#print axioms InitECandidate.Solver.Input.Main.RequestPrefix.ready_frame

#print axioms InitECandidate.Solver.Input.Main.RequestPrefix.ready_si
