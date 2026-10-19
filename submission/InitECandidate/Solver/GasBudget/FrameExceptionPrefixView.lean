import InitECandidate.Solver.GasBudget.FramePrefixEffect
import InitECandidate.Solver.GasBudget.FrameExceptionAccountedView

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Reconstruct the actual exception-handler fields after CALL's pre-charge
SP/footer writes. Message-reservoir ownership is a current separation fact. -/
def View.after_frame_prefix {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (view : View source) {paid : Nat} (effect : FramePrefixEffect source target view.frame paid)
    (aligned : view.frame.toNat % 8 = 0) (fits : view.frame.toNat + 280 < 2^64)
    (reservoirAway : MemoryWriter.BytesAway (view.frame + 240#64) (view.message + 48#64) 20) : View target := by
  apply view.after_accounted
  · intro key other
    rw [effect.globals_eq]
  · exact effect.memaddrs_eq
  · exact effect.budget
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact effect.outside _ (offsets_ne view.frame 72#64 16#64 (by decide)) (AddressMasked.header_away view.frame 72 aligned fits (by decide))
    · exact effect.outside _ (offsets_ne view.frame 112#64 16#64 (by decide)) (AddressMasked.header_away view.frame 112 aligned fits (by decide))
    · exact effect.outside _ (offsets_ne view.frame 192#64 16#64 (by decide)) (AddressMasked.header_away view.frame 192 aligned fits (by decide))
  · exact effect.outside _ view.reservoirOutsideSP reservoirAway

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.View.after_frame_prefix
