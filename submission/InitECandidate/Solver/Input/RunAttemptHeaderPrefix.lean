import InitECandidate.Solver.Input.RunAttemptRead
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def headerEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (payload : BitVec 64) := bind source "pl" payload

def restoreHeader (source : PanSemStateFiniteExact 64 Guest.HostMemory) (payload : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "pl" (restore (headerEntry source payload) "vh" target)

/-- Original run_attempt815 reaches its real validator directly after the
actual SI0 payload declaration. Every outcome either fits the validator's
own allowance or resumes at its true returned pair and preserved context. -/
theorem header_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (si payload array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    (context : Headers.Validate.Context source array heap count cursor limit stp pad pointers lengths lower upper budget)
    (siArena : AllocatedBytes.Arena si 96) (siAligned : si.toNat%8=0)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (payloadCell : source.memory (byteAddress si 0)=.word payload)
    (arrayCell : source.memory (byteAddress si 72)=.word array) (countCell : source.memory (byteAddress si 80)=.word count)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤Headers.Validate.bodyPrice count budget+1 ∨
      ∃ target inner,Headers.Validate.Returned (headerEntry source payload) target array heap count cursor limit stp pad pointers lengths lower upper budget ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry (headerEntry source payload) target "vh" (Headers.Validate.result heap (Headers.Validate.hashesPointer heap count))) afterHeaders=(outcome,inner) ∧
        post=restoreHeader source payload inner := by
  have payloadRead:=field_read source si payload 0 context.arena.domain siArena siAligned (by decide) (by decide) siCell payloadCell
  rw [shapes.1] at run
  obtain ⟨first,continued,endpoint⟩ := Input.ScalarScope.declare_trace source post "pl" (field 0) payload afterPayload outcome payloadRead run
  let entry:=headerEntry source payload
  change evaluateHOLFiniteState entry afterPayload=(outcome,first) at continued
  have ready:=context.of_fields source entry array heap count cursor limit stp pad pointers lengths lower upper budget rfl rfl rfl rfl rfl ⟨by intro query low high; rfl⟩
  have entrySi : entry.locals.lookup (ofString "si")=some (.val (.word si)) :=
    (bind_lookup_other source "pl" "si" payload (by decide)).trans siCell
  have args:=header_arguments_read entry si array count ready.arena.domain siArena siAligned entrySi arrayCell countCell
  rw [shapes.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip,shapes.2.2.1] at continued
  rcases Headers.Validate.scoped_trace entry first array heap count cursor limit stp pad pointers lengths lower upper budget ready "vh" headerArguments afterHeaders args outcome continued with stopped|reached
  · have clock : post.clock=first.clock := by rw [endpoint]; rfl
    change source.clock-first.clock≤Headers.Validate.bodyPrice count budget+1 at stopped
    rw [clock]
    exact Or.inl stopped
  · obtain ⟨target,inner,returned,remaining,restored⟩ := reached
    exact Or.inr ⟨target,inner,returned,remaining,by rw [endpoint,restored]; rfl⟩

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.header_prefix
