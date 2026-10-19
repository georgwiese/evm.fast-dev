import InitECandidate.Solver.MutableTable.MemeqSmallNormal
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.MutableTable.MemeqSmall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Real small comparison declarations inside a continuing loop body expose
their actual binary result and paid prefix, including the original fast paths. -/
theorem none_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (small : length ≤ 64) (aFits : a.toNat + length < 2^64) (bFits : b.toNat + length < 2^64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (MemeqByteRuntime.values a b length))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "memeq") arguments continuation) = (none, post)) :
    ∃ paid answer inner, 1 ≤ paid ∧ paid ≤ MemeqByteRuntime.price length + 1 ∧ paid ≤ source.clock ∧
      (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name answer) continuation = (none, inner) ∧
      post = restore source name inner := by
  obtain ⟨callee, called, aLocal, bLocal, lengthLocal⟩ := MemeqByteRuntime.environment source.code.lookup a b length code
  obtain ⟨positive, target, returned, inner, bodyRun, checked, tailRun, scope⟩ :=
    Input.CallNormal.scoped_none source post name .one (ofString "memeq") arguments _ Memeq32.body continuation callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨spent, answer, bounded, funded, binary, resultEq, fields⟩ :=
    body_normal entry target a b length aLocal bLocal lengthLocal small aFits bFits leftMapped rightMapped returned bodyRun
  have restored := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) fields
  change {target with locals := source.locals} = {source with clock := source.clock - 1 - spent} at restored
  have subtract : source.clock - 1 - spent = source.clock - (spent + 1) := by omega
  rw [subtract] at restored
  have canonical : Input.CallNormal.continuationEntry source target name returned =
      bind {source with clock := source.clock - (spent + 1)} name answer := by
    rw [resultEq]
    exact congrArg (setVarHOLFinite (ofString name) (.val (.word answer))) restored
  change spent ≤ source.clock - 1 at funded
  refine ⟨spent + 1, answer, inner, by omega, by omega, by omega, binary, ?_, scope⟩
  rw [canonical] at tailRun
  exact tailRun

end InitECandidate.Solver.MutableTable.MemeqSmall

#print axioms InitECandidate.Solver.MutableTable.MemeqSmall.none_prefix
