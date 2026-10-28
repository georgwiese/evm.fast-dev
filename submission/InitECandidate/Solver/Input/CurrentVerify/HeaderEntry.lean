import InitECandidate.Solver.Input.CurrentVerify.HeaderProgram
import InitECandidate.Solver.Input.CurrentStartup.WitnessArrayArguments
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The real run_attempt payload read and initial skip expose the exact
validator caller on every outcome. Only the actual PL binding is restored. -/
theorem header_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (si record : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (siArena : AllocatedBytes.Arena si 96) (aligned : si.toNat%8=0)
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si))) (cell : source.memory si=.word record)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body=(result,post)) :
    ∃ inner,evaluateHOLFiniteState (bind source "pl" record) headerCall=(result,inner) ∧ post=restore source "pl" inner := by
  have read := Witness.load_word_read source (Scalar.plus (localVar "si") 0) si record
    (by simpa only [BitVec.add_zero] using Scalar.plus_read source (localVar "si") si 0 (Request.local_word source "si" si siLocal))
    (by simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source si 96 0 domain siArena (by decide) aligned (by decide)) cell
  change eval source (field 0)=some (.val (.word record)) at read
  rw [header_shapes.1] at actual
  obtain ⟨inner,run,endpoint⟩ := ScalarScope.declare_trace source post "pl" (field 0) record afterPayload result read actual
  rw [header_shapes.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip] at run
  exact ⟨inner,run,endpoint⟩

/-- The same decoded header image supplies both actual validator arguments
after the real PL declaration. Empty arrays still need only the SI record. -/
theorem header_arguments {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array : BitVec 64} {start length boundary : Nat}
    (data : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 72 1024 256)
    (record : BitVec 64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si))) :
    evalListHOLFinite (bind source "pl" record) (h:=fun address=>Classical.propDecidable ((bind source "pl" record).memaddrs address)) headerArguments=
      some [.val (.word (VarList.decodedArray array length)),.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))] := by
  have next : CurrentStartup.WitnessArrays.Image input (bind source "pl" record) pointer si array start length boundary 72 1024 256 :=
    data.of_interval (by decide) (by intro query lower upper; rfl)
  have siNext := (bind_lookup_other source "pl" "si" record (by decide)).trans siLocal
  have arguments:=next.arguments domain siNext (by decide) (by decide)
  exact arguments

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.header_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.header_arguments
