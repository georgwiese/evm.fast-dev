import InitECandidate.Solver.Input.RunAttemptRead
import InitECandidate.Solver.MutableTable.WitnessBuildInputsFrame

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem node_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (si array : BitVec 64) (count : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena si 96) (aligned : si.toNat%8=0)
    (binding : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (arrayCell : source.memory (byteAddress si 40)=.word array) (countCell : source.memory (byteAddress si 48)=.word (BitVec.ofNat 64 count)) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) nodeArguments=some (MutableTable.WitnessBuild.values array count) := by
  have first:=field_read source si array 40 domain arena aligned (by decide) (by decide) binding arrayCell
  have second:=field_read source si (BitVec.ofNat 64 count) 48 domain arena aligned (by decide) (by decide) binding countCell
  simp only [eval] at first second
  simp [nodeArguments,MutableTable.WitnessBuild.values,evalListHOLFinite,evalListHOLExact,first,second]

theorem code_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (si array : BitVec 64) (count : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena si 96) (aligned : si.toNat%8=0)
    (binding : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (arrayCell : source.memory (byteAddress si 56)=.word array) (countCell : source.memory (byteAddress si 64)=.word (BitVec.ofNat 64 count)) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) codeArguments=some (MutableTable.WitnessBuild.values array count) := by
  have first:=field_read source si array 56 domain arena aligned (by decide) (by decide) binding arrayCell
  have second:=field_read source si (BitVec.ofNat 64 count) 64 domain arena aligned (by decide) (by decide) binding countCell
  simp only [eval] at first second
  simp [codeArguments,MutableTable.WitnessBuild.values,evalListHOLFinite,evalListHOLExact,first,second]

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.node_arguments_read
#print axioms InitECandidate.Solver.Input.RunAttempt.code_arguments_read
