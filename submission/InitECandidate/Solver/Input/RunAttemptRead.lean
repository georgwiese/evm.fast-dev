import InitECandidate.Solver.Input.RunAttemptProgram
import InitECandidate.Solver.Headers.ValidateContextFrame

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual scalar SI fields, including their mapping, are read from the
existing96-byte decoder allocation rather than assumed expression results. -/
theorem field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (si word : BitVec 64) (offset : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena si 96) (aligned : si.toNat%8=0)
    (inside : offset<96) (offsetAligned : offset%8=0)
    (binding : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (cell : source.memory (byteAddress si offset)=.word word) : eval source (field offset)=some (.val (.word word)) := by
  have mapped:=AllocatedBytes.word_mapped source si 96 offset domain arena inside aligned offsetAligned
  simp only [byteAddress] at cell mapped
  simp [field,eval,evalHOLExact,evalListHOLExact,localVar,toExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,mapped,cell]

theorem header_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (si array count : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena si 96) (aligned : si.toNat%8=0)
    (binding : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (arrayCell : source.memory (byteAddress si 72)=.word array) (countCell : source.memory (byteAddress si 80)=.word count) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) headerArguments=some [.val (.word array),.val (.word count)] := by
  have first:=field_read source si array 72 domain arena aligned (by decide) (by decide) binding arrayCell
  have second:=field_read source si count 80 domain arena aligned (by decide) (by decide) binding countCell
  simp only [eval] at first second
  simp [headerArguments,evalListHOLFinite,evalListHOLExact,first,second]

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.field_read
#print axioms InitECandidate.Solver.Input.RunAttempt.header_arguments_read
