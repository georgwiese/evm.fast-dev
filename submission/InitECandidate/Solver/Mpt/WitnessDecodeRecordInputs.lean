import InitECandidate.Solver.Mpt.WitnessDecodeRecordNormal

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchWords (array pointer length branch : BitVec 64) : String→BitVec 64
  | "arr"=>array | "p"=>pointer | "n"=>length | "br"=>branch | _=>0#64
def extensionWords (array pointer length nibbles nibbleLength : BitVec 64) : String→BitVec 64
  | "arr"=>array | "p"=>pointer | "n"=>length | "nib"=>nibbles | "nlen"=>nibbleLength | _=>0#64

theorem branch_record_ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array pointer length branch : BitVec 64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch))) :
    ∀ field∈RecordKind.fields .branch (branchWords array pointer length branch),field.value.Ready source := by
  simp [RecordKind.fields,branchFields,branchWords,LocalFields.Operand.Ready,arrayCell,pointerCell,lengthCell,branchCell]

theorem extension_record_ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array pointer length nibbles nibbleLength leaf : BitVec 64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)])) :
    ∀ field∈RecordKind.fields .extension (extensionWords array pointer length nibbles nibbleLength),field.value.Ready source := by
  simp [RecordKind.fields,extensionFields,extensionWords,LocalFields.Operand.Ready,eval,evalHOLExact,localVar,toExact,
    arrayCell,pointerCell,lengthCell,compactCell]

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_record_ready
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_record_ready
