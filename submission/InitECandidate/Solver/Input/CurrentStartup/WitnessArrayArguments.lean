import InitECandidate.Solver.Input.CurrentStartup.WitnessArrayImage

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessArrays
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def arguments (offset : Nat) : List (ExpHOL 64) :=
  [.load .one (Scalar.plus (localVar "si") offset),.load .one (Scalar.plus (localVar "si") (offset+8))]

/-- Both actual SI arguments load from the same physical decoded image,
including empty arrays. No input-pointer mapping is assumed for an empty list. -/
theorem Image.arguments {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array : BitVec 64} {start length boundary offset itemLimit countLimit : Nat}
    (data : Image input source pointer si array start length boundary offset itemLimit countLimit)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (offsetBound : offset+8<96) (aligned : offset%8=0) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (arguments offset)=
      some [.val (.word (VarList.decodedArray array length)),.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))] := by
  classical
  have localRead := Request.local_word source "si" si siLocal
  have pointerRead := Witness.load_word_read source (Scalar.plus (localVar "si") offset) (si+BitVec.ofNat 64 offset) _
    (Scalar.plus_read source (localVar "si") si offset localRead)
    (AllocatedBytes.word_mapped source si 96 offset domain data.siArena (by omega) data.siAligned aligned) data.pointerCell
  have countRead := Witness.load_word_read source (Scalar.plus (localVar "si") (offset+8)) (si+BitVec.ofNat 64 (offset+8)) _
    (Scalar.plus_read source (localVar "si") si (offset+8) localRead)
    (AllocatedBytes.word_mapped source si 96 (offset+8) domain data.siArena (by omega) data.siAligned (by omega)) data.countCell
  change evalHOLExact source.toExact (.load .one (Scalar.plus (localVar "si") offset))=_ at pointerRead
  change evalHOLExact source.toExact (.load .one (Scalar.plus (localVar "si") (offset+8)))=_ at countRead
  simp [WitnessArrays.arguments,evalListHOLFinite,evalListHOLExact,pointerRead,countRead]

end InitECandidate.Solver.Input.CurrentStartup.WitnessArrays

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessArrays.Image.arguments
