import InitECandidate.Solver.Input.PBytesProgram

namespace InitECandidate.Solver.Input.BytesListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htr_bytes_list with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "n",.one),(ofString "limit_chunks",.one),(ofString "out",.one)]
def afterMark : ProgHOL 64 := match body with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterPack : ProgHOL 64 := match afterMark with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterMerkle : ProgHOL 64 := match afterPack with | .seq _ tail=>tail | _=>.skip
def afterRelease : ProgHOL 64 := match afterMerkle with | .seq _ tail=>tail | _=>.skip

def packArguments : List (ExpHOL 64) := [localVar "p",localVar "n"]
def merkleArguments : List (ExpHOL 64) := [.rfield 0 (localVar "pk"),.rfield 1 (localVar "pk"),localVar "limit_chunks",localVar "out"]
def mixArguments : List (ExpHOL 64) := [localVar "out",localVar "n",localVar "out"]

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark ∧
    afterMark=.decCall (ofString "pk") PackBytes.returnShape (ofString "pack_bytes") packArguments afterPack ∧
    afterPack=.seq (.call (some (none,none)) (ofString "merkleize") merkleArguments) afterMerkle ∧
    afterMerkle=.seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) afterRelease ∧
    afterRelease=.seq (.call (some (none,none)) (ofString "mix_in_length") mixArguments) (.return (.const 0#64)) := by
  simp only [body,afterMark,afterPack,afterMerkle,afterRelease,Guest.guestFn_htr_bytes_list,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,packArguments,merkleArguments,mixArguments,PackBytes.returnShape,localVar]
  exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro⟩

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_bytes_list")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 183 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htr_bytes_list) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_htr_bytes_list,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Main's only actual byte-list use is payload extra data: at most32bytes
and original literal limit1. The real pack tuple supplies its actual count. -/
theorem merkle_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out : BitVec 64) (n : Nat)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) merkleArguments=
      some (Merkle.values cursor (BitVec.ofNat 64 (PackBytes.chunks n)) 1#64 out) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,merkleArguments,localVar,packed,limitLocal,output,PackBytes.packedValue,Merkle.values]

theorem extra_chunks (n : Nat) (short : n≤32) : PackBytes.chunks n≤1 := by unfold PackBytes.chunks; omega

end InitECandidate.Solver.Input.BytesListHash

#print axioms InitECandidate.Solver.Input.BytesListHash.body_shape
#print axioms InitECandidate.Solver.Input.BytesListHash.original_code
#print axioms InitECandidate.Solver.Input.BytesListHash.merkle_arguments
#print axioms InitECandidate.Solver.Input.BytesListHash.extra_chunks
