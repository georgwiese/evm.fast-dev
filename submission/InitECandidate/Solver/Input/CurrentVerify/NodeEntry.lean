import InitECandidate.Solver.Input.CurrentVerify.NodePrefix
import InitECandidate.Solver.Input.CurrentStartup.WitnessArrayArguments
import InitECandidate.Solver.Input.CurrentTable.NodeBuildSyntax
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def nodeArguments : List (ExpHOL 64) := [field 40,field 48]
def afterNodes : ProgHOL 64 := match nodeCall with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem node_shape : nodeCall=.decCall (ofString "nodedb") .one (ofString "nodedb_build") nodeArguments afterNodes := by
  simp only [nodeCall,afterNodes,nodeArguments,field,afterHeaders,headerCall,afterPayload,body,
    Guest.Software.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar,
    CallPrefix.cut,if_neg (show ofString "check_gas_limit"≠ofString "nodedb_build" from by decide),↓reduceIte]

/-- The preserved actual node image supplies both builder arguments and
a strict count bound. The count bound follows from the real allocated
record extent and current heap ceiling, including empty arrays. -/
theorem node_arguments {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) :
    ∃ array start length,
      CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 40 1024 (2^31) ∧
      VarList.decodedCount input start length<2^31 ∧
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) nodeArguments=
        some [.val (.word (VarList.decodedArray array length)),.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))] := by
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩:=data.witnesses
  obtain ⟨heap,cell,lower,upper,aligned⟩:=data.heap
  have countBound : VarList.decodedCount input nodeStart nodeLength<2^31 := by have before:=nodeImage.before; omega
  have args:=nodeImage.arguments data.arena.domain data.siLocal (by decide) (by decide)
  exact ⟨nodes,nodeStart,nodeLength,nodeImage,countBound,args⟩

/-- The actual current nodedb caller has the real two-word callee ABI and
strict capacity-loop count bound, not a previous hash-map environment. -/
theorem node_environment {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) :
    ∃ array start length callee,
      CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 40 1024 (2^31) ∧
      VarList.decodedCount input start length<2^31 ∧
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) nodeArguments=
        some [.val (.word (VarList.decodedArray array length)),.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "nodedb_build")
        [.val (.word (VarList.decodedArray array length)),.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))]=
        some (CurrentTable.NodeBuild.body,callee,.one) ∧
      callee.lookup (ofString "slice_arr")=some (.val (.word (VarList.decodedArray array length))) ∧
      callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))) := by
  obtain ⟨array,start,length,image,small,args⟩:=node_arguments data
  obtain ⟨callee,called,arrayCell,countCell⟩:=word_pair_environment source.code.lookup (ofString "nodedb_build") (ofString "slice_arr") (ofString "n")
    CurrentTable.NodeBuild.body .one (VarList.decodedArray array length) (BitVec.ofNat 64 (VarList.decodedCount input start length)) (by decide)
    (CurrentTable.NodeBuild.original_code source.code data.arena.code)
  exact ⟨array,start,length,callee,image,small,args,called,arrayCell,countCell⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.node_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.node_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.node_environment
