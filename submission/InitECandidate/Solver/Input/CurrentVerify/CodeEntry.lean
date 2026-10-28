import InitECandidate.Solver.Input.CurrentVerify.NodeEntry

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def codeArguments : List (ExpHOL 64) := [field 56,field 64]
def afterCodes : ProgHOL 64 := match afterNodes with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem code_shape : afterNodes=.decCall (ofString "codedb") .one (ofString "nodedb_build") codeArguments afterCodes := by
  simp only [afterNodes,codeArguments,afterCodes,nodeCall,afterHeaders,headerCall,afterPayload,body,
    Guest.Software.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar,field,
    CallPrefix.cut,if_neg (show ofString "check_gas_limit"≠ofString "nodedb_build" from by decide),↓reduceIte]

theorem code_arguments {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) :
    ∃ array start length,
      CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 56 65536 (2^31) ∧
      VarList.decodedCount input start length<2^31 ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) codeArguments=
        some [.val (.word (VarList.decodedArray array length)),.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))] := by
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩ := data.witnesses
  obtain ⟨heap,cell,lower,upper,aligned⟩ := data.heap
  have countBound : VarList.decodedCount input codeStart codeLength<2^31 := by have := codeImage.before; omega
  have args := codeImage.arguments data.arena.domain data.siLocal (by decide) (by decide)
  exact ⟨codes,codeStart,codeLength,codeImage,countBound,args⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.code_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.code_arguments
