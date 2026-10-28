import InitECandidate.Solver.Input.CurrentVerify.HeaderReached
import InitECandidate.Solver.Headers.CurrentValidate.RowsFromImage
import InitECandidate.Solver.Headers.CurrentValidate.Call

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The same reached main input supplies the complete current validator
context, including actual initialized Keccak pointers and physical row sizes. -/
theorem header_context {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array : BitVec 64} {start length boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (image : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 72 1024 256) :
    ∃ heap,Headers.CurrentValidate.Context source (VarList.decodedArray array length) heap
      (BitVec.ofNat 64 (VarList.decodedCount input start length)) 2701132160#64 2701132360#64
      (VarList.recordPointer input pointer start) (VarList.recordLength input start length (VarList.decodedCount input start length)) 2701134824 boundary := by
  have small : VarList.decodedCount input start length<2^64 := by have h:=image.countBound; omega
  have countNumber : (BitVec.ofNat 64 (VarList.decodedCount input start length)).toNat=VarList.decodedCount input start length := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have rows:=Headers.CurrentValidate.rows_from_image image data.arena.domain
  obtain ⟨heap,cell,lower,upper,aligned⟩:=data.heap
  refine ⟨heap,data.arena,data.keccak,?_,cell,?_,upper,aligned,(by omega),by decide,by decide,by decide,by decide,?_⟩
  · simpa only [countNumber] using rows
  · have low:=image.siLower
    have high:=image.siBefore
    omega
  · simpa only [countNumber] using image.lengths

/-- Any real run_attempt outcome either stops within the whole current
header allowance or reaches its actual after-header continuation with the
returned arrays and protected next physical context. -/
theorem header_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤51528323 ∨ ∃ array start length heap target nextHeap inner,
      Headers.CurrentValidate.Returned (bind source "pl" record) target (VarList.decodedArray array length) heap
        (BitVec.ofNat 64 (VarList.decodedCount input start length)) 2701132160#64 2701132360#64 nextHeap
        (VarList.recordPointer input pointer start) (VarList.recordLength input start length (VarList.decodedCount input start length)) 2701134824 boundary ∧
      (bind source "pl" record).globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry (bind source "pl" record) target "vh"
        (Headers.CurrentValidate.result heap (Headers.CurrentValidate.hashesPointer heap (BitVec.ofNat 64 (VarList.decodedCount input start length))))) afterHeaders=(outcome,inner) ∧
      post=restore source "pl" (restore (bind source "pl" record) "vh" inner) := by
  obtain ⟨headerPost,array,start,length,next,image,called,endpoint,args⟩:=header_reached data outcome run
  obtain ⟨heap,context⟩:=header_context next image
  rw [header_shapes.2.2] at called
  change evaluateHOLFiniteState (bind source "pl" record) (.decCall (ofString "vh") Headers.Validate.resultShape (ofString "validate_headers") headerArguments afterHeaders)=(outcome,headerPost) at called
  rcases Headers.CurrentValidate.scoped_trace (bind source "pl" record) headerPost (VarList.decodedArray array length) heap
    (BitVec.ofNat 64 (VarList.decodedCount input start length)) 2701132160#64 2701132360#64 (VarList.recordPointer input pointer start)
    (VarList.recordLength input start length (VarList.decodedCount input start length)) 2701134824 boundary context "vh" headerArguments afterHeaders args outcome called with stopped|reached
  · have clock : post.clock=headerPost.clock := by rw [endpoint]; rfl
    change source.clock-headerPost.clock≤51528323 at stopped
    exact Or.inl (by rw [clock]; exact stopped)
  · obtain ⟨target,nextHeap,inner,returned,continued,restored⟩:=reached
    exact Or.inr ⟨array,start,length,heap,target,nextHeap,inner,returned,context.heapCell,continued,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.header_context
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.header_trace
