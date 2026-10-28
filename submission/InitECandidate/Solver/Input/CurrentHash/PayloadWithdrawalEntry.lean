import InitECandidate.Solver.Input.CurrentHash.PayloadStateCalls

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def withdrawalCount (input : Guest.InputBlob) := ((Payload.offsetWords input 3).toNat-(Payload.offsetWords input 2).toNat)/44
def withdrawalPointer (input : Guest.InputBlob) (blob : BitVec 64) := blob+62#64+Payload.offsetWords input 2

theorem State.withdrawal_data {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) :
    eval source (fieldExpression 48)=some (.val (.word (withdrawalPointer input blob))) ∧
    eval source (fieldExpression 56)=some (.val (.word (BitVec.ofNat 64 (withdrawalCount input)))) ∧
    withdrawalCount input≤134217728 ∧ AllocatedBytes.Arena (withdrawalPointer input blob) (44*withdrawalCount input) := by
  obtain ⟨count,wd,countCell,p,n,countBound,exactBytes,wdArena,nEq,nBound,arena⟩ := remaining_regions data.decoded data.inputBound data.inputArena
  have number : count.toNat=withdrawalCount input := by unfold withdrawalCount; omega
  have pointerRead := data.field_read 48 (by decide) (by decide) _ wd
  have countRead := data.field_read 56 (by decide) (by decide) _ countCell
  have value : BitVec.ofNat 64 (withdrawalCount input)=count := by rw [←number]; simp
  exact ⟨pointerRead,by rw [value]; exact countRead,by omega,by simpa only [number,withdrawalPointer] using wdArena⟩

theorem roots_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (n : Nat)
    (count : source.locals.lookup (ofString name)=some (.val (.word (BitVec.ofNat 64 n)))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (rootsAllocationArguments name)=
      some (PersistentAlloc.values (BitVec.ofNat 64 (32*n+32))) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,rootsAllocationArguments,localVar,count,PersistentAlloc.values,valueIsWord,valueWord,
    wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,BitVec.ofNat_add,Nat.mul_comm]

theorem roots_amount_number (n : Nat) (bounded : n≤134217728) : (BitVec.ofNat 64 (32*n+32)).toNat=32*n+32 := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.withdrawal_data
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.roots_arguments_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.roots_amount_number
