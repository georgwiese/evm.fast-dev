import InitECandidate.Solver.Input.VarList.RecordCells
import InitECandidate.Solver.WitnessRadix.AllocationArithmetic

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def nextCursor (array : BitVec 64) (count : Nat) : BitVec 64:=BitVec.ofNat 64 (array.toNat+16*count)

/-- Record arrays occupy an exact multiple of eight bytes, so the real
allocator's rounding adds no slack, including a zero-count array. -/
theorem nextCursor_geometry (array : BitVec 64) (count : Nat)
    (aligned : array.toNat%8=0) (room : array.toNat+16*count≤33806089496) :
    (nextCursor array count).toNat=array.toNat+16*count ∧ (nextCursor array count).toNat%8=0 ∧
      PersistentAlloc.rounded array (BitVec.ofNat 64 (16*count))=nextCursor array count := by
  have cursorNat : (nextCursor array count).toNat=array.toNat+16*count := by
    rw [nextCursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have amountNat : (BitVec.ofNat 64 (16*count)).toNat=16*count := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have roundedNat:=PersistentAlloc.rounded_nat array (BitVec.ofNat 64 (16*count)) (by rw [amountNat];omega)
  rw [amountNat] at roundedNat
  refine ⟨cursorNat,by rw [cursorNat];omega,?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [roundedNat,cursorNat]
  omega

/-- A real decoded-list control frame determines the actual next heap word.
Empty input keeps the cursor, while a nonempty decoder advances by 16*N. -/
theorem cursor_of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (array : BitVec 64) (start length : Nat)
    (countBound : decodedCount input start length≤length/4)
    (aligned : array.toNat%8=0) (room : array.toNat+4*length≤33806089496)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (control : BackingLayout.control target=BackingLayout.control
      (if length=0 then source else PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4))))) :
    target.globals.lookup (ofString "heap_ptr")=some (.val (.word (nextCursor array (decodedCount input start length)))) ∧
      (nextCursor array (decodedCount input start length)).toNat=array.toNat+16*decodedCount input start length ∧
      (nextCursor array (decodedCount input start length)).toNat%8=0 ∧
      array.toNat≤(nextCursor array (decodedCount input start length)).toNat ∧
      (nextCursor array (decodedCount input start length)).toNat≤array.toNat+4*length ∧
      (nextCursor array (decodedCount input start length)).toNat≤33806089496 := by
  have geometry:=nextCursor_geometry array (decodedCount input start length) aligned (by omega)
  refine ⟨?_,geometry.1,geometry.2.1,by rw [geometry.1];omega,by rw [geometry.1];omega,by rw [geometry.1];omega⟩
  by_cases empty : length=0
  · simp only [if_pos empty] at control
    have globals : target.globals=source.globals:=congrArg (fun state=>state.globals) control
    have zeroCount : decodedCount input start length=0:=by simp [decodedCount,empty]
    have unchanged : nextCursor array (decodedCount input start length)=array := by
      apply BitVec.eq_of_toNat_eq
      rw [geometry.1,zeroCount]
      omega
    rw [globals,unchanged]
    exact heap
  · simp only [if_neg empty] at control
    have globals:=congrArg (fun state=>state.globals) control
    change target.globals=source.globals.update _ at globals
    have countValue : decodedCount input start length=Guest.GasLimit.le32 input start/4:=by simp [decodedCount,empty]
    rw [globals]
    simp only [HolFiniteMapExact.lookup_update,FUPDATE,beq_self_eq_true,if_true]
    rw [←countValue,geometry.2.2]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.nextCursor_geometry
#print axioms InitECandidate.Solver.Input.VarList.cursor_of_control
