import InitECandidate.Solver.Input.Scalar64

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem convert_nat (byte : BitVec 8) : (Framing.convert byte).toNat=byte.toNat := by
  simp only [Framing.convert,UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt byte.isLt

theorem heap_le32 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (start : Nat) (expression : ExpHOL 64)
    (heap : Blob.HeapInput source input pointer) (inside : start+4≤input.length%2^64)
    (addressRead : eval source expression=some (.val (.word (pointer+BitVec.ofNat 64 start)))) :
    eval source (le32 expression)=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input start)))) := by
  let bytes : Fin 4→UInt8:=fun index=>Framing.convert ((input[start+index.val]?).getD 0)
  have read:=le32_read source expression (pointer+BitVec.ofNat 64 start) bytes addressRead (by
    intro index
    have byte:=heap (start+index.val) (by have:=index.isLt; omega)
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using byte)
  have v0 : (0 : Fin 4).val=0 := rfl
  have v1 : (1 : Fin 4).val=1 := rfl
  have v2 : (2 : Fin 4).val=2 := rfl
  have v3 : (3 : Fin 4).val=3 := rfl
  simpa only [bytes,convert_nat,Guest.GasLimit.le32,Guest.GasLimit.byte,v0,v1,v2,v3,Nat.reduceAdd,Nat.add_zero] using read

theorem heap_le64 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (start : Nat) (expression : ExpHOL 64)
    (heap : Blob.HeapInput source input pointer) (inside : start+8≤input.length%2^64)
    (addressRead : eval source expression=some (.val (.word (pointer+BitVec.ofNat 64 start)))) :
    eval source (le64 expression)=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)))) := by
  let bytes : Fin 8→UInt8:=fun index=>Framing.convert ((input[start+index.val]?).getD 0)
  have read:=le64_read source expression (pointer+BitVec.ofNat 64 start) bytes addressRead (by
    intro index
    have byte:=heap (start+index.val) (by have:=index.isLt; omega)
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using byte)
  have v0 : (0 : Fin 8).val=0 := rfl
  have v1 : (1 : Fin 8).val=1 := rfl
  have v2 : (2 : Fin 8).val=2 := rfl
  have v3 : (3 : Fin 8).val=3 := rfl
  have v4 : (4 : Fin 8).val=4 := rfl
  have v5 : (5 : Fin 8).val=5 := rfl
  have v6 : (6 : Fin 8).val=6 := rfl
  have v7 : (7 : Fin 8).val=7 := rfl
  simpa only [bytes,convert_nat,Guest.GasLimit.le64,Guest.GasLimit.le32,Guest.GasLimit.byte,
    v0,v1,v2,v3,v4,v5,v6,v7,Nat.reduceAdd,Nat.add_zero,Nat.add_assoc] using read

/-- Actual LD_LE64 of the copied gas field satisfies the certificate's declared
limit once both actual container offset equalities have been established. -/
theorem gas_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (expression : ExpHOL 64)
    (heap : Blob.HeapInput source input pointer) (inside : 482≤input.length%2^64)
    (addressRead : eval source expression=some (.val (.word (pointer+474#64))))
    (request : Guest.GasLimit.le32 input 2=16) (payload : Guest.GasLimit.le32 input 18=44)
    (gas : Guest.GasLimit.declaredGasLimit input≤200000000) :
    ∃ value : BitVec 64,eval source (le64 expression)=some (.val (.word value)) ∧ value.toNat≤200000000 := by
  have read:=heap_le64 source input pointer 474 expression heap inside addressRead
  have bound : Guest.GasLimit.le64 input 474≤200000000 := by
    rw [←Framing.declared_gas_at_474 input request payload]
    exact gas
  refine ⟨_,read,?_⟩
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  exact bound

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.convert_nat
#print axioms InitECandidate.Solver.Input.Scalar.heap_le32
#print axioms InitECandidate.Solver.Input.Scalar.heap_le64
#print axioms InitECandidate.Solver.Input.Scalar.gas_read
