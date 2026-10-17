import InitECandidate.Solver.Input.Witness.StoredListNormal
import InitECandidate.Solver.Input.VarList.RecordsIntervalFrame

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

structure Environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one)
  failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one)
  exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one
  varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape)
  code : source.code.lookup (ofString "decode_bytes_list")=some (BytesList.formals,BytesList.body,VarList.returnShape)

theorem Environment.after_list (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array amount : BitVec 64)
    (empty : Prop) [Decidable empty]
    (control : BackingLayout.control target=BackingLayout.control (if empty then source else PersistentAlloc.post source array amount))
    (environment : Environment source) : Environment target := by
  obtain ⟨domain,codes,shapes⟩:=allocation_control_fields source target array amount empty control
  refine ⟨domain.trans environment.domain,?_,?_,?_,?_,?_⟩
  · rw [codes];exact environment.allocCode
  · rw [codes];exact environment.failCode
  · rw [shapes];exact environment.exceptionShape
  · rw [codes];exact environment.varCode
  · rw [codes];exact environment.code

theorem local_after_tuple (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name other : String)
    (tuple value : ValueHOL 64) (different : ofString name≠ofString other)
    (locals : target.locals=source.locals.update (ofString name,tuple))
    (saved : source.locals.lookup (ofString other)=some value) : target.locals.lookup (ofString other)=some value := by
  rw [locals]
  simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString name==ofString other)=false from beq_eq_false_iff_ne.mpr different] using saved

/-- Retain an earlier decoded array through a later decoder and its SI stores.
Only the actual old record interval needs a memory frame. -/
theorem records_through_list (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer array si : BitVec 64) (start length boundary offset : Nat)
    (records : VarList.Records source input pointer array start length)
    (before : array.toNat+16*VarList.decodedCount input start length≤boundary)
    (siArena : Arena si 96) (siBefore : si.toNat+96≤array.toNat) (inside : offset+16≤96)
    (frame : ∀ query,query.toNat<boundary → query≠byteAddress si offset → query≠byteAddress si (offset+8) → target.memory query=source.memory query) :
    VarList.Records target input pointer array start length := by
  apply VarList.Records.of_interval source target input pointer array start length boundary records before
  intro query lower upper
  have firstNumber:=byteAddress_toNat si offset (by have:=siArena.upper;omega)
  have secondNumber:=byteAddress_toNat si (offset+8) (by have:=siArena.upper;omega)
  exact frame query upper (by intro equal;have:=congrArg BitVec.toNat equal;omega)
    (by intro equal;have:=congrArg BitVec.toNat equal;omega)

/-- Other SI fields survive a later list's two field stores and fresh array. -/
theorem field_through_list (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (si : BitVec 64) (boundary oldOffset newOffset : Nat) (value : HolWordLab 64)
    (siArena : Arena si 96) (siBefore : si.toNat+96≤boundary)
    (oldInside : oldOffset<96) (newInside : newOffset+16≤96)
    (different : oldOffset≠newOffset ∧ oldOffset≠newOffset+8)
    (stored : source.memory (byteAddress si oldOffset)=value)
    (frame : ∀ query,query.toNat<boundary → query≠byteAddress si newOffset → query≠byteAddress si (newOffset+8) → target.memory query=source.memory query) :
    target.memory (byteAddress si oldOffset)=value := by
  have oldNumber:=byteAddress_toNat si oldOffset (by have:=siArena.upper;omega)
  exact (frame _ (by rw [oldNumber];omega)
    (byteAddress_ne si oldOffset newOffset (by have:=siArena.upper;omega) (by have:=siArena.upper;omega) different.1)
    (byteAddress_ne si oldOffset (newOffset+8) (by have:=siArena.upper;omega) (by have:=siArena.upper;omega) different.2)).trans stored

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.Environment.after_list
#print axioms InitECandidate.Solver.Input.Witness.local_after_tuple
#print axioms InitECandidate.Solver.Input.Witness.records_through_list
#print axioms InitECandidate.Solver.Input.Witness.field_through_list
