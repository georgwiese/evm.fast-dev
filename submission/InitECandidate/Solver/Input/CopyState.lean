import InitECandidate.Solver.Input.CopyStep

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem wordPost_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer index : BitVec 64)
    (name : MlS) (notIndex : ofString "i"≠name) (notWord : ofString "w"≠name) :
    (wordPost source pointer index).locals.lookup name=source.locals.lookup name := by
  simp [wordPost,SharedRead.post,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notIndex,notWord]

theorem wordPost_index (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer index : BitVec 64) :
    (wordPost source pointer index).locals.lookup (ofString "i")=some (.val (.word (index+8#64))) :=
  bind_lookup_same _ _ _

theorem wordPost_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer index : BitVec 64) :
    (wordPost source pointer index).locals.lookup (ofString "w")=
      some (.val (.word (Guest.wordOfLeBytes (SharedRead.bytes source.ffi.ffiState (Guest.inputDataAddr+index))))) := by
  exact (bind_lookup_other _ "i" "w" _ (by decide)).trans (bind_lookup_same _ _ _)

/-- Shared reads append their real event while preserving the actual host
memory and oracle. Ordinary writes leave all address domains unchanged. -/
theorem wordPost_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer index : BitVec 64) :
    (wordPost source pointer index).clock=source.clock ∧
    (wordPost source pointer index).memaddrs=source.memaddrs ∧
    (wordPost source pointer index).shMemaddrs=source.shMemaddrs ∧
    (wordPost source pointer index).ffi.ffiState=source.ffi.ffiState ∧
    (wordPost source pointer index).ffi.oracle=source.ffi.oracle := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem copy_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index length : Nat)
    (indexSmall : index<2^64) (lengthSmall : length<2^64)
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source copyCondition=some (.val (.word (if index<length then 1#64 else 0#64))) := by
  classical
  simp [eval,copyCondition,localVar,evalHOLExact,toExact,indexLocal,lengthLocal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.toNat_ofNat,Nat.mod_eq_of_lt indexSmall,Nat.mod_eq_of_lt lengthSmall]

noncomputable def walk (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) : Nat → PanSemStateFiniteExact 64 Guest.HostMemory
  | 0 => source
  | rounds+1 => walk (wordPost (decClockHOLFinite source) pointer (BitVec.ofNat 64 index)) pointer (index+8) rounds

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.wordPost_other
#print axioms InitECandidate.Solver.Input.Blob.wordPost_index
#print axioms InitECandidate.Solver.Input.Blob.wordPost_word
#print axioms InitECandidate.Solver.Input.Blob.wordPost_frame
#print axioms InitECandidate.Solver.Input.Blob.copy_test
