import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.WitnessRadix.StateSteps
import InitECandidate.Solver.Rlp.SliceArrayModel

namespace InitECandidate.Solver.Mpt.CodeSlice
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual two-word representation stored in the original code cache. -/
structure Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (slice code : BitVec 64) (length : Nat) : Prop where
  arena : AllocatedBytes.Arena slice 16
  aligned : slice.toNat % 8 = 0
  codeArena : AllocatedBytes.Arena code length
  pointerStored : source.memory slice = .word code
  lengthStored : source.memory (slice + 8#64) = .word (BitVec.ofNat 64 length)

def stores : ProgHOL 64 := .seq (.store (localVar "sl") (localVar "code"))
  (.store (.op .add [localVar "sl",.const 8#64]) (localVar "code_len"))
def written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (slice code : BitVec 64) (length : Nat) :=
  {source with memory := StoreWord.put (StoreWord.put source.memory slice code) (slice + 8#64) (BitVec.ofNat 64 length)}

theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (slice code : BitVec 64) (length : Nat)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena slice 16) (aligned : slice.toNat % 8 = 0)
    (codeArena : AllocatedBytes.Arena code length)
    (sliceLocal : source.locals.lookup (ofString "sl") = some (.val (.word slice)))
    (codeLocal : source.locals.lookup (ofString "code") = some (.val (.word code)))
    (lengthLocal : source.locals.lookup (ofString "code_len") = some (.val (.word (BitVec.ofNat 64 length)))) :
    evaluateHOLFiniteState source stores = (none,written source slice code length) ∧ Image (written source slice code length) slice code length ∧
      Rlp.Slices.Window source (written source slice code length) slice.toNat (slice.toNat + 16) := by
  have sliceRead : eval source (localVar "sl") = some (.val (.word slice)) := by simp [eval,localVar,evalHOLExact,toExact,sliceLocal]
  have codeRead : eval source (localVar "code") = some (.val (.word code)) := by simp [eval,localVar,evalHOLExact,toExact,codeLocal]
  have first := StoreWord.execute source (localVar "sl") (localVar "code") slice code sliceRead codeRead
    (by simpa [byteAddress] using AllocatedBytes.word_mapped source slice 16 0 domain arena (by decide) aligned (by decide))
  let middle := {source with memory := StoreWord.put source.memory slice code}
  have nextSlice : eval middle (.op .add [localVar "sl",.const 8#64]) = some (.val (.word (slice + 8#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,show middle.locals = source.locals from rfl,sliceLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  have nextLength : eval middle (localVar "code_len") = some (.val (.word (BitVec.ofNat 64 length))) := by
    simp [eval,localVar,evalHOLExact,toExact,show middle.locals = source.locals from rfl,lengthLocal]
  have last := StoreWord.execute middle _ _ (slice + 8#64) (BitVec.ofNat 64 length) nextSlice nextLength
    (AllocatedBytes.word_mapped source slice 16 8 domain arena (by decide) aligned (by decide))
  have number : (slice + 8#64).toNat = slice.toNat + 8 := byteAddress_toNat slice 8 (by have := arena.upper; omega)
  have different : slice ≠ slice + 8#64 := by intro same; have := congrArg BitVec.toNat same; omega
  refine ⟨?_,⟨arena,aligned,codeArena,?_,?_⟩,?_⟩
  · rw [stores,StateSteps.next_sequence source middle _ _ first (Nat.le_refl _)]
    exact last
  · simp [written,StoreWord.put,different]
  · simp [written,StoreWord.put]
  · intro query away
    have firstAway : query ≠ slice := by intro same; subst query; rcases away with before | after <;> omega
    have lastAway : query ≠ slice + 8#64 := by intro same; rw [same,number] at away; rcases away with before | after <;> omega
    simp [written,StoreWord.put,firstAway,lastAway]

theorem Image.of_agreement (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (slice code : BitVec 64) (length : Nat)
    (image : Image source slice code length)
    (pointer : post.memory slice = source.memory slice)
    (size : post.memory (slice + 8#64) = source.memory (slice + 8#64)) : Image post slice code length :=
  ⟨image.arena,image.aligned,image.codeArena,pointer.trans image.pointerStored,size.trans image.lengthStored⟩

end InitECandidate.Solver.Mpt.CodeSlice

#print axioms InitECandidate.Solver.Mpt.CodeSlice.stores_execute
#print axioms InitECandidate.Solver.Mpt.CodeSlice.Image.of_agreement
