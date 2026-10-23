import InitECandidate.Solver.Mpt.CompactToNibblesNibbles
import InitECandidate.Solver.Mpt.CompactToNibblesSnapshotNormal

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

private theorem output_count_unique (pointer : BitVec 64) (left right : Nat) (leftLeaf rightLeaf : BitVec 64)
    (leftSmall : left<2^64) (rightSmall : right<2^64)
    (same : output pointer left leftLeaf=output pointer right rightLeaf) : left=right ∧ leftLeaf=rightLeaf := by
  have equal : BitVec.ofNat 64 left=BitVec.ofNat 64 right ∧ leftLeaf=rightLeaf:=by
    simpa only [output,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,true_and,and_true] using same
  have numbers:=congrArg BitVec.toNat equal.1
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt leftSmall,BitVec.toNat_ofNat,Nat.mod_eq_of_lt rightSmall] at numbers
  exact ⟨numbers,equal.2⟩

/-- Join the existing real allocation/scratch snapshot and the new byte
range proof at the same original child execution and same returned tuple. -/
theorem body_snapshot_nibbles (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap cursor limit : BitVec 64) (length : Nat) (bounded : length≤1024)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (inputArena : AllocatedBytes.Arena pointer length)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ nibbles leaf,value=output heap nibbles leaf ∧ Snapshot source target length heap cursor limit nibbles leaf ∧
      KeyToNibbles.NibblePrefix target heap nibbles := by
  obtain ⟨nibbles,leaf,answer,snapshot⟩:=body_snapshot source target pointer heap cursor limit length bounded pointerCell lengthCell heapCell heapArena aligned arena installed value normal
  obtain ⟨positive,outputArena,actualNibbles,actualLeaf,nibbleBound,binary,valueEq,nibblesValid⟩:=body_nibbles source target pointer heap length bounded domain little
    pointerCell lengthCell inputArena heapCell heapArena installed value normal
  have same:=output_count_unique heap nibbles actualNibbles leaf actualLeaf (by have bound:=snapshot.nibbleBound; omega) (by omega) (answer.symm.trans valueEq)
  rcases same with ⟨sameNibbles,sameLeaf⟩
  subst actualNibbles
  subst actualLeaf
  exact ⟨nibbles,leaf,answer,snapshot,nibblesValid⟩

/-- A true normal scoped compact call supplies both the physical snapshot
and actual path-byte nibble range at its genuine resumed continuation. -/
theorem normal_snapshot_nibbles_call (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap cursor limit : BitVec 64) (length : Nat) (bounded : length≤1024)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))])
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false) (inputArena : AllocatedBytes.Arena pointer length)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "compact_to_nibbles") arguments continuation)=(some (.returned value),post)) :
    1≤source.clock ∧ ∃ child nibbles leaf inner,
      Snapshot source (Input.CallNormal.continuationEntry source child name (output heap nibbles leaf)) length heap cursor limit nibbles leaf ∧
      KeyToNibbles.NibblePrefix (Input.CallNormal.continuationEntry source child name (output heap nibbles leaf)) heap nibbles ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source child name (output heap nibbles leaf)) continuation=(some (.returned value),inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,pointerCell,lengthCell⟩:=Input.word_pair_environment source.code.lookup (ofString "compact_to_nibbles")
    (ofString "p") (ofString "n") body resultShape pointer (BitVec.ofNat 64 length) (by decide) (original_code source.code installed)
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post name resultShape (ofString "compact_to_nibbles") arguments _ body continuation callee resultShape args called value normal
  have entryArena:=Rlp.Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  obtain ⟨nibbles,leaf,valueEq,snapshot,nibblesValid⟩:=body_snapshot_nibbles (callEntryStateHOLFinite source callee) child pointer heap cursor limit length bounded domain little
    pointerCell lengthCell inputArena heapCell heapArena aligned entryArena installed returned run
  rw [valueEq] at continued
  exact ⟨funded,child,nibbles,leaf,inner,(snapshot.from_call_entry source child callee length heap cursor limit nibbles leaf).resumed source child length heap cursor limit nibbles leaf name,
    nibblesValid,continued,endpoint⟩

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.body_snapshot_nibbles
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.normal_snapshot_nibbles_call
