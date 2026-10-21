import InitECandidate.Solver.Input.WitnessDecodeArrayEntry
import InitECandidate.Solver.Mpt.WitnessDecodePairNormal
import InitECandidate.Solver.Mpt.WitnessDecodeBranchView
import InitECandidate.Solver.Mpt.WitnessDecodeResult

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original decoder return at the real count decision follows
the actual two-item or17-item branch and derives its complete physical
output. The current heap and all row/input geometry come from the same
actual list snapshot and the original main-built databases. -/
theorem decode_array_result_normal (input : Guest.InputBlob)
    (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length array cursor limit header payload count : BitVec 64) (items : List Rlp.ListItem)
    (entry : DecodeSliceEntry input origin source db pointer length array cursor limit header payload count items)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (below : cursor.toNat≤2713717616) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Mpt.WitnessDecode.afterArray=(some (.returned value),post)) :
    Mpt.WitnessDecode.NormalFrame source post (PersistentAlloc.rounded array (count*16#64)) cursor limit ∧
      Mpt.WitnessDecode.NormalResult post db pointer length array cursor limit value := by
  let next:=PersistentAlloc.rounded array (count*16#64)
  have rows:=entry.rows input origin source db pointer length array cursor limit header payload count items
  have arrayFloor : 2713731432≤array.toNat:=by have lower:=entry.inputLower; have before:=entry.inputBeforeHeap; omega
  have beforeArray : array.toNat+16*items.length≤next.toNat:=by
    have growth : array.toNat+16*count.toNat≤next.toNat:=entry.snapshot.grows
    rwa [entry.snapshot.countExact] at growth
  have grows : array.toNat≤next.toNat:=by omega
  obtain ⟨codeArray,nodes,codes,heap,nodeData,codeData,nodeCell,heapCell,heapArena,heapAligned,nodeBefore,codeBefore⟩:=entry.boundary
  have nodeEq : nodes=db:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nodeCell.symm.trans entry.dbCell)))
  subst nodes
  have heapEq : heap=next:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (heapCell.symm.trans entry.snapshot.heapCell)))
  subst heap
  have dbBefore : db.toNat≤next.toNat:=by obtain ⟨capacity,cell,bound⟩:=nodeBefore; omega
  have payloadLower : pointer.toNat≤(pointer+header).toNat:=by rw [entry.pointerNumber]; omega
  have payloadUpper : (pointer+header).toNat+payload.toNat≤pointer.toNat+length.toNat:=by
    rw [entry.pointerNumber]
    have extent:=entry.extent
    omega
  rw [Mpt.WitnessDecode.array_choice source array count entry.sliceCell] at normal
  by_cases pair : count=2#64
  · rw [if_pos pair] at normal
    have countLength : items.length=2:=by rw [←entry.snapshot.countExact,pair]; rfl
    obtain ⟨frame,nibbleLength,result⟩:=Mpt.WitnessDecode.pair_normal source post db array pointer length (pointer+header) next cursor limit payload.toNat items rows countLength arrayCell entry.pointerCell entry.lengthCell
      entry.snapshot.heapCell entry.snapshot.nextArena entry.snapshot.nextAligned entry.snapshot.arena below arrayFloor beforeArray (arrayFloor.trans grows) dbBefore
      entry.lengthBound entry.inputLower entry.inputBeforeDb payloadLower payloadUpper entry.installed value normal
    refine ⟨frame,?_⟩
    rcases result with ⟨node,valuePointer,valueLength,valueEq,view,freshNode,scratch,finalHeap,finalCell,finalArena,finalAligned,nodeBefore⟩|
      ⟨finalHeap,valueEq,view,before,finalCell,finalArena,finalAligned,nextGrows,scratch,drop⟩
    · rw [valueEq]
      exact .leaf node next nibbleLength valuePointer valueLength finalHeap view grows (grows.trans freshNode) scratch finalCell finalArena finalAligned nodeBefore
    · rw [valueEq]
      exact .record (Mpt.WitnessDecode.extensionDescription array pointer length (pointer+header) payload.toNat items next nibbleLength) finalHeap view rfl rfl before
        (Nat.le_refl _) grows trivial trivial finalCell finalArena finalAligned scratch drop
  · rw [if_neg pair] at normal
    obtain ⟨valueEq,view,before,scratch,finalCell,finalArena,finalAligned,nodeBefore,drop⟩:=Mpt.WitnessDecode.branch_view_normal source post db array pointer length count (pointer+header) next cursor limit payload.toNat items rows entry.snapshot.countExact
      arrayCell entry.pointerCell entry.lengthCell entry.sliceCell entry.snapshot.heapCell entry.snapshot.nextArena entry.snapshot.nextAligned entry.snapshot.arena below arrayFloor beforeArray
      entry.lengthBound entry.inputLower entry.inputBeforeDb payloadLower payloadUpper entry.installed value normal
    obtain ⟨countEq,nodeArena,room,recordArena,scratch2,drop2,valueEq2,funding,postEq⟩:=Mpt.WitnessDecode.branch_normal source post array pointer length count next cursor limit
      arrayCell entry.pointerCell entry.lengthCell entry.sliceCell entry.snapshot.heapCell entry.snapshot.nextArena entry.snapshot.nextAligned entry.snapshot.arena entry.installed value normal
    have frame:=Mpt.WitnessDecode.branch_frame_of_post source post next cursor limit (Mpt.WitnessDecode.branchWords array pointer length next) nodeArena entry.snapshot.arena room scratch2 postEq
    have initial:=Mpt.WitnessDecode.branch_empty_normal source post array pointer length count next cursor limit
      arrayCell entry.pointerCell entry.lengthCell entry.sliceCell entry.snapshot.heapCell entry.snapshot.nextArena entry.snapshot.nextAligned entry.snapshot.arena
      (by omega) entry.installed value normal
    refine ⟨frame,?_⟩
    rw [valueEq]
    exact .record (Mpt.WitnessDecode.branchDescription array pointer length (pointer+header) payload.toNat items next) (PersistentAlloc.rounded next 176#64)
      view rfl rfl before (Nat.le_refl _) grows ⟨rfl,rfl⟩ initial finalCell finalArena finalAligned scratch drop

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.decode_array_result_normal
