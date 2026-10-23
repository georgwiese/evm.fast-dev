import InitECandidate.Solver.Input.WitnessDecodeArrayNormal
import InitECandidate.Solver.Input.WitnessDecodeArrayNibblesNormal

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete normal contract for unchanged original237. The genuine
caught parser, actual list allocation/count decision and all original
scopes yield a fresh physical leaf/record or the literal empty result.
Every allocation, heap/scratch frame and record decrease is derived. -/
theorem decode_body_nibbles_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputLower : 2713731432≤pointer.toNat) (below : cursor.toNat≤2713717616) (little : source.be=false)
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (Mpt.WitnessStep.body .decode)=(some (.returned value),post)) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 0 ∧ heap.toNat%8=0 ∧ Mpt.WitnessDecode.NormalFrame source post heap cursor limit ∧
      Mpt.WitnessDecode.NibbleResult post db pointer length heap cursor limit value := by
  have originalBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,heap,nodeData,codeData,nodeCell,heapCell,heapArena,heapAligned,nodeBefore,codeBefore⟩:=boundary
  rcases decode_array_normal input source post db pointer length cursor limit originalBoundary dbCell pointerCell lengthCell arena before small inputLower below installed value normal with empty|reached
  · obtain ⟨valueEq,scratch,above,globals⟩:=empty
    have fields:=Input.evaluation_fields source post (Mpt.WitnessStep.body .decode) (some (.returned value)) normal
    have frame : Mpt.WitnessDecode.NormalFrame source post heap cursor limit:=
      ⟨⟨heap,(globals _).trans heapCell,heapArena,heapAligned,Nat.le_refl _⟩,⟨cursor,scratch,Nat.le_refl _⟩,
        fields.1,fields.2.1,fields.2.2.2,fun key _ _=>globals key,fun query lower upper=>above query lower⟩
    refine ⟨heap,heapCell,heapArena,heapAligned,frame,?_⟩
    rw [valueEq]
    exact .empty scratch
  · obtain ⟨origin,current,header,payload,arrayHeap,count,items,inner,entry,originAbove,originGlobals,originDomain,originEndian,originCode,continued,endpoint⟩:=reached
    let ready:=QueryBranch.bind current "arr" arrayHeap
    have sameHeap : arrayHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (entry.sourceHeap.symm.trans ((originGlobals _).trans heapCell))))
    subst arrayHeap
    have readyLittle : ready.be=false:=entry.snapshot.endian.trans (originEndian.trans little)
    obtain ⟨arrayFrame,result⟩:=decode_array_nibbles_normal input origin ready inner db pointer length heap cursor limit header payload count items entry (bind_lookup_same _ _ _) below readyLittle value continued
    have slicesFrame : Mpt.WitnessDecode.NormalFrame origin ready heap cursor limit:=
      (Mpt.WitnessDecode.slices_snapshot_frame (LocalEffects.erase origin) ready (pointer+header) payload heap cursor limit count items entry.snapshot).prefix
        origin (LocalEffects.erase origin) ready heap cursor limit rfl rfl rfl (fun _=>rfl) (fun _ _=>rfl)
    have prefixFrame:=slicesFrame.prefix source origin ready heap cursor limit originDomain originEndian originCode originGlobals originAbove
    have grows : heap.toNat≤(PersistentAlloc.rounded heap (count*16#64)).toNat:=by
      have allocated:=entry.snapshot.grows
      omega
    have frame : Mpt.WitnessDecode.NormalFrame source post heap cursor limit:=
      (prefixFrame.compose source ready inner heap cursor (PersistentAlloc.rounded heap (count*16#64)) cursor limit arrayFrame grows (Nat.le_refl _)).of_erase
        source post inner heap cursor limit (by rw [endpoint]; rfl)
    have finalResult : Mpt.WitnessDecode.NibbleResult post db pointer length heap cursor limit value:=by
      apply result.of_fields inner post db pointer length heap cursor limit value
      · rw [endpoint]; rfl
      · rw [endpoint]; rfl
      · rw [endpoint]; rfl
      · rw [endpoint]; rfl
    exact ⟨heap,heapCell,heapArena,heapAligned,frame,finalResult⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.decode_body_nibbles_normal
