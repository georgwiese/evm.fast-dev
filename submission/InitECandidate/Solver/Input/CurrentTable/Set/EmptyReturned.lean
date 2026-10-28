import InitECandidate.Solver.Input.CurrentTable.Set.EmptyCost
import InitECandidate.Solver.Input.CurrentTable.Set.Result
import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Memory
import InitECandidate.Solver.Input.CurrentTable.EarlierWrites

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem empty_leaf_returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap pointer value : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop} (query : KeyBits.Key)
    (image : Image source table cap 0#64 next count valid bits left right keys ValueOf)
    (locals : Locals source table pointer value) (installed : OriginalCode.Installed source.code)
    (little : source.be = false) (aligned : pointer.toNat%8 = 0) (beforeTable : pointer.toNat+32 ≤ table.toNat)
    (view : FirstDiff.ByteView source pointer query) (valueMember : ValueOf value)
    (answer : ValueHOL 64) (normal : evaluateHOLFiniteState source emptyLeafCall = (some (.returned answer),post)) :
    answer = .val (.word 0#64) ∧ Result source post table cap count ValueOf := by
  rcases empty_leaf_trace query image locals installed little aligned beforeTable view valueMember (some (.returned answer)) normal with stopped | returned
  · exact (stopped.2 answer rfl).elim
  · obtain ⟨returned,cost,returnedImage,frame⟩ := returned
    have zero : answer = .val (.word 0#64) := by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using returned
    have metadata : MemoryMetadata.erase (firstState source table cap (BitVec.ofNat 64 next) pointer value) = MemoryMetadata.erase source := by
      rw [firstState,header_metadata,NewLeaf.model_metadata]
    refine ⟨zero,⟨⟨_,2,1,_,_,_,_,_,returnedImage,by omega⟩,(MemoryMetadata.of_frame frame).trans metadata,?_⟩⟩
    intro address before
    rw [LocalEffects.memory_of_erase _ _ frame,firstState,header_before _ table _ address 56 image.geometry.table (by decide) before]
    have countZero := image.empty.mp rfl
    have nextOne : next = 1 := by have := image.nextLower; have := image.countNodes; omega
    have inside : (BitVec.ofNat 64 next).toNat ≤ cap.toNat := by
      rw [nextOne]
      have := image.capLower
      change 1 ≤ cap.toNat
      omega
    exact NewLeaf.memory_before source table cap (BitVec.ofNat 64 next) 0#64 pointer value address image.geometry inside (by change 0 ≤ cap.toNat; omega) before

theorem empty_after_leaf_returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap pointer value : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop} (query : KeyBits.Key)
    (image : Image source table cap 0#64 next count valid bits left right keys ValueOf)
    (locals : Locals source table pointer value) (leafCell : source.locals.lookup (ofString "leaf") = some (.val (.word 0#64)))
    (installed : OriginalCode.Installed source.code) (little : source.be = false) (aligned : pointer.toNat%8 = 0)
    (beforeTable : pointer.toNat+32 ≤ table.toNat) (view : FirstDiff.ByteView source pointer query) (valueMember : ValueOf value)
    (answer : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLeaf = (some (.returned answer),post)) :
    answer = .val (.word 0#64) ∧ Result source post table cap count ValueOf := by
  let selected := keysEntry source table
  have data : Locals selected table pointer value := locals.with_local "keys" _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have currentImage : Image selected table cap 0#64 next count valid bits left right keys ValueOf := image.of_frame rfl
  have currentLeaf : selected.locals.lookup (ofString "leaf") = some (.val (.word 0#64)) :=
    (bind_lookup_other _ "keys" "leaf" _ (by decide)).trans leafCell
  rw [keys_setup image locals.tableCell] at normal
  change (let output := evaluateHOLFiniteState selected afterKeys;(output.1,restore source "keys" output.2)) = _ at normal
  rw [after_keys_empty selected currentLeaf] at normal
  let output := evaluateHOLFiniteState selected emptyLeafCall
  have observed := congrArg Prod.fst normal
  have endpoint := congrArg Prod.snd normal
  change restore source "keys" output.2 = post at endpoint
  have run : evaluateHOLFiniteState selected emptyLeafCall = (some (.returned answer),output.2) := Prod.ext observed rfl
  obtain ⟨zero,result⟩ := empty_leaf_returned query currentImage data installed little aligned beforeTable (view.of_frame rfl) valueMember answer run
  exact ⟨zero,result.of_frames rfl (by rw [←endpoint]; rfl)⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.empty_leaf_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.empty_after_leaf_returned
