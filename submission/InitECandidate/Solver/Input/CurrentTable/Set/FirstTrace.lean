import InitECandidate.Solver.Input.CurrentTable.Set.FirstImage
import InitECandidate.Solver.Input.CurrentTable.Set.Locals
import InitECandidate.Solver.Input.CurrentTable.Set.Guards
import InitECandidate.Solver.Input.LocalFrameFields

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem empty_finish_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table leaf : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (leafCell : source.locals.lookup (ofString "nl") = some (.val (.word leaf))) :
    evaluateHOLFiniteState source emptyFinish =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (New.putField source table 56 leaf)) := by
  have store := New.store_field source table leaf 56 (localVar "nl") domain arena aligned (by decide) (by decide) tableCell
    (Request.local_word source "nl" leaf leafCell)
  change evaluateHOLFiniteState source (.store (.op .add [localVar "t",.const 56#64]) (localVar "nl")) = _ at store
  rw [guard_shapes.2.2.1,evaluateHOLFiniteState_seq_line780,store]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- The actual empty insertion either stops within its four call ticks or
returns zero with the full genuinely nonempty table image. -/
theorem empty_leaf_trace {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap pointer value : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop} (query : KeyBits.Key)
    (image : Image source table cap 0#64 next count valid bits left right keys ValueOf)
    (locals : Locals source table pointer value) (installed : OriginalCode.Installed source.code)
    (little : source.be = false) (aligned : pointer.toNat%8 = 0) (beforeTable : pointer.toNat+32 ≤ table.toNat)
    (bytes : FirstDiff.ByteView source pointer query) (validValue : ValueOf value)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source emptyLeafCall = (outcome,post)) :
    (source.clock-post.clock ≤ 4 ∧ ∀ returned,outcome ≠ some (.returned returned)) ∨
      (outcome = some (.returned (.val (.word 0#64))) ∧ source.clock-post.clock ≤ 4 ∧
        Image post table cap (BitVec.ofNat 64 next) 2 1 (fun node => node = BitVec.ofNat 64 next)
          (fun _ => 256) (fun _ => 0#64) (fun _ => 0#64) (fun _ => query) ValueOf ∧
        LocalEffects.erase post = LocalEffects.erase (firstState source table cap (BitVec.ofNat 64 next) pointer value)) := by
  have countZero := image.empty.mp rfl
  have nextOne : next = 1 := by have := image.nextLower; have := image.countNodes; omega
  have available : next ≤ cap.toNat := by have := image.capLower; omega
  let leaf := BitVec.ofNat 64 next
  have leafOne : leaf = 1#64 := by change BitVec.ofNat 64 next = 1#64; rw [nextOne]
  have ready := image.allocator_context available
  have fields : NewLeaf.Fields source table cap leaf 0#64 pointer query := by
    have derived := NewLeaf.fields_from_image query image available little aligned beforeTable bytes
    rw [countZero] at derived
    exact derived
  have args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) leafArguments =
      some [.val (.word table),.val (.word pointer),.val (.word value)] := by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,locals.tableCell,locals.keyCell,locals.valueCell]
  rw [guard_shapes.2.1] at run
  rcases NewLeaf.scoped_trace source post table cap leaf 0#64 pointer value query ready fields beforeTable installed
    "nl" leafArguments emptyFinish args outcome run with stopped | reached
  · exact Or.inl stopped
  · obtain ⟨target,inner,frame,forward,cost,continued,endpoint⟩ := reached
    let resumed := CallNormal.continuationEntry source target "nl" (.val (.word leaf))
    have physical : LocalEffects.erase resumed = LocalEffects.erase (NewLeaf.model source table cap leaf 0#64 pointer value) := frame
    have domain := LocalEffects.domain_of_erase _ _ physical
    rw [NewLeaf.model_domain] at domain
    have tableCell := (CallNormal.continuation_lookup_other source target "nl" "t" (.val (.word leaf)) (by decide)).trans locals.tableCell
    have finished := empty_finish_execute resumed table leaf (domain.trans image.domain) image.geometry.table image.aligned tableCell
      (CallNormal.continuation_lookup_same source target "nl" (.val (.word leaf)))
    rw [finished] at continued
    have answer := congrArg Prod.fst continued
    have innerEq := congrArg Prod.snd continued
    dsimp only at innerEq
    have finalFrame : LocalEffects.erase post = LocalEffects.erase (firstState source table cap leaf pointer value) := by
      rw [endpoint,←innerEq]
      exact header_frame _ _ table leaf 56 physical
    have price : source.clock-post.clock ≤ 4 := by
      rw [endpoint,←innerEq]
      exact cost
    exact Or.inr ⟨answer.symm,price,(first_image query leafOne image fields beforeTable validValue).of_frame finalFrame,finalFrame⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.empty_finish_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.empty_leaf_trace
