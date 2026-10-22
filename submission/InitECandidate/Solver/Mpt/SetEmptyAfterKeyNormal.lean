import InitECandidate.Solver.Mpt.SetRootStore
import InitECandidate.Solver.Mpt.InsertEmptyCall
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Compose the genuine root declaration, assigned insertion and final
store/return. The actual ending state contains the new physical leaf and
its live heap; lexical restoration does not discard its graph or values. -/
theorem after_key_empty_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m heap key length pointer size : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m))) (rootMapped : source.memaddrs m) (emptyRoot : source.memory m=.word 0#64)
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))) (pointerActive : pointer≠0#64) (sizeActive : size≠0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (older : m.toNat<heap.toNat)
    (fits : key.toNat+min length.toNat 64<2^64)
    (mapped : ∀ offset<min length.toNat 64,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterKey=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ target.memory m=.word heap ∧ source.clock-target.clock≤4 ∧
      target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      AllocatedBytes.Arena heap 64 ∧ AllocatedBytes.Arena (PersistentAlloc.rounded heap 64#64) 0 ∧
      (PersistentAlloc.rounded heap 64#64).toNat%8=0 ∧ heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat ∧
      ∃ graph : TrieWalk.Graph target.memory target.memaddrs,
        (∀ node,graph.valid node ↔ node=0#64 ∨ node=heap) ∧ graph.valid heap ∧
        graph.Regions heap.toNat (PersistentAlloc.rounded heap 64#64).toNat ∧ graph.Disjoint ∧ Nonempty (TrieWalk.Values graph limit property) := by
  have rootRead : eval source rootExpression=some (.val (.word 0#64)):=by
    simp [eval,rootExpression,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,mCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,rootMapped,emptyRoot]
  rw [mutation_shapes.1] at normal
  obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=Input.CallNormal.declaration_normal_entry source target "root" .one rootExpression afterRoot value normal
  have declaredEq : declared=.val (.word 0#64):=Option.some.inj (read.symm.trans rootRead)
  subst declared
  let ready:=bind source "root" 0#64
  have saved (name : String) (different : ofString "root"≠ofString name) : ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    bind_lookup_other source "root" name 0#64 different
  have readyPointer:=(saved "vptr" (by decide)).trans pointerCell
  have readySize:=(saved "vlen" (by decide)).trans sizeCell
  have chosen:=insert_selected ready pointer size readyPointer readySize pointerActive sizeActive
  have insertSafe : Input.LocalPrefix (ofString "m") insertCall:=
    Input.LocalPrefix.call (key:=ofString "m") (some (ofString "root")) _ _ (by intro name same; have equal:=Option.some.inj same; subst name; decide)
  rw [mutation_shapes.2.1] at continued
  obtain ⟨assigned,choiceRun,footerRun⟩:=Input.sequence_returned ready inner mutationChoice footer value
    (by intro returned; rw [chosen]; exact (insertSafe.summary_full ready).2.1 returned) continued
  have insertRun : evaluateHOLFiniteState ready insertCall=(none,assigned):=chosen.symm.trans choiceRun
  have rootCell : ready.locals.lookup (ofString "root")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) insertArguments=
      some (Insert.values 0#64 key length 0#64 pointer size):=by
    simp [insertArguments,Insert.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,rootCell,
      (saved "nk" (by decide)).trans nkCell,readyPointer,readySize]
  obtain ⟨arena,newRoot,cost,globals,nextArena,nextAligned,before,graph,valid,member,regions,disjoint,values⟩:=
    Insert.empty_assigned_graph ready assigned heap key length pointer size (ofString "root") insertArguments args installed domain heapCell frontier aligned
      fits mapped limit property payload extra insertRun
  have mPreserved:=insertSafe.summary_full ready
  unfold Input.LocalSummary at mPreserved
  rw [insertRun] at mPreserved
  have assignedM : assigned.locals.lookup (ofString "m")=some (.val (.word m)):=
    (mPreserved.1 rfl).trans ((saved "m" (by decide)).trans mCell)
  have fields:=Input.evaluation_fields ready assigned mutationChoice none choiceRun
  have assignedMapped : assigned.memaddrs m:=by rw [fields.1]; exact rootMapped
  obtain ⟨executed,stored,next,validEq,nextRegions,nextDisjoint,nextValues⟩:=
    footer_graph assigned m heap assignedM newRoot assignedMapped graph limit heap.toNat (PersistentAlloc.rounded heap 64#64).toNat property
      (Classical.choice values) regions disjoint older
  have same:=executed.symm.trans footerRun
  have valueEq : value=.val (.word 0#64):=by
    have equal:=congrArg Prod.fst same
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using equal.symm
  have innerEq:=congrArg Prod.snd same
  change emptyLocalsHOLFinite (rootStored assigned m heap)=inner at innerEq
  have targetClock : target.clock=assigned.clock:=by rw [endpoint,←innerEq]; rfl
  refine ⟨valueEq,?_,?_,?_,arena,nextArena,nextAligned,before,?_⟩
  · rw [endpoint,←innerEq]
    exact stored
  · rw [targetClock]
    exact cost
  · rw [endpoint,←innerEq]
    exact globals
  · rw [endpoint,←innerEq]
    refine ⟨next,?_,?_,nextRegions,nextDisjoint,nextValues⟩
    · intro node
      rw [validEq]
      exact valid node
    · rw [validEq]
      exact member

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.after_key_empty_normal
