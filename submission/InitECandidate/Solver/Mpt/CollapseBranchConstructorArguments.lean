import InitECandidate.Solver.Mpt.CollapseBranchSuffixProgram
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem constructor_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word tag))) :
    evaluateHOLFiniteState source afterConcat=if tag=1#64 then evaluateHOLFiniteState source (.call none (ofString "node_new_leaf") leafArguments)
      else evaluateHOLFiniteState source extensionTail := by
  have guard : evaluateHOLFiniteState source leafGuard=if tag=1#64 then evaluateHOLFiniteState source (.call none (ofString "node_new_leaf") leafArguments) else (none,source):=by
    rw [merge_shapes.2.2.2.2.1,evaluateHOLFiniteState_ite]
    by_cases selected : tag=1#64 <;> simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,selected,evaluateHOLFiniteState_skip]
  rw [merge_shapes.2.2.2.1]
  exact Input.sequence_choice source leafGuard (.call none (ofString "node_new_leaf") leafArguments) extensionTail (tag=1#64) guard (.tail_call _ _)

/-- The unchanged constructors compute their length directly from the
actual stored child field, rather than a new temporary local. -/
theorem joined_length_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid child) (active : child≠0#64)
    (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child))) :
    eval source joinedLength=some (.val (.word (1#64+wordAt source.memory (child+40#64)))) := by
  let path:=graph.path child member active tag
  have stored : source.memory (child+40#64)=.word (wordAt source.memory (child+40#64)):=by simp only [wordAt,path.sizeStored,MemoryBytes.wordBits]
  simp [eval,joinedLength,field,localVar,evalHOLExact,evalListHOLExact,toExact,childCell,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,path.sizeMapped,stored]

theorem extension_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child key : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=2#64)
    (keyCell : source.locals.lookup (ofString "cat")=some (.val (.word key)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child))) :
    graph.valid (wordAt source.memory (child+48#64)) ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) extensionArguments=
        some [.val (.word key),.val (.word (1#64+wordAt source.memory (child+40#64))),.val (.word (wordAt source.memory (child+48#64)))] := by
  classical
  let next:=graph.extension child member active tag
  have number : wordAt source.memory (child+48#64)=next.child:=by simp [wordAt,next.stored,MemoryBytes.wordBits]
  have childRead : eval source (field "child" 48#64)=some (.val (.word next.child)):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read source "child" child 48#64 next.child childCell next.mapped next.stored
  have lengthRead:=joined_length_read source child graph member active (Or.inr tag) childCell
  have keyRead : eval source (localVar "cat")=some (.val (.word key)):=by simp [eval,localVar,evalHOLExact,toExact,keyCell]
  simp only [eval] at childRead lengthRead keyRead
  rw [number]
  exact ⟨next.member,by simp only [extensionArguments,evalListHOLFinite,evalListHOLExact,keyRead,lengthRead,childRead]⟩

theorem leaf_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child key : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=1#64)
    (keyCell : source.locals.lookup (ofString "cat")=some (.val (.word key)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child))) :
    TrieWalk.Payload source.memaddrs (wordAt source.memory (child+48#64)) (wordAt source.memory (child+56#64)) limit ∧
      property (wordAt source.memory (child+48#64)) (wordAt source.memory (child+56#64)) ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) leafArguments=
        some [.val (.word key),.val (.word (1#64+wordAt source.memory (child+40#64))),.val (.word (wordAt source.memory (child+48#64))),.val (.word (wordAt source.memory (child+56#64)))] := by
  classical
  let data:=values.leaf child member active tag
  have pointer : wordAt source.memory (child+48#64)=data.pointer:=by simp [wordAt,data.pointerStored,MemoryBytes.wordBits]
  have size : wordAt source.memory (child+56#64)=data.length:=by simp [wordAt,data.lengthStored,MemoryBytes.wordBits]
  have pointerRead : eval source (field "child" 48#64)=some (.val (.word data.pointer)):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read source "child" child 48#64 data.pointer childCell data.pointerMapped data.pointerStored
  have sizeRead : eval source (field "child" 56#64)=some (.val (.word data.length)):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read source "child" child 56#64 data.length childCell data.lengthMapped data.lengthStored
  have lengthRead:=joined_length_read source child graph member active (Or.inl tag) childCell
  have keyRead : eval source (localVar "cat")=some (.val (.word key)):=by simp [eval,localVar,evalHOLExact,toExact,keyCell]
  simp only [eval] at pointerRead sizeRead lengthRead keyRead
  rw [pointer,size]
  exact ⟨data.payload,data.extra,by simp only [leafArguments,evalListHOLFinite,evalListHOLExact,keyRead,lengthRead,pointerRead,sizeRead]⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.constructor_dispatch
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.joined_length_read
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.extension_arguments
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.leaf_arguments
