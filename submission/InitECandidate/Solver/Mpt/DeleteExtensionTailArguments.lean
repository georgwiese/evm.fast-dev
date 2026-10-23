import InitECandidate.Solver.Mpt.DeleteExtensionProgram
import InitECandidate.Solver.Mpt.TrieWalkValues
import InitECandidate.Solver.Input.SequenceChoice
import InitECandidate.Solver.Input.TailCallNoFallthrough

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (node offset word : BitVec 64)
    (cell : source.locals.lookup (ofString name)=some (.val (.word node)))
    (mapped : source.memaddrs (node+offset)) (stored : source.memory (node+offset)=.word word) :
    eval source (field name offset)=some (.val (.word word)) := by
  simp [eval,field,localVar,evalHOLExact,evalListHOLExact,toExact,cell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

theorem constructor_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word tag))) :
    evaluateHOLFiniteState source afterLength=if tag=2#64 then evaluateHOLFiniteState source (.call none (ofString "node_new_ext") extensionArguments)
      else evaluateHOLFiniteState source leafTail := by
  have read : evaluateHOLFiniteState source extensionGuard=if tag=2#64 then evaluateHOLFiniteState source (.call none (ofString "node_new_ext") extensionArguments) else (none,source):=by
    rw [merge_shapes.2.2.2.2.2.1,evaluateHOLFiniteState_ite]
    by_cases selected : tag=2#64 <;>
      simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,selected,evaluateHOLFiniteState_skip]
  rw [merge_shapes.2.2.2.2.1]
  exact Input.sequence_choice source extensionGuard (.call none (ofString "node_new_ext") extensionArguments) leafTail (tag=2#64) read (.tail_call _ _)

/-- The extension case uses the real registered grandchild. -/
theorem extension_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child key length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid child) (active : child≠0#64)
    (tag : wordAt source.memory child=2#64)
    (keyCell : source.locals.lookup (ofString "cat")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "cl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child))) :
    graph.valid (wordAt source.memory (child+48#64)) ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) extensionArguments=
        some [.val (.word key),.val (.word length),.val (.word (wordAt source.memory (child+48#64)))] := by
  classical
  let next:=graph.extension child member active tag
  have number : wordAt source.memory (child+48#64)=next.child:=by simp [wordAt,next.stored,MemoryBytes.wordBits]
  have childRead:=field_read source "nc" child 48#64 next.child childCell next.mapped next.stored
  simp only [eval] at childRead
  have keyRead : evalHOLExact source.toExact (localVar "cat")=some (.val (.word key)):=by simp [localVar,evalHOLExact,toExact,keyCell]
  have lengthRead : evalHOLExact source.toExact (localVar "cl")=some (.val (.word length)):=by simp [localVar,evalHOLExact,toExact,lengthCell]
  rw [number]
  exact ⟨next.member,by simp only [extensionArguments,evalListHOLFinite,evalListHOLExact,keyRead,lengthRead,childRead]⟩

/-- The leaf case uses its actual bounded registered value, including the
caller's retained value property. -/
theorem leaf_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child key length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=1#64)
    (keyCell : source.locals.lookup (ofString "cat")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "cl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child))) :
    TrieWalk.Payload source.memaddrs (wordAt source.memory (child+48#64)) (wordAt source.memory (child+56#64)) limit ∧
      property (wordAt source.memory (child+48#64)) (wordAt source.memory (child+56#64)) ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) leafArguments=
        some [.val (.word key),.val (.word length),.val (.word (wordAt source.memory (child+48#64))),.val (.word (wordAt source.memory (child+56#64)))] := by
  classical
  let data:=values.leaf child member active tag
  have pointer : wordAt source.memory (child+48#64)=data.pointer:=by simp [wordAt,data.pointerStored,MemoryBytes.wordBits]
  have size : wordAt source.memory (child+56#64)=data.length:=by simp [wordAt,data.lengthStored,MemoryBytes.wordBits]
  have pointerRead:=field_read source "nc" child 48#64 data.pointer childCell data.pointerMapped data.pointerStored
  have sizeRead:=field_read source "nc" child 56#64 data.length childCell data.lengthMapped data.lengthStored
  simp only [eval] at pointerRead sizeRead
  have keyRead : evalHOLExact source.toExact (localVar "cat")=some (.val (.word key)):=by simp [localVar,evalHOLExact,toExact,keyCell]
  have lengthRead : evalHOLExact source.toExact (localVar "cl")=some (.val (.word length)):=by simp [localVar,evalHOLExact,toExact,lengthCell]
  rw [pointer,size]
  exact ⟨data.payload,data.extra,by simp only [leafArguments,evalListHOLFinite,evalListHOLExact,keyRead,lengthRead,pointerRead,sizeRead]⟩

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.field_read
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.constructor_dispatch
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.extension_arguments
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.leaf_arguments
