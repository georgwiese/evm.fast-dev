import InitECandidate.Solver.Mpt.SetProgram
import InitECandidate.Solver.Mpt.InsertEnvironment

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def rootExpression : ExpHOL 64:=.load .one (addConst (localVar "m") 0#64)
def afterRoot : ProgHOL 64:=match afterKey with | .dec _ _ _ rest=>rest | _=>.skip
def mutationChoice : ProgHOL 64:=match afterRoot with | .seq first _=>first | _=>.skip
def footer : ProgHOL 64:=match afterRoot with | .seq _ rest=>rest | _=>.skip
def deletionTest : ExpHOL 64:=.cmp .notEqual (.const 0#64) (.op .or
  [.cmp .equal (localVar "vptr") (.const 0#64),.cmp .equal (localVar "vlen") (.const 0#64)])
def deletionCall : ProgHOL 64:=match mutationChoice with | .ite _ yes _=>yes | _=>.skip
def insertArguments : List (ExpHOL 64):=[localVar "root",.rfield 0 (localVar "nk"),.rfield 1 (localVar "nk"),
  .const 0#64,localVar "vptr",localVar "vlen"]
def insertCall : ProgHOL 64:=.call (some (some (.local,ofString "root"),none)) (ofString "_mpt_insert_node") insertArguments

set_option maxRecDepth 100000 in
theorem mutation_shapes : afterKey=.dec (ofString "root") .one rootExpression afterRoot ∧
    afterRoot=.seq mutationChoice footer ∧ mutationChoice=.ite deletionTest deletionCall insertCall ∧
    footer=.seq (.store (addConst (localVar "m") 0#64) (localVar "root")) (.return (.const 0#64)) := by
  simp only [afterRoot,mutationChoice,footer,deletionTest,deletionCall,insertArguments,insertCall,afterKey,body,rootExpression,
    Guest.guestFn_mpt_set,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar,addConst]
  simp

theorem footer_quiet (code) : Input.QuietClock.Preserves code footer:=by
  rw [mutation_shapes.2.2.2]
  exact Input.QuietClock.sequence code _ _ (Input.QuietClock.store code _ _) (Input.QuietClock.returned code _)

/-- Nonzero current payload words select insertion in the original setter. -/
theorem insert_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer size : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))) (pointerActive : pointer≠0#64) (sizeActive : size≠0#64) :
    evaluateHOLFiniteState source mutationChoice=evaluateHOLFiniteState source insertCall := by
  have observed : eval source deletionTest=some (.val (.word 0#64)):=by
    simp [eval,deletionTest,localVar,evalHOLExact,evalListHOLExact,toExact,pointerCell,sizeCell,pointerActive,sizeActive,
      valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> decide
  simp only [eval] at observed
  rw [mutation_shapes.2.2.1,evaluateHOLFiniteState_ite,observed]
  rfl

theorem after_root_empty_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length pointer size : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word 0#64)))
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))) (pointerActive : pointer≠0#64) (sizeActive : size≠0#64) :
    source.clock-(evaluateHOLFiniteState source afterRoot).2.clock≤5 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) insertArguments=
      some (Insert.values 0#64 key length 0#64 pointer size):=by
    simp [insertArguments,Insert.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,rootCell,nkCell,pointerCell,sizeCell]
  have price:=Insert.empty_call_cost source key length 0#64 pointer size (some (some (ofString "root"))) insertArguments args installed
  rw [mutation_shapes.2.1]
  exact Input.ClockCost.sequence_current source mutationChoice footer 5 0
    (by rw [insert_selected source pointer size pointerCell sizeCell pointerActive sizeActive]; exact price)
    (Input.ClockCost.of_quiet source.code footer (footer_quiet source.code))

/-- The actual post-key setter suffix, including its root load and final
root store, costs at most five ticks for a current empty root. -/
theorem after_key_empty_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m key length pointer size : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m))) (mapped : source.memaddrs m) (stored : source.memory m=.word 0#64)
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))) (pointerActive : pointer≠0#64) (sizeActive : size≠0#64) :
    source.clock-(evaluateHOLFiniteState source afterKey).2.clock≤5 := by
  have read : eval source rootExpression=some (.val (.word 0#64)):=by
    simp [eval,rootExpression,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,mCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]
  rw [mutation_shapes.1]
  apply Input.ClockCost.declared_current source "root" rootExpression 0#64 afterRoot 5 read
  exact after_root_empty_cost (bind source "root" 0#64) key length pointer size installed (bind_lookup_same _ _ _)
    ((bind_lookup_other source "root" "nk" 0#64 (by decide)).trans nkCell)
    ((bind_lookup_other source "root" "vptr" 0#64 (by decide)).trans pointerCell)
    ((bind_lookup_other source "root" "vlen" 0#64 (by decide)).trans sizeCell) pointerActive sizeActive

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.mutation_shapes
#print axioms InitECandidate.Solver.Mpt.SetTrie.footer_quiet
#print axioms InitECandidate.Solver.Mpt.SetTrie.insert_selected
#print axioms InitECandidate.Solver.Mpt.SetTrie.after_root_empty_cost
#print axioms InitECandidate.Solver.Mpt.SetTrie.after_key_empty_cost
