import InitECandidate.Solver.GasBudget.StateChargeCall

namespace InitECandidate.Solver.GasBudget.Halt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_frame_halt with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "err",.one)]
def usedExpression : ExpHOL 64 := .op .add [frameLoad 184#64,frameLoad 64#64]
def writes (frame gas used err : BitVec 64) : List (BitVec 64×BitVec 64) :=
  [(frame+184#64,used+gas),(frame+64#64,0#64),(frame+160#64,err)]

theorem body_shape : body=.seq (.store (frameAddress 184#64) usedExpression)
    (.seq (.store (frameAddress 64#64) (.const 0#64)) (.seq (.store (frameAddress 160#64) (localVar "err")) (.return (.const 0#64)))) := by
  simp only [body,Guest.guestFn_frame_halt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,frameAddress,frameLoad,usedExpression,localVar]

/-- Actual exceptional frame halt moves liquid gas to the regular-used
counter, zeros liquid gas and records the error, preserving every other cell. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used err : BitVec 64)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (errLocal : source.locals.lookup (ofString "err")=some (.val (.word err)))
    (mapped : ∀ offset∈([64,160,184] : List Nat),source.memaddrs (frame+BitVec.ofNat 64 offset))
    (gasCell : source.memory (frame+64#64)=.word gas) (usedCell : source.memory (frame+184#64)=.word used) :
    evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),
      emptyLocalsHOLFinite {source with memory:=WitnessRadix.WordWrites.write source.memory (writes frame gas used err)}) := by
  classical
  have gasRead:=frame_read source frame 64#64 gas ev (mapped 64 (by simp)) gasCell
  have usedRead:=frame_read source frame 184#64 used ev (mapped 184 (by simp)) usedCell
  have addRead : eval source usedExpression=some (.val (.word (used+gas))) := by
    simp only [eval] at gasRead usedRead ⊢
    simp only [usedExpression,evalHOLExact,evalListHOLExact,gasRead,usedRead]
    simp [valueIsWord,valueWord,wordOpHOL,wordOp]
  have firstRun:=WitnessRadix.StoreWord.execute source (frameAddress 184#64) usedExpression (frame+184#64) (used+gas)
    (address_read source frame 184#64 ev) addRead (mapped 184 (by simp))
  let first:={source with memory:=WitnessRadix.StoreWord.put source.memory (frame+184#64) (used+gas)}
  have secondRun:=WitnessRadix.StoreWord.execute first (frameAddress 64#64) (.const 0#64) (frame+64#64) 0#64
    (address_read first frame 64#64 ev) rfl (mapped 64 (by simp))
  let second:={first with memory:=WitnessRadix.StoreWord.put first.memory (frame+64#64) 0#64}
  have errSecond : second.locals.lookup (ofString "err")=some (.val (.word err)):=errLocal
  have errRead : eval second (localVar "err")=some (.val (.word err)) := by simp [eval,evalHOLExact,toExact,localVar,errSecond]
  have thirdRun:=WitnessRadix.StoreWord.execute second (frameAddress 160#64) (localVar "err") (frame+160#64) err
    (address_read second frame 160#64 ev) errRead (mapped 160 (by simp))
  let third:={second with memory:=WitnessRadix.StoreWord.put second.memory (frame+160#64) err}
  rw [body_shape,WitnessRadix.StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence second third _ _ thirdRun (Nat.le_refl _)]
  simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rfl

theorem preserves_regular_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used err : BitVec 64)
    (gasCell : source.memory (frame+64#64)=.word gas) (usedCell : source.memory (frame+184#64)=.word used)
    (fits : gas.toNat+used.toNat<2^64) :
    regularBudget (WitnessRadix.WordWrites.write source.memory (writes frame gas used err)) frame=regularBudget source.memory frame := by
  have d18464:=offsets_ne frame 184#64 64#64 (by decide)
  have d184160:=offsets_ne frame 184#64 160#64 (by decide)
  have d64160:=offsets_ne frame 64#64 160#64 (by decide)
  have distinct : ((writes frame gas used err).map Prod.fst).Nodup := by simp [writes,d18464,d184160,d64160]
  have gasAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes frame gas used err) (frame+64#64,0#64) distinct (by simp [writes])
  have usedAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes frame gas used err) (frame+184#64,used+gas) distinct (by simp [writes])
  have spillAfter:=WitnessRadix.WordWrites.write_away source.memory (writes frame gas used err) (frame+192#64)
    (by simp [writes,offsets_ne frame 192#64 184#64 (by decide),offsets_ne frame 192#64 64#64 (by decide),offsets_ne frame 192#64 160#64 (by decide)])
  simp only [regularBudget,wordAt,gasAfter,usedAfter,spillAfter,gasCell,usedCell,WitnessRadix.MemoryBytes.wordBits]
  change 0+(used+gas).toNat+(wordAt source.memory (frame+192#64)).toNat=
    gas.toNat+used.toNat+(wordAt source.memory (frame+192#64)).toNat
  rw [BitVec.toNat_add_of_lt (by omega)]
  omega

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used err : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word err)])
    (code : source.code.lookup (ofString "frame_halt")=some (formals,body,.one))
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (mapped : ∀ offset∈([64,160,184] : List Nat),source.memaddrs (frame+BitVec.ofNat 64 offset))
    (gasCell : source.memory (frame+64#64)=.word gas) (usedCell : source.memory (frame+184#64)=.word used)
    (fits : gas.toNat+used.toNat<2^64) (enough : 1≤source.clock) :
    ∃ memory,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "frame_halt") expressions)=
        (none,{source with memory:=memory,clock:=source.clock-1}) ∧
      regularBudget memory frame=regularBudget source.memory frame ∧ memory (frame+64#64)=.word 0#64 := by
  obtain ⟨callee,called,errLocal⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "frame_halt") "err" body err code
  let entry:=callEntryStateHOLFinite source callee
  let memory:=WitnessRadix.WordWrites.write source.memory (writes frame gas used err)
  have run:=execute entry frame gas used err ev errLocal mapped gasCell usedCell
  have frameEq : emptyLocalsHOLFinite (emptyLocalsHOLFinite {entry with memory:=memory})=
      emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1}:=rfl
  refine ⟨memory,ignored_return source _ _ expressions _ body callee 1 args called enough run frameEq,
    preserves_regular_budget source frame gas used err gasCell usedCell fits,?_⟩
  exact WitnessRadix.WordWrites.write_unique source.memory (writes frame gas used err) (frame+64#64,0#64)
    (by simp [writes,offsets_ne frame 184#64 64#64 (by decide),offsets_ne frame 184#64 160#64 (by decide),offsets_ne frame 64#64 160#64 (by decide)]) (by simp [writes])

end InitECandidate.Solver.GasBudget.Halt

#print axioms InitECandidate.Solver.GasBudget.Halt.body_shape
#print axioms InitECandidate.Solver.GasBudget.Halt.execute
#print axioms InitECandidate.Solver.GasBudget.Halt.preserves_regular_budget
#print axioms InitECandidate.Solver.GasBudget.Halt.call_execute
