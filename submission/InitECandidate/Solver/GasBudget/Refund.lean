import InitECandidate.Solver.GasBudget.Minimum

namespace InitECandidate.Solver.GasBudget.Refund
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_credit_state_gas_refund with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "amount",.one)]
def gasExpression : ExpHOL 64 := .op .add [frameLoad 64#64,localVar "from_gl"]
def spillExpression : ExpHOL 64 := .op .sub [localVar "spilled",localVar "from_gl"]
def stateExpression : ExpHOL 64 := .op .add [frameLoad 72#64,.op .sub [localVar "amount",localVar "from_gl"]]
def tail : ProgHOL 64 := .seq (.store (frameAddress 64#64) gasExpression)
  (.seq (.store (frameAddress 192#64) spillExpression) (.seq (.store (frameAddress 72#64) stateExpression) (.return (.const 0#64))))
def afterSpill : ProgHOL 64 := .decCall (ofString "from_gl") .one (ofString "min") [localVar "amount",localVar "spilled"] tail
def writes (frame gas state spill amount : BitVec 64) : List (BitVec 64×BitVec 64) :=
  let repayment:=Minimum.selected amount spill
  [(frame+64#64,gas+repayment),(frame+192#64,spill-repayment),(frame+72#64,state+(amount-repayment))]

theorem body_shape : body=.dec (ofString "spilled") .one (frameLoad 192#64) afterSpill := by
  simp only [body,Guest.guestFn_credit_state_gas_refund,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    afterSpill,tail,gasExpression,spillExpression,stateExpression,frameLoad,frameAddress,localVar]

/-- Actual state-gas refund: the selected minimum repays prior regular spill;
the remaining credit goes to the state reservoir. All three stores are real. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (amountLocal : source.locals.lookup (ofString "amount")=some (.val (.word amount)))
    (mapped : ∀ offset∈([64,72,192] : List Nat),source.memaddrs (frame+BitVec.ofNat 64 offset))
    (gasCell : source.memory (frame+64#64)=.word gas) (stateCell : source.memory (frame+72#64)=.word state)
    (spillCell : source.memory (frame+192#64)=.word spill)
    (minCode : source.code.lookup (ofString "min")=some (Minimum.formals,Minimum.body,.one)) (enough : 1≤source.clock) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),target) ∧
      target.memory=WitnessRadix.WordWrites.write source.memory (writes frame gas state spill amount) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-1} := by
  classical
  let repayment:=Minimum.selected amount spill
  have spillRead:=frame_read source frame 192#64 spill ev (mapped 192 (by simp)) spillCell
  let ss:=bind source "spilled" spill
  have amountS : ss.locals.lookup (ofString "amount")=some (.val (.word amount)):=
    (bind_lookup_other _ "spilled" "amount" _ (by decide)).trans amountLocal
  have spillS : ss.locals.lookup (ofString "spilled")=some (.val (.word spill)):=bind_lookup_same _ _ _
  have args : evalListHOLFinite ss (h:=fun address=>Classical.propDecidable (ss.memaddrs address)) [localVar "amount",localVar "spilled"]=
      some [.val (.word amount),.val (.word spill)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,amountS,spillS]
  have minRun:=Minimum.call_execute ss amount spill "from_gl" [localVar "amount",localVar "spilled"] tail args minCode enough
  let entered:=bind {ss with clock:=ss.clock-1} "from_gl" repayment
  have repaymentE : entered.locals.lookup (ofString "from_gl")=some (.val (.word repayment)):=bind_lookup_same _ _ _
  have spillE : entered.locals.lookup (ofString "spilled")=some (.val (.word spill)):=
    (bind_lookup_other _ "from_gl" "spilled" _ (by decide)).trans spillS
  have amountE : entered.locals.lookup (ofString "amount")=some (.val (.word amount)):=
    (bind_lookup_other _ "from_gl" "amount" _ (by decide)).trans amountS
  have gasRead:=frame_read entered frame 64#64 gas ev (mapped 64 (by simp)) gasCell
  have gasValue : eval entered gasExpression=some (.val (.word (gas+repayment))) := by
    simp only [eval] at gasRead ⊢
    simp only [gasExpression,evalHOLExact,evalListHOLExact,gasRead]
    simp [evalHOLExact,toExact,localVar,repaymentE,valueIsWord,valueWord,wordOpHOL,wordOp]
  have firstRun:=WitnessRadix.StoreWord.execute entered (frameAddress 64#64) gasExpression (frame+64#64) (gas+repayment)
    (address_read entered frame 64#64 ev) gasValue (mapped 64 (by simp))
  let first:={entered with memory:=WitnessRadix.StoreWord.put entered.memory (frame+64#64) (gas+repayment)}
  have repaymentF : first.locals.lookup (ofString "from_gl")=some (.val (.word repayment)):=repaymentE
  have spillF : first.locals.lookup (ofString "spilled")=some (.val (.word spill)):=spillE
  have spillValue : eval first spillExpression=some (.val (.word (spill-repayment))) := by
    simp [eval,spillExpression,evalHOLExact,evalListHOLExact,toExact,localVar,repaymentF,spillF,valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondRun:=WitnessRadix.StoreWord.execute first (frameAddress 192#64) spillExpression (frame+192#64) (spill-repayment)
    (address_read first frame 192#64 ev) spillValue (mapped 192 (by simp))
  let second:={first with memory:=WitnessRadix.StoreWord.put first.memory (frame+192#64) (spill-repayment)}
  have stateSecond : second.memory (frame+72#64)=.word state := by
    simp only [second,first,WitnessRadix.StoreWord.put,
      if_neg (offsets_ne frame 72#64 192#64 (by decide)),if_neg (offsets_ne frame 72#64 64#64 (by decide))]
    exact stateCell
  have stateRead:=frame_read second frame 72#64 state ev (mapped 72 (by simp)) stateSecond
  have repaymentS : second.locals.lookup (ofString "from_gl")=some (.val (.word repayment)):=repaymentE
  have amountSecond : second.locals.lookup (ofString "amount")=some (.val (.word amount)):=amountE
  have stateValue : eval second stateExpression=some (.val (.word (state+(amount-repayment)))) := by
    simp only [eval] at stateRead ⊢
    simp only [stateExpression,evalHOLExact,evalListHOLExact,stateRead]
    simp [evalHOLExact,evalListHOLExact,toExact,localVar,repaymentS,amountSecond,valueIsWord,valueWord,wordOpHOL,wordOp]
  have thirdRun:=WitnessRadix.StoreWord.execute second (frameAddress 72#64) stateExpression (frame+72#64) (state+(amount-repayment))
    (address_read second frame 72#64 ev) stateValue (mapped 72 (by simp))
  let third:={second with memory:=WitnessRadix.StoreWord.put second.memory (frame+72#64) (state+(amount-repayment))}
  have returned : evaluateHOLFiniteState third (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite third) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have tailRun : evaluateHOLFiniteState entered tail=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite third) := by
    rw [tail,WitnessRadix.StateSteps.next_sequence entered first _ _ firstRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence second third _ _ thirdRun (Nat.le_refl _)]
    exact returned
  have afterRun : evaluateHOLFiniteState ss afterSpill=
      (some (.returned (.val (.word 0#64))),restore ss "from_gl" (emptyLocalsHOLFinite third)) := by rw [afterSpill,minRun,tailRun]
  let target:=restore source "spilled" (restore ss "from_gl" (emptyLocalsHOLFinite third))
  refine ⟨target,?_,rfl,rfl⟩
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "spilled" (frameLoad 192#64) spill afterSpill _ spillRead afterRun

theorem preserves_regular_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (gasCell : source.memory (frame+64#64)=.word gas) (spillCell : source.memory (frame+192#64)=.word spill)
    (fits : gas.toNat+spill.toNat<2^64) :
    regularBudget (WitnessRadix.WordWrites.write source.memory (writes frame gas state spill amount)) frame=regularBudget source.memory frame := by
  let repayment:=Minimum.selected amount spill
  have repaymentSmall : repayment.toNat≤spill.toNat := by rw [Minimum.selected_number]; exact Nat.min_le_right _ _
  have repayWord : repayment≤spill:=repaymentSmall
  have d64192:=offsets_ne frame 64#64 192#64 (by decide)
  have d6472:=offsets_ne frame 64#64 72#64 (by decide)
  have d19272:=offsets_ne frame 192#64 72#64 (by decide)
  have distinct : ((writes frame gas state spill amount).map Prod.fst).Nodup := by simp [writes,d64192,d6472,d19272]
  have gasAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes frame gas state spill amount) (frame+64#64,gas+repayment) distinct (by simp [writes,repayment])
  have spillAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes frame gas state spill amount) (frame+192#64,spill-repayment) distinct (by simp [writes,repayment])
  have usedAfter:=WitnessRadix.WordWrites.write_away source.memory (writes frame gas state spill amount) (frame+184#64)
    (by simp [writes,offsets_ne frame 184#64 64#64 (by decide),offsets_ne frame 184#64 192#64 (by decide),offsets_ne frame 184#64 72#64 (by decide)])
  simp only [regularBudget,wordAt,gasAfter,spillAfter,usedAfter,gasCell,spillCell,WitnessRadix.MemoryBytes.wordBits]
  change (gas+repayment).toNat+(wordAt source.memory (frame+184#64)).toNat+(spill-repayment).toNat=
    gas.toNat+(wordAt source.memory (frame+184#64)).toNat+spill.toNat
  rw [BitVec.toNat_add_of_lt (by omega),BitVec.toNat_sub_of_le repayWord]
  omega

end InitECandidate.Solver.GasBudget.Refund

#print axioms InitECandidate.Solver.GasBudget.Refund.body_shape
#print axioms InitECandidate.Solver.GasBudget.Refund.execute
#print axioms InitECandidate.Solver.GasBudget.Refund.preserves_regular_budget
