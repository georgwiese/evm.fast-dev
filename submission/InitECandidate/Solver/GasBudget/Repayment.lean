import InitECandidate.Solver.GasBudget.ChildErrorCall

namespace InitECandidate.Solver.GasBudget.Repayment
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def choose : ProgHOL 64 := .ite (.cmp .lower (frameLoad 192#64) (localVar "rep"))
  (.assign .local (ofString "rep") (frameLoad 192#64)) .skip
def gasExpression : ExpHOL 64 := .op .add [frameLoad 64#64,localVar "rep"]
def stateExpression : ExpHOL 64 := .op .sub [frameLoad 72#64,localVar "rep"]
def spillExpression : ExpHOL 64 := .op .sub [frameLoad 192#64,localVar "rep"]
def stores (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (frameAddress 64#64) gasExpression)
    (.seq (.store (frameAddress 72#64) stateExpression)
      (.seq (.store (frameAddress 192#64) spillExpression) continuation))
def program (continuation : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "rep") .one (frameLoad 72#64) (.seq choose (stores continuation))
def writes (frame gas state spill : BitVec 64) : List (BitVec 64×BitVec 64) :=
  let rep:=Minimum.selected spill state
  [(frame+64#64,gas+rep),(frame+72#64,state-rep),(frame+192#64,spill-rep)]

/-- The literal successful-child spill repayment, up to an arbitrary following
continuation. Its lexical rep scope is retained through that continuation. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill : BitVec 64)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (mapped : ∀ offset∈([64,72,192] : List Nat),source.memaddrs (frame+BitVec.ofNat 64 offset))
    (gasCell : source.memory (frame+64#64)=.word gas) (stateCell : source.memory (frame+72#64)=.word state)
    (spillCell : source.memory (frame+192#64)=.word spill) :
    ∃ target,target.memory=WitnessRadix.WordWrites.write source.memory (writes frame gas state spill) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory} ∧
      (∀ name : String,ofString "rep"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      (∀ continuation,evaluateHOLFiniteState source (program continuation)=
        (let output:=evaluateHOLFiniteState target continuation
        (output.1,restore source "rep" output.2))) := by
  classical
  have stateRead:=frame_read source frame 72#64 state ev (mapped 72 (by simp)) stateCell
  let bound:=bind source "rep" state
  have repB : bound.locals.lookup (ofString "rep")=some (.val (.word state)):=bind_lookup_same _ _ _
  have spillRead:=frame_read bound frame 192#64 spill ev (mapped 192 (by simp)) spillCell
  have assignRun:=WitnessRadix.StateSteps.assign_execute bound "rep" (frameLoad 192#64) state spill repB spillRead
  let chosen:=if spill<state then bind bound "rep" spill else bound
  have chooseRun : evaluateHOLFiniteState bound choose=(none,chosen) := by
    rw [choose,evaluateHOLFiniteState_ite]
    simp only [eval] at spillRead
    by_cases less : spill<state
    · simpa [evalHOLExact,spillRead,toExact,localVar,repB,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,less,chosen] using assignRun
    · simp [evalHOLExact,spillRead,toExact,localVar,repB,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,less,chosen]
  let rep:=Minimum.selected spill state
  have repC : chosen.locals.lookup (ofString "rep")=some (.val (.word rep)) := by
    by_cases less : spill<state
    · simpa only [chosen,rep,Minimum.selected,if_pos less] using (bind_lookup_same bound "rep" spill)
    · simpa only [chosen,rep,Minimum.selected,if_neg less] using repB
  have chosenMemory : chosen.memory=source.memory := by dsimp [chosen]; split <;> rfl
  have chosenEv : chosen.globals.lookup (ofString "ev")=some (.val (.word frame)) := by
    dsimp [chosen]; split <;> exact ev
  have chosenMapped : ∀ offset∈([64,72,192] : List Nat),chosen.memaddrs (frame+BitVec.ofNat 64 offset) := by
    dsimp [chosen]; split <;> exact mapped
  have gasRead:=frame_read chosen frame 64#64 gas chosenEv (chosenMapped 64 (by simp)) (by rw [chosenMemory];exact gasCell)
  have gasValue : eval chosen gasExpression=some (.val (.word (gas+rep))) := by
    simp only [eval] at gasRead ⊢
    simp only [gasExpression,evalHOLExact,evalListHOLExact,gasRead]
    simp [evalHOLExact,toExact,localVar,repC,valueIsWord,valueWord,wordOpHOL,wordOp]
  have firstRun:=WitnessRadix.StoreWord.execute chosen (frameAddress 64#64) gasExpression (frame+64#64) (gas+rep)
    (address_read chosen frame 64#64 chosenEv) gasValue (chosenMapped 64 (by simp))
  let first:={chosen with memory:=WitnessRadix.StoreWord.put chosen.memory (frame+64#64) (gas+rep)}
  have stateFirst : first.memory (frame+72#64)=.word state := by
    simp only [first,WitnessRadix.StoreWord.put,if_neg (offsets_ne frame 72#64 64#64 (by decide)),chosenMemory]
    exact stateCell
  have stateF:=frame_read first frame 72#64 state chosenEv (chosenMapped 72 (by simp)) stateFirst
  have repF : first.locals.lookup (ofString "rep")=some (.val (.word rep)):=repC
  have stateValue : eval first stateExpression=some (.val (.word (state-rep))) := by
    simp only [eval] at stateF ⊢
    simp only [stateExpression,evalHOLExact,evalListHOLExact,stateF]
    simp [evalHOLExact,toExact,localVar,repF,valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondRun:=WitnessRadix.StoreWord.execute first (frameAddress 72#64) stateExpression (frame+72#64) (state-rep)
    (address_read first frame 72#64 chosenEv) stateValue (chosenMapped 72 (by simp))
  let second:={first with memory:=WitnessRadix.StoreWord.put first.memory (frame+72#64) (state-rep)}
  have spillSecond : second.memory (frame+192#64)=.word spill := by
    simp only [second,first,WitnessRadix.StoreWord.put,
      if_neg (offsets_ne frame 192#64 72#64 (by decide)),if_neg (offsets_ne frame 192#64 64#64 (by decide)),chosenMemory]
    exact spillCell
  have spillS:=frame_read second frame 192#64 spill chosenEv (chosenMapped 192 (by simp)) spillSecond
  have repS : second.locals.lookup (ofString "rep")=some (.val (.word rep)):=repC
  have spillValue : eval second spillExpression=some (.val (.word (spill-rep))) := by
    simp only [eval] at spillS ⊢
    simp only [spillExpression,evalHOLExact,evalListHOLExact,spillS]
    simp [evalHOLExact,toExact,localVar,repS,valueIsWord,valueWord,wordOpHOL,wordOp]
  have thirdRun:=WitnessRadix.StoreWord.execute second (frameAddress 192#64) spillExpression (frame+192#64) (spill-rep)
    (address_read second frame 192#64 chosenEv) spillValue (chosenMapped 192 (by simp))
  let target:={second with memory:=WitnessRadix.StoreWord.put second.memory (frame+192#64) (spill-rep)}
  have memoryEq : target.memory=WitnessRadix.WordWrites.write source.memory (writes frame gas state spill) := by
    simp only [target,second,first,chosenMemory,writes,WitnessRadix.WordWrites.write,rep]
  refine ⟨target,memoryEq,?_,?_,?_⟩
  · dsimp [target,second,first,chosen]; split <;> rfl
  · intro name different
    dsimp only [target,second,first]
    dsimp only [chosen]
    split
    · exact (bind_lookup_other _ "rep" name _ different).trans (bind_lookup_other _ "rep" name _ different)
    · exact bind_lookup_other _ "rep" name _ different
  · intro continuation
    have storeRun : evaluateHOLFiniteState chosen (stores continuation)=evaluateHOLFiniteState target continuation := by
      rw [stores,WitnessRadix.StateSteps.next_sequence chosen first _ _ firstRun (Nat.le_refl _),
        WitnessRadix.StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
        WitnessRadix.StateSteps.next_sequence second target _ _ thirdRun (Nat.le_refl _)]
    have chosenClock : chosen.clock=bound.clock := by dsimp [chosen]; split <;> rfl
    rw [program]
    have bodyRun : evaluateHOLFiniteState bound (.seq choose (stores continuation))=evaluateHOLFiniteState target continuation := by
      rw [WitnessRadix.StateSteps.next_sequence bound chosen _ _ chooseRun (by omega),storeRun]
    exact Input.ScalarScope.declare_execute source (evaluateHOLFiniteState target continuation).2 "rep"
      (frameLoad 72#64) state _ (evaluateHOLFiniteState target continuation).1 stateRead
      (by simpa only [Prod.mk.eta] using bodyRun)

/-- Repayment transfers only between liquid gas and outstanding spill. -/
theorem preserves_regular_budget (memory : Memory) (frame gas state spill : BitVec 64)
    (gasCell : memory (frame+64#64)=.word gas) (spillCell : memory (frame+192#64)=.word spill)
    (fits : gas.toNat+spill.toNat<2^64) :
    regularBudget (WitnessRadix.WordWrites.write memory (writes frame gas state spill)) frame=regularBudget memory frame := by
  let rep:=Minimum.selected spill state
  have small : rep.toNat≤spill.toNat := by rw [Minimum.selected_number];exact Nat.min_le_left _ _
  have wordSmall : rep≤spill:=small
  have distinct : ((writes frame gas state spill).map Prod.fst).Nodup := by
    simp [writes,offsets_ne frame 64#64 72#64 (by decide),offsets_ne frame 64#64 192#64 (by decide),offsets_ne frame 72#64 192#64 (by decide)]
  have gasAfter:=WitnessRadix.WordWrites.write_unique memory (writes frame gas state spill) (frame+64#64,gas+rep) distinct (by simp [writes,rep])
  have spillAfter:=WitnessRadix.WordWrites.write_unique memory (writes frame gas state spill) (frame+192#64,spill-rep) distinct (by simp [writes,rep])
  have usedAfter:=WitnessRadix.WordWrites.write_away memory (writes frame gas state spill) (frame+184#64)
    (by simp [writes,offsets_ne frame 184#64 64#64 (by decide),offsets_ne frame 184#64 72#64 (by decide),offsets_ne frame 184#64 192#64 (by decide)])
  simp only [regularBudget,wordAt,gasAfter,spillAfter,usedAfter,gasCell,spillCell,WitnessRadix.MemoryBytes.wordBits]
  change (gas+rep).toNat+(wordAt memory (frame+184#64)).toNat+(spill-rep).toNat=
    gas.toNat+(wordAt memory (frame+184#64)).toNat+spill.toNat
  rw [BitVec.toNat_add_of_lt (by omega),BitVec.toNat_sub_of_le wordSmall]
  omega

end InitECandidate.Solver.GasBudget.Repayment

#print axioms InitECandidate.Solver.GasBudget.Repayment.execute
#print axioms InitECandidate.Solver.GasBudget.Repayment.preserves_regular_budget
