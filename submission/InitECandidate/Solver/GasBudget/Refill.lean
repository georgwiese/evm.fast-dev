import InitECandidate.Solver.GasBudget.Frame

namespace InitECandidate.Solver.GasBudget.Refill
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_refill_frame_state_gas with | .function fn=>progToHOL fn.body | _=>.skip
def messageLoad : ExpHOL 64 := frameLoad 112#64
def replenish : ProgHOL 64 := .store (frameAddress 64#64) (.op .add [frameLoad 64#64,frameLoad 192#64])
def restoreReservoir : ProgHOL 64 := .store (frameAddress 72#64) (.load .one (.op .add [localVar "msg",.const 48#64]))
def clearSpill : ProgHOL 64 := .store (frameAddress 192#64) (.const 0#64)
def tail : ProgHOL 64 := .seq replenish (.seq restoreReservoir (.seq clearSpill (.return (.const 0#64))))
def writes (frame gas spill reservoir : BitVec 64) : List (BitVec 64×BitVec 64) :=
  [(frame+64#64,gas+spill),(frame+72#64,reservoir),(frame+192#64,0#64)]

theorem body_shape : body=.dec (ofString "msg") .one messageLoad tail := by
  simp only [body,Guest.guestFn_refill_frame_state_gas,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    messageLoad,tail,replenish,restoreReservoir,clearSpill,frameLoad,frameAddress,localVar]

/-- Actual rollback refill returns the outstanding spill to regular gas and
restores the message reservoir. It makes no call or while-clock payment. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame message gas spill reservoir : BitVec 64)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (mapped : ∀ offset∈([64,72,112,192] : List Nat),source.memaddrs (frame+BitVec.ofNat 64 offset))
    (messageCell : source.memory (frame+112#64)=.word message)
    (gasCell : source.memory (frame+64#64)=.word gas) (spillCell : source.memory (frame+192#64)=.word spill)
    (reservoirMapped : source.memaddrs (message+48#64)) (reservoirCell : source.memory (message+48#64)=.word reservoir)
    (reservoirAway : message+48#64≠frame+64#64) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),target) ∧
      target.memory=WitnessRadix.WordWrites.write source.memory (writes frame gas spill reservoir) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory} := by
  classical
  have messageRead:=frame_read source frame 112#64 message ev (mapped 112 (by simp)) messageCell
  let entered:=bind source "msg" message
  have msg : entered.locals.lookup (ofString "msg")=some (.val (.word message)):=bind_lookup_same _ _ _
  have gasRead:=frame_read entered frame 64#64 gas ev (mapped 64 (by simp)) gasCell
  have spillRead:=frame_read entered frame 192#64 spill ev (mapped 192 (by simp)) spillCell
  have addRead : eval entered (.op .add [frameLoad 64#64,frameLoad 192#64])=some (.val (.word (gas+spill))) := by
    simp only [eval] at gasRead spillRead ⊢
    simp only [evalHOLExact,evalListHOLExact,gasRead,spillRead]
    simp [valueIsWord,valueWord,wordOpHOL,wordOp]
  have firstRun:=WitnessRadix.StoreWord.execute entered (frameAddress 64#64) _ (frame+64#64) (gas+spill)
    (address_read entered frame 64#64 ev) addRead (mapped 64 (by simp))
  let first:={entered with memory:=WitnessRadix.StoreWord.put entered.memory (frame+64#64) (gas+spill)}
  have msgFirst : first.locals.lookup (ofString "msg")=some (.val (.word message)):=msg
  have reservoirFirst : first.memory (message+48#64)=.word reservoir := by
    simp only [first,WitnessRadix.StoreWord.put,if_neg reservoirAway]
    exact reservoirCell
  have reservoirRead : eval first (.load .one (.op .add [localVar "msg",.const 48#64]))=some (.val (.word reservoir)) := by
    have mappedFirst : first.memaddrs (message+48#64):=reservoirMapped
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,msgFirst,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,mappedFirst,reservoirFirst]
  have secondRun:=WitnessRadix.StoreWord.execute first (frameAddress 72#64) _ (frame+72#64) reservoir
    (address_read first frame 72#64 ev) reservoirRead (mapped 72 (by simp))
  let second:={first with memory:=WitnessRadix.StoreWord.put first.memory (frame+72#64) reservoir}
  have thirdRun:=WitnessRadix.StoreWord.execute second (frameAddress 192#64) (.const 0#64) (frame+192#64) 0#64
    (address_read second frame 192#64 ev) rfl (mapped 192 (by simp))
  let third:={second with memory:=WitnessRadix.StoreWord.put second.memory (frame+192#64) 0#64}
  have returned : evaluateHOLFiniteState third (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite third) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have actual : evaluateHOLFiniteState entered tail=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite third) := by
    change evaluateHOLFiniteState entered replenish=(none,first) at firstRun
    change evaluateHOLFiniteState first restoreReservoir=(none,second) at secondRun
    change evaluateHOLFiniteState second clearSpill=(none,third) at thirdRun
    rw [tail,WitnessRadix.StateSteps.next_sequence entered first _ _ firstRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence second third _ _ thirdRun (Nat.le_refl _)]
    exact returned
  let target:=restore source "msg" (emptyLocalsHOLFinite third)
  refine ⟨target,?_,rfl,rfl⟩
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "msg" messageLoad message tail _ messageRead actual

theorem preserves_regular_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas spill reservoir : BitVec 64)
    (gasCell : source.memory (frame+64#64)=.word gas) (spillCell : source.memory (frame+192#64)=.word spill)
    (fits : gas.toNat+spill.toNat<2^64) :
    regularBudget (WitnessRadix.WordWrites.write source.memory (writes frame gas spill reservoir)) frame=regularBudget source.memory frame := by
  have d6472:=offsets_ne frame 64#64 72#64 (by decide)
  have d64192:=offsets_ne frame 64#64 192#64 (by decide)
  have d72192:=offsets_ne frame 72#64 192#64 (by decide)
  have distinct : ((writes frame gas spill reservoir).map Prod.fst).Nodup := by simp [writes,d6472,d64192,d72192]
  have gasAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes frame gas spill reservoir) (frame+64#64,gas+spill) distinct (by simp [writes])
  have spillAfter:=WitnessRadix.WordWrites.write_unique source.memory (writes frame gas spill reservoir) (frame+192#64,0#64) distinct (by simp [writes])
  have usedAfter:=WitnessRadix.WordWrites.write_away source.memory (writes frame gas spill reservoir) (frame+184#64)
    (by simp [writes,offsets_ne frame 184#64 64#64 (by decide),offsets_ne frame 184#64 72#64 (by decide),offsets_ne frame 184#64 192#64 (by decide)])
  simp only [regularBudget,wordAt,gasAfter,spillAfter,usedAfter,gasCell,spillCell,WitnessRadix.MemoryBytes.wordBits]
  change (gas+spill).toNat+(wordAt source.memory (frame+184#64)).toNat+0=
    gas.toNat+(wordAt source.memory (frame+184#64)).toNat+spill.toNat
  rw [BitVec.toNat_add_of_lt fits]
  omega

end InitECandidate.Solver.GasBudget.Refill

#print axioms InitECandidate.Solver.GasBudget.Refill.body_shape
#print axioms InitECandidate.Solver.GasBudget.Refill.execute
#print axioms InitECandidate.Solver.GasBudget.Refill.preserves_regular_budget
