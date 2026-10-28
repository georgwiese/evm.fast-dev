import InitECandidate.Solver.Rlp.ValidationProgram

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem push_moves_price (code) : Input.ClockCost.Bound code pushMoves 0 :=
  Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.assign code _ _))
theorem push_stores_price (code) : Input.ClockCost.Bound code pushStores 0 :=
  Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _)
      (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) (push_moves_price code)))
theorem push_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code push 2 :=
  Arenas.scoped_price code installed .down (ofString "rec") .one [.const 24#64] pushStores 0 (push_stores_price code)
theorem after_header_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterHeader 2 := by
  apply Input.ClockCost.declared
  apply Input.ClockCost.declared
  exact Input.ClockCost.conditional code _ _ _ 2 0 (push_price code installed) (Input.ClockCost.assign code _ _)
theorem at_end_price (code) : Input.ClockCost.Bound code atEnd 0 :=
  Input.ClockCost.conditional code _ _ _ 0 0 (Input.ClockCost.assign code _ _)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _)
      (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.assign code _ _)))

theorem header_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (position ending : BitVec 64)
    (positionCell : source.locals.lookup (ofString "pos")=some (.val (.word position)))
    (endCell : source.locals.lookup (ofString "end")=some (.val (.word ending))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) headerArguments=some (Header.values position (ending-position)) := by
  simp [headerArguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,positionCell,endCell,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Every current original validator-body outcome costs<=13source ticks.
The parse arm derives actual header arguments; no mapped/funded future helper
or successful scratch allocation is a premise. -/
theorem loop_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (position ending : BitVec 64)
    (positionCell : source.locals.lookup (ofString "pos")=some (.val (.word position)))
    (endCell : source.locals.lookup (ofString "end")=some (.val (.word ending)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source loopBody).2.clock≤13 := by
  have choice : evaluateHOLFiniteState source loopBody=
      if position=ending then evaluateHOLFiniteState source atEnd else evaluateHOLFiniteState source parse := by
    simp [loop_body_shape,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,positionCell,endCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [choice]
  by_cases same : position=ending
  · rw [if_pos same]
    exact Nat.le_trans (at_end_price source.code source rfl) (by decide)
  · rw [if_neg same]
    exact Header.scoped_cost source position (ending-position) (ofString "h") headerArguments afterHeader 2
      (header_arguments source position ending positionCell endCell) installed (after_header_price source.code installed)

theorem loop_body_prefix : Input.LocalPrefix (ofString "p") loopBody := by
  rw [loop_body_shape]
  simp only [atEnd,stop,pop,parse,afterHeader,choose,push,pushStores,pushMoves,move]
  repeat first
    | apply Input.LocalPrefix.seq
    | apply Input.LocalPrefix.ite
    | apply Input.LocalPrefix.dec _ _ _ (by decide)
    | apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
    | exact Input.LocalPrefix.assign _ _ (by decide)
    | exact Input.LocalPrefix.store _ _

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.push_moves_price
#print axioms InitECandidate.Solver.Rlp.Validation.push_stores_price
#print axioms InitECandidate.Solver.Rlp.Validation.push_price
#print axioms InitECandidate.Solver.Rlp.Validation.after_header_price
#print axioms InitECandidate.Solver.Rlp.Validation.at_end_price
#print axioms InitECandidate.Solver.Rlp.Validation.header_arguments
#print axioms InitECandidate.Solver.Rlp.Validation.loop_body_cost
#print axioms InitECandidate.Solver.Rlp.Validation.loop_body_prefix
