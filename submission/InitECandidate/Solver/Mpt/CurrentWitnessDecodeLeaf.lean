import InitECandidate.Solver.Mpt.WitnessDecodeRows
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.Rlp.CurrentItem.Call
import InitECandidate.Solver.Input.ReturnFactsScopedAny
import InitECandidate.Solver.Input.NoReturnIgnored
import InitECandidate.Solver.Input.NoReturnScoped
import InitECandidate.Solver.Input.ClockCostScoped

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def ZeroResult (value : ValueHOL 64) : Prop := ∃ second,value=.rStruct [.val (.word 0#64),second]

set_option maxRecDepth 100000 in
theorem after_leaf_shape : afterLeaf=
    .seq (.store (.op .add [localVar "lf",.const 8#64]) (localVar "p"))
      (.seq (.store (.op .add [localVar "lf",.const 16#64]) (localVar "n"))
        (.return (.rstruct [.const 0#64,localVar "lf"]))) := by
  simp only [afterLeaf,leafAllocate,afterValue,leafBody,afterCompact,compactCall,afterPath,pairBody,afterArray,afterSlices,slicesCall,
    WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem after_leaf_price (code) : ClockCost.Bound code afterLeaf 0 := by
  rw [after_leaf_shape]
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _)
    (ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.returned code _))

theorem leaf_allocate_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code leafAllocate 3 := by
  rw [leaf_shape]
  exact ClockCost.scoped_body code (ofString "lf") .one (ofString "node_new_leaf") _ afterLeaf (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
    2 0 (NodeConstructor.original_code .leaf code installed) (NodeConstructor.scalar_body_price .leaf (by decide) code installed) (after_leaf_price code)

theorem after_value_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterValue 4 := by
  rw [after_value_shape]
  exact ClockCost.sequence code _ _ 1 3
    (ClockCost.conditional code _ _ _ 1 0 (Fail.call_price code installed [.const 6#64]) (ClockCost.skip code)) (leaf_allocate_price code installed)

/-- The actual second-item leaf path uses its real bounded descriptor and
current item decoder; constructor/store failures are included in this bound. -/
theorem current_leaf_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source leafBody).2.clock≤46*bytes+15 := by
  obtain ⟨args,positive,small,lower,upper⟩:=rows.arguments source array pointer bytes 1 items item selected arrayCell
  have fits : (Rlp.Slices.itemPointer pointer items 1).toNat+item.total.toNat<2^64 := by have h:=rows.fits; omega
  rw [value_shape]
  have price:=Rlp.CurrentItem.scoped_valid_cost source (Rlp.Slices.itemPointer pointer items 1) item.total arena fits "vi" (recordArguments 1) afterValue 4 args (by
    intro answer clock valid
    exact after_value_price source.code arena.code (setVarHOLFinite (ofString "vi") answer {source with clock:=clock}) rfl)
  omega

theorem zero_pair_return (source : PanSemStateFiniteExact 64 Guest.HostMemory) (expression : ExpHOL 64) :
    ReturnFacts.Returns source (.return (.rstruct [.const 0#64,expression])) ZeroResult := by
  cases read : eval source expression with
  | none=>
    have failed : eval source (.rstruct [.const 0#64,expression])=none := by
      simp only [eval] at read
      simp [eval,evalHOLExact,evalListHOLExact,read]
    intro post value normal
    have observed:=(Input.return_normal source post _ value normal).1
    rw [failed] at observed
    cases observed
  | some second=>
    apply ReturnFacts.returned source _ (.rStruct [.val (.word 0#64),second]) ZeroResult _ ⟨second,rfl⟩
    simp only [eval] at read
    simp [eval,evalHOLExact,evalListHOLExact,read]

theorem after_leaf_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) : ReturnFacts.Returns source afterLeaf ZeroResult := by
  rw [after_leaf_shape]
  apply ReturnFacts.sequence
  · intro post value normal
    exact (NoReturn.store _ _ source value (congrArg Prod.fst normal)).elim
  · intro middle firstRun
    apply ReturnFacts.sequence
    · intro post value normal
      exact (NoReturn.store _ _ middle value (congrArg Prod.fst normal)).elim
    · intro last secondRun
      exact zero_pair_return last (localVar "lf")

/-- Every actual leaf return has flag0, even if malformed arguments would
make its parser, constructor or stores fail earlier. -/
theorem leaf_body_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) : ReturnFacts.Returns source leafBody ZeroResult := by
  rw [value_shape]
  apply ReturnFacts.scoped_any
  intro ready
  rw [after_value_shape]
  apply ReturnFacts.sequence
  · apply ReturnFacts.conditional
    · intro post value normal
      exact (NoReturn.ignored_call _ _ ready value (congrArg Prod.fst normal)).elim
    · exact ReturnFacts.skip ready ZeroResult
  · intro middle guardRun
    rw [leaf_shape]
    exact ReturnFacts.scoped_any middle _ _ _ _ _ ZeroResult after_leaf_zero

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_leaf_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_body_zero
