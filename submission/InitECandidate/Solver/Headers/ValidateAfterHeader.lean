import InitECandidate.Solver.Headers.ValidateHeaderStore
import InitECandidate.Solver.Headers.ValidateHashNormal
import InitECandidate.Solver.Headers.ValidateIncrement
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_header_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count) (header : BitVec 64)
    (headerLocal : source.locals.lookup (ofString "h")=some (.val (.word header))) :
    source.clock-(evaluateHOLFiniteState source afterHeader).2.clock≤Keccak256.price (data.lengths index).toNat+1 := by
  obtain ⟨_,_,_,_,_,_,_,_,headerShape,_,_⟩ := shapes
  rw [headerShape]
  obtain ⟨stored,next,cell⟩ := store_header data origin source index state layout inside header headerLocal
  rw [evaluateHOLFiniteState_seq_line780,stored]
  have hashPrice:=hash_cost data origin (storedHeader source data.hs header index) index next layout inside
  have price:=Input.ClockCost.sequence_current (storedHeader source data.hs header index)
    (.call (some (none,none)) (ofString "keccak256") hashArguments) increment (Keccak256.price (data.lengths index).toNat+1) 0 hashPrice
    (Input.ClockCost.assign source.code (ofString "i") (.op .add [localVar "i",.const 1#64]))
  have storedClock : (storedHeader source data.hs header index).clock=source.clock := rfl
  rw [storedClock,Nat.add_zero] at price
  exact price

theorem after_header_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count) (header : BitVec 64)
    (headerLocal : source.locals.lookup (ofString "h")=some (.val (.word header)))
    (normal : evaluateHOLFiniteState source afterHeader=(none,post)) : RoundState data origin post (index+1) := by
  obtain ⟨_,_,_,_,_,_,_,_,headerShape,_,_⟩ := shapes
  rw [headerShape] at normal
  obtain ⟨stored,next,cell⟩ := store_header data origin source index state layout inside header headerLocal
  rw [evaluateHOLFiniteState_seq_line780,stored] at normal
  obtain ⟨hashed,hashRun,incrementRun⟩ := Input.sequence_none (storedHeader source data.hs header index) post _ _ normal
  have hashedState:=hash_normal data origin (storedHeader source data.hs header index) hashed index next layout inside hashRun
  obtain ⟨incrementedRun,finalState⟩ := increment_round data origin hashed index hashedState
  have endpoint : incremented hashed index=post := congrArg Prod.snd (incrementedRun.symm.trans incrementRun)
  exact endpoint ▸ finalState

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.after_header_cost
#print axioms InitECandidate.Solver.Headers.Validate.after_header_normal
