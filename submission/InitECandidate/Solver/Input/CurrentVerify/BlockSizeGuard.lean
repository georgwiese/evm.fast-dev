import InitECandidate.Solver.Input.CurrentVerify.BlockLengthReached
import InitECandidate.Solver.Input.PureGuardNormal
import InitECandidate.Solver.Input.NoReturnDecision

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def sizeTest : ExpHOL 64:=.cmp .lower (.const 8388608#64) (localVar "bl")
def sizeGuard : ProgHOL 64:=.ite sizeTest (.raise (ofString "BlockErr") (.const 7#64)) .skip
def afterSizeGuard : ProgHOL 64:=match PayloadHeader.afterLength with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem length_guard_shape : PayloadHeader.afterLength=.seq sizeGuard afterSizeGuard:=by
  simp only [PayloadHeader.afterLength,PayloadHeader.lengthCall,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    afterSizeGuard,sizeGuard,sizeTest,localVar] <;> rfl

theorem size_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (encoded : Nat)
    (bl : source.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (number : (BitVec.ofNat 64 encoded).toNat=encoded) :
    eval source sizeTest=some (.val (.word (if 8388608<encoded then 1#64 else 0#64))):=by
  have comparison : 8388608#64<BitVec.ofNat 64 encoded↔8388608<encoded:=by
    change (8388608#64).toNat<(BitVec.ofNat 64 encoded).toNat↔8388608<encoded
    rw [number]
    rfl
  simp [eval,sizeTest,localVar,evalHOLExact,toExact,bl,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,comparison]

/-- The unchanged computed-size guard either stops without further source
clock cost or exposes its actual next caller. Its genuine passing branch
supplies the withdrawal cap; no exception-shape premise is needed. -/
theorem size_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (encoded : Nat)
    (minimum : 25*Payload.withdrawalCount input≤encoded)
    (bl : source.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (number : (BitVec.ofNat 64 encoded).toNat=encoded)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source PayloadHeader.afterLength=(outcome,post)) :
    (source.clock-post.clock≤0 ∧ ∀ value,outcome≠some (.returned value)) ∨
      (encoded≤8388608 ∧ Payload.withdrawalCount input≤335544 ∧ evaluateHOLFiniteState source afterSizeGuard=(outcome,post)) := by
  have read:=size_read source encoded bl number
  simp only [eval] at read
  by_cases small : encoded≤8388608
  · have passed : evaluateHOLFiniteState source sizeGuard=(none,source):=by
      rw [sizeGuard,evaluateHOLFiniteState_ite,read,if_neg (by omega)]
      simp [evaluateHOLFiniteState_skip]
    rw [length_guard_shape,StateSteps.next_sequence source source _ _ passed (Nat.le_refl _)] at actual
    exact Or.inr ⟨small,by omega,actual⟩
  · have branch : evaluateHOLFiniteState source sizeGuard=evaluateHOLFiniteState source (.raise (ofString "BlockErr") (.const 7#64)):=by
      rw [sizeGuard,evaluateHOLFiniteState_ite,read,if_pos (by omega)]
      rfl
    have stops : (evaluateHOLFiniteState source sizeGuard).1≠none:=by
      rw [branch]
      exact raise_ne_none source (ofString "BlockErr") (.const 7#64)
    have noReturn : NoReturn.Never sizeGuard:=NoReturn.conditional _ _ _ (NoReturn.raise _ _) NoReturn.skip
    have cost:=ClockCost.conditional source.code sizeTest (.raise (ofString "BlockErr") (.const 7#64)) .skip 0 0
      (ClockCost.raised source.code _ _) (ClockCost.skip source.code) source rfl
    change source.clock-(evaluateHOLFiniteState source sizeGuard).2.clock≤0 at cost
    rw [length_guard_shape,evaluateHOLFiniteState_seq_line780] at actual
    generalize computed : evaluateHOLFiniteState source sizeGuard=output at actual cost stops
    obtain ⟨result,target⟩:=output
    cases result with
    | none=>exact (stops rfl).elim
    | some result=>
      have endpoint:=congrArg Prod.snd actual
      have resultEq:=congrArg Prod.fst actual
      change target=post at endpoint
      refine Or.inl ⟨by rw [←endpoint]; exact cost,?_⟩
      intro value returned
      have impossible : (evaluateHOLFiniteState source sizeGuard).1=some (.returned value):=by
        rw [computed]
        exact resultEq.trans returned
      exact noReturn source value impossible

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.length_guard_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.size_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.size_trace
