import InitECandidate.Solver.GasBudget.ForwardSites

namespace InitECandidate.Solver.GasBudget.SaturatingAdd
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def resultWord (a b : BitVec 64) : BitVec 64 := if a+b<a then 18446744073709551615#64 else a+b

theorem carry_iff (a b : BitVec 64) : a + b < a ↔ 2 ^ 64 ≤ a.toNat + b.toNat := by
  change (a + b).toNat < a.toNat ↔ _
  rw [BitVec.toNat_add]
  have first := a.isLt
  have second := b.isLt
  omega

theorem result_nat (a b : BitVec 64) : (resultWord a b).toNat = min (2 ^ 64 - 1) (a.toNat + b.toNat) := by
  by_cases carry : a + b < a
  · have overflow := (carry_iff a b).mp carry
    simp only [resultWord, if_pos carry]
    change 18446744073709551615 = min (2 ^ 64 - 1) (a.toNat + b.toNat)
    omega
  · have notOverflow : ¬2 ^ 64 ≤ a.toNat + b.toNat := fun larger => carry ((carry_iff a b).mpr larger)
    have fits : a.toNat + b.toNat < 2 ^ 64 := by omega
    rw [resultWord, if_neg carry, BitVec.toNat_add_of_lt fits]
    omega

theorem covers (a b amount : BitVec 64) (affordable : amount.toNat ≤ a.toNat + b.toNat) : amount ≤ resultWord a b := by
  change amount.toNat ≤ (resultWord a b).toNat
  rw [result_nat]
  have small := amount.isLt
  omega

/-- Both actual add_sat branches, including overflow. The lower bound used
for up-front call fees does not require exact natural addition. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) :
    ∃ target,evaluateHOLFiniteState source AddExact.body=(some (.returned (.val (.word (resultWord a b)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  classical
  have sumRead : eval source AddExact.sumExpression=some (.val (.word (a+b))) := by
    simp [eval,AddExact.sumExpression,evalHOLExact,evalListHOLExact,toExact,localVar,aLocal,bLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  let entered:=WitnessRadix.QueryBranch.bind source "s" (a+b)
  have aE : entered.locals.lookup (ofString "a")=some (.val (.word a)):=
    (bind_lookup_other _ "s" "a" _ (by decide)).trans aLocal
  have sE : entered.locals.lookup (ofString "s")=some (.val (.word (a+b))):=bind_lookup_same _ _ _
  have tailRun : evaluateHOLFiniteState entered AddExact.tail=(some (.returned (.val (.word (resultWord a b)))),emptyLocalsHOLFinite entered) := by
    by_cases overflow : a+b<a
    all_goals simp [AddExact.tail,resultWord,evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,
      evalHOLExact,toExact,localVar,aE,sE,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,overflow,
      shapeOfHOLExact,sizeOfShapeWithContextHOL,fixClockHOLFinite,emptyLocalsHOLFinite]
  refine ⟨restore source "s" (emptyLocalsHOLFinite entered),?_,rfl⟩
  rw [AddExact.body_shape]
  exact Input.ScalarScope.declare_execute source _ "s" AddExact.sumExpression (a+b) AddExact.tail _ sumRead tailRun

theorem ge_left (a b : BitVec 64) : a≤resultWord a b := by
  by_cases overflow : a+b<a
  · rw [resultWord,if_pos overflow]
    change a.toNat≤18446744073709551615
    have bound:=a.isLt
    omega
  · rw [resultWord,if_neg overflow]
    change ¬(a+b).toNat<a.toNat at overflow
    change a.toNat≤(a+b).toNat
    omega

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word a),.val (.word b)])
    (code : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one)) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "add_sat") expressions continuation)=
      (let output:=evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock:=source.clock-1} name (resultWord a b)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,aLocal,bLocal⟩:=AddExact.environment source.code.lookup a b code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,run,frame⟩:=execute entry a b aLocal bLocal
  have actual:=Input.CallNormal.pure_return_execute source target name (ofString "add_sat") expressions [.val (.word a),.val (.word b)]
    AddExact.body continuation callee (resultWord a b) 0 args called enough run frame
  simpa only [Nat.sub_zero] using actual

theorem value_fee_lower (access memory : BitVec 64) (small : access.toNat≤3000) :
    11300≤(resultWord (access+11300#64) memory).toNat := by
  have available : (access+11300#64).toNat=access.toNat+11300 := by
    rw [BitVec.toNat_add_of_lt (by change access.toNat+11300<2^64; omega)]
    rfl
  have bound:=ge_left (access+11300#64) memory
  change (access+11300#64).toNat≤(resultWord (access+11300#64) memory).toNat at bound
  omega

end InitECandidate.Solver.GasBudget.SaturatingAdd

#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.execute
#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.ge_left
#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.call_execute
#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.value_fee_lower

#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.carry_iff
#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.result_nat
#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.covers
