import InitECandidate.Solver.Input.CurrentHash.MerklePairLoops
import InitECandidate.Solver.Input.ClockCostPotentialLoop
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostCurrentConditional
import InitECandidate.Solver.WitnessRadix.BindingLookup
import InitECandidate.Solver.WitnessRadix.RestoreLookup
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def loop : ProgHOL 64 := (BuildProgram.loops (Code.body .merkleize))[0]?.getD .skip
def step : ProgHOL 64 := match loop with | .while _ body => body | _ => .skip
def halfExpression : ExpHOL 64 := .shift .lsr (localVar "cur") (.const 1#64)
def assignment : ProgHOL 64 := .assign .local (ofString "cur") (localVar "half")
def innerTail : ProgHOL 64 := .seq (MerklePairLoops.loop .dense) assignment
def afterHalf : ProgHOL 64 := .dec (ofString "j") .one (.const 0#64) innerTail
def halfEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat) := bind source "half" (BitVec.ofNat 64 (cur/2))
def innerEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat) := bind (halfEntry source cur) "j" 0#64

set_option maxRecDepth 100000 in
theorem source_shape : loop = .while (.cmp .less (.const 1#64) (localVar "cur")) step ∧
    step = .dec (ofString "half") .one halfExpression afterHalf := by
  simp only [loop, step, MerklePairLoops.loop, MerklePairLoops.index, BuildProgram.loops,
    Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_merkleize, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.append_nil, List.nil_append, List.cons_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    halfExpression, afterHalf, innerTail, assignment, localVar]
  exact ⟨True.intro, True.intro⟩

theorem inner_other (key : MlS) (different : key ≠ ofString "j") : LocalPrefix key (MerklePairLoops.loop .dense) := by
  rw [(MerklePairLoops.source_shape .dense).1]
  exact .loop _ (MerklePairLoops.other .dense key different)

theorem other (key : MlS) (notCur : key ≠ ofString "cur") (notHalf : key ≠ ofString "half") (notJ : key ≠ ofString "j") :
    LocalPrefix key step := by
  rw [source_shape.2]
  exact .dec _ _ _ notHalf (.dec _ _ _ notJ (.seq (inner_other key notJ) (.assign _ _ notCur)))

theorem half_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat) (small : cur < 2^64)
    (current : source.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur)))) :
    eval source halfExpression = some (.val (.word (BitVec.ofNat 64 (cur/2)))) := by
  have number : (BitVec.ofNat 64 cur).toNat = cur := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have halfNumber : (BitVec.ofNat 64 (cur/2)).toNat = cur/2 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have shifted : ((BitVec.ofNat 64 cur) >>> (1 : Nat)) = BitVec.ofNat 64 (cur/2) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, number, halfNumber, Nat.shiftRight_eq_div_pow]
  simp [eval, halfExpression, localVar, evalHOLExact, toExact, current, wordShiftHOL, shifted]

/-- A normal actual outer body halves its original counter, through the real
inner-loop continuation and local-scope restoration. -/
theorem halves (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat)
    (small : cur < 2^64) (current : source.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur))))
    (actual : evaluateHOLFiniteState source step = (none, post)) :
    post.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 (cur/2)))) := by
  rw [source_shape.2] at actual
  obtain ⟨halfPost, halfRun, endpoint⟩ := declaration_none source post "half" halfExpression (BitVec.ofNat 64 (cur/2)) afterHalf (half_read source cur small current) actual
  change evaluateHOLFiniteState (halfEntry source cur) (.dec (ofString "j") .one (.const 0#64) innerTail) = (none, halfPost) at halfRun
  obtain ⟨rawPost, bodyRun, halfEndpoint⟩ := declaration_none (halfEntry source cur) halfPost "j" (.const 0#64) 0#64 innerTail rfl halfRun
  change evaluateHOLFiniteState (innerEntry source cur) (.seq (MerklePairLoops.loop .dense) assignment) = (none, rawPost) at bodyRun
  obtain ⟨innerPost, innerRun, assigned⟩ := sequence_none (innerEntry source cur) rawPost (MerklePairLoops.loop .dense) assignment bodyRun
  have halfCell : (innerEntry source cur).locals.lookup (ofString "half") = some (.val (.word (BitVec.ofNat 64 (cur/2)))) :=
    (bind_lookup_other _ "j" "half" _ (by decide)).trans (bind_lookup_same source "half" _)
  have summary := (inner_other (ofString "half") (by decide)).summary_full (innerEntry source cur)
  unfold LocalSummary at summary
  rw [innerRun] at summary
  have halfValue := (summary.1 rfl).trans halfCell
  have read : eval innerPost (localVar "half") = some (.val (.word (BitVec.ofNat 64 (cur/2)))) := by
    simpa [eval, localVar, evalHOLExact, toExact] using halfValue
  have rawEq := assign_none innerPost rawPost "cur" (localVar "half") (BitVec.ofNat 64 (cur/2)) read assigned
  rw [endpoint, halfEndpoint]
  rw [restore_lookup_other source _ "half" "cur" (by decide), restore_lookup_other (halfEntry source cur) _ "j" "cur" (by decide), rawEq]
  exact bind_lookup_same _ _ _

/-- The entire actual outer body spends at most twice its current half count,
including failed argument/memory operations and partial inner loops. -/
theorem step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat)
    (small : cur < 2^63) (installed : OriginalCode.Installed source.code)
    (current : source.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur)))) :
    source.clock - (evaluateHOLFiniteState source step).2.clock ≤ 2 * (cur/2) := by
  have halfCell : (innerEntry source cur).locals.lookup (ofString "half") = some (.val (.word (BitVec.ofNat 64 (cur/2)))) :=
    (bind_lookup_other _ "j" "half" _ (by decide)).trans (bind_lookup_same source "half" _)
  have jCell : (innerEntry source cur).locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 0))) := bind_lookup_same _ _ _
  have innerCost := MerklePairLoops.cost .dense (innerEntry source cur) 0 (cur/2) (by omega) (by omega) installed jCell halfCell
  rw [source_shape.2]
  apply ClockCost.declared_current source "half" halfExpression (BitVec.ofNat 64 (cur/2)) afterHalf (2 * (cur/2)) (half_read source cur (by omega) current)
  change (halfEntry source cur).clock - (evaluateHOLFiniteState (halfEntry source cur) (.dec (ofString "j") .one (.const 0#64) innerTail)).2.clock ≤ _
  apply ClockCost.declared_current (halfEntry source cur) "j" (.const 0#64) 0#64 innerTail (2 * (cur/2)) rfl
  exact ClockCost.sequence_current (innerEntry source cur) (MerklePairLoops.loop .dense) assignment (2 * (cur/2)) 0
    (by simpa only [Nat.sub_zero] using innerCost) (ClockCost.assign (innerEntry source cur).code _ _)

def invariant (capacity : Nat) (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ cur : Nat, 1 ≤ cur ∧ cur ≤ capacity ∧ state.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur)))
def allowance (state : PanSemStateFiniteExact 64 Guest.HostMemory) := 3 * ((CounterFlow.counterWord state (ofString "cur")).toNat - 1)

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat) (small : cur < 2^63)
    (current : source.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur)))) :
    evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) (.cmp .less (.const 1#64) (localVar "cur")) =
      some (.val (.word (if 1 < cur then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 cur).toNat = cur := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have sign : cur < 9223372036854775808 := small
  simp [evalHOLFinite, evalHOLExact, toExact, localVar, current, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, number, sign]

/-- Linear all-outcome cost of the actual software dense tree. The allowance
pays each shrinking pair loop and outer tick, without a logarithmic multiplier. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur capacity : Nat)
    (positive : 1 ≤ cur) (inside : cur ≤ capacity) (small : capacity < 2^63)
    (installed : OriginalCode.Installed source.code)
    (current : source.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur)))) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ 3 * (cur - 1) := by
  classical
  have transition : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory, state.code = source.code → invariant capacity state → ∀ word,
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) (.cmp .less (.const 1#64) (localVar "cur")) = some (.val (.word word)) → word ≠ 0 → state.clock ≠ 0 →
      let output := evaluateHOLFiniteState (decClockHOLFinite state) step
      state.clock - output.2.clock ≤ allowance state ∧
      ((output.1 = none ∨ output.1 = some .continue) → invariant capacity output.2 ∧
        state.clock - output.2.clock + allowance output.2 ≤ allowance state) := by
    intro state codeEq valid word read nonzero funded
    obtain ⟨count, countPositive, countBound, countCell⟩ := valid
    have number : (BitVec.ofNat 64 count).toNat = count := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have expected := test_read state count (by omega) countCell
    have active : 1 < count := by
      by_cases active : 1 < count
      · exact active
      rw [if_neg active] at expected
      have zero : word = 0#64 := by simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using read.symm.trans expected
      exact False.elim (nonzero zero)
    have allowanceEq : allowance state = 3 * (count - 1) := by simp [allowance, CounterFlow.counterWord, countCell, valueWord, number]
    let output := evaluateHOLFiniteState (decClockHOLFinite state) step
    have currentCode : OriginalCode.Installed (decClockHOLFinite state).code := by change OriginalCode.Installed state.code; rw [codeEq]; exact installed
    have bodyCost := step_cost (decClockHOLFinite state) count (by omega) currentCode countCell
    have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) step
    change state.clock - 1 - output.2.clock ≤ 2 * (count/2) at bodyCost
    change output.2.clock ≤ state.clock - 1 at bodyClock
    have spent : state.clock - output.2.clock ≤ 2 * (count/2) + 1 := by omega
    have stopped : state.clock - output.2.clock ≤ allowance state := by rw [allowanceEq]; omega
    refine ⟨stopped, ?_⟩
    intro continuing
    have summary := (other (ofString "buf") (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite state)
    unfold LocalSummary at summary
    have normal : output.1 = none := continuing.resolve_right summary.2.2.2
    have actual : evaluateHOLFiniteState (decClockHOLFinite state) step = (none, output.2) := Prod.ext normal rfl
    have next := halves (decClockHOLFinite state) output.2 count (by omega) countCell actual
    have nextNumber : (BitVec.ofNat 64 (count/2)).toNat = count/2 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have nextAllowance : allowance output.2 = 3 * (count/2 - 1) := by simp [allowance, CounterFlow.counterWord, next, valueWord, nextNumber]
    have paid : state.clock - output.2.clock + allowance output.2 ≤ allowance state := by
      rw [nextAllowance, allowanceEq]
      omega
    exact ⟨⟨count/2, by omega, by omega, next⟩, paid⟩
  have priced := ClockCost.potential_loop source.code _ step (invariant capacity) allowance transition source rfl ⟨cur, positive, inside, current⟩
  have number : (BitVec.ofNat 64 cur).toNat = cur := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [source_shape.1]
  simpa only [allowance, CounterFlow.counterWord, current, Option.getD_some, valueWord, number] using priced

end InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost.inner_other
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost.other
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost.half_read
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost.halves
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost.step_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost.test_read
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost.cost
