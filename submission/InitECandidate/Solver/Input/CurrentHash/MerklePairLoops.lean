import InitECandidate.Solver.Input.CurrentHash.Sha256Pair
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.PanTraversal

namespace InitECandidate.Solver.Input.CurrentHash.MerklePairLoops
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual dense-pair and depth-extension loops, selected from current syntax. -/
inductive Phase where | dense | extension

def index : Phase → Nat | .dense => 1 | .extension => 2
def counter : Phase → MlS | .dense => ofString "j" | .extension => ofString "d"
def limit : Phase → MlS | .dense => ofString "half" | .extension => ofString "target"
def loop (phase : Phase) : ProgHOL 64 := (BuildProgram.loops (Code.body .merkleize))[index phase]?.getD .skip
def step (phase : Phase) : ProgHOL 64 := match loop phase with | .while _ body => body | _ => .skip
def arguments (phase : Phase) : List (ExpHOL 64) := match step phase with
  | .seq (.call _ _ args) _ => args | _ => []
def pairCall (phase : Phase) : ProgHOL 64 := .call (some (none, none)) (Code.name .sha256_pair) (arguments phase)
def increment (phase : Phase) : ProgHOL 64 := .assign .local (counter phase) (.op .add [.var .local (counter phase), .const 1#64])

set_option maxRecDepth 100000 in
theorem source_shape (phase : Phase) :
    loop phase = .while (.cmp .less (.var .local (counter phase)) (.var .local (limit phase))) (step phase) ∧
    step phase = .seq (pairCall phase) (increment phase) := by
  cases phase <;>
    simp only [loop, step, index, counter, limit, arguments, pairCall, increment,
      BuildProgram.loops, Code.body, Code.entry, Code.declaration, Code.name,
      GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
      Guest.Software.guestFn_merkleize, progToHOL, expToHOL, shapeToHOL,
      List.map_cons, List.map_nil, List.append_nil, List.nil_append, List.cons_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Option.map_none]
  all_goals exact ⟨True.intro, True.intro⟩

theorem advances (phase : Phase) : CounterFlow.Advances (counter phase) 1 (step phase) := by
  rw [(source_shape phase).2]
  exact CounterFlow.sequence _ _ _ 0 1
    (CounterFlow.preserved _ _ (.call none _ _ (by intro name impossible; cases impossible))) (CounterFlow.increment _)

theorem other (phase : Phase) (key : MlS) (different : key ≠ counter phase) : LocalPrefix key (step phase) := by
  rw [(source_shape phase).2]
  exact .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)

/-- One actual software SHA call and a pure local increment: at most one body
source tick on every outcome, without mapped input or successful SHA premises. -/
theorem step_cost (phase : Phase) (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (step phase) 1 := by
  rw [(source_shape phase).2]
  exact ClockCost.sequence code _ _ 1 0 (Sha256Pair.call_cost code installed (some none) _) (ClockCost.assign code _ _)

theorem step_globals (phase : Phase) (selected : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves selected code (step phase) := by
  rw [(source_shape phase).2]
  exact GlobalEffects.sequence selected code _ _
    (GlobalEffects.call_body selected code (some none) (Code.name .sha256_pair) _
      (Code.formals .sha256_pair) (Code.body .sha256_pair) (Code.shape .sha256_pair)
      (Code.installed code installed .sha256_pair) (Sha256Pair.any_key selected code)) (GlobalEffects.assign selected code _ _)

/-- Both actual signed-counter loops spend at most two source ticks for each
remaining pair: one loop tick and one pair call. Failed/timeout paths are included. -/
theorem cost (phase : Phase) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (position bound : Nat)
    (small : bound < 2^63) (inside : position ≤ bound) (installed : OriginalCode.Installed source.code)
    (current : source.locals.lookup (counter phase) = some (.val (.word (BitVec.ofNat 64 position))))
    (maximum : source.locals.lookup (limit phase) = some (.val (.word (BitVec.ofNat 64 bound)))) :
    source.clock - (evaluateHOLFiniteState source (loop phase)).2.clock ≤ 2 * (bound - position) := by
  have different : limit phase ≠ counter phase := by cases phase <;> decide
  have number : (BitVec.ofNat 64 position).toNat = position := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have priced := CounterFlow.signed_loop_cost source.code (counter phase) (limit phase) (step phase) 1 bound small
    (step_cost phase source.code installed) (advances phase) (other phase _ different)
    source (BitVec.ofNat 64 position) rfl current maximum (by rw [number]; exact inside)
  rw [(source_shape phase).1]
  simpa only [number] using priced

theorem globals (phase : Phase) (selected : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves selected code (loop phase) := by
  rw [(source_shape phase).1]
  exact GlobalEffects.loop selected code _ _ (step_globals phase selected code installed)

end InitECandidate.Solver.Input.CurrentHash.MerklePairLoops

#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairLoops.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairLoops.advances
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairLoops.other
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairLoops.step_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairLoops.step_globals
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairLoops.cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairLoops.globals
