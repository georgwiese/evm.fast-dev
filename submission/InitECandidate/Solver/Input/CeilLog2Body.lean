import InitECandidate.Solver.Input.CeilLog2
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.Input.CeilLog2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def frozen (source : PanSemStateFiniteExact 64 Guest.HostMemory) := emptyLocalsHOLFinite {source with clock:=0}
def formals : List (MlS×ShapeHOL) := [(ofString "n",.one)]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ceil_log2")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 31 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_ceil_log2) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_ceil_log2,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Literal original ceil_log2 returns its actual least covering exponent,
spends exactly that many loop ticks and preserves all nonlocal state. -/
theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : BitVec 64) (depth : Nat)
    (small : depth<64) (bounded : n.toNat≤2^depth) (enough : depth≤source.clock)
    (number : source.locals.lookup (ofString "n")=some (.val (.word n))) :
    ∃ post exponent,exponent≤depth ∧ n.toNat≤2^exponent ∧ (0<exponent→2^(exponent-1)<n.toNat) ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 exponent)))),post) ∧
      post.clock=source.clock-exponent ∧ frozen post=frozen source := by
  classical
  let entry := bind source "d" 0#64
  have nEntry : entry.locals.lookup (ofString "n")=some (.val (.word n)) := (bind_lookup_other source "d" "n" _ (by decide)).trans number
  obtain ⟨target,exponent,paid,paidBound,exponentEq,exponentBound,ceiling,previous,run,frame,finalD,others⟩ :=
    loop_execute entry n depth 0 small (by omega) bounded (by change depth-0≤source.clock; omega) (bind_lookup_same _ _ _) nEntry
  have paidEq : paid=exponent := by omega
  have targetClock : target.clock=source.clock-exponent := by
    have h := congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at h
    simpa only [paidEq] using h
  have returned : evaluateHOLFiniteState target finish=(some (.returned (.val (.word (BitVec.ofNat 64 exponent)))),emptyLocalsHOLFinite target) := by
    simp [finish,evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,finalD,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have suffix : evaluateHOLFiniteState entry (.seq loop finish)=(some (.returned (.val (.word (BitVec.ofNat 64 exponent)))),emptyLocalsHOLFinite target) := by
    rw [WitnessRadix.StateSteps.next_sequence entry target _ _ run (by change target.clock≤source.clock; omega)]
    exact returned
  have declared := ScalarScope.declare_execute source (emptyLocalsHOLFinite target) "d" (.const 0#64) 0#64 (.seq loop finish)
    (some (.returned (.val (.word (BitVec.ofNat 64 exponent))))) rfl suffix
  refine ⟨restore source "d" (emptyLocalsHOLFinite target),exponent,exponentBound,ceiling,previous,?_,targetClock,?_⟩
  · rw [body_shape]; exact declared
  · change frozen target=frozen source
    rw [frame]
    rfl

/-- Dense Merkle tree storage is less than twice the actual nonempty input
count. A large declared limit contributes logarithmic extension work only. -/
theorem ceiling_size (n exponent : Nat) (ceiling : n≤2^exponent) (previous : 0<exponent→2^(exponent-1)<n) :
    n≤2^exponent ∧ 2^exponent≤max 1 (2*n) := by
  refine ⟨ceiling,?_⟩
  by_cases zero : exponent=0
  · simp [zero]
  · have positive : 0<exponent := by omega
    have before := previous positive
    have split : exponent=(exponent-1)+1 := by omega
    conv_lhs => rw [split,Nat.pow_succ]
    omega

end InitECandidate.Solver.Input.CeilLog2

#print axioms InitECandidate.Solver.Input.CeilLog2.original_code
#print axioms InitECandidate.Solver.Input.CeilLog2.body_execute
#print axioms InitECandidate.Solver.Input.CeilLog2.ceiling_size
