import InitECandidate.Solver.Headers.CurrentValidate.LinkLoop
import InitECandidate.Solver.Headers.CurrentValidate.DecodeLoop
import InitECandidate.Solver.Input.NoReturnScoped
import InitECandidate.Solver.Input.ReturnFactsLoop

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def resetIndex (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind source "i" 1#64

theorem reset_round (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) :
    evaluateHOLFiniteState source (.assign .local (ofString "i") (.const 1#64))=(none,resetIndex source) ∧ RoundState data origin (resetIndex source) 1 := by
  have actual:=WitnessRadix.StateSteps.assign_execute source "i" (.const 1#64) (BitVec.ofNat 64 index) 1#64 state.indexCell rfl
  refine ⟨actual,?_⟩
  apply state.nonlocal data origin source (resetIndex source) index 1 rfl
  · exact (bind_lookup_other source "i" "arr" 1#64 (by decide)).trans state.arrayCell
  · exact (bind_lookup_other source "i" "n" 1#64 (by decide)).trans state.countCell
  · exact (bind_lookup_other source "i" "hs" 1#64 (by decide)).trans state.hsCell
  · exact (bind_lookup_other source "i" "hashes" 1#64 (by decide)).trans state.hashesCell
  · exact bind_lookup_same source "i" 1#64

theorem link_step_never : Input.NoReturn.Never linkStep := by
  obtain ⟨_,_,_,_,_,_,_,_,_,linkShape,afterShape⟩ := shapes
  rw [linkShape]
  apply Input.NoReturn.scoped_call
  rw [afterShape]
  apply Input.NoReturn.sequence
  · intro F source value
    exact (Input.PureGuard.ite _ (.raise _ _) .skip).summary source |>.2 value
  · intro F source value
    exact (Input.LocalPrefix.assign (key:=ofString "n") (ofString "i") _ (by decide)).summary source |>.2 value

theorem link_loop_never (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) :
    (evaluateHOLFiniteState source (.while test linkStep)).1≠some (.returned value) := by
  intro returned
  have facts:=Input.ReturnFacts.loop source.code test linkStep (fun _=>True) (fun _=>False)
    (by intro current codeEq valid word read nonzero funded post value run; exact link_step_never _ value (congrArg Prod.fst run))
    (by intros; trivial) source rfl True.intro
  exact facts _ value (Prod.ext returned rfl)

theorem link_tail_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (state : RoundState data origin source 1) (layout : RoundLayout data) :
    source.clock-(evaluateHOLFiniteState source linkTail).2.clock≤130*(data.count-1) := by
  obtain ⟨_,_,_,_,_,_,tailShape,_,_,_,_⟩ := shapes
  rw [tailShape]
  have front:=link_loop_cost data origin source 1 state layout (by omega)
  have price:=Input.ClockCost.sequence_current source (.while test linkStep) (.return (.rstruct [localVar "hs",localVar "hashes"])) (130*(data.count-1)) 0 front
    (Input.ClockCost.returned source.code _)
  simpa only [Nat.add_zero] using price

theorem after_decode_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) :
    source.clock-(evaluateHOLFiniteState source afterDecode).2.clock≤130*(data.count-1) := by
  obtain ⟨_,_,_,_,_,resetShape,_,_,_,_,_⟩ := shapes
  rw [resetShape]
  obtain ⟨actual,next⟩ := reset_round data origin source index state
  rw [evaluateHOLFiniteState_seq_line780,actual]
  have price:=link_tail_cost data origin (resetIndex source) next layout
  have clock : (resetIndex source).clock=source.clock := rfl
  rwa [clock] at price

theorem loops_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (state : RoundState data origin source 0) (layout : RoundLayout data) :
    source.clock-(evaluateHOLFiniteState source loops).2.clock≤258497*data.count+130*(data.count-1) := by
  obtain ⟨_,_,_,_,loopsShape,_,_,_,_,_,_⟩ := shapes
  rw [loopsShape]
  have front:=decode_loop_cost data origin source 0 state layout (by omega)
  change source.clock-(evaluateHOLFiniteState source (.while test decodeStep)).2.clock≤258497*data.count at front
  apply Input.ClockCost.sequence_reached_current source (.while test decodeStep) afterDecode (258497*data.count) (130*(data.count-1)) front
  intro middle normal
  obtain ⟨index,bounded,next⟩ := decode_loop_normal data origin source middle 0 state layout (by omega) normal
  exact after_decode_cost data origin middle index next layout

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.reset_round
#print axioms InitECandidate.Solver.Headers.CurrentValidate.link_step_never
#print axioms InitECandidate.Solver.Headers.CurrentValidate.link_loop_never
#print axioms InitECandidate.Solver.Headers.CurrentValidate.link_tail_cost
#print axioms InitECandidate.Solver.Headers.CurrentValidate.after_decode_cost
#print axioms InitECandidate.Solver.Headers.CurrentValidate.loops_cost
