import InitECandidate.Solver.Mpt.KeyToNibblesAnyLoops
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.Input.GlobalByteEffects
import InitECandidate.Solver.Input.GlobalEffectsLoop

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def anyValues (key length out : BitVec 64) : List (ValueHOL 64):=[.val (.word key),.val (.word length),.val (.word out)]
def anyRawLocals (key length out : BitVec 64) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "n" then some (.val (.word length)) else
    if name=ofString "key" then some (.val (.word key)) else none

theorem any_environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (key length out : BitVec 64)
    (known : table (ofString "key_to_nibbles")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite table (ofString "key_to_nibbles") (anyValues key length out)=some (body,callee,.one) ∧
      callee.lookup (ofString "key")=some (.val (.word key)) ∧ callee.lookup (ofString "n")=some (.val (.word length)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(anyValues key length out).length ∧
      ((formals.zip (anyValues key length out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,anyValues,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "key_to_nibbles") (anyValues key length out)=some (body,anyRawLocals key length out,.one):=by
    simp only [lookupCodeHOLExact,known,valid,if_pos]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  exact ⟨callee,called,
    by rw [locals]; simp [anyRawLocals,show ofString "key"≠ofString "out" from by decide,show ofString "key"≠ofString "n" from by decide],
    by rw [locals]; simp [anyRawLocals,show ofString "n"≠ofString "out" from by decide],by rw [locals]; simp [anyRawLocals]⟩

/-- Original nibble conversion at every nonwrapping loop length, including
all reads/stores failing. No byte view or allocation success is required. -/
theorem call_any_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64) (length : Nat)
    (small : length+4<2^64) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (anyValues key (BitVec.ofNat 64 length) out))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "key_to_nibbles") arguments)).2.clock≤length/4+4 := by
  obtain ⟨callee,called,keyCell,lengthCell,outCell⟩:=any_environment source.code.lookup key (BitVec.ofNat 64 length) out (original_code source.code installed)
  have cost:=body_any_cost (callEntryStateHOLFinite source callee) length small lengthCell
  exact Input.ClockCost.call_current source destination (ofString "key_to_nibbles") arguments _ body callee .one (length/4+3) args called cost

theorem pair_globals (key : MlS) (code) (name : String) (offset : Nat) (rest : ProgHOL 64)
    (kept : Input.GlobalEffects.Preserves key code rest) : Input.GlobalEffects.Preserves key code (pair name offset rest) :=
  Input.GlobalEffects.sequence key code _ _ (Input.GlobalEffects.byte_store key code _ _)
    (Input.GlobalEffects.sequence key code _ _ (Input.GlobalEffects.byte_store key code _ _) kept)

/-- All globals survive the complete original nibble converter, even when
its byte loads or stores fail. In particular heap and scratch cursors stay. -/
theorem all_globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code body := by
  rw [body_shape,loop_shapes.1,loop_shapes.2,block_body_shape,tail_body_shape,after_tail_shape]
  repeat' first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.loop
    | apply pair_globals
    | exact Input.GlobalEffects.byte_store key code _ _
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.returned key code _

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.any_environment
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.call_any_cost
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_globals
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.all_globals
