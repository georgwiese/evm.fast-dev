import InitECandidate.Solver.WitnessRadix.ZeroConditions

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def byteBody : ProgHOL 64 := match loopBytes with | .while _ code => code | _ => .skip
def tailBody : ProgHOL 64 := match loopTail with | .while _ code => code | _ => .skip

theorem other_loop_shapes : loopBytes = .while (condition 8#64) byteBody ∧
    loopTail = .while (.cmp .lower (localVar "i") (localVar "n")) tailBody := by
  simp only [loopBytes, loopTail, byteBody, tailBody, body, BuildProgram.loops, Guest.Software.guestFn_memzero,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    condition, Copy32.condition, localVar, addConst]
  exact ⟨True.intro, True.intro⟩

theorem remaining_loops {F : Type} (source : PanSemStateFiniteExact 64 F) (length : Nat)
    (small : length + 32 < 2 ^ 64)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 length))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    evaluateHOLFiniteState source loopBytes = (none, source) ∧
      evaluateHOLFiniteState source loopTail = (none, source) := by
  classical
  have test := condition_read source length length 8 small (Nat.le_refl _) (by decide) indexLocal lengthLocal
  have inactive : ¬ length + 8 ≤ length := by omega
  simp only [if_neg inactive] at test
  have tailTest : @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address))
      (.cmp .lower (localVar "i") (localVar "n")) = some (.val (.word 0#64)) := by
    simp [evalHOLFinite, localVar, evalHOLExact, toExact, indexLocal, lengthLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [other_loop_shapes.1, other_loop_shapes.2]
  refine ⟨?_, ?_⟩
  · rw [evaluateHOLFiniteState_while_total, test]; simp
  · rw [evaluateHOLFiniteState_while_total, tailTest]; simp

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.remaining_loops
