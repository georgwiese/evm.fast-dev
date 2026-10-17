import InitECandidate.Solver.WitnessRadix.Copy32Block

namespace InitECandidate.Solver.WitnessRadix.Copy32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def wordTailBody : ProgHOL 64 := match loopWord with | .while _ code => code | _ => .skip
def byteBody : ProgHOL 64 := match loopBytes with | .while _ code => code | _ => .skip
def tailBody : ProgHOL 64 := match loopTail with | .while _ code => code | _ => .skip

theorem other_loop_shapes : loopWord = .while (condition 8#64) wordTailBody ∧
    loopBytes = .while (condition 8#64) byteBody ∧
    loopTail = .while (.cmp .lower (localVar "i") (localVar "n")) tailBody := by
  simp only [loopWord, loopBytes, loopTail, wordTailBody, byteBody, tailBody, body, BuildProgram.loops, Guest.guestFn_memcpy,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, condition, localVar, addConst]
  exact ⟨True.intro, True.intro, True.intro⟩

theorem condition_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index step : BitVec 64)
    (iLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word 32#64))) :
    @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address)) (condition step) = some (.val (.word (if (32#64 : BitVec 64) < index + step then 0#64 else 1#64))) := by
  classical
  by_cases lower : (32#64 : BitVec 64) < index + step
  all_goals simp [lower, evalHOLFinite, condition, localVar, addConst, evalHOLExact, evalListHOLExact, toExact, iLocal, nLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem alignment_read {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (mask : (dst ||| src) &&& 7#64 = 0#64) : eval source alignment = some (.val (.word 1#64)) := by
  classical
  have opOr : wordOpHOL .or [dst, src] = some (dst ||| src) := by
    change some (dst ||| (src ||| 0#64)) = _
    rw [BitVec.or_zero]
  have opAnd : wordOpHOL .and [dst ||| src, 7#64] = some ((dst ||| src) &&& 7#64) := by
    change some ((dst ||| src) &&& (7#64 &&& ~~~(0#64))) = _
    rw [BitVec.not_zero, BitVec.and_allOnes]
  simp only [eval, alignment, localVar, evalHOLExact, evalListHOLExact, toExact, srcLocal, dstLocal,
    valueIsWord, valueWord, List.all_cons, List.all_nil, Bool.and_self, List.map_cons, List.map_nil,
    opOr, opAnd, Option.map_some, ↓reduceIte, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, mask, beq_self_eq_true]
  rfl

end InitECandidate.Solver.WitnessRadix.Copy32

#print axioms InitECandidate.Solver.WitnessRadix.Copy32.condition_read
#print axioms InitECandidate.Solver.WitnessRadix.Copy32.alignment_read
