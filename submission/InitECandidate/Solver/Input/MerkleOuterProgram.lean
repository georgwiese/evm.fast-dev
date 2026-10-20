import InitECandidate.Solver.Input.MerkleInnerLoop
import InitECandidate.Solver.WitnessRadix.RestoreLookup
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def outerLoop : ProgHOL 64 := (BuildProgram.loops body)[0]?.getD .skip
def outerStep : ProgHOL 64 := match outerLoop with | .while _ step=>step | _=>.skip
def halfExpression : ExpHOL 64 := .shift .lsr (localVar "cur") (.const 1#64)
def outerAssign : ProgHOL 64 := .assign .local (ofString "cur") (localVar "half")
def outerInnerTail : ProgHOL 64 := .seq innerLoop outerAssign
def afterHalf : ProgHOL 64 := .dec (ofString "j") .one (.const 0#64) outerInnerTail
def halfEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat) := bind source "half" (BitVec.ofNat 64 (cur/2))
def innerEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat) := bind (halfEntry source cur) "j" 0#64

def afterDense : ProgHOL 64 := match denseContinuation with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem outer_shape : outerLoop=.while (.cmp .less (.const 1#64) (localVar "cur")) outerStep ∧
    outerStep=.dec (ofString "half") .one halfExpression afterHalf ∧ denseContinuation=.seq outerLoop afterDense := by
  simp only [outerLoop,outerStep,innerLoop,afterDense,denseContinuation,afterClear,afterCopy,afterBuffer,afterMark,afterZero,afterDepth,afterCount,afterLimit,
    body,BuildProgram.loops,Guest.guestFn_merkleize,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,halfExpression,afterHalf,outerInnerTail,outerAssign,localVar]
  exact ⟨True.intro,True.intro,True.intro⟩

theorem half_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat) (small : cur<2^64)
    (current : source.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur)))) :
    eval source halfExpression=some (.val (.word (BitVec.ofNat 64 (cur/2)))) := by
  have number : (BitVec.ofNat 64 cur).toNat=cur := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have halfNumber : (BitVec.ofNat 64 (cur/2)).toNat=cur/2 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have shifted : ((BitVec.ofNat 64 cur) >>> (1:Nat))=BitVec.ofNat 64 (cur/2) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight,number,halfNumber,Nat.shiftRight_eq_div_pow]
  simp [eval,halfExpression,localVar,evalHOLExact,toExact,current,wordShiftHOL,shifted]

theorem outer_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code outerStep := by
  rw [outer_shape.2.1]
  unfold afterHalf outerInnerTail outerAssign
  apply GlobalEffects.declared
  apply GlobalEffects.declared
  exact GlobalEffects.sequence key code _ _ (inner_loop_globals key code installed) (GlobalEffects.assign key code _ _)

theorem outer_other (key : MlS) (notCur : key≠ofString "cur") (notHalf : key≠ofString "half") (notJ : key≠ofString "j") :
    LocalPrefix key outerStep := by
  rw [outer_shape.2.1]
  exact .dec _ _ _ notHalf (.dec _ _ _ notJ (.seq (inner_loop_other key notJ) (.assign _ _ notCur)))

/-- Every actual normal outer body halves its original cur counter. This
comes from the real declarations/inner-loop/assignment and restored scopes,
without assuming any future completed dense loop. -/
theorem outer_advances (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat)
    (small : cur<2^64) (current : source.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur))))
    (run : evaluateHOLFiniteState source outerStep=(none,post)) :
    post.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 (cur/2)))) := by
  rw [outer_shape.2.1] at run
  obtain ⟨halfPost,halfRun,endpoint⟩ := declaration_none source post "half" halfExpression (BitVec.ofNat 64 (cur/2)) afterHalf (half_read source cur small current) run
  change evaluateHOLFiniteState (halfEntry source cur) (.dec (ofString "j") .one (.const 0#64) outerInnerTail)=(none,halfPost) at halfRun
  obtain ⟨rawPost,bodyRun,halfEndpoint⟩ := declaration_none (halfEntry source cur) halfPost "j" (.const 0#64) 0#64 outerInnerTail rfl halfRun
  change evaluateHOLFiniteState (innerEntry source cur) (.seq innerLoop outerAssign)=(none,rawPost) at bodyRun
  obtain ⟨innerPost,innerRun,assigned⟩ := sequence_none (innerEntry source cur) rawPost innerLoop outerAssign bodyRun
  have halfCell : (innerEntry source cur).locals.lookup (ofString "half")=some (.val (.word (BitVec.ofNat 64 (cur/2)))) :=
    (bind_lookup_other _ "j" "half" _ (by decide)).trans (bind_lookup_same source "half" _)
  have summary := (inner_loop_other (ofString "half") (by decide)).summary_full (innerEntry source cur)
  unfold LocalSummary at summary
  rw [innerRun] at summary
  have halfValue := (summary.1 rfl).trans halfCell
  have read : eval innerPost (localVar "half")=some (.val (.word (BitVec.ofNat 64 (cur/2)))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using halfValue
  have rawEq := assign_none innerPost rawPost "cur" (localVar "half") (BitVec.ofNat 64 (cur/2)) read assigned
  rw [endpoint,halfEndpoint]
  rw [restore_lookup_other source _ "half" "cur" (by decide),restore_lookup_other (halfEntry source cur) _ "j" "cur" (by decide),rawEq]
  exact bind_lookup_same _ _ _

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.outer_shape
#print axioms InitECandidate.Solver.Input.Merkle.half_read
#print axioms InitECandidate.Solver.Input.Merkle.outer_globals
#print axioms InitECandidate.Solver.Input.Merkle.outer_other
#print axioms InitECandidate.Solver.Input.Merkle.outer_advances
