import InitECandidate.Solver.Mpt.NodeRefLenNormal
import InitECandidate.Solver.Input.ReturnFactsScalar

namespace InitECandidate.Solver.Mpt.NodeRefLen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Bounded (value : ValueHOL 64) : Prop:=∃ word : BitVec 64,value=.val (.word word) ∧ word.toNat≤33

/-- A normal length-selection tail itself derives a word operand and
the unsigned33-byte cap. Unreadable or nonword operands cannot return. -/
theorem length_tail_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Input.ReturnFacts.Returns source lengthTail Bounded := by
  intro target value normal
  cases lookup : source.locals.lookup (ofString "rl") with
  | none=>simp [lengthTail,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,lookup] at normal
  | some loaded=>
    cases loaded with
    | rStruct fields=>simp [lengthTail,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,lookup] at normal
    | nStruct name fields=>simp [lengthTail,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,lookup] at normal
    | val word=>
      cases word with
      | word word=>
        have actual:=length_tail_execute source word lookup
        have answer : value=.val (.word (if word.toNat<32 then word else 33#64)):=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (normal.symm.trans actual)))
        refine ⟨_,answer,?_⟩
        split <;> simp_all <;> omega

/-- The complete original helper's normal result is bounded without
assuming cache words, readable operands or any future child result.
Each successful branch establishes its own word or returns a literal. -/
theorem normal_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Input.ReturnFacts.Returns source body Bounded := by
  have literal (current : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64) (small : word.toNat≤33) :
      Input.ReturnFacts.Returns current (.return (.const word)) Bounded:=Input.ReturnFacts.returned current (.const word) (.val (.word word)) Bounded rfl ⟨word,rfl,small⟩
  have guard : Input.LocalPrefix (ofString "child") cacheGuard:=.ite cacheTest (.call none _ _ (by intro name same; cases same)) .skip
  have checked (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Input.ReturnFacts.Returns current checkedTail Bounded:=
    Input.ReturnFacts.sequence current cacheGuard afterCache Bounded (Input.ReturnFacts.local_prefix current (ofString "child") cacheGuard guard Bounded)
      (fun middle _=>Input.ReturnFacts.declared middle (ofString "rl") .one (readAt 16) lengthTail Bounded (fun _=>length_tail_bound _))
  rw [body_shape]
  apply Input.ReturnFacts.sequence
  · exact Input.ReturnFacts.conditional source _ _ _ Bounded (literal source 1#64 (by decide)) (Input.ReturnFacts.skip source Bounded)
  · intro middle _
    apply Input.ReturnFacts.sequence
    · exact Input.ReturnFacts.conditional middle _ _ _ Bounded (literal middle 33#64 (by decide)) (Input.ReturnFacts.skip middle Bounded)
    · intro current _
      exact checked current

end InitECandidate.Solver.Mpt.NodeRefLen

#print axioms InitECandidate.Solver.Mpt.NodeRefLen.length_tail_bound
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.normal_bound
