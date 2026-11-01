import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Branch
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The real leaf guard stops at its actual declared marker; internal
nodes alone enter the original key-bit branch. -/
theorem after_bit_execute_marker (marker : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bits : Nat) (small : bits≤marker.toNat)
    (bitCell : source.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 bits))))
    (bitsCell : source.locals.lookup (ofString "keybits")=some (.val (.word marker))) :
    evaluateHOLFiniteState source afterBit=if bits=marker.toNat then (some .break,source) else evaluateHOLFiniteState source branch := by
  have number : (BitVec.ofNat 64 bits).toNat=bits := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have upper:=marker.isLt; omega)]
  by_cases leaf : bits=marker.toNat
  · simp [shapes.2.2.1,leafGuard,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_break,
      evalHOLExact,localVar,bitCell,bitsCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,leaf]
  · have different : BitVec.ofNat 64 bits≠marker := by intro equal; have same:=congrArg BitVec.toNat equal; rw [number] at same; exact leaf same
    simp [shapes.2.2.1,leafGuard,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,
      evalHOLExact,localVar,bitCell,bitsCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,different,leaf]

theorem after_bit_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bits : Nat) (small : bits≤256)
    (bitCell : source.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 bits))))
    (bitsCell : source.locals.lookup (ofString "keybits")=some (.val (.word 256#64))) :
    evaluateHOLFiniteState source afterBit=if bits=256 then (some .break,source) else evaluateHOLFiniteState source branch :=
  after_bit_execute_marker 256#64 source bits small bitCell bitsCell

theorem after_bit_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bit marker : BitVec 64)
    (bitCell : source.locals.lookup (ofString "b") = some (.val (.word bit)))
    (bitsCell : source.locals.lookup (ofString "keybits") = some (.val (.word marker))) :
    evaluateHOLFiniteState source afterBit =
      if bit = marker then (some .break, source) else evaluateHOLFiniteState source branch := by
  by_cases leaf : bit = marker
  · simp [shapes.2.2.1, leafGuard, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_break, evalHOLExact, localVar, bitCell, bitsCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, leaf]
  · simp [shapes.2.2.1, leafGuard, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_skip, evalHOLExact, localVar, bitCell, bitsCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, leaf]

/-- Exact single-step behavior for the range-only node image. The branch is
the actual key-byte test in fixed memory, including failed reads. -/
theorem range_step_execute {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node marker key : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (image : RangeNodes origin base marker limit bits left right)
    (ready : State origin source base node marker)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (nonzero : node ≠ 0#64) (inside : node.toNat < limit) :
    evaluateHOLFiniteState source step =
      if bits node = marker then (some .break, source) else
      match keyProbe origin key (bits node) with
      | some (.val (.word choice)) =>
          (none, bind source "n" (if choice = 0#64 then right node else left node))
      | _ => (some .error, source) := by
  let entered := bind source "b" (bits node)
  have state := ready.with_bit (bits node)
  have bitCell : entered.locals.lookup (ofString "b") = some (.val (.word (bits node))) := bind_lookup_same _ _ _
  have read := ready.word_read 24 (image.bitMapped node nonzero inside) (image.bitCell node nonzero inside)
  have afterRun := after_bit_word entered (bits node) marker bitCell state.bitsCell
  rw [shapes.2.1]
  by_cases leaf : bits node = marker
  · rw [if_pos leaf] at afterRun ⊢
    have full := ScalarScope.declare_execute source entered "b" (.load .one (address 24)) (bits node) afterBit (some .break) read afterRun
    simpa only [entered, restore_bound] using full
  · rw [if_neg leaf] at afterRun ⊢
    have branchRun:=range_branch_execute image ⟨state.frame,state.nodeCell,state.baseCell⟩ nonzero inside leaf
      ((bind_lookup_other source "b" "key" (bits node) (by decide)).trans keyCell) bitCell
    have whole := afterRun.trans branchRun
    generalize observed : keyProbe origin key (bits node) = value at whole ⊢
    cases value with
    | none =>
      have full := ScalarScope.declare_execute source entered "b" (.load .one (address 24)) (bits node) afterBit (some .error) read whole
      simpa only [entered, restore_bound] using full
    | some value =>
      cases value with
      | rStruct fields =>
        have full := ScalarScope.declare_execute source entered "b" (.load .one (address 24)) (bits node) afterBit (some .error) read whole
        simpa only [entered, restore_bound] using full
      | nStruct name fields =>
        have full := ScalarScope.declare_execute source entered "b" (.load .one (address 24)) (bits node) afterBit (some .error) read whole
        simpa only [entered, restore_bound] using full
      | val payload =>
        cases payload with
        | word choice =>
          let child := if choice = 0#64 then right node else left node
          have full := ScalarScope.declare_execute source (bind entered "n" child) "b" (.load .one (address 24)) (bits node) afterBit none read whole
          rw [restore_bind_other source entered "b" "n" child (by decide), show restore source "b" entered = source from restore_bound source "b" (bits node)] at full
          exact full

/-- A continuing actual traversal step selects zero or a real child with
a strictly larger bit position. In particular, the original body cannot
export continue and cannot repeatedly traverse the same bit rank. -/
theorem step_progress {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64} {marker : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right marker.toNat) (ready : State origin source base node marker) (member : valid node)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source step=(result,post))
    (continuing : result=none ∨ result=some .continue) :
    ∃ child,result=none ∧ post=bind source "n" child ∧ (child=0#64 ∨ valid child ∧ bits node<bits child) := by
  let entered:=bind source "b" (BitVec.ofNat 64 (bits node))
  have current:=ready.with_bit (BitVec.ofNat 64 (bits node))
  have bitCell : entered.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 (bits node)))) := bind_lookup_same _ _ _
  have afterRun:=after_bit_execute_marker marker entered (bits node) (image.bitBound node member) bitCell current.bitsCell
  by_cases leaf : bits node=marker.toNat
  · rw [if_pos leaf] at afterRun
    have actual:=ScalarScope.declare_execute source entered "b" (.load .one (address 24)) (BitVec.ofNat 64 (bits node)) afterBit (some .break) (bit_read image ready member) afterRun
    rw [shapes.2.1,actual] at run
    have equal:=congrArg Prod.fst run
    dsimp only at equal
    rw [←equal] at continuing
    simp at continuing
  · rw [if_neg leaf] at afterRun
    let output:=evaluateHOLFiniteState entered branch
    have actual:=ScalarScope.declare_execute source output.2 "b" (.load .one (address 24)) (BitVec.ofNat 64 (bits node)) afterBit output.1 (bit_read image ready member) afterRun
    rw [shapes.2.1,actual] at run
    have resultEq:=congrArg Prod.fst run
    have endpoint:=congrArg Prod.snd run
    dsimp only at resultEq endpoint
    have summary:=branch_safe.summary_full entered
    unfold LocalSummary at summary
    have normal : output.1=none := by
      rcases continuing with normal|continued
      · exact resultEq.trans normal
      · exact (summary.2.2.2 (resultEq.trans continued)).elim
    have branchRun : evaluateHOLFiniteState entered branch=(none,output.2) := Prod.ext normal rfl
    obtain ⟨child,childState,ordered⟩:=branch_normal image current member (by have bound:=image.bitBound node member; omega) branchRun
    have postEq : post=bind source "n" child := by
      rw [←endpoint,childState,restore_bind_other source entered "b" "n" child (by decide)]
      rw [restore_bound]
    exact ⟨child,resultEq.symm.trans normal,postEq,ordered⟩

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.after_bit_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.step_progress

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.after_bit_execute_marker
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.after_bit_word
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.range_step_execute
