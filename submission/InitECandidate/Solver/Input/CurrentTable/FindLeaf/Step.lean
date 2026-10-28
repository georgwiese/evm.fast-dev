import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Branch
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The real leaf guard stops at the256 marker; internal nodes alone enter
the original key-bit branch. -/
theorem after_bit_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bits : Nat) (small : bits≤256)
    (bitCell : source.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 bits))))
    (bitsCell : source.locals.lookup (ofString "keybits")=some (.val (.word 256#64))) :
    evaluateHOLFiniteState source afterBit=if bits=256 then (some .break,source) else evaluateHOLFiniteState source branch := by
  have number : (BitVec.ofNat 64 bits).toNat=bits := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  by_cases leaf : bits=256
  · simp [shapes.2.2.1,leafGuard,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_break,
      evalHOLExact,localVar,bitCell,bitsCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,leaf]
  · have different : BitVec.ofNat 64 bits≠256#64 := by intro equal; have same:=congrArg BitVec.toNat equal; rw [number] at same; exact leaf same
    simp [shapes.2.2.1,leafGuard,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,
      evalHOLExact,localVar,bitCell,bitsCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,different,leaf]

/-- A continuing actual traversal step selects zero or a real child with
a strictly larger bit position. In particular, the original body cannot
export continue and cannot repeatedly traverse the same bit rank. -/
theorem step_progress {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (ready : State origin source base node) (member : valid node)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source step=(result,post))
    (continuing : result=none ∨ result=some .continue) :
    ∃ child,result=none ∧ post=bind source "n" child ∧ (child=0#64 ∨ valid child ∧ bits node<bits child) := by
  let entered:=bind source "b" (BitVec.ofNat 64 (bits node))
  have current:=ready.with_bit (BitVec.ofNat 64 (bits node))
  have bitCell : entered.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 (bits node)))) := bind_lookup_same _ _ _
  have afterRun:=after_bit_execute entered (bits node) (image.bitBound node member) bitCell current.bitsCell
  by_cases leaf : bits node=256
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
