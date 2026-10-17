import InitECandidate.Solver.WitnessRadix.SplitScopeInputs

namespace InitECandidate.Solver.WitnessRadix.SplitScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem sorted_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) :
    emptyLocalsHOLFinite (sorted source context) = emptyLocalsHOLFinite (base source context) := by
  have frame := SortProgram.sorted_frame (entered source context) context.src context.dst context.keyFor
    context.position context.start context.limit context.input premises.fits premises.allocation
  simpa only [sorted, base, entered, cursorState, QueryBranch.bind, setVarHOLFinite,
    emptyLocalsHOLFinite, SortProgram.sortedMemory] using frame

theorem sorted_other {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) (query : MlS)
    (notZero : query ≠ ofString "zero_cursor") (notOne : query ≠ ofString "one_cursor") :
    (sorted source context).locals.lookup query = source.locals.lookup query := by
  have index := (sort_inputs source context premises).indexLocal
  exact (SortProgram.sorted_outside_cursors (entered source context) context.src context.dst context.keyFor
    context.position context.start context.input index query notZero notOne).trans
      (entered_other source context query notZero notOne)

theorem allocation_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) :
    SplitProgram.EntryLocals (sorted source context) context.node context.depth (BitVec.ofNat 64 context.start)
      (BitVec.ofNat 64 context.input.length) (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position)
      context.dest context.pendingStart context.pendingCount context.pendingNode := by
  have other (name : String) (nz : ofString name ≠ ofString "zero_cursor") (no : ofString name ≠ ofString "one_cursor") :=
    sorted_other source context premises (ofString name) nz no
  exact ⟨(other _ (by decide) (by decide)).trans premises.locals.nextLocal,
    (other _ (by decide) (by decide)).trans premises.locals.depthLocal,
    (other _ (by decide) (by decide)).trans premises.locals.startLocal,
    (other _ (by decide) (by decide)).trans premises.locals.countLocal,
    (other _ (by decide) (by decide)).trans premises.locals.zerosLocal,
    (other _ (by decide) (by decide)).trans premises.locals.bitLocal,
    (other _ (by decide) (by decide)).trans premises.locals.destLocal,
    (other _ (by decide) (by decide)).trans premises.locals.pendingStartLocal,
    (other _ (by decide) (by decide)).trans premises.locals.pendingCountLocal,
    (other _ (by decide) (by decide)).trans premises.locals.pendingNodeLocal⟩

theorem allocation_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) :
    SplitProgram.Mapped (sorted source context) context.node context.depth context.dest
      context.pendingStart context.pendingCount context.pendingNode := by
  have domainEq : source.memaddrs = (sorted source context).memaddrs :=
    (congrArg (fun state => state.memaddrs) (sorted_frame source context premises)).symm
  exact SplitProgram.mapped_of_field (source := source) (target := sorted source context) domainEq premises.mapped

end InitECandidate.Solver.WitnessRadix.SplitScope

#print axioms InitECandidate.Solver.WitnessRadix.SplitScope.allocation_locals
#print axioms InitECandidate.Solver.WitnessRadix.SplitScope.allocation_mapped
