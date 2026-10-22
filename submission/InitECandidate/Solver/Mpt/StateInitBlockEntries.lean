import InitECandidate.Solver.Mpt.StateInitBlockTable
import InitECandidate.Solver.MutableTable.TableFamily

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable MutableTable.NaturalLayout

structure TableEntry where
  kind : KeyHash.Kind
  bits : Nat
  offset : Nat
  start : Nat

def TableEntry.object (entry : TableEntry) : TableFamily.Object:=
  ⟨entry.kind,fresh entry.kind entry.start (2^entry.bits),[],entry.start⟩

def entries (start : Nat) : List Action → List TableEntry
  | []=>[]
  | .table kind bits offset::rest=>⟨kind,bits,offset,start⟩::entries (freshEnd kind start (2^bits)) rest
  | .scalar ..::rest=>entries start rest

theorem entries_lower (start : Nat) (specs : List Action) (entry : TableEntry)
    (member : entry∈entries start specs) : start≤entry.start:=by
  induction specs generalizing start with
  | nil=>cases member
  | cons action rest ih=>
    cases action with
    | scalar offset value=>exact ih start member
    | table kind bits offset=>
      rcases List.mem_cons.mp member with equal|member
      · cases equal; exact Nat.le_refl _
      · exact (step_grows start (.table kind bits offset)).trans (ih _ member)

/-- Every actual constructor appears in allocation order, so all six pools
of an earlier table precede every pool of a later table. -/
theorem entries_separated (start : Nat) (specs : List Action) :
    (entries start specs).Pairwise (fun first second=>∀ left right,
      first.object.plan.base left+size first.object.kind first.object.plan left≤second.object.plan.base right):=by
  induction specs generalizing start with
  | nil=>exact .nil
  | cons action rest ih=>
    cases action with
    | scalar offset value=>exact ih start
    | table kind bits offset=>
      apply List.pairwise_cons.mpr
      constructor
      · intro later member left right
        have lower:=entries_lower (freshEnd kind start (2^bits)) rest later member
        exact ((fresh_bounds kind start (2^bits) left).2.trans lower).trans
          (fresh_bounds later.kind later.start (2^later.bits) right).1
      · exact ih _

/-- Complete empty physical models for all seven actual block tables.
Each model uses the current final cursor and its own real allocation floor. -/
theorem entries_models (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block start : Nat) (recordValid : MemoryRegion.Valid ⟨block,80⟩)
    (wellFormed : ∀ action∈specs,action.Valid) (layouts : Layouts start specs) (before : block+80≤start)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false) :
    ∀ entry∈entries start specs,TableState (walk source block start specs) entry.object.kind entry.object.plan []
      (cursor start specs) entry.start:=by
  induction specs generalizing source start with
  | nil=>intro entry impossible; cases impossible
  | cons action rest ih=>
    have currentValid:=wellFormed action List.mem_cons_self
    have tailValid : ∀ later∈rest,later.Valid:=fun later member=>wellFormed later (List.mem_cons_of_mem _ member)
    cases action with
    | scalar offset value=>
      intro entry member
      exact ih (stepState source block start (.scalar offset value)) start tailValid layouts.2 before domain little entry member
    | table kind bits offset=>
      intro entry member
      change entry∈⟨kind,bits,offset,start⟩::entries (freshEnd kind start (2^bits)) rest at member
      rw [cursor_cons]
      rcases List.mem_cons.mp member with equal|member
      · subst entry
        have table:=table_at_step source block start bits offset kind recordValid currentValid before layouts.1 domain little
        exact table_after_walk rest (stepState source block start (.table kind bits offset)) block (freshEnd kind start (2^bits))
          kind (fresh kind start (2^bits)) [] start table recordValid tailValid layouts.2
          (fun pool=>before.trans (fresh_bounds kind start (2^bits) pool).1)
      · exact ih (stepState source block start (.table kind bits offset)) (freshEnd kind start (2^bits)) tailValid layouts.2
          (before.trans (step_grows start (.table kind bits offset))) domain little entry member

/-- Indexing real constructor outputs supplies a disjoint family, with no
header, occupied-slot or future-success model supplied by the caller. -/
theorem entries_family (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block start : Nat) (recordValid : MemoryRegion.Valid ⟨block,80⟩)
    (wellFormed : ∀ action∈specs,action.Valid) (layouts : Layouts start specs) (before : block+80≤start)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false) :
    TableFamily.Model (walk source block start specs) (cursor start specs)
      (fun index : Fin (entries start specs).length=>((entries start specs)[index]).object):=by
  constructor
  · intro index
    exact entries_models specs source block start recordValid wellFormed layouts before domain little _ (List.getElem_mem index.isLt)
  · intro first second different
    have separated:=entries_separated start specs
    rcases lt_or_gt_of_ne (fun equal=>different (Fin.ext equal)) with less|greater
    · intro left right
      left
      exact (List.pairwise_iff_getElem.mp separated) first.val second.val first.isLt second.isLt less left right
    · intro left right
      right
      exact (List.pairwise_iff_getElem.mp separated) second.val first.val second.isLt first.isLt greater right left

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.entries_lower
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.entries_separated
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.entries_models
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.entries_family
