import InitECandidate.Solver.WitnessRadix.QueryMemory
import InitECandidate.Solver.WitnessRadix.MemoryAgreement

namespace InitECandidate.Solver.WitnessRadix.QueryMemory
open Flapjack PanSemStateFiniteExact
open QueryLeaf

def leafReads (table keys vals ordinal record query : BitVec 64) : Prop :=
  query = table + 32#64 ∨ query = table + 40#64 ∨ query = vals + ordinal * 8#64 ∨
  query = record ∨ query = record + 8#64 ∨
  ∃ byte : Fin 32, query = panByteAlignHOL (width := 64) (keys + ordinal * 32#64 + BitVec.ofNat 64 byte.val)

/-- The concrete words read by an already represented tree. A builder may
write elsewhere without invalidating this subtree. -/
def reads {F : Type} (source : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64) :
    BitVec 64 → Graph.Tree → BitVec 64 → Prop
  | _, .empty, _ => False
  | root, .leaf _ _, query =>
      leafReads table keys vals (root >>> (1 : Nat))
        (MemoryBytes.wordBits (source.memory (vals + (root >>> (1 : Nat)) * 8#64))) query
  | root, .branch _ zero one, query =>
      query = root ∨ query = root + 8#64 ∨ query = root + 16#64 ∨
      reads source table keys vals (MemoryBytes.wordBits (source.memory (root + 8#64))) zero query ∨
      reads source table keys vals (MemoryBytes.wordBits (source.memory (root + 16#64))) one query

theorem leaf_cells_of_agreement {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (domain : source.memaddrs = target.memaddrs) (table keys vals ordinal record pointer length : BitVec 64)
    (agree : ∀ query, leafReads table keys vals ordinal record query → source.memory query = target.memory query)
    (cells : LeafCells source table keys vals ordinal record pointer length) :
    LeafCells target table keys vals ordinal record pointer length := by
  rcases cells with ⟨a,b,c,d,e,f,g,h,i,j⟩
  rw [domain] at a c e g h
  exact ⟨a, (agree _ (Or.inl rfl)).symm.trans b,
    c, (agree _ (Or.inr (Or.inl rfl))).symm.trans d,
    e, (agree _ (Or.inr (Or.inr (Or.inl rfl)))).symm.trans f,
    g, h, (agree _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).symm.trans i,
    (agree _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).symm.trans j⟩

/-- Local memory agreement, rather than equality of the whole heap, preserves
all actual lookup premises for a represented subtree. -/
theorem represents_of_agreement {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (table keys vals root : BitVec 64) (tree : Graph.Tree)
    (agree : ∀ query, reads source table keys vals root tree query → source.memory query = target.memory query)
    (rep : Represents source table keys vals root tree) : Represents target table keys vals root tree := by
  induction tree generalizing root with
  | empty => exact rep
  | leaf key value =>
      obtain ⟨ordinal, record, small, tag, cells, view, fits⟩ := rep
      have region : ∀ query, leafReads table keys vals (BitVec.ofNat 64 ordinal) record query →
          source.memory query = target.memory query := by
        simpa only [reads, tag, WordBits.leafTag_decode ordinal small, cells.recordWord, MemoryBytes.wordBits] using agree
      refine ⟨ordinal, record, small, tag,
        leaf_cells_of_agreement source target domain _ _ _ _ _ _ _ region cells, ?_, fits⟩
      apply MemoryBytes.byteView_of_cells source target domain endian _ _ _ view
      intro byte
      exact region _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨byte, rfl⟩)))))
  | branch position zero one ihZero ihOne =>
      obtain ⟨nonzero, even, inside, mapped, bitWord, zeroMapped, oneMapped,
        zeroRoot, oneRoot, zeroWord, oneWord, zeroRep, oneRep⟩ := rep
      have region : ∀ query, (query = root ∨ query = root + 8#64 ∨ query = root + 16#64 ∨
          reads source table keys vals zeroRoot zero query ∨ reads source table keys vals oneRoot one query) →
          source.memory query = target.memory query := by
        simpa only [reads, zeroWord, oneWord, MemoryBytes.wordBits] using agree
      rw [domain] at mapped zeroMapped oneMapped
      refine ⟨nonzero, even, inside, mapped, (region _ (Or.inl rfl)).symm.trans bitWord,
        zeroMapped, oneMapped, zeroRoot, oneRoot,
        (region _ (Or.inr (Or.inl rfl))).symm.trans zeroWord,
        (region _ (Or.inr (Or.inr (Or.inl rfl)))).symm.trans oneWord, ?_, ?_⟩
      · exact ihZero zeroRoot (fun query member => region query (Or.inr (Or.inr (Or.inr (Or.inl member))))) zeroRep
      · exact ihOne oneRoot (fun query member => region query (Or.inr (Or.inr (Or.inr (Or.inr member))))) oneRep

end InitECandidate.Solver.WitnessRadix.QueryMemory

#print axioms InitECandidate.Solver.WitnessRadix.QueryMemory.leaf_cells_of_agreement
#print axioms InitECandidate.Solver.WitnessRadix.QueryMemory.represents_of_agreement
