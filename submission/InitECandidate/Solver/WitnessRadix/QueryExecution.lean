import InitECandidate.Solver.WitnessRadix.QueryLoop

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.WitnessRadix.QueryExecution
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch QueryLeaf

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

def valueOf : Option Graph.Slice → ValueHOL 64
  | none => QueryEmpty.zeros
  | some value => found value.1 value.2

def Correct (result : Option (PanSemResultExact 64)) (answer : Option Graph.Slice) : Prop :=
  result = some (.returned (valueOf answer)) ∨ (result = none ∧ answer = none)

/-- Actual HOL lookup loop from a represented immutable tree. At most one
clock per branch and six for the terminal leaf are consumed. -/
theorem loop_execute {F : Type} (tree : Graph.Tree) (source : PanSemStateFiniteExact 64 F)
    (table keys vals hash root : BitVec 64) (query : ByteKeys.Key)
    (rep : QueryMemory.Represents source table keys vals root tree)
    (node : source.locals.lookup (ofString "node") = some (.val (.word root)))
    (db : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (hashLocal : source.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (view : MemoryBytes.ByteView source hash query)
    (fits : hash.toNat + 32 < 2 ^ 64) (little : source.be = false)
    (enough : compactHeight tree + 6 ≤ source.clock) :
    ∃ paid, paid ≤ compactHeight tree + 6 ∧
      Correct (evaluateHOLFiniteState source QueryLoop.loop).1 (fastLookup ByteKeys.bit query tree) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source QueryLoop.loop).2 =
        emptyLocalsHOLFinite { source with clock := source.clock - paid } := by
  classical
  induction tree generalizing source root with
  | empty =>
      change root = 0#64 at rep
      subst root
      rw [QueryLoop.empty source node]
      refine ⟨0, by simp [compactHeight], Or.inr ⟨rfl, rfl⟩, ?_⟩
      simp
  | leaf key value =>
      obtain ⟨ordinal, record, small, tag, cells, storedView, storedFits⟩ := rep
      subst root
      let entry := decClockHOLFinite source
      have cells' := QueryMemory.cells_of_fields source entry rfl rfl _ _ _ _ _ _ _ cells
      have stored' := MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ storedView
      have view' := MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ view
      obtain ⟨paid, bound, result, frame⟩ := leaf_return entry table keys vals hash record value.1 value.2
        ordinal key query small node db hashLocal code cells' stored' view' storedFits fits little
        (by dsimp [entry, decClockHOLFinite]; simp only [compactHeight] at enough; omega)
      have bodyResult := leaf_iteration entry (WordBits.leafTag ordinal)
        (if key = query then found value.1 value.2 else QueryEmpty.zeros) paid node
        (WordBits.leafTag_odd ordinal small) result frame
      have loopResult := QueryLoop.returned source (WordBits.leafTag ordinal)
        (if key = query then found value.1 value.2 else QueryEmpty.zeros) paid node
        (WordBits.leafTag_nonzero ordinal small)
        (by simp only [compactHeight] at enough; omega) bodyResult.1 bodyResult.2
      refine ⟨paid + 1, by simp only [compactHeight]; omega, Or.inl ?_, loopResult.2⟩
      rw [loopResult.1]
      by_cases same : key = query <;> simp [fastLookup, valueOf, same]
  | branch position zero one ihZero ihOne =>
      obtain ⟨nonzero, even, inside, bitMapped, bitWord, zeroMapped, oneMapped,
        zeroRoot, oneRoot, zeroWord, oneWord, zeroRep, oneRep⟩ := rep
      let entry := decClockHOLFinite source
      have view' := MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ view
      obtain ⟨byte, loaded, digitEq⟩ := QueryMemory.query_digit entry hash query position inside view'
      let digit := WordBits.digit (BitVec.ofNat 8 byte.toNat) (BitVec.ofNat 64 position)
      let child := if ByteKeys.bit query position then oneRoot else zeroRoot
      let selected := if ByteKeys.bit query position then one else zero
      have choose : (if digit = 0#64 then 8#64 else 16#64) =
          (if ByteKeys.bit query position then 16#64 else 8#64) := by
        cases bit : ByteKeys.bit query position with
        | false => change (if digit = 0#64 then 8#64 else 16#64) = 8#64; rw [if_pos (digitEq.mpr bit)]
        | true =>
            have neq : digit ≠ 0#64 := by intro eq; have := digitEq.mp eq; simp [bit] at this
            simp only [bit, ↓reduceIte, if_neg neq]
      have childMapped : entry.memaddrs (root + if digit = 0#64 then 8#64 else 16#64) := by
        rw [choose]
        cases bit : ByteKeys.bit query position
        · exact zeroMapped
        · exact oneMapped
      have childWord : entry.memory (root + if digit = 0#64 then 8#64 else 16#64) = .word child := by
        rw [choose]
        cases bit : ByteKeys.bit query position <;> simp only [child, bit, ↓reduceIte]
        · exact zeroWord
        · exact oneWord
      have body := branch_iteration entry root (BitVec.ofNat 64 position) hash child byte
        node hashLocal even bitMapped bitWord loaded childMapped childWord
      let next := bind entry "node" child
      have dbNode : ofString "node" ≠ ofString "db" := by decide
      have hashNode : ofString "node" ≠ ofString "hash" := by decide
      have node' : next.locals.lookup (ofString "node") = some (.val (.word child)) := by
        simp [next, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
      have db' : next.locals.lookup (ofString "db") = some (.val (.word table)) := by
        simp [next, entry, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite,
          HolFiniteMapExact.update, FUPDATE, dbNode, db]
      have hash' : next.locals.lookup (ofString "hash") = some (.val (.word hash)) := by
        simp [next, entry, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite,
          HolFiniteMapExact.update, FUPDATE, hashNode, hashLocal]
      have selectedRep : QueryMemory.Represents next table keys vals child selected := by
        apply QueryMemory.represents_of_fields source next rfl rfl rfl
        cases bit : ByteKeys.bit query position <;> simp only [child, selected, bit, ↓reduceIte]
        · exact zeroRep
        · exact oneRep
      have selectedHeight : compactHeight selected ≤ max (compactHeight zero) (compactHeight one) := by
        dsimp only [selected]
        split <;> omega
      have nextEnough : compactHeight selected + 6 ≤ next.clock := by
        change compactHeight selected + 6 ≤ source.clock - 1
        simp only [compactHeight] at enough
        omega
      have nextView := MemoryBytes.byteView_of_fields source next rfl rfl rfl _ _ view
      have nextRun : ∃ paid, paid ≤ compactHeight selected + 6 ∧
          Correct (evaluateHOLFiniteState next QueryLoop.loop).1 (fastLookup ByteKeys.bit query selected) ∧
          emptyLocalsHOLFinite (evaluateHOLFiniteState next QueryLoop.loop).2 =
            emptyLocalsHOLFinite { next with clock := next.clock - paid } := by
        cases bit : ByteKeys.bit query position with
        | false =>
            simp only [selected, bit, Bool.false_eq_true, ↓reduceIte] at selectedRep nextEnough ⊢
            exact ihZero next child selectedRep node' db' hash' code nextView little nextEnough
        | true =>
            simp only [selected, bit, ↓reduceIte] at selectedRep nextEnough ⊢
            exact ihOne next child selectedRep node' db' hash' code nextView little nextEnough
      obtain ⟨paid, bound, answer, frame⟩ := nextRun
      have unfolded := QueryLoop.branch source root child node nonzero
        (by simp only [compactHeight] at enough; omega) body
      refine ⟨paid + 1, ?_, ?_, ?_⟩
      · simp only [compactHeight]
        omega
      · rw [unfolded]
        change Correct (evaluateHOLFiniteState next QueryLoop.loop).1 _
        cases bit : ByteKeys.bit query position <;> simpa [fastLookup, selected, bit] using answer
      · rw [unfolded]
        have clockSub : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
        simpa only [next, entry, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite,
          emptyLocalsHOLFinite, clockSub] using frame

end InitECandidate.Solver.WitnessRadix.QueryExecution

#print axioms InitECandidate.Solver.WitnessRadix.QueryExecution.loop_execute
