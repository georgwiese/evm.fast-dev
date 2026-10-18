import InitECandidate.Solver.GasBudget.MessageFieldFrame
import InitECandidate.Solver.MutableTable.TableStateFrame
import InitECandidate.Solver.MutableTable.MemoryRegionWord
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.GasBudget.MessageField
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

def putState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start offset : Nat) (value : BitVec 64) :=
  {source with memory := StoreWord.put source.memory (BitVec.ofNat 64 start + BitVec.ofNat 64 offset) value}

theorem scalar_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start offset : Nat) (value : BitVec 64) (expression : ExpHOL 64)
    (region : MemoryRegion.Valid ⟨start, 176⟩) (inside : offset + 8 ≤ 176) (aligned : offset % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))))
    (read : eval source expression = some (.val (.word value))) :
    evaluateHOLFiniteState source (store offset expression) = (none, putState source start offset value) := by
  have addressRead : eval source (addConst (localVar "m") (BitVec.ofNat 64 offset)) =
      some (.val (.word (BitVec.ofNat 64 start + BitVec.ofNat 64 offset))) := by
    simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, messageLocal, valueIsWord, valueWord, wordOpHOL, wordOp]
  have mapped : source.memaddrs (BitVec.ofNat 64 start + BitVec.ofNat 64 offset) := by
    rw [domain]
    exact MemoryRegion.word_mapped ⟨start, 176⟩ region offset inside aligned
  exact StoreWord.execute source _ expression _ value addressRead read mapped

theorem scalar_outside (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start offset : Nat) (value query : BitVec 64)
    (region : MemoryRegion.Valid ⟨start, 176⟩) (inside : offset < 176)
    (outside : query.toNat < start ∨ start + 176 ≤ query.toNat) :
    (putState source start offset value).memory query = source.memory query := by
  have different : query ≠ BitVec.ofNat 64 start + BitVec.ofNat 64 offset := by
    intro same
    have numeric := congrArg BitVec.toNat same
    rw [field_number start offset region (by omega)] at numeric
    omega
  exact if_neg different

theorem scalar_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start offset field : Nat) (value : BitVec 64)
    (different : field ≠ offset) (smallField : field < 2 ^ 64) (smallOffset : offset < 2 ^ 64) :
    (putState source start offset value).memory (BitVec.ofNat 64 start + BitVec.ofNat 64 field) =
      source.memory (BitVec.ofNat 64 start + BitVec.ofNat 64 field) := by
  have away : BitVec.ofNat 64 start + BitVec.ofNat 64 field ≠ BitVec.ofNat 64 start + BitVec.ofNat 64 offset := by
    intro same
    have words := (BitVec.add_right_inj (BitVec.ofNat 64 start)).mp same
    have numeric := congrArg BitVec.toNat words
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt smallField, Nat.mod_eq_of_lt smallOffset] at numeric
    exact different numeric
  exact if_neg away

theorem scalar_table (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor start offset : Nat) (value : BitVec 64)
    (table : TableState source kind plan slots cursor floor) (region : MemoryRegion.Valid ⟨start, 176⟩)
    (inside : offset < 176) (later : ∀ pool, start + 176 ≤ plan.base pool) :
    TableState (putState source start offset value) kind plan slots cursor floor := by
  apply TableState.of_pool_frame (target := putState source start offset value) table rfl rfl rfl
  intro pool index insidePool
  apply scalar_outside source start offset value _ region inside
  right
  rw [NaturalLayout.number kind plan table.valid pool index (by omega)]
  have lower := later pool
  omega

end InitECandidate.Solver.GasBudget.MessageField

#print axioms InitECandidate.Solver.GasBudget.MessageField.scalar_execute
#print axioms InitECandidate.Solver.GasBudget.MessageField.scalar_outside
#print axioms InitECandidate.Solver.GasBudget.MessageField.scalar_other
#print axioms InitECandidate.Solver.GasBudget.MessageField.scalar_table
