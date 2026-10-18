import InitECandidate.Solver.MutableTable.DeleteScanFinish

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def headerState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) :=
  bind (bind (bind (bind (bind (bind (bind source "klen" (BitVec.ofNat 64 (KeyHash.keySize kind)))
    "stride" (BitVec.ofNat 64 (NaturalLayout.stride kind))) "keys" (cell plan .keys 0)) "vals" (cell plan .values 0))
    "used" (cell plan .used 0)) "order" (cell plan .order 0)) "order_pos" (cell plan .position 0)

def headerValues (kind : KeyHash.Kind) (plan : Plan) : List (String × BitVec 64) :=
  [("klen", BitVec.ofNat 64 (KeyHash.keySize kind)), ("stride", BitVec.ofNat 64 (NaturalLayout.stride kind)),
   ("keys", cell plan .keys 0), ("vals", cell plan .values 0), ("used", cell plan .used 0),
   ("order", cell plan .order 0), ("order_pos", cell plan .position 0)]

theorem header_lookup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (name : String) (word : BitVec 64) (member : (name, word) ∈ headerValues kind plan) :
    (headerState source kind plan).locals.lookup (ofString name) = some (.val (.word word)) := by
  simp only [headerValues, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [headerState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]

theorem header_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (name : String)
    (away : ∀ saved ∈ (["klen", "stride", "keys", "vals", "used", "order", "order_pos"] : List String), ofString saved ≠ ofString name) :
    (headerState source kind plan).locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
  exact (bind_lookup_other _ "order_pos" name _ (away _ (by simp))).trans
    ((bind_lookup_other _ "order" name _ (away _ (by simp))).trans
    ((bind_lookup_other _ "used" name _ (away _ (by simp))).trans
    ((bind_lookup_other _ "vals" name _ (away _ (by simp))).trans
    ((bind_lookup_other _ "keys" name _ (away _ (by simp))).trans
    ((bind_lookup_other _ "stride" name _ (away _ (by simp))).trans
    (bind_lookup_other _ "klen" name _ (away _ (by simp))))))))

/-- All seven literal original deletion header declarations, retaining their
real restoration stack and deriving every read from the physical header. -/
theorem header_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : BitVec 64)
    (header : MemoryModel.Header source.memory kind plan count)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0)))) :
    ∃ restoreStack, Executes source headerActions (headerState source kind plan) restoreStack := by
  let sl := bind source "klen" (BitVec.ofNat 64 (KeyHash.keySize kind))
  let ss := bind sl "stride" (BitVec.ofNat 64 (NaturalLayout.stride kind))
  let sk := bind ss "keys" (cell plan .keys 0)
  let sv := bind sk "vals" (cell plan .values 0)
  let su := bind sv "used" (cell plan .used 0)
  let so := bind su "order" (cell plan .order 0)
  have tL : sl.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "klen" "t" _ (by decide)).trans tableLocal
  have tS : ss.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "stride" "t" _ (by decide)).trans tL
  have tK : sk.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "keys" "t" _ (by decide)).trans tS
  have tV : sv.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "vals" "t" _ (by decide)).trans tK
  have tU : su.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "used" "t" _ (by decide)).trans tV
  have tO : so.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "order" "t" _ (by decide)).trans tU
  have read (target : PanSemStateFiniteExact 64 Guest.HostMemory) (t : target.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
      (sameMemory : target.memory = source.memory) (sameDomain : target.memaddrs = source.memaddrs)
      (offset : Nat) (inside : offset < 72) (aligned : offset % 8 = 0) (word : BitVec 64)
      (member : (offset, word) ∈ MemoryModel.headerEntries kind plan count) :
      eval target (Find.tableLoad (BitVec.ofNat 64 offset)) = some (.val (.word word)) := by
    apply Find.table_read target _ _ word t
    · rw [sameDomain, domain, constant_cell]
      exact mapped kind plan valid .header offset inside aligned
    · rw [sameMemory, constant_cell]
      exact header offset word member
  exact ⟨_, .declare _ (read source tableLocal rfl rfl 0 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries]))
    (.declare _ (read sl tL rfl rfl 8 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries]))
    (.declare _ (read ss tS rfl rfl 32 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries]))
    (.declare _ (read sk tK rfl rfl 40 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries]))
    (.declare _ (read sv tV rfl rfl 48 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries]))
    (.declare _ (read su tU rfl rfl 56 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries]))
    (.declare _ (read so tO rfl rfl 64 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])) (.done _)))))))⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.header_lookup
#print axioms InitECandidate.Solver.MutableTable.Delete.header_other
#print axioms InitECandidate.Solver.MutableTable.Delete.header_executes
