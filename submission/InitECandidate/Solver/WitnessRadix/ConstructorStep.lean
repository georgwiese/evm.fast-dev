import InitECandidate.Solver.WitnessRadix.ConstructorData
import InitECandidate.Solver.WitnessRadix.LoopCompose

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

theorem scratch_before_keys (layout : Layout) (valid : Valid layout) (index : Nat) (inside : index < layout.count)
    (hashScratch : BitVec 64) (srcFits : hashScratch.toNat + 32 < 2 ^ 64)
    (beforeKeys : hashScratch.toNat + 32 ≤ layout.keys.toNat) :
    ∀ read write : Fin 4, hashScratch + BitVec.ofNat 64 (8 * read.val) ≠
      layout.keys + BitVec.ofNat 64 index * 32#64 + BitVec.ofNat 64 (8 * write.val) := by
  intro read write same
  rw [hash_limb_cell] at same
  have number := congrArg BitVec.toNat same
  have left := byteAddress_toNat hashScratch (8 * read.val) (by have := read.isLt; omega)
  have right := byteAddress_toNat layout.keys (32 * index + 8 * write.val) (by
    have bound := valid.noWrap .keys; have room := valid.room; have := write.isLt
    change layout.keys.toNat + 32 * layout.capacity < 2 ^ 64 at bound
    omega)
  change (byteAddress hashScratch _).toNat = (byteAddress layout.keys _).toNat at number
  rw [left, right] at number
  have := read.isLt
  omega

/-- One whole real after-hash constructor iteration establishes the next
initialized prefix from scratch bytes and the shared allocation layout.
Individual mapped-store and old-entry preservation assumptions are derived. -/
theorem after_hash_step {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (index : Nat) (inside : index < layout.count)
    (locals : Locals source layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index))
    (prefixData : Prefix source layout keyFor index) (fixedData : FixedData source layout sliceFor)
    (hashScratch : BitVec 64)
    (global : source.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word hashScratch)))
    (code : source.code.lookup (ofString "memcpy") = some (Copy32.formals, Copy32.body, .one))
    (srcAligned : hashScratch.toNat % 8 = 0) (srcFits : hashScratch.toNat + 32 < 2 ^ 64)
    (beforeKeys : hashScratch.toNat + 32 ≤ layout.keys.toNat)
    (digest : MemoryBytes.ByteView source hashScratch (keyFor (BitVec.ofNat 64 index)))
    (little : source.be = false) (enough : 2 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source afterHash = (none, target) ∧
      Prefix target layout keyFor (index + 1) ∧ FixedData target layout sliceFor ∧ Mapped target layout ∧
      Locals target layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 (index + 1)) ∧
      control target = control source ∧ target.clock = source.clock - 2 ∧
      (∀ name : MlS, ofString "i" ≠ name → target.locals.lookup name = source.locals.lookup name) := by
  classical
  let words := MemoryBytes.wordsOf source hashScratch
  have view := MemoryBytes.byteView_words source hashScratch _ srcAligned srcFits digest
  have currentKey := MemoryBytes.byteView_unique source hashScratch (WordKeys.key words) _
    (MemoryBytes.wordView_bytes source hashScratch words srcAligned srcFits little view) digest
  have hashMapped (limb : Fin 4) : source.memaddrs
      (layout.keys + BitVec.ofNat 64 index * 32#64 + BitVec.ofNat 64 (8 * limb.val)) := by
    rw [hash_limb_cell]
    apply mapped .keys _ (by omega)
    change 32 * index + 8 * limb.val + 8 ≤ 32 * layout.capacity
    have := limb.isLt; have room := valid.room; omega
  have valsMapped : source.memaddrs (layout.vals + BitVec.ofNat 64 index * 8#64) := by
    rw [vals_cell]
    apply mapped .vals _ (by omega)
    change 8 * index + 8 ≤ 8 * layout.capacity
    have room := valid.room; omega
  have orderMapped : source.memaddrs (layout.primary + BitVec.ofNat 64 index * 8#64) := by
    rw [primary_cell]
    apply mapped .primary _ (by omega)
    change 8 * index + 8 ≤ 8 * layout.capacity
    have room := valid.room; omega
  have run := after_hash_execute source layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index)
    hashScratch words locals global code srcAligned (hash_aligned layout valid index inside) view hashMapped
    (scratch_before_keys layout valid index inside hashScratch srcFits beforeKeys) valsMapped orderMapped enough
  let target := suffixState source layout index words
  have others (name : MlS) (different : ofString "i" ≠ name) : target.locals.lookup name = source.locals.lookup name := by
    simp [target, suffixState, storesPost, copyPost, QueryBranch.bind, setVarHOLFinite,
      HolFiniteMapExact.update, FUPDATE, different]
  refine ⟨target, run, prefix_step source layout valid mapped keyFor index inside words prefixData little currentKey,
    suffix_fixed_data source layout valid sliceFor index inside words fixedData, mapped, ?_, rfl, rfl, others⟩
  refine ⟨(others _ (by decide)).trans locals.keysLocal, (others _ (by decide)).trans locals.valsLocal,
    (others _ (by decide)).trans locals.orderLocal, (others _ (by decide)).trans locals.recordsLocal, ?_⟩
  change (bind _ "i" _).locals.lookup (ofString "i") = _
  rw [bind_lookup_same]
  rw [BitVec.ofNat_add_ofNat index 1]

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.scratch_before_keys
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.after_hash_step
