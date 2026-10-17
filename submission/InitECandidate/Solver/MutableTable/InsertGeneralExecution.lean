import InitECandidate.Solver.MutableTable.InsertGeneralEntry

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Complete unchanged htab_insert_raw for every original key width. Header
reads, hash, first-empty scan, arbitrary-alignment copy, all bookkeeping
stores, return and scopes are derived. Entry/ownership/count conditions remain
explicit; this is a source-clock result, not a target runtime bound. -/
theorem general_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count value : BitVec 64) (bits : Nat) (items : List Nat)
    (data : GeneralData source table p kind vals order position count bits items)
    (tLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word p.key)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (enough : items.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ paid index target, paid ≤ items.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ∧
      index.toNat < p.capacity.toNat ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite
        {source with
          memory := (generalResultMemory source.memory source.be (KeyHash.keySize kind) p table vals order position index count value)
          clock := source.clock - paid} ∧ Find.usedByte source p index = some 0 := by
  classical
  have cells := Find.HeaderData.with_locals source source table p data.header rfl rfl tLocal keyLocal
  let headers := headerState source p order position
  have distinct : ([ofString "order_pos", ofString "order", ofString "used", ofString "keys", ofString "stride", ofString "klen", ofString "cap", ofString "key"] : List MlS).Nodup := by decide
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true, List.nodup_nil] at distinct
  have keyH : headers.locals.lookup (ofString "key") = some (.val (.word p.key)) := by
    have original := keyLocal
    simp_all [headers, headerState, Find.headerState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have klenH : headers.locals.lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) := by
    have keyLength := data.keyLength
    simp_all [headers, headerState, Find.headerState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have args : evalListHOLFinite headers (h := fun address => Classical.propDecidable (headers.memaddrs address))
      [localVar "key", localVar "klen"] = some (KeyHash.values kind p.key) := by
    simp [KeyHash.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, keyH, klenH]
  obtain ⟨hash, hashRun⟩ := KeyHash.call_of_mapped headers kind p.key "h" [localVar "key", localVar "klen"] afterHash args
    data.hashCode data.queryFits data.queryMapped data.little (by change KeyHash.hashPrice kind ≤ source.clock; omega)
  let index := hash &&& (p.capacity - 1#64)
  let start := hash.toNat % (2 ^ bits)
  let hashEntered := bind {headers with clock := source.clock - KeyHash.hashPrice kind} "h" hash
  let entered := WitnessRadix.QueryBranch.bind hashEntered "i" index
  have indexEq : index = Find.pathIndex bits start 0 := Find.masked_start p hash bits data.small data.capacity
  have startInside : start < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos bits)
  have previous := prepared_locals source p order position hash index keyLocal
  have locals : Find.Locals entered p (Find.pathIndex bits start 0) := by
    rw [← indexEq]
    exact ⟨previous.cap, previous.klen, previous.stride, previous.keys, previous.used, previous.key, previous.index⟩
  obtain ⟨stop, scanned, stopBound, scanRun, scanFrame, scanLocals, empty, otherLocals⟩ := scan_count_bound entered p bits start data.small startInside
    data.capacity items data.room data.binary data.covered locals (by change items.length ≤ source.clock - KeyHash.hashPrice kind; omega)
  let slot := Find.pathIndex bits start stop
  have emptySource : Find.usedByte source p slot = some 0 := empty
  have capNumber : p.capacity.toNat = 2 ^ bits := by
    rw [data.capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) data.small)]
  have slotInside : slot.toNat < p.capacity.toNat := by
    rw [Find.path_number bits start stop data.small, capNumber]
    exact Nat.mod_lt _ (Nat.two_pow_pos bits)
  have scanMemory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) scanFrame
  have scanDomain := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) scanFrame
  have scanEndian := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) scanFrame
  have scanCode := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) scanFrame
  have scanClock := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) scanFrame
  change scanned.memory = source.memory at scanMemory
  change scanned.memaddrs = source.memaddrs at scanDomain
  change scanned.be = source.be at scanEndian
  change scanned.code = source.code at scanCode
  change scanned.clock = source.clock - KeyHash.hashPrice kind - stop at scanClock
  have slotData : SlotData scanned.memaddrs p table vals order position count slot (KeyHash.keySize kind) := by
    rw [scanDomain]
    exact data.slots slot slotInside
  have valsMap : scanned.memaddrs (table + 40#64) := by rw [scanDomain]; exact data.valsMapped
  have valsRead : scanned.memory (table + 40#64) = .word vals := by rw [scanMemory]; exact data.valsCell
  have countMap : scanned.memaddrs (table + 24#64) := by rw [scanDomain]; exact data.countMapped
  have countRead : scanned.memory (table + 24#64) = .word count := by rw [scanMemory]; exact data.countCell
  have queryMap : ∀ offset < KeyHash.keySize kind, scanned.memaddrs (panByteAlignHOL (width := 64) (byteAddress p.key offset)) := by
    rw [scanDomain]
    exact data.queryMapped
  have code : scanned.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one) := by rw [scanCode]; exact data.copyCode
  have little : scanned.be = false := scanEndian.trans data.little
  have previousData := prepared_data source p table order position hash index value tLocal valueLocal
  have tEntered : entered.locals.lookup (ofString "t") = some (.val (.word table)) := previousData.1
  have valueEntered : entered.locals.lookup (ofString "value") = some (.val (.word value)) := previousData.2.1
  have orderEntered : entered.locals.lookup (ofString "order") = some (.val (.word order)) := previousData.2.2.1
  have positionEntered : entered.locals.lookup (ofString "order_pos") = some (.val (.word position)) := previousData.2.2.2
  obtain ⟨copyPaid, post, copyBound, tailRun, tailFrame⟩ := general_tail_execute scanned p table vals order position slot count value scanLocals
    (KeyHash.keySize kind) (KeyHash.key_size_small kind) data.keyLength
    ((otherLocals _ (by decide)).trans tEntered) ((otherLocals _ (by decide)).trans valueEntered)
    ((otherLocals _ (by decide)).trans orderEntered) ((otherLocals _ (by decide)).trans positionEntered)
    valsMap valsRead slotData.valueMapped slotData.usedMapped slotData.orderMapped slotData.positionMapped countMap countRead
    slotData.awayValue slotData.awayUsed slotData.awayValsHeader slotData.awayCountHeader little code data.queryFits slotData.fits queryMap slotData.mapped
    (by rw [scanClock]; omega)
  have restRun : evaluateHOLFiniteState entered afterIndex = (some (.returned (.val (.word 0#64))), post) := by
    rw [afterIndex, StateSteps.next_sequence entered scanned loop afterLoop scanRun (by change scanned.clock ≤ source.clock - KeyHash.hashPrice kind; omega)]
    exact tailRun
  have iRun : evaluateHOLFiniteState hashEntered afterHash = (some (.returned (.val (.word 0#64))), restore hashEntered "i" post) :=
    Input.ScalarScope.declare_execute hashEntered post "i" Find.initialIndex index afterIndex _ (initial_index_read source p order position hash) restRun
  change evaluateHOLFiniteState headers (.decCall (ofString "h") .one (ofString "htab_hash") [localVar "key", localVar "klen"] afterHash) =
    (let output := evaluateHOLFiniteState hashEntered afterHash; (output.1, restore headers "h" output.2)) at hashRun
  rw [iRun] at hashRun
  obtain ⟨restoreStack, setup⟩ := header_executes source table p order position cells data.orderMapped data.orderCell data.positionMapped data.positionCell
  have prefixRun := ProgramPrefix.execute setup (.decCall (ofString "h") .one (ofString "htab_hash") [localVar "key", localVar "klen"] afterHash)
  let paid := KeyHash.hashPrice kind + stop + copyPaid
  let finalMemory := generalResultMemory source.memory source.be (KeyHash.keySize kind) p table vals order position slot count value
  have copyMemory : generalResultMemory scanned.memory scanned.be (KeyHash.keySize kind) p table vals order position slot count value = finalMemory := by
    rw [scanMemory, scanEndian]
  have finalClock : scanned.clock - copyPaid = source.clock - paid := by dsimp only [paid]; rw [scanClock]; omega
  have postFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - paid} := by
    rw [tailFrame, copyMemory, finalClock]
    exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := finalMemory, clock := source.clock - paid}) scanFrame
  let target := restoreStack (restore headers "h" (restore hashEntered "i" post))
  refine ⟨paid, slot, target, by dsimp only [paid]; omega, slotInside, ?_, ?_, emptySource⟩
  · rw [body_shape, prefixRun, hashRun]
  · rw [show emptyLocalsHOLFinite target = emptyLocalsHOLFinite (restore headers "h" (restore hashEntered "i" post)) from ProgramPrefix.restoration_frame setup _]
    exact postFrame

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.general_execute
