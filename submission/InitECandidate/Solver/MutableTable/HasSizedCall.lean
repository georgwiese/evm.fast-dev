import InitECandidate.Solver.MutableTable.HasSizedExecution

namespace InitECandidate.Solver.MutableTable.Has
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (table key : BitVec 64)
    (code : codeFn (ofString "htab_has")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htab_has") [.val (.word table),.val (.word key)]=some (body,callee,.one) ∧
      callee.lookup (ofString "t")=some (.val (.word table)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word table),.val (.word key)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word table),.val (.word key)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,Find.formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "htab_has") [.val (.word table),.val (.word key)]=some (body,Find.rawLocals table key,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [Find.rawLocals,show ofString "t"≠ofString "key" from by decide]
  · simp [Find.rawLocals]

/-- Real original account/storage membership caller with full scopes and
caller overhead; all nonlocal state is unchanged. -/
theorem sized_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : HashSized.Kind) (cells : Find.HeaderData source table p)
    (keyLength : p.keyLength = BitVec.ofNat 64 (HashSized.keySize kind))
    (bits : Nat) (small : bits < 64) (capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits))
    (order : List Nat) (room : order.length < 2 ^ bits)
    (binary : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ Find.usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i < 2 ^ bits, (p.keys + BitVec.ofNat 64 i * p.stride).toNat + HashSized.keySize kind < 2 ^ 64)
    (mapped : ∀ i < 2 ^ bits, ∀ offset < HashSized.keySize kind, source.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress (p.keys + BitVec.ofNat 64 i * p.stride) offset)))
    (queryFits : p.key.toNat + HashSized.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < HashSized.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress p.key offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (hasCode : source.code.lookup (ofString "htab_has") = some (formals, body, .one))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word table), .val (.word p.key)])
    (enough : Find.sizedProbePrice kind * order.length + 3 ≤ source.clock) :
    ∃ paid answer, paid ≤ Find.sizedProbePrice kind * order.length + 3 ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_has") expressions continuation) =
        (let output := evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name answer) continuation
         (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, tLocal, keyLocal⟩ := environment source.code.lookup table p.key hasCode
  let entry := callEntryStateHOLFinite source callee
  have entryCells := Find.HeaderData.with_locals source entry table p cells rfl rfl tLocal keyLocal
  obtain ⟨paid, answer, target, bound, binaryAnswer, run, frame⟩ := sized_has entry table p kind entryCells keyLength bits small capacity order room
    binary covered fits mapped queryFits queryMapped hashCode memeqCode findCode
    (by change Find.sizedProbePrice kind * order.length + 2 ≤ source.clock - 1; omega)
  have callerFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} := frame
  have actual := Input.CallNormal.pure_return_execute source target name (ofString "htab_has") expressions _ body continuation callee answer paid args called (by omega) run callerFrame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  exact ⟨paid + 1, answer, by omega, binaryAnswer, by simpa only [subtract] using actual⟩

end InitECandidate.Solver.MutableTable.Has

#print axioms InitECandidate.Solver.MutableTable.Has.environment
#print axioms InitECandidate.Solver.MutableTable.Has.sized_call
