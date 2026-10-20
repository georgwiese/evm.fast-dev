import InitECandidate.Solver.Input.SerializeProgram

namespace InitECandidate.Solver.Input.Serialize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch GasBudget.MemoryWriter

private theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64) (offset : Nat)
    (binding : source.locals.lookup (ofString "out") = some (.val (.word out))) :
    eval source (address offset) = some (.val (.word (out + BitVec.ofNat 64 offset))) := by
  simp [eval,evalHOLExact,evalListHOLExact,address,localVar,binding,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- The original serializer always returns43 after its genuine memcpy and
little-endian writer. Arbitrary current contents and arbitrary scalar fields
are retained in the exact resulting memory image. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out root succ chain schema : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (outBinding : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (rootBinding : source.locals.lookup (ofString "root") = some (.val (.word root)))
    (succBinding : source.locals.lookup (ofString "succ") = some (.val (.word succ)))
    (chainBinding : source.locals.lookup (ofString "chain_id") = some (.val (.word chain)))
    (schemaBinding : source.locals.lookup (ofString "schema_id") = some (.val (.word schema)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (outArena : AllocatedBytes.Arena out 43) (rootArena : AllocatedBytes.Arena root 32)
    (outAligned : out.toNat % 8 = 0) (rootAligned : root.toNat % 8 = 0) (enough : 5 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 43#64))),emptyLocalsHOLFinite (post source out root succ chain schema)) := by
  have mask : CopyGeneral.aligned root out := Copy32.alignment_mask root out rootAligned outAligned
  have price : CopyGeneral.cost root out 32 = 1 := by
    simp [CopyGeneral.cost,mask,CopyWords.prefixCost,CopyWords.prefixIndex,CopyBytes.suffixCost]
  have arguments : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) copyArgs = some (CopyGeneral.values out root 32) := by
    simp [copyArgs,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,outBinding,rootBinding,CopyGeneral.values]
  have copyRun := CopyGeneral.call_execute source copyArgs root out 32 arguments (CopyGeneral.original_code source.code installed)
    (AllocatedBytes.copy_mapped source root out 32 domain rootArena (outArena.weaken out 43 32 (by decide))) (by decide) (by rw [price]; omega)
  let first := copied source out root
  have firstClock : first.clock = source.clock - 2 := by simp only [first,copied,CopyGeneral.callState,price]
  let second := succeeded first out succ
  have succRun : evaluateHOLFiniteState first successStore = (none,second) :=
    ByteStore.execute_word first (address 32) (localVar "succ") (out + 32#64) succ (address_read first out 32 outBinding)
      (by simp [eval,evalHOLExact,localVar,first,copied,CopyGeneral.callState,succBinding])
      (AllocatedBytes.byte_mapped first out 43 32 domain outArena (by decide))
  have chainArgsRead : evalListHOLFinite second (h := fun address => Classical.propDecidable (second.memaddrs address)) chainArgs =
      some [.val (.word (out + 33#64)),.val (.word chain)] := by
    simp [chainArgs,address,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,second,succeeded,first,copied,CopyGeneral.callState,outBinding,chainBinding,valueIsWord,valueWord,wordOpHOL,wordOp]
  have chainMapped : BytesMapped second (out + 33#64) 8 := by
    intro offset bounded
    have mapped := AllocatedBytes.byte_mapped second out 43 (33 + offset) domain outArena (by omega)
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using mapped
  let third := chained second out chain
  have chainRun : evaluateHOLFiniteState second (.call (some (none,none)) (ofString "st_le64") chainArgs) = (none,third) :=
    MemoryWordCalls.le64_execute second (out + 33#64) chain chainArgs installed chainArgsRead chainMapped (by change 3 ≤ first.clock; rw [firstClock]; omega)
  let fourth := {third with memory := ByteStore.put third.memory third.be (out + 41#64) (BitVec.ofNat 8 (schema &&& 255#64).toNat)}
  have lowMask : (255#64 : BitVec 64) &&& 18446744073709551615#64 = 255#64 := by decide
  have lowRead : eval third schemaLow = some (.val (.word (schema &&& 255#64))) := by
    simp [schemaLow,localVar,eval,evalHOLExact,evalListHOLExact,third,chained,second,succeeded,first,copied,CopyGeneral.callState,schemaBinding,valueIsWord,valueWord,wordOpHOL,wordOp]
    change schema &&& ((255#64 : BitVec 64) &&& 18446744073709551615#64) = schema &&& 255#64
    rw [lowMask]
  have lowRun : evaluateHOLFiniteState third (.storeByte (address 41) schemaLow) = (none,fourth) :=
    ByteStore.execute_word third _ _ (out + 41#64) (schema &&& 255#64) (address_read third out 41 outBinding) lowRead
      (AllocatedBytes.byte_mapped third out 43 41 domain outArena (by decide))
  have highRead : eval fourth schemaHigh = some (.val (.word (schema >>> 8))) := by
    simp [schemaHigh,localVar,eval,evalHOLExact,fourth,third,chained,second,succeeded,first,copied,CopyGeneral.callState,schemaBinding,wordShiftHOL]
  have highRun : evaluateHOLFiniteState fourth (.storeByte (address 42) schemaHigh) = (none,post source out root succ chain schema) :=
    ByteStore.execute_word fourth _ _ (out + 42#64) (schema >>> 8) (address_read fourth out 42 outBinding) highRead
      (AllocatedBytes.byte_mapped fourth out 43 42 domain outArena (by decide))
  rw [original_shape,StateSteps.next_sequence source first _ _ copyRun (by rw [firstClock]; omega),
    StateSteps.next_sequence first second _ _ succRun (Nat.le_refl _),
    StateSteps.next_sequence second third _ _ chainRun (Nat.sub_le _ _),tail,
    StateSteps.next_sequence third fourth _ _ lowRun (Nat.le_refl _),
    StateSteps.next_sequence fourth (post source out root succ chain schema) _ _ highRun (Nat.le_refl _)]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.Input.Serialize

#print axioms InitECandidate.Solver.Input.Serialize.execute
