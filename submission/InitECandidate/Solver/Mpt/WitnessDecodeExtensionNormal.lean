import InitECandidate.Solver.Mpt.WitnessDecodeRecordInputs
import InitECandidate.Solver.Mpt.FailGuardReturn

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original extension return has a nonempty compact path and
the actual initialized88-byte record. Its room, next scratch arena, physical
post-state and allowance decrease are derived from the same normal run. -/
theorem extension_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length nibbles nibbleLength leaf cursor limit : BitVec 64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source extensionBody=(some (.returned value),target)) :
    nibbleLength≠0#64 ∧ Arenas.Room .down cursor limit 88#64 ∧
      AllocatedBytes.Arena (WitnessRecord.pointer cursor) 88 ∧ Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit ∧
      (WitnessRecord.pointer cursor).toNat+88≤cursor.toNat ∧
      ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88 ∧
      value=.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))] ∧ 1≤source.clock ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {Arenas.post {source with clock:=source.clock-1} .down cursor 88#64 with
          memory:=WordWrites.write source.memory
            (LocalFields.writes (WitnessRecord.pointer cursor) (extensionFields (extensionWords array pointer length nibbles nibbleLength)))} := by
  rw [extension_shape] at normal
  obtain ⟨guardRun,recordRun⟩:=Fail.guard_return source target (.cmp .equal (field "cn" 1) (.const 0#64)) [.const 7#64]
    (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 88#64] afterExtension) value installed normal
  have passed:=(Fail.guard_normal source source _ [.const 7#64] installed guardRun).1
  have nonempty : nibbleLength≠0#64:=by
    intro zero
    have test : eval source (.cmp .equal (field "cn" 1) (.const 0#64))=some (.val (.word 1#64)):=by
      simp [eval,field,evalHOLExact,localVar,toExact,compactCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using test.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  have recordShape:=RecordKind.call_shape .extension
  change extensionAllocate=.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 88#64] afterExtension at recordShape
  rw [←recordShape] at recordRun
  have recordReady:=extension_record_ready (bind source "rec" (WitnessRecord.pointer cursor)) array pointer length nibbles nibbleLength leaf
    ((bind_lookup_other source "rec" "arr" _ (by decide)).trans arrayCell)
    ((bind_lookup_other source "rec" "p" _ (by decide)).trans pointerCell)
    ((bind_lookup_other source "rec" "n" _ (by decide)).trans lengthCell)
    (by
      have other : (bind source "rec" (WitnessRecord.pointer cursor)).locals.lookup (ofString "cn")=source.locals.lookup (ofString "cn"):=
        bind_lookup_other source "rec" "cn" _ (by decide)
      exact other.trans compactCell)
  exact ⟨nonempty,record_call_normal .extension source target cursor limit (extensionWords array pointer length nibbles nibbleLength)
    arena recordReady installed value recordRun⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_normal
