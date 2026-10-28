import InitECandidate.Solver.Input.CurrentHash.PayloadStaticStep
import InitECandidate.Solver.Input.CurrentHash.FixedRecordMemorySteps

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Share the current fixed-field memory proof while retaining the literal
payload argument expressions, including raw+0. -/
theorem step_frame (field : Field) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (raw ch cursor zeros query : BitVec 64) (valid : field.Valid) (context : MerkleMemory.Context source cursor zeros query)
    (pointer : source.locals.lookup (ofString "raw")=some (.val (.word raw))) (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (inputArena : AllocatedBytes.Arena (raw+BitVec.ofNat 64 field.inputOffset) field.length)
    (outArena : AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*field.field)) 32)
    (outAligned : (ch+BitVec.ofNat 64 (32*field.field)).toNat%8=0) (outAway : CopyGeneral.Away (ch+BitVec.ofNat 64 (32*field.field)) query 32)
    (actual : evaluateHOLFiniteState source (step field)=(none,post)) : post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query :=
  field.frame source post "raw" raw ch cursor zeros query valid context pointer chunks inputArena outArena outAligned outAway
    ((argument_equivalence field source raw ch pointer chunks).symm.trans actual)

/-- A real normal prefix supplies the next memory/context facts. No later
field return, allocation room or output contents are assumed. -/
theorem program_frame (fields : List Field) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (raw ch cursor zeros query : BitVec 64)
    (valid : ∀ field∈fields,field.Valid) (context : MerkleMemory.Context source cursor zeros query)
    (pointer : source.locals.lookup (ofString "raw")=some (.val (.word raw))) (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (geometry : ∀ field∈fields,AllocatedBytes.Arena (raw+BitVec.ofNat 64 field.inputOffset) field.length ∧
      AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*field.field)) 32 ∧ (ch+BitVec.ofNat 64 (32*field.field)).toNat%8=0 ∧ CopyGeneral.Away (ch+BitVec.ofNat 64 (32*field.field)) query 32)
    (actual : evaluateHOLFiniteState source (program fields .skip)=(none,post)) : post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query := by
  induction fields generalizing source with
  | nil=>
    change evaluateHOLFiniteState source .skip=(none,post) at actual
    rw [evaluateHOLFiniteState_skip] at actual
    have endpoint : post=source := (congrArg Prod.snd actual).symm
    rw [endpoint]
    exact ⟨rfl,context⟩
  | cons field rest ih=>
    change evaluateHOLFiniteState source (.seq (step field) (program rest .skip))=(none,post) at actual
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_none source post _ _ actual
    have shape := geometry field (by simp)
    have front := step_frame field source middle raw ch cursor zeros query (valid field (by simp)) context pointer chunks shape.1 shape.2.1 shape.2.2.1 shape.2.2.2 normal
    have kept (name : String) := CallNormal.ignored_lookup source middle (ofString name) field.function (arguments field) normal
    have back := ih middle (by intro item present; exact valid item (by simp [present])) front.2 ((kept "raw").trans pointer) ((kept "ch").trans chunks)
      (by intro item present; exact geometry item (by simp [present])) remaining
    exact ⟨back.1.trans front.1,back.2⟩

theorem fields_geometry (raw ch query : BitVec 64) (field : Field) (member : field∈firstFields++middleFields++lastFields)
    (rawArena : AllocatedBytes.Arena raw 540) (chArena : AllocatedBytes.Arena ch 608) (aligned : ch.toNat%8=0) (below : query.toNat<ch.toNat) :
    AllocatedBytes.Arena (raw+BitVec.ofNat 64 field.inputOffset) field.length ∧ AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*field.field)) 32 ∧
      (ch+BitVec.ofNat 64 (32*field.field)).toNat%8=0 ∧ CopyGeneral.Away (ch+BitVec.ofNat 64 (32*field.field)) query 32 := by
  have bounds := fields_valid field member
  have fits : ch.toNat+32*field.field<2^64 := by have h:=chArena.upper; omega
  have slotAligned : (ch+BitVec.ofNat 64 (32*field.field)).toNat%8=0 := byteAddress_aligned ch (32*field.field) aligned (by omega) fits
  have output : AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*field.field)) 32 := AllocatedBytes.Arena.subrange ch 608 (32*field.field) 32 chArena (by omega)
  refine ⟨AllocatedBytes.Arena.subrange raw 540 field.inputOffset field.length rawArena bounds.2.1,output,slotAligned,?_⟩
  apply CopyGeneral.Away.after _ _ 32 slotAligned (by have h:=output.upper; omega)
  change query.toNat<(byteAddress ch (32*field.field)).toNat
  rw [byteAddress_toNat ch (32*field.field) fits]
  omega

theorem program_local (fields : List Field) (name : MlS) : LocalPrefix name (program fields .skip) := by
  induction fields with
  | nil=>exact .skip
  | cons field rest ih=>exact .seq (step_local field name) ih

theorem program_globals (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (fields : List Field) :
    GlobalEffects.Preserves (key cursor) code (program fields .skip) := by
  induction fields with
  | nil=>exact GlobalEffects.skip _ _
  | cons field rest ih=>
    apply GlobalEffects.sequence _ _ _ _ _ ih
    change GlobalEffects.Preserves _ code (.call (some (none,none)) field.function (arguments field))
    rw [field.function_name]
    exact Effects.call_preserves cursor code installed field.routine (some none) (arguments field)

/-- Reuse the complete finite pipeline proof for the literal payload syntax.
The callback gets only the same actually completed prefix. -/
theorem program_memory (fields : List Field) (tail : ProgHOL 64) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (raw ch cursor zeros query : BitVec 64) (valid : ∀ field∈fields,field.Valid) (context : MerkleMemory.Context source cursor zeros query)
    (pointer : source.locals.lookup (ofString "raw")=some (.val (.word raw))) (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (geometry : ∀ field∈fields,AllocatedBytes.Arena (raw+BitVec.ofNat 64 field.inputOffset) field.length ∧
      AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*field.field)) 32 ∧ (ch+BitVec.ofNat 64 (32*field.field)).toNat%8=0 ∧ CopyGeneral.Away (ch+BitVec.ofNat 64 (32*field.field)) query 32)
    (tailFrame : ∀ middle,MerkleMemory.Context middle cursor zeros query → evaluateHOLFiniteState source (program fields .skip)=(none,middle) → ∀ value,
      evaluateHOLFiniteState middle tail=(some (.returned value),post) → post.memory query=middle.memory query)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source (program fields tail)=(some (.returned value),post)) : post.memory query=source.memory query :=
  FixedRecord.pipeline_memory fields "raw" tail valid source post raw ch cursor zeros query context pointer chunks geometry
    (by intro middle ready normal observed returned
        exact tailFrame middle ready ((program_equivalence fields source raw ch .skip pointer chunks).trans normal) observed returned)
    value ((program_equivalence fields source raw ch tail pointer chunks).symm.trans actual)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.step_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.program_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.fields_geometry

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.program_local
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.program_globals

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.program_memory
