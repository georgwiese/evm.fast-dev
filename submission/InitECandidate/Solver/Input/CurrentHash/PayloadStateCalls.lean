import InitECandidate.Solver.Input.CurrentHash.PayloadState
import InitECandidate.Solver.Input.Witness.LoadedOffsets

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem State.field_read (data : State input source blob record array ch cursor chunk out zeros length start size)
    (offset : Nat) (inside : offset<136) (aligned : offset%8=0) (word : BitVec 64) (cell : source.memory (record+BitVec.ofNat 64 offset)=.word word) :
    eval source (fieldExpression offset)=some (.val (.word word)) := by
  have read : eval source (localVar "pl")=some (.val (.word record)) := by simpa [eval,evalHOLExact,toExact,localVar] using data.payload
  exact Witness.load_word_read source _ _ word (Scalar.plus_read source _ record offset read)
    (AllocatedBytes.word_mapped source record 136 offset data.context.domain data.recordArena inside data.recordAligned aligned) cell

theorem State.output_arena (data : State input source blob record array ch cursor chunk out zeros length start size) (slot : Nat) (inside : slot<19) :
    AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*slot)) 32 :=
  AllocatedBytes.Arena.subrange ch 608 (32*slot) 32 data.chunksArena (by omega)

theorem State.output_away (data : State input source blob record array ch cursor chunk out zeros length start size)
    (slot : Nat) (inside : slot<19) (query : BitVec 64) (before : query.toNat<ch.toNat) : CopyGeneral.Away (ch+BitVec.ofNat 64 (32*slot)) query 32 := by
  have fits : ch.toNat+32*slot<2^64 := by have h:=data.chunksArena.upper; omega
  have aligned : (ch+BitVec.ofNat 64 (32*slot)).toNat%8=0 := byteAddress_aligned ch (32*slot) data.chunksAligned (by omega) fits
  have arena := data.output_arena slot inside
  apply CopyGeneral.Away.after _ _ 32 aligned (by have h:=arena.upper; omega)
  change query.toNat<(byteAddress ch (32*slot)).toNat
  rw [byteAddress_toNat ch (32*slot) fits]
  omega

theorem State.chunk_away (data : State input source blob record array ch cursor chunk out zeros length start size)
    (query : BitVec 64) (afterRecord : record.toNat≤query.toNat) : CopyGeneral.Away chunk query 32 :=
  CopyGeneral.Away.before chunk query 32 record.toNat data.chunkBefore record.isLt afterRecord

/-- Share the actual caller restoration and immutable-global frame after
any current helper whose same normal call supplies the metadata/heap frame. -/
theorem State.after_call (data : State input source blob record array ch cursor chunk out zeros length start size)
    (routine : Code.Routine) (arguments : List (ExpHOL 64))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name routine) arguments)=(none,post))
    (frame : ∀ query : BitVec 64,record.toNat≤query.toNat → query.toNat<ch.toNat →
      post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) :
    State input post blob record array ch cursor chunk out zeros length start size := by
  have heap := (frame record (Nat.le_refl _) (by have h:=data.afterRecord; omega)).2
  have context := data.context.after_call routine arguments heap actual
  have global := Effects.call_preserves .lengthChunk source.code data.context.installed routine (some none) arguments source rfl
  change GlobalEffects.erase (key .lengthChunk) (evaluateHOLFiniteState source (.call (some (none,none)) (Code.name routine) arguments)).2=_ at global
  rw [actual] at global
  exact data.after_memory context (by intro query lower upper; exact (frame query lower upper).1)
    (by intro name; exact CallNormal.ignored_lookup source post name (Code.name routine) arguments actual)
    ((congrArg Prod.snd global).trans data.chunkCell)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.field_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.output_arena
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.output_away
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.chunk_away
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_call
