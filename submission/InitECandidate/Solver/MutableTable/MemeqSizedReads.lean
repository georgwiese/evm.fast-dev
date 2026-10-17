import InitECandidate.Solver.MutableTable.MemeqSizedFast

namespace InitECandidate.Solver.MutableTable.MemeqSized
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

/-- The exact two/six word reads and four trailing bytes of a fast key. -/
structure Data {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64)
    (words : Fin 6 → BitVec 64) (bytes : Fin 4 → UInt8) : Prop where
  mapped : ∀ i : Fin 6, i.val < wordCount kind → source.memaddrs (pointer + BitVec.ofNat 64 (8 * i.val))
  stored : ∀ i : Fin 6, i.val < wordCount kind → source.memory (pointer + BitVec.ofNat 64 (8 * i.val)) = .word (words i)
  trailing : ∀ i : Fin 4, @panMemLoadByteHOL 64 _ source.memory source.memaddrs
    (fun address => Classical.propDecidable (source.memaddrs address)) source.be
    (pointer + BitVec.ofNat 64 (8 * wordCount kind + i.val)) = some (bytes i)

theorem byte_read {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (pointer : BitVec 64)
    (offset : Nat) (byte : UInt8)
    (argument : source.locals.lookup (ofString name) = some (.val (.word pointer)))
    (loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (pointer + BitVec.ofNat 64 offset) = some byte) :
    eval source (byteAt name offset) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
  simp [eval, byteAt, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, argument,
    valueIsWord, valueWord, wordOpHOL, wordOp, loaded]

theorem checks_ready {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : Kind) (a b : BitVec 64)
    (left right : Fin 6 → BitVec 64) (leftBytes rightBytes : Fin 4 → UInt8)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (leftData : Data source kind a left leftBytes) (rightData : Data source kind b right rightBytes) :
    ∀ check ∈ checks kind left right leftBytes rightBytes, CompareChain.Ready source check := by
  have wordRead (i : Fin 6) (offset : Nat) (position : 8 * i.val = offset) (inside : i.val < wordCount kind) :
      CompareChain.Ready source ⟨Memeq32.wordAt "a" offset, Memeq32.wordAt "b" offset, left i, right i⟩ := by
    subst offset
    exact ⟨Memeq32.eval_wordAt source "a" a (left i) _ aLocal (leftData.mapped i inside) (leftData.stored i inside),
      Memeq32.eval_wordAt source "b" b (right i) _ bLocal (rightData.mapped i inside) (rightData.stored i inside)⟩
  have byteRead (i : Fin 4) (offset : Nat) (position : 8 * wordCount kind + i.val = offset) :
      CompareChain.Ready source ⟨byteAt "a" offset, byteAt "b" offset,
        BitVec.ofNat 64 (leftBytes i).toNat, BitVec.ofNat 64 (rightBytes i).toNat⟩ := by
    subst offset
    exact ⟨byte_read source "a" a _ _ aLocal (leftData.trailing i), byte_read source "b" b _ _ bLocal (rightData.trailing i)⟩
  intro check member
  cases kind with
  | address =>
    simp only [checks, wordCount, HashSized.wordCount, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact wordRead 0 0 (by decide) (by decide)
    · exact wordRead 1 8 (by decide) (by decide)
    · exact byteRead 0 16 (by decide)
    · exact byteRead 1 17 (by decide)
    · exact byteRead 2 18 (by decide)
    · exact byteRead 3 19 (by decide)
  | storage =>
    simp only [checks, wordCount, HashSized.wordCount, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact wordRead 0 0 (by decide) (by decide)
    · exact wordRead 1 8 (by decide) (by decide)
    · exact wordRead 2 16 (by decide) (by decide)
    · exact wordRead 3 24 (by decide) (by decide)
    · exact wordRead 4 32 (by decide) (by decide)
    · exact wordRead 5 40 (by decide) (by decide)
    · exact byteRead 0 48 (by decide)
    · exact byteRead 1 49 (by decide)
    · exact byteRead 2 50 (by decide)
    · exact byteRead 3 51 (by decide)

theorem alignment_read {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (aligned : (a ||| b) &&& 7#64 = 0#64) :
    eval source Memeq32.alignmentTest = some (.val (.word 1#64)) := by
  simp [eval, Memeq32.alignmentTest, localVar, evalHOLExact, evalListHOLExact, toExact, aLocal, bLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, OrOp.or, AndOp.and, aligned,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- Discharge every fast-path read and alignment expression from actual
physical input words/bytes and local bindings. -/
theorem aligned_of_data {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : Kind) (a b : BitVec 64)
    (left right : Fin 6 → BitVec 64) (leftBytes rightBytes : Fin 4 → UInt8)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 (keySize kind)))))
    (aligned : (a ||| b) &&& 7#64 = 0#64)
    (leftData : Data source kind a left leftBytes) (rightData : Data source kind b right rightBytes) :
    evaluateHOLFiniteState source Memeq32.body =
      (some (.returned (.val (.word (if CompareChain.agrees (checks kind left right leftBytes rightBytes) then 1#64 else 0#64)))),
        restore source "i" (emptyLocalsHOLFinite (WitnessRadix.QueryBranch.bind source "i" 0#64))) := by
  let loaded := WitnessRadix.QueryBranch.bind source "i" 0#64
  have aReady : loaded.locals.lookup (ofString "a") = some (.val (.word a)) :=
    (bind_lookup_other _ "i" "a" _ (by decide)).trans aLocal
  have bReady : loaded.locals.lookup (ofString "b") = some (.val (.word b)) :=
    (bind_lookup_other _ "i" "b" _ (by decide)).trans bLocal
  have leftReady : Data loaded kind a left leftBytes := ⟨leftData.mapped, leftData.stored, leftData.trailing⟩
  have rightReady : Data loaded kind b right rightBytes := ⟨rightData.mapped, rightData.stored, rightData.trailing⟩
  exact aligned_execute source kind left right leftBytes rightBytes length
    (alignment_read loaded a b aReady bReady aligned) (checks_ready loaded kind a b left right leftBytes rightBytes aReady bReady leftReady rightReady)

end InitECandidate.Solver.MutableTable.MemeqSized

#print axioms InitECandidate.Solver.MutableTable.MemeqSized.byte_read
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.checks_ready
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.alignment_read
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.aligned_of_data
