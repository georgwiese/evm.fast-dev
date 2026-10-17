import InitECandidate.Solver.GasBudget.FrameNewZero
import InitECandidate.Solver.PanFieldStores

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure MessageWords where
  code : BitVec 64
  length : BitVec 64
  gas : BitVec 64
  reservoir : BitVec 64

def MessageWords.atOffset (words : MessageWords) (offset : Nat) : BitVec 64 :=
  if offset = 112 then words.code else if offset = 120 then words.length else if offset = 40 then words.gas else words.reservoir

def messageOffsets : List Nat := [112, 120, 40, 48]
def frameOffsets : List Nat := [224, 24, 40, 48, 56, 64, 72]
def fields (mark pointer : BitVec 64) (words : MessageWords) : List FieldStores.Field := [
  ⟨224, .saved "mem_mark" mark⟩,
  ⟨24, .saved "mem" pointer⟩,
  ⟨40, .literal 1024#64⟩,
  ⟨48, .copied 112 words.code⟩,
  ⟨56, .copied 120 words.length⟩,
  ⟨64, .copied 40 words.gas⟩,
  ⟨72, .copied 48 words.reservoir⟩]
def emptyWords : MessageWords := ⟨0#64, 0#64, 0#64, 0#64⟩
def gasProgram (continuation : ProgHOL 64) : ProgHOL 64 :=
  FieldStores.program "e" "msg" (fields 0#64 0#64 emptyWords) continuation

def gasSite : ProgHOL 64 := match afterZero with
  | .decCall _ _ _ _ (.seq _ (.seq _ (.seq _ (.decCall _ _ _ _ rest)))) => rest
  | _ => .skip
def afterGas : ProgHOL 64 := match gasSite with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ rest)))))) => rest
  | _ => .skip

set_option maxRecDepth 10000 in
/-- The complete seven stores preceding compute_jumpdests in frame_new. -/
theorem actual_gas_stores : gasSite = gasProgram afterGas := by
  simp only [gasSite, afterGas, afterZero, body, Guest.guestFn_frame_new, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some,
    gasProgram, FieldStores.program, fields, FieldStores.address, FieldStores.Value.expression,
    localVar, addConst]

/-- Execute the actual message-to-frame stores with reads justified by the
message's protected words. The two regular counter cells are untouched. -/
theorem gas_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message mark pointer : BitVec 64) (words : MessageWords)
    (frameLocal : source.locals.lookup (ofString "e") = some (.val (.word frame)))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (markLocal : source.locals.lookup (ofString "mem_mark") = some (.val (.word mark)))
    (pointerLocal : source.locals.lookup (ofString "mem") = some (.val (.word pointer)))
    (frameMapped : ∀ offset ∈ frameOffsets, source.memaddrs (frame + BitVec.ofNat 64 offset))
    (messageMapped : ∀ offset ∈ messageOffsets, source.memaddrs (message + BitVec.ofNat 64 offset))
    (messageCells : ∀ offset ∈ messageOffsets,
      source.memory (message + BitVec.ofNat 64 offset) = .word (words.atOffset offset))
    (separate : ∀ readOffset ∈ messageOffsets, ∀ writeOffset ∈ frameOffsets,
      message + BitVec.ofNat 64 readOffset ≠ frame + BitVec.ofNat 64 writeOffset)
    (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (gasProgram continuation) =
      evaluateHOLFiniteState {source with memory := (WitnessRadix.WordWrites.write source.memory
        (FieldStores.writes frame (fields mark pointer words)))} continuation := by
  have reads : ∀ field ∈ fields mark pointer words, field.value.Ready source "msg" message := by
    intro field member
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact markLocal
    · exact pointerLocal
    · trivial
    · exact ⟨messageLocal, messageMapped 112 (by simp [messageOffsets]),
        by simpa [MessageWords.atOffset] using messageCells 112 (by simp [messageOffsets])⟩
    · exact ⟨messageLocal, messageMapped 120 (by simp [messageOffsets]),
        by simpa [MessageWords.atOffset] using messageCells 120 (by simp [messageOffsets])⟩
    · exact ⟨messageLocal, messageMapped 40 (by simp [messageOffsets]),
        by simpa [MessageWords.atOffset] using messageCells 40 (by simp [messageOffsets])⟩
    · exact ⟨messageLocal, messageMapped 48 (by simp [messageOffsets]),
        by simpa [MessageWords.atOffset] using messageCells 48 (by simp [messageOffsets])⟩
  have mapped : ∀ field ∈ fields mark pointer words, source.memaddrs (frame + BitVec.ofNat 64 field.offset) := by
    intro field member
    apply frameMapped
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [frameOffsets]
  have guardedReads : ∀ reader ∈ fields mark pointer words, ∀ writer ∈ fields mark pointer words,
      reader.value.Avoid message (frame + BitVec.ofNat 64 writer.offset) := by
    intro reader readerIn writer writerIn
    have inside : writer.offset ∈ frameOffsets := by
      simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at writerIn
      rcases writerIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [frameOffsets]
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at readerIn
    rcases readerIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · trivial
    · exact separate 112 (by simp [messageOffsets]) writer.offset inside
    · exact separate 120 (by simp [messageOffsets]) writer.offset inside
    · exact separate 40 (by simp [messageOffsets]) writer.offset inside
    · exact separate 48 (by simp [messageOffsets]) writer.offset inside
  have run := FieldStores.execute source "e" "msg" frame message (fields mark pointer words)
    frameLocal reads mapped guardedReads continuation
  exact run

/-- Exact regular-ledger initialization from the incoming message gas: no
state-reservoir size or signed state-use premise enters the regular total. -/
theorem initialized_budget (memory : Memory) (frame mark pointer : BitVec 64) (words : MessageWords)
    (used : memory (frame + 184#64) = .word 0#64) (spill : memory (frame + 192#64) = .word 0#64) :
    regularBudget (WitnessRadix.WordWrites.write memory (FieldStores.writes frame (fields mark pointer words))) frame =
      words.gas.toNat := by
  have distinct : ((FieldStores.writes frame (fields mark pointer words)).map Prod.fst).Nodup := by
    simp [FieldStores.writes, fields, BitVec.add_right_inj]
  have gas := WitnessRadix.WordWrites.write_unique memory (FieldStores.writes frame (fields mark pointer words))
    (frame + 64#64, words.gas) distinct (by simp [FieldStores.writes, fields, FieldStores.Value.word])
  have keptUsed : WitnessRadix.WordWrites.write memory (FieldStores.writes frame (fields mark pointer words)) (frame + 184#64) = .word 0#64 := by
    rw [WitnessRadix.WordWrites.write_away]
    · exact used
    · simp [FieldStores.writes, fields, BitVec.add_right_inj]
  have keptSpill : WitnessRadix.WordWrites.write memory (FieldStores.writes frame (fields mark pointer words)) (frame + 192#64) = .word 0#64 := by
    rw [WitnessRadix.WordWrites.write_away]
    · exact spill
    · simp [FieldStores.writes, fields, BitVec.add_right_inj]
  simp only [regularBudget, wordAt, gas, keptUsed, keptSpill, WitnessRadix.MemoryBytes.wordBits,
    BitVec.toNat_zero, Nat.add_zero]

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.actual_gas_stores
#print axioms InitECandidate.Solver.GasBudget.FrameNew.gas_stores_execute
#print axioms InitECandidate.Solver.GasBudget.FrameNew.initialized_budget
