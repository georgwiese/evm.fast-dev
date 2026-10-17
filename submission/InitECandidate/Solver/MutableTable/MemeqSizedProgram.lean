import InitECandidate.Solver.MutableTable.HashSized
import InitECandidate.Solver.WitnessRadix.Memeq32Entry

namespace InitECandidate.Solver.MutableTable.MemeqSized
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix
abbrev Kind := HashSized.Kind
abbrev keySize := HashSized.keySize
abbrev wordCount := HashSized.wordCount

def byteAt (name : String) (offset : Nat) : ExpHOL 64 := .loadByte (addConst (localVar name) (BitVec.ofNat 64 offset))
def checks (kind : Kind) (left right : Fin 6 → BitVec 64) (leftBytes rightBytes : Fin 4 → UInt8) : List CompareChain.Comparison :=
  (match kind with
  | .address => [⟨Memeq32.wordAt "a" 0, Memeq32.wordAt "b" 0, left 0, right 0⟩,
                 ⟨Memeq32.wordAt "a" 8, Memeq32.wordAt "b" 8, left 1, right 1⟩]
  | .storage => [⟨Memeq32.wordAt "a" 0, Memeq32.wordAt "b" 0, left 0, right 0⟩,
                 ⟨Memeq32.wordAt "a" 8, Memeq32.wordAt "b" 8, left 1, right 1⟩,
                 ⟨Memeq32.wordAt "a" 16, Memeq32.wordAt "b" 16, left 2, right 2⟩,
                 ⟨Memeq32.wordAt "a" 24, Memeq32.wordAt "b" 24, left 3, right 3⟩,
                 ⟨Memeq32.wordAt "a" 32, Memeq32.wordAt "b" 32, left 4, right 4⟩,
                 ⟨Memeq32.wordAt "a" 40, Memeq32.wordAt "b" 40, left 5, right 5⟩]) ++
  [⟨byteAt "a" (8 * wordCount kind), byteAt "b" (8 * wordCount kind), BitVec.ofNat 64 (leftBytes 0).toNat, BitVec.ofNat 64 (rightBytes 0).toNat⟩,
   ⟨byteAt "a" (8 * wordCount kind + 1), byteAt "b" (8 * wordCount kind + 1), BitVec.ofNat 64 (leftBytes 1).toNat, BitVec.ofNat 64 (rightBytes 1).toNat⟩,
   ⟨byteAt "a" (8 * wordCount kind + 2), byteAt "b" (8 * wordCount kind + 2), BitVec.ofNat 64 (leftBytes 2).toNat, BitVec.ofNat 64 (rightBytes 2).toNat⟩,
   ⟨byteAt "a" (8 * wordCount kind + 3), byteAt "b" (8 * wordCount kind + 3), BitVec.ofNat 64 (leftBytes 3).toNat, BitVec.ofNat 64 (rightBytes 3).toNat⟩]

def fiftyTwo : ProgHOL 64 := match Memeq32.parts.otherAligned with | .seq (.ite _ block _) _ => block | _ => .skip
def alignedLoops : ProgHOL 64 := match Memeq32.parts.otherAligned with | .seq _ rest => rest | _ => .skip
def selectedBranch : Kind → ProgHOL 64 | .address => Memeq32.parts.twenty | .storage => fiftyTwo

theorem other_shape : Memeq32.parts.otherAligned = .seq (.ite (Memeq32.sizeTest 52#64) fiftyTwo .skip) alignedLoops := by
  simp only [fiftyTwo, alignedLoops, Memeq32.parts, Memeq32.body, Guest.guestFn_memeq,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Memeq32.sizeTest, localVar]

theorem branch_shape (kind : Kind) (left right : Fin 6 → BitVec 64) (leftBytes rightBytes : Fin 4 → UInt8) :
    selectedBranch kind = CompareChain.chain (checks kind left right leftBytes rightBytes) := by
  cases kind <;>
    simp only [selectedBranch, fiftyTwo, Memeq32.parts, Memeq32.body, Guest.guestFn_memeq,
      progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, checks, wordCount, HashSized.wordCount,
      List.cons_append, List.nil_append, CompareChain.chain, CompareChain.returned, Memeq32.wordAt, byteAt,
      addConst, localVar, ↓reduceIte]
  all_goals rfl

theorem branch_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : Kind)
    (left right : Fin 6 → BitVec 64) (leftBytes rightBytes : Fin 4 → UInt8)
    (ready : ∀ check ∈ checks kind left right leftBytes rightBytes, CompareChain.Ready source check) :
    evaluateHOLFiniteState source (selectedBranch kind) =
      (some (.returned (.val (.word (if CompareChain.agrees (checks kind left right leftBytes rightBytes) then 1#64 else 0#64)))), emptyLocalsHOLFinite source) := by
  rw [branch_shape]
  exact CompareChain.execute source _ ready

end InitECandidate.Solver.MutableTable.MemeqSized

#print axioms InitECandidate.Solver.MutableTable.MemeqSized.other_shape
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.branch_shape
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.branch_execute
