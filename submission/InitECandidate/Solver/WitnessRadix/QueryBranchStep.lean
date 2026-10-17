import InitECandidate.Solver.WitnessRadix.QueryBranch

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.WitnessRadix.QueryBranch
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

def bind {F : Type} (state : PanSemStateFiniteExact 64 F) (name : String)
    (word : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString name) (.val (.word word)) state

def restore {F : Type} (saved : PanSemStateFiniteExact 64 F) (name : String)
    (state : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  { state with locals := HolFiniteMapExact.resVarEq state.locals (ofString name, saved.locals.lookup (ofString name)) }

def branchPost {F : Type} (source : PanSemStateFiniteExact 64 F)
    (position digit child : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let bitState := bind source "bit" position
  let digitState := bind bitState "digit" digit
  restore source "bit" (restore bitState "digit" (bind digitState "node" child))

theorem branchPost_eq {F : Type} (source : PanSemStateFiniteExact 64 F)
    (position digit child : BitVec 64) :
    branchPost source position digit child = bind source "node" child := by
  have bitDigit : ofString "bit" ≠ ofString "digit" := by decide
  have bitNode : ofString "bit" ≠ ofString "node" := by decide
  have digitNode : ofString "digit" ≠ ofString "node" := by decide
  dsimp only [branchPost, restore, bind, setVarHOLFinite]
  congr 1
  apply HolFiniteMapExact.ext
  funext name
  by_cases atBit : name = ofString "bit"
  · subst name
    cases bitSaved : source.locals.lookup (ofString "bit") <;>
      cases digitSaved : source.locals.lookup (ofString "digit") <;>
      simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL,
        bitSaved, digitSaved, bitDigit, bitNode, digitNode,
        Ne.symm bitDigit, Ne.symm bitNode, Ne.symm digitNode]
  · by_cases atDigit : name = ofString "digit"
    · subst name
      cases bitSaved : source.locals.lookup (ofString "bit") <;>
        cases digitSaved : source.locals.lookup (ofString "digit") <;>
        simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
          HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL,
          bitSaved, digitSaved, bitDigit, bitNode, digitNode,
        Ne.symm bitDigit, Ne.symm bitNode, Ne.symm digitNode]
    · cases bitSaved : source.locals.lookup (ofString "bit") <;>
        cases digitSaved : source.locals.lookup (ofString "digit") <;>
        simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
          HolFiniteMapExact.eraseEq, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL,
          bitSaved, digitSaved, bitDigit, bitNode, digitNode, atBit, atDigit,
          Ne.symm bitDigit, Ne.symm bitNode, Ne.symm digitNode, Ne.symm atBit, Ne.symm atDigit]

theorem branch_code {F : Type} (source : PanSemStateFiniteExact 64 F)
    (root position digit child : BitVec 64)
    (node : source.locals.lookup (ofString "node") = some (.val (.word root)))
    (readBit : eval source bitLoad = some (.val (.word position)))
    (readDigit : eval (bind source "bit" position) digitExpression = some (.val (.word digit)))
    (mapped : source.memaddrs (root + if digit = 0#64 then 8#64 else 16#64))
    (childWord : source.memory (root + if digit = 0#64 then 8#64 else 16#64) = .word child) :
    evaluateHOLFiniteState source branchCode = (none, branchPost source position digit child) := by
  classical
  let bitState := bind source "bit" position
  let digitState := bind bitState "digit" digit
  have bitNotNode : ofString "bit" ≠ ofString "node" := by decide
  have digitNotNode : ofString "digit" ≠ ofString "node" := by decide
  have currentNode : digitState.locals.lookup (ofString "node") = some (.val (.word root)) := by
    simp [digitState, bitState, bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      node, bitNotNode, digitNotNode]
  have currentDigit : digitState.locals.lookup (ofString "digit") = some (.val (.word digit)) := by
    simp [digitState, bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have chosen : evaluateHOLFiniteState digitState
      (.ite digitTest (assignChild 8#64) (assignChild 16#64)) =
      (none, bind digitState "node" child) := by
    by_cases zero : digit = 0#64
    · have mapped' : digitState.memaddrs (root + 8#64) := by simpa [zero, digitState, bitState, bind, setVarHOLFinite] using mapped
      have child' : digitState.memory (root + 8#64) = .word child := by simpa [zero, digitState, bitState, bind, setVarHOLFinite] using childWord
      have assignment := assign_child digitState root 8#64 child currentNode mapped' child'
      rw [evaluateHOLFiniteState_ite]
      simpa [digitTest, localVar, evalHOLExact, toExact, currentDigit, zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bind] using assignment
    · have mapped' : digitState.memaddrs (root + 16#64) := by simpa [zero, digitState, bitState, bind, setVarHOLFinite] using mapped
      have child' : digitState.memory (root + 16#64) = .word child := by simpa [zero, digitState, bitState, bind, setVarHOLFinite] using childWord
      have assignment := assign_child digitState root 16#64 child currentNode mapped' child'
      rw [evaluateHOLFiniteState_ite]
      simpa [digitTest, localVar, evalHOLExact, toExact, currentDigit, zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bind] using assignment
  simp only [eval] at readBit readDigit
  rw [branchCode, evaluateHOLFiniteState_dec_total]
  simp only [readBit, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := (evaluateHOLFiniteState bitState
      (ProgHOL.dec (ofString "digit") .one digitExpression
        (.ite digitTest (assignChild 8#64) (assignChild 16#64))));
    (output.1, restore source "bit" output.2)) = _
  rw [evaluateHOLFiniteState_dec_total]
  have readDigit' : eval bitState digitExpression = some (.val (.word digit)) := readDigit
  simp only [eval] at readDigit'
  simp only [readDigit', shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let result := evaluateHOLFiniteState digitState (.ite digitTest (assignChild 8#64) (assignChild 16#64));
    (result.1, restore source "bit" (restore bitState "digit" result.2))) = _
  rw [chosen]
  rfl

/-- One complete branch iteration of the actual candidate lookup body. It
updates only `node`; temporary bindings are restored at every initial clock.
The surrounding while loop pays its own single clock before entering here. -/
theorem branch_iteration {F : Type} (source : PanSemStateFiniteExact 64 F)
    (root position query child : BitVec 64) (byte : UInt8)
    (node : source.locals.lookup (ofString "node") = some (.val (.word root)))
    (hash : source.locals.lookup (ofString "hash") = some (.val (.word query)))
    (even : root &&& 1#64 = 0#64)
    (rootMapped : source.memaddrs root) (positionWord : source.memory root = .word position)
    (loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (query + (position >>> (3 : Nat))) = some byte)
    (childMapped : source.memaddrs (root +
      if WordBits.digit (BitVec.ofNat 8 byte.toNat) position = 0#64 then 8#64 else 16#64))
    (childWord : source.memory (root +
      if WordBits.digit (BitVec.ofNat 8 byte.toNat) position = 0#64 then 8#64 else 16#64) = .word child) :
    evaluateHOLFiniteState source QueryEmpty.loopBody = (none, bind source "node" child) := by
  classical
  have bitNotHash : ofString "bit" ≠ ofString "hash" := by decide
  have hash' : (bind source "bit" position).locals.lookup (ofString "hash") = some (.val (.word query)) := by
    simp [bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, bitNotHash, hash]
  have bit' : (bind source "bit" position).locals.lookup (ofString "bit") = some (.val (.word position)) := by
    simp [bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have digitRead := eval_digit (bind source "bit" position) query position byte hash' bit' loaded
  have continuation := branch_code source root position
    (WordBits.digit (BitVec.ofNat 8 byte.toNat) position) child node
    (eval_bitLoad source root position node rootMapped positionWord) digitRead childMapped childWord
  rw [branchPost_eq] at continuation
  have leafRead := eval_leafTest source root node even
  simp only [eval] at leafRead
  have skipped : evaluateHOLFiniteState source (.ite leafTest leafCode .skip) = (none, source) := by
    rw [evaluateHOLFiniteState_ite, leafRead]
    simp
  rw [loop_shape, evaluateHOLFiniteState_seq, skipped]
  have fixed : fixClockHOLFinite source ((none : Option (PanSemResultExact 64)), source) =
      (none, source) := by simp [fixClockHOLFinite]
  simpa only [fixed] using continuation

end InitECandidate.Solver.WitnessRadix.QueryBranch

#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.branch_code
#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.branchPost_eq
#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.branch_iteration
