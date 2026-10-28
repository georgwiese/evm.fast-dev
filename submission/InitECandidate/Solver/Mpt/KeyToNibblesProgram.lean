import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.PanState
import InitECandidate.Solver.WitnessRadix.BindingLookup
import InitECandidate.Solver.Input.ByteStoreClock

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_key_to_nibbles with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "key", .one), (ofString "n", .one), (ofString "out", .one)]
def afterIndex : ProgHOL 64 := match body with | .dec _ _ _ rest => rest | _ => .skip
def blockLoop : ProgHOL 64 := match afterIndex with | .seq first _ => first | _ => .skip
def afterBlocks : ProgHOL 64 := match afterIndex with | .seq _ rest => rest | _ => .skip
def tailLoop : ProgHOL 64 := match afterBlocks with | .seq first _ => first | _ => .skip
def afterTail : ProgHOL 64 := match afterBlocks with | .seq _ rest => rest | _ => .skip
def blockBody : ProgHOL 64 := match blockLoop with | .while _ rest => rest | _ => .skip
def tailBody : ProgHOL 64 := match tailLoop with | .while _ rest => rest | _ => .skip
def blockCondition : ExpHOL 64 := .cmp .notLower (localVar "n") (addConst (localVar "i") 4#64)
def tailCondition : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "n")
def inputAddress (offset : Nat) : ExpHOL 64 :=
  if offset = 0 then .op .add [localVar "key", localVar "i"]
  else .op .add [localVar "key", localVar "i", .const (BitVec.ofNat 64 offset)]
def outputAddress (offset : Nat) : ExpHOL 64 :=
  if offset = 0 then .op .add [localVar "out", .panop .mul [.const 2#64, localVar "i"]]
  else .op .add [localVar "out", .panop .mul [.const 2#64, localVar "i"], .const (BitVec.ofNat 64 offset)]
def pair (name : String) (offset : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.storeByte (outputAddress (2 * offset)) (.shift .lsr (localVar name) (.const 4#64)))
    (.seq (.storeByte (outputAddress (2 * offset + 1)) (.op .and [localVar name, .const 15#64])) rest)
def increment (amount : BitVec 64) : ProgHOL 64 := .assign .local (ofString "i") (addConst (localVar "i") amount)

set_option maxRecDepth 10000
theorem body_shape : body = .dec (ofString "i") .one (.const 0#64) (.seq blockLoop (.seq tailLoop afterTail)) := by
  simp only [body, afterIndex, blockLoop, afterBlocks, tailLoop, afterTail, Guest.Software.guestFn_key_to_nibbles,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]
theorem loop_shapes : blockLoop = .while blockCondition blockBody ∧ tailLoop = .while tailCondition tailBody := by
  simp only [blockLoop, blockBody, tailLoop, tailBody, afterIndex, afterBlocks, body, Guest.Software.guestFn_key_to_nibbles,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, blockCondition, tailCondition, addConst, localVar]
  exact ⟨True.intro, True.intro⟩
theorem block_body_shape : blockBody =
    .dec (ofString "b0") .one (.loadByte (inputAddress 0)) (pair "b0" 0
      (.dec (ofString "b1") .one (.loadByte (inputAddress 1)) (pair "b1" 1
        (.dec (ofString "b2") .one (.loadByte (inputAddress 2)) (pair "b2" 2
          (.dec (ofString "b3") .one (.loadByte (inputAddress 3)) (pair "b3" 3 (increment 4#64)))))))) := by
  simp only [blockBody, blockLoop, afterIndex, body, Guest.Software.guestFn_key_to_nibbles, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, pair, inputAddress, outputAddress, increment, addConst, localVar]
  rfl
theorem tail_body_shape : tailBody = .dec (ofString "b") .one (.loadByte (inputAddress 0)) (pair "b" 0 (increment 1#64)) := by
  simp only [tailBody, tailLoop, afterBlocks, afterIndex, body, Guest.Software.guestFn_key_to_nibbles, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, pair, inputAddress, outputAddress, increment, addConst, localVar]
  rfl
theorem after_tail_shape : afterTail = .return (.const 0#64) := by
  simp only [afterTail, afterBlocks, afterIndex, body, Guest.Software.guestFn_key_to_nibbles, progToHOL, expToHOL]
theorem pair_quiet (code) (name : String) (offset : Nat) (rest : ProgHOL 64)
    (quiet : Input.QuietClock.Preserves code rest) : Input.QuietClock.Preserves code (pair name offset rest) :=
  Input.QuietClock.sequence code _ _ (Input.QuietClock.store_byte code _ _)
    (Input.QuietClock.sequence code _ _ (Input.QuietClock.store_byte code _ _) quiet)
theorem bodies_quiet (code) : Input.QuietClock.Preserves code blockBody ∧ Input.QuietClock.Preserves code tailBody := by
  rw [block_body_shape, tail_body_shape]
  constructor
  all_goals
    repeat first
      | apply Input.QuietClock.declared
      | apply pair_quiet
      | exact Input.QuietClock.assign code _ _

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "key_to_nibbles") = some (formals, body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 222 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_key_to_nibbles) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals,
    Guest.Software.guestFn_key_to_nibbles, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.body_shape
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.loop_shapes
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.block_body_shape
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.tail_body_shape
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.after_tail_shape
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_quiet
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.bodies_quiet
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.original_code
