import InitECandidate.Solver.Rlp.ItemSyntax
import InitECandidate.Solver.Input.SequenceChoice

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem single_stops : Input.NoFallthrough single := by
  rw [single_shape]
  exact Input.NoFallthrough.returned _
theorem short_string_stops : Input.NoFallthrough shortString := by
  rw [short_string_shape]
  apply Input.NoFallthrough.declared
  apply Input.NoFallthrough.sequence
  apply Input.NoFallthrough.sequence
  exact Input.NoFallthrough.returned _
theorem short_list_stops : Input.NoFallthrough shortList := by
  rw [short_list_shape]
  apply Input.NoFallthrough.declared
  apply Input.NoFallthrough.sequence
  apply Input.NoFallthrough.sequence
  exact Input.NoFallthrough.returned _
theorem long_stops (base flag : BitVec 64) : Input.NoFallthrough (longCase base flag) := by
  unfold longCase
  apply Input.NoFallthrough.declared
  apply Input.NoFallthrough.sequence
  apply Input.NoFallthrough.scoped
  unfold afterRead
  apply Input.NoFallthrough.sequence
  apply Input.NoFallthrough.sequence
  unfold longTail
  split
  · exact Input.NoFallthrough.returned _
  · apply Input.NoFallthrough.sequence
    exact Input.NoFallthrough.returned _

/-- Exact case dispatch of the literal original decoder. Each selected
item case stops, so later source tests are not evaluated after a return. -/
theorem after_byte_evaluate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte : BitVec 64)
    (cell : source.locals.lookup (ofString "b")=some (.val (.word byte))) :
    evaluateHOLFiniteState source afterByte=
      if byte.toNat<128 then evaluateHOLFiniteState source single
      else if byte.toNat≤183 then evaluateHOLFiniteState source shortString
      else if byte.toNat≤191 then evaluateHOLFiniteState source longString
      else if byte.toNat≤247 then evaluateHOLFiniteState source shortList
      else evaluateHOLFiniteState source longList := by
  let first : ProgHOL 64 := .ite (.cmp .lower (localVar "b") (.const 128#64)) single .skip
  let second : ProgHOL 64 := .ite (.cmp .notLower (.const 183#64) (localVar "b")) shortString .skip
  let third : ProgHOL 64 := .ite (.cmp .notLower (.const 191#64) (localVar "b")) longString .skip
  let fourth : ProgHOL 64 := .ite (.cmp .notLower (.const 247#64) (localVar "b")) shortList .skip
  have firstRead : evaluateHOLFiniteState source first=if byte.toNat<128 then evaluateHOLFiniteState source single else (none,source) := by
    simp [first,evaluateHOLFiniteState_ite,evalHOLExact,localVar,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,evaluateHOLFiniteState_skip]
    split_ifs <;> first | rfl | omega
  have secondRead : evaluateHOLFiniteState source second=if byte.toNat≤183 then evaluateHOLFiniteState source shortString else (none,source) := by
    simp [second,evaluateHOLFiniteState_ite,evalHOLExact,localVar,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,evaluateHOLFiniteState_skip]
    split_ifs <;> first | rfl | omega
  have thirdRead : evaluateHOLFiniteState source third=if byte.toNat≤191 then evaluateHOLFiniteState source longString else (none,source) := by
    simp [third,evaluateHOLFiniteState_ite,evalHOLExact,localVar,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,evaluateHOLFiniteState_skip]
    split_ifs <;> first | rfl | omega
  have fourthRead : evaluateHOLFiniteState source fourth=if byte.toNat≤247 then evaluateHOLFiniteState source shortList else (none,source) := by
    simp [fourth,evaluateHOLFiniteState_ite,evalHOLExact,localVar,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,evaluateHOLFiniteState_skip]
    split_ifs <;> first | rfl | omega
  have longStringStops : Input.NoFallthrough longString := by rw [long_string_shape]; exact long_stops _ _
  have firstEq := Input.sequence_choice source first single (.seq second (.seq third (.seq fourth longList))) _ firstRead single_stops
  have secondEq := Input.sequence_choice source second shortString (.seq third (.seq fourth longList)) _ secondRead short_string_stops
  have thirdEq := Input.sequence_choice source third longString (.seq fourth longList) _ thirdRead longStringStops
  have fourthEq := Input.sequence_choice source fourth shortList longList _ fourthRead short_list_stops
  rw [cases_shape]
  change evaluateHOLFiniteState source (.seq first (.seq second (.seq third (.seq fourth longList))))=_
  rw [firstEq,secondEq,thirdEq,fourthEq]

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.single_stops
#print axioms InitECandidate.Solver.Rlp.Item.short_string_stops
#print axioms InitECandidate.Solver.Rlp.Item.short_list_stops
#print axioms InitECandidate.Solver.Rlp.Item.long_stops
#print axioms InitECandidate.Solver.Rlp.Item.after_byte_evaluate
