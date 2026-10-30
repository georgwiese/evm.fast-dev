import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
import Flapjack.Pancake.Semantics.PanSem.ClockTimeout
import InitECandidate.Solver.WitnessRadix.RestoreLookup
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.Input.LoadWord
import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.Input.WordTupleFour
import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.WitnessRadix.AllocatedArena
import InitECandidate.Solver.Input.UDivMod.CurrentCost
import InitECandidate.Solver.Input.LocalEffectsCurrentScoped
import InitECandidate.Solver.GasBudget.U256LessThanCall
import InitECandidate.Solver.Input.AssignedCallData
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A real non-timeout run derives its funding from a checked run that uses
exactly the candidate allowance. This is the pinned evaluator's clock theorem. -/
theorem normal_from_zero_clock (source target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (program : ProgHOL 64) (price : Nat) (baseResult result : Option (PanSemResultExact 64))
    (base : evaluateHOLFiniteState {source with clock:=price} program=(baseResult,target))
    (zero : target.clock=0) (baseNotTimeout : baseResult≠some .timeOut)
    (normal : evaluateHOLFiniteState source program=(result,post)) (notTimeout : result≠some .timeOut) :
    price≤source.clock ∧ result=baseResult ∧ post={target with clock:=source.clock-price} := by
  have targetSame : {target with clock:=0}=target:=by rw [←zero]
  have baseZero : evaluateHOLFiniteState {source with clock:=price} program=(baseResult,{target with clock:=0}):=by
    rw [targetSame]
    exact base
  have actual : evaluateHOLFiniteState {{source with clock:=price} with clock:=source.clock} program=(result,post):=normal
  rcases evaluateHOLFiniteState_add_clock_or_timeout program {source with clock:=price} baseResult target
    baseZero baseNotTimeout source.clock result post actual with short|completed
  · exact (notTimeout short.1).elim
  · exact ⟨completed.2.1,completed.1,completed.2.2⟩

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.normal_from_zero_clock

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem arithmetic_frame (code) : LocalEffects.Preserves code (.seq smallGuard setupProgram) := by
  unfold smallGuard setupProgram initializedBody loop loopBody subtractBody returnPair
  exact LocalEffects.sequence code _ _
    (LocalEffects.conditional code _ _ _ (LocalEffects.returned code _) (LocalEffects.skip code))
    (LocalEffects.declared code _ _ _ _ (LocalEffects.declared code _ _ _ _ (LocalEffects.declared code _ _ _ _
    (LocalEffects.sequence code _ _ (LocalEffects.loop code _ _ (LocalEffects.sequence code _ _ (LocalEffects.assign code _ _)
    (LocalEffects.sequence code _ _ (LocalEffects.assign code _ _) (LocalEffects.conditional code _ _ _
    (LocalEffects.sequence code _ _ (LocalEffects.assign code _ _) (LocalEffects.assign code _ _)) (LocalEffects.skip code)))))
    (LocalEffects.returned code _)))))

/-- With the actual nonzero divisor, the trap branch is not executed.
Every outcome, including short-clock timeout, keeps all nonlocal fields. -/
theorem nonzero_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (b : BitVec 64)
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) (nonzero : b≠0#64) :
    LocalEffects.erase (evaluateHOLFiniteState source body).2=LocalEffects.erase source := by
  have read : eval source zeroTest=some (.val (.word 0#64)) := by
    simp [eval,zeroTest,localVar,evalHOLExact,toExact,bLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  simp only [eval] at read
  have guard : evaluateHOLFiniteState source zeroGuard=(none,source) := by
    rw [zeroGuard,evaluateHOLFiniteState_ite,read]
    simp
  rw [body_shape,evaluateHOLFiniteState_seq_line780,guard]
  exact arithmetic_frame source.code source rfl

namespace Divide

theorem nonzero_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) (nonzero : b≠0#64)
    (code : source.code.lookup (ofString "udivmod")=some (formals,UDivMod.body,returnShape)) :
    LocalEffects.erase (evaluateHOLFiniteState source body).2=LocalEffects.erase source := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "a",localVar "b"]=some [.val (.word a),.val (.word b)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,aLocal,bLocal]
  obtain ⟨callee,called,aCell,bCell⟩:=word_pair_environment source.code.lookup (ofString "udivmod") (ofString "a") (ofString "b") UDivMod.body returnShape a b (by decide) code
  rw [shape]
  exact LocalEffects.scoped_current source (ofString "qr") returnShape (ofString "udivmod") [localVar "a",localVar "b"] _ UDivMod.body tail callee returnShape args called
    (UDivMod.nonzero_frame (callEntryStateHOLFinite source callee) b bCell nonzero) (LocalEffects.returned source.code _)

end Divide
end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.nonzero_frame
#print axioms InitECandidate.Solver.Input.UDivMod.Divide.nonzero_frame


namespace InitECandidate.Solver.Input.UDivMod.WideDigits
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
abbrev Quad:=RlpWrite.U256Value.Words

def digit (words : Quad) (index : Nat) : BitVec 64:=match index with
  | 0=>words 0 &&& 4294967295#64 | 1=>words 0>>>(32:Nat)
  | 2=>words 1 &&& 4294967295#64 | 3=>words 1>>>(32:Nat)
  | 4=>words 2 &&& 4294967295#64 | 5=>words 2>>>(32:Nat)
  | 6=>words 3 &&& 4294967295#64 | _=>words 3>>>(32:Nat)

def number (contents : Nat→ BitVec 64) : Nat→ Nat
  | 0=>0
  | count+1=>number contents count+2^(32*count)*(contents count).toNat

def quadNumber (words : Quad) : Nat:=
  (words 0).toNat+2^64*(words 1).toNat+2^128*(words 2).toNat+2^192*(words 3).toNat

private theorem half_number (word : BitVec 64) :
    (word &&& 4294967295#64).toNat+2^32*(word>>>(32:Nat)).toNat=word.toNat := by
  have lower : (word &&& 4294967295#64).toNat=word.toNat%2^32:=by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod word.toNat 32
  have upper : (word>>>(32:Nat)).toNat=word.toNat/2^32:=by
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rw [lower,upper]
  omega

theorem digit_small (words : Quad) (index : Nat) (inside : index<8) : (digit words index).toNat<2^32 := by
  have lower (word : BitVec 64) : (word &&& 4294967295#64).toNat<2^32:=by
    rw [BitVec.toNat_and]
    change word.toNat &&& (2^32-1)<2^32
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have upper (word : BitVec 64) : (word>>>(32:Nat)).toNat<2^32:=by
    have bounded:=word.isLt
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    omega
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7:=by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact lower _ | exact upper _

theorem digits_number (words : Quad) : number (digit words) 8=quadNumber words := by
  have first:=half_number (words 0)
  have second:=half_number (words 1)
  have third:=half_number (words 2)
  have fourth:=half_number (words 3)
  simp only [number,digit,quadNumber]
  omega

theorem number_zero (contents : Nat→ BitVec 64) (count : Nat) (zero : ∀ index,index<count→ contents index=0#64) :
    number contents count=0 := by
  induction count with
  | zero=>rfl
  | succ count ih=>
    rw [number,ih (by intro index inside;exact zero index (by omega)),zero count (by omega)]
    simp

def slot (pointer : BitVec 64) (index : Nat) : BitVec 64:=pointer+BitVec.ofNat 64 (8*index)
def Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→ BitVec 64) (count : Nat) : Prop:=
  ∀ index,index<count→ source.memory (slot pointer index)=.word (contents index)

theorem slot_injective (pointer : BitVec 64) (left right : Nat) (leftSmall : left<16) (rightSmall : right<16)
    (same : slot pointer left=slot pointer right) : left=right := by
  have equal : (BitVec.ofNat 64 (8*left))=(BitVec.ofNat 64 (8*right)):=
    (BitVec.add_right_inj pointer).mp same
  have native:=congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at native
  omega

def writeMemory (memory : BitVec 64→ HolWordLab 64) (pointer : BitVec 64) (contents : Nat→ BitVec 64) : Nat→ BitVec 64→ HolWordLab 64
  | 0=>memory
  | count+1=>StoreWord.put (writeMemory memory pointer contents count) (slot pointer count) (contents count)
def written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→ BitVec 64) (count : Nat) :=
  {source with memory:=writeMemory source.memory pointer contents count}

theorem written_image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→ BitVec 64)
    (count : Nat) (small : count≤16) : Image (written source pointer contents count) pointer contents count := by
  intro index inside
  change writeMemory source.memory pointer contents count (slot pointer index)=.word (contents index)
  induction count with
  | zero=>omega
  | succ count ih=>
    rw [writeMemory]
    by_cases last : index=count
    · subst index
      simp [StoreWord.put]
    · have away : slot pointer index≠slot pointer count:=by
        intro same
        exact last (slot_injective pointer index count (by omega) (by omega) same)
      simp only [StoreWord.put,if_neg away]
      exact ih (by omega) (by omega)

theorem written_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (contents : Nat→ BitVec 64)
    (count : Nat) (away : ∀ index,index<count→ query≠slot pointer index) :
    (written source pointer contents count).memory query=source.memory query := by
  change writeMemory source.memory pointer contents count query=source.memory query
  induction count with
  | zero=>rfl
  | succ count ih=>
    simp only [writeMemory,StoreWord.put,if_neg (away count (by omega))]
    exact ih (by intro index inside;exact away index (by omega))

theorem mapped_arena (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 64)
    (aligned : pointer.toNat%8=0) : ∀ index,index<8→ source.memaddrs (slot pointer index) := by
  intro index inside
  exact AllocatedBytes.word_mapped source pointer 64 (8*index) domain arena (by omega) aligned (by omega)

end InitECandidate.Solver.Input.UDivMod.WideDigits

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.digit_small
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.digits_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.number_zero
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.slot_injective
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.written_image
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.written_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.mapped_arena

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_u256_to_digits with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "p",.one),(ofString "a",RlpWrite.U256Value.tupleShape)]
def destination (index : Nat) : ExpHOL 64:=
  if index=0 then localVar "p" else .op .add [localVar "p",.const (BitVec.ofNat 64 (8*index))]
def expression (index : Nat) : ExpHOL 64:=
  if index%2=0 then .op .and [.rfield (index/2) (localVar "a"),.const 4294967295#64]
  else .shift .lsr (.rfield (index/2) (localVar "a")) (.const 32#64)
def stores (index : Nat) : Nat→ ProgHOL 64
  | 0=>.return (.const 0#64)
  | count+1=>.seq (.store (destination index) (expression index)) (stores (index+1) count)

theorem body_shape : body=stores 0 8 := by
  simp [body,Guest.Software.guestFn_u256_to_digits,progToHOL,expToHOL,shapeToHOL,stores,destination,expression,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "u256_to_digits")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 58 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_u256_to_digits) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,RlpWrite.U256Value.tupleShape,
    Guest.Software.guestFn_u256_to_digits,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

private theorem destination_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer))) :
    eval source (destination index)=some (.val (.word (slot pointer index))) := by
  by_cases zero : index=0
  · subst index
    simp [eval,destination,slot,localVar,evalHOLExact,toExact,p]
  · simp [eval,destination,slot,zero,localVar,evalHOLExact,evalListHOLExact,toExact,p,valueIsWord,valueWord,wordOpHOL,wordOp]

private theorem expression_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Quad) (index : Nat) (inside : index<8)
    (a : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple words)) :
    eval source (expression index)=some (.val (.word (digit words index))) := by
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7:=by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [eval,expression,digit,localVar,evalHOLExact,evalListHOLExact,toExact,a,RlpWrite.U256Value.tuple,
    valueWord,valueIsWord,wordOpHOL,wordOp,wordShiftHOL,AndOp.and]
  all_goals rfl

/-- The exact original ordered word stores construct the corresponding
physical prefix image, with no incoming content assumption. -/
theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Quad) (index count : Nat)
    (inside : index+count≤8)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (a : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple words))
    (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index)) :
    evaluateHOLFiniteState (written source pointer (digit words) index) (stores index count)=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (written source pointer (digit words) (index+count))) := by
  classical
  induction count generalizing index with
  | zero=>
    simp [stores,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  | succ count ih=>
    let entry:=written source pointer (digit words) index
    have pEntry : entry.locals.lookup (ofString "p")=some (.val (.word pointer)):=p
    have aEntry : entry.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple words):=a
    have currentMapped : entry.memaddrs (slot pointer index):=mapped index (by omega)
    have actual:=StoreWord.execute entry (destination index) (expression index) (slot pointer index) (digit words index)
      (destination_read entry pointer index pEntry) (expression_read entry words index (by omega) aEntry) currentMapped
    change evaluateHOLFiniteState entry (.store (destination index) (expression index))=
      (none,written source pointer (digit words) (index+1)) at actual
    change evaluateHOLFiniteState entry (stores index (count+1))=_
    rw [stores,WitnessRadix.StateSteps.next_sequence entry _ _ _ actual (Nat.le_refl _)]
    have sum : index+1+count=index+(count+1):=by omega
    simpa only [sum] using ih (index+1) (by omega)

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Quad)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (a : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple words))
    (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index)) :
    evaluateHOLFiniteState source body=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (written source pointer (digit words) 8)) := by
  rw [body_shape]
  exact stores_execute source pointer words 0 8 (by decide) p a mapped

private theorem stores_cost (code) (index count : Nat) : ClockCost.Bound code (stores index count) 0 := by
  induction count generalizing index with
  | zero=>exact ClockCost.returned code _
  | succ count ih=>exact ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ih (index+1))

theorem body_cost (code) : ClockCost.Bound code body 0 := by
  rw [body_shape]
  exact stores_cost code 0 8

end InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.body_shape
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.stores_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.body_cost


namespace InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private def rawLocals (pointer : BitVec 64) (words : Quad) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "a" then some (RlpWrite.U256Value.tuple words) else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS→ Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer : BitVec 64) (words : Quad)
    (code : codeFn (ofString "u256_to_digits")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "u256_to_digits") [.val (.word pointer),RlpWrite.U256Value.tuple words]=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "a")=some (RlpWrite.U256Value.tuple words) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word pointer),RlpWrite.U256Value.tuple words] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word pointer),RlpWrite.U256Value.tuple words]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=by
    simp [formals,RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "p"≠ofString "a" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "u256_to_digits") [.val (.word pointer),RlpWrite.U256Value.tuple words]=some (body,rawLocals pointer words,.one):=by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "p"≠ofString "a" by decide]
  · simp [rawLocals]

def callerPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Quad) :=
  {source with memory:=writeMemory source.memory pointer (digit words) 8,clock:=source.clock-1}

/-- Original ignored-result caller, including its actual argument ABI and
one call tick, installs the exact physical digit image. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Quad)
    (arguments : List (ExpHOL 64)) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word pointer),RlpWrite.U256Value.tuple words])
    (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index)) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "u256_to_digits") arguments)=(none,callerPost source pointer words) := by
  obtain ⟨callee,called,pCell,aCell⟩:=environment source.code.lookup pointer words (original_code source.code installed)
  have run:=execute (callEntryStateHOLFinite source callee) pointer words pCell aCell mapped
  exact evaluateHOLFiniteState_call_return_caller_locals source none (ofString "u256_to_digits") arguments _ body callee .one
    (.val (.word 0#64)) _ args called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])

theorem call_cost (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (some (none,none)) (ofString "u256_to_digits") arguments) 1 := by
  exact ClockCost.call_body code (some none) (ofString "u256_to_digits") arguments formals body .one 0
    (original_code code installed) (body_cost code)

/-- A genuine normally continuing caller derives its own funding and exact
returned memory state; no future normal helper run is supplied. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Quad)
    (arguments : List (ExpHOL 64)) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word pointer),RlpWrite.U256Value.tuple words])
    (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "u256_to_digits") arguments)=(none,post)) :
    1≤source.clock ∧ post=callerPost source pointer words := by
  obtain ⟨callee,called,pCell,aCell⟩:=environment source.code.lookup pointer words (original_code source.code installed)
  have funded:=(CallNormal.ignored_callee_return source post (ofString "u256_to_digits") arguments _ body callee .one args called normal).1
  have expected:=call_execute source pointer words arguments installed args mapped funded
  exact ⟨funded,congrArg Prod.snd (normal.symm.trans expected)⟩

theorem caller_image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Quad) :
    Image (callerPost source pointer words) pointer (digit words) 8 :=
  written_image source pointer (digit words) 8 (by decide)

theorem caller_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (words : Quad)
    (away : ∀ index,index<8→ query≠slot pointer index) : (callerPost source pointer words).memory query=source.memory query :=
  written_away source pointer query (digit words) 8 away

theorem caller_away_range (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (words : Quad)
    (fits : pointer.toNat+64≤2^64) (outside : query.toNat<pointer.toNat ∨ pointer.toNat+64≤query.toNat) :
    (callerPost source pointer words).memory query=source.memory query := by
  apply caller_away
  intro index inside hit
  have offset : (BitVec.ofNat 64 (8*index)).toNat=8*index:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have location : (slot pointer index).toNat=pointer.toNat+8*index:=by
    rw [slot,BitVec.toNat_add_of_lt (by rw [offset];omega),offset]
  have same:=congrArg BitVec.toNat hit
  rw [location] at same
  rcases outside with before|after <;> omega

end InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.environment
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.call_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.call_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.call_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.caller_image
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.caller_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToDigits.caller_away_range


namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Length
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def result (contents : Nat→ BitVec 64) : Nat→ Nat
  | 0=>0
  | count+1=>if contents count=0#64 then result contents count else count+1
def scans (contents : Nat→ BitVec 64) : Nat→ Nat
  | 0=>0
  | count+1=>if contents count=0#64 then scans contents count+1 else 1

theorem result_bound (contents : Nat→ BitVec 64) (count : Nat) : result contents count≤count := by
  induction count with
  | zero=>rfl
  | succ count ih=>simp only [result];split_ifs <;> omega

theorem scans_bound (contents : Nat→ BitVec 64) (count : Nat) : scans contents count≤count := by
  induction count with
  | zero=>rfl
  | succ count ih=>simp only [scans];split_ifs <;> omega

theorem result_zero (contents : Nat→ BitVec 64) (count : Nat) : result contents count=0 ↔ ∀ index,index<count→ contents index=0#64 := by
  induction count with
  | zero=>simp [result]
  | succ count ih=>
    by_cases zero : contents count=0#64
    · rw [result,if_pos zero,ih]
      constructor
      · intro all index inside
        by_cases last : index=count
        · simpa only [last] using zero
        · exact all index (by omega)
      · intro all index inside
        exact all index (by omega)
    · rw [result,if_neg zero]
      constructor
      · omega
      · intro all
        exact (zero (all count (by omega))).elim

theorem result_leading (contents : Nat→ BitVec 64) (count : Nat) (positive : 0<result contents count) :
    contents (result contents count-1)≠0#64 := by
  induction count with
  | zero=>simp [result] at positive
  | succ count ih=>
    by_cases zero : contents count=0#64
    · rw [result,if_pos zero] at positive ⊢
      exact ih positive
    · simpa only [result,if_neg zero,Nat.add_sub_cancel] using zero

theorem result_suffix (contents : Nat→ BitVec 64) (count index : Nat)
    (after : result contents count≤index) (inside : index<count) : contents index=0#64 := by
  induction count with
  | zero=>omega
  | succ count ih=>
    by_cases zero : contents count=0#64
    · rw [result,if_pos zero] at after
      by_cases last : index=count
      · simpa only [last] using zero
      · exact ih after (by omega)
    · rw [result,if_neg zero] at after
      omega

def body : ProgHOL 64:=match Guest.Software.guestFn_digits_len with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "p",.one),(ofString "n",.one)]
def loopTest : ExpHOL 64:=.cmp .lower (.const 0#64) (localVar "n")
def previous : ExpHOL 64:=.op .sub [localVar "n",.const 1#64]
def address : ExpHOL 64:=.op .add [localVar "p",.panop .mul [previous,.const 8#64]]
def nonzeroTest : ExpHOL 64:=.cmp .notEqual (.load .one address) (.const 0#64)
def guard : ProgHOL 64:=.ite nonzeroTest (.return (localVar "n")) .skip
def loopBody : ProgHOL 64:=.seq guard (.assign .local (ofString "n") previous)
def loop : ProgHOL 64:=.while loopTest loopBody
def returnZero : ProgHOL 64:=.return (.const 0#64)

theorem body_shape : body=.seq loop returnZero := by
  simp only [body,Guest.Software.guestFn_digits_len,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    loop,loopTest,loopBody,guard,nonzeroTest,address,previous,returnZero,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "digits_len")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 60 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_digits_len) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_digits_len,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

private theorem loop_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (small : count≤16)
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) loopTest=
      some (.val (.word (if 0<count then 1#64 else 0#64))) := by
  have encoded : (BitVec.ofNat 64 count).toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [finite_eval]
  simp [eval,loopTest,localVar,evalHOLExact,toExact,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,encoded]

private theorem previous_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (positive : 0<count)
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    eval source previous=some (.val (.word (BitVec.ofNat 64 (count-1)))) := by
  have subtraction:=BitVec.ofNat_sub_ofNat_of_le (w:=64) count 1 (by decide) positive
  simp [eval,previous,localVar,evalHOLExact,evalListHOLExact,toExact,n,valueIsWord,valueWord,wordOpHOL,wordOp,subtraction]

private theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (count : Nat) (positive : 0<count)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    eval source address=some (.val (.word (slot pointer (count-1)))) := by
  have index:=previous_read source count positive n
  simp only [eval] at index
  simp [eval,address,localVar,evalHOLExact,evalListHOLExact,toExact,p,index,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,Nat.mul_comm]

/-- Exact real body at a mapped digit, including its early caller return. -/
theorem body_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→ BitVec 64) (count : Nat)
    (positive : 0<count)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (mapped : source.memaddrs (slot pointer (count-1))) (cell : source.memory (slot pointer (count-1))=.word (contents (count-1))) :
    evaluateHOLFiniteState source loopBody=
      if contents (count-1)=0#64 then (none,bind source "n" (BitVec.ofNat 64 (count-1)))
      else (some (.returned (.val (.word (BitVec.ofNat 64 count)))),emptyLocalsHOLFinite source) := by
  classical
  have loaded:=Witness.load_word_read source address (slot pointer (count-1)) (contents (count-1)) (address_read source pointer count positive p n) mapped cell
  have tested : eval source nonzeroTest=some (.val (.word (if contents (count-1)=0#64 then 0#64 else 1#64))):=by
    simp only [eval] at loaded ⊢
    rw [nonzeroTest,evalHOLExact,loaded]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at tested
  rw [loopBody,evaluateHOLFiniteState_seq_line780,guard,evaluateHOLFiniteState_ite,tested]
  by_cases zero : contents (count-1)=0#64
  · simp only [if_pos zero,if_pos (show (0#64 : BitVec 64)=0 from rfl),evaluateHOLFiniteState_skip]
    exact WitnessRadix.StateSteps.assign_execute source "n" previous _ _ n (previous_read source count positive n)
  · simp only [if_neg zero,if_neg (show (1#64 : BitVec 64)≠0 by decide)]
    have returned : evaluateHOLFiniteState source (.return (localVar "n"))=
        (some (.returned (.val (.word (BitVec.ofNat 64 count)))),emptyLocalsHOLFinite source):=by
      simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,n,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [returned]

/-- Complete actual scan, at every clock, over the initialized physical image. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (small : count≤16)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→ source.memaddrs (slot pointer index)) :
    evaluateHOLFiniteState source body=
      if scans contents count≤source.clock then
        (some (.returned (.val (.word (BitVec.ofNat 64 (result contents count))))),
          emptyLocalsHOLFinite {source with clock:=source.clock-scans contents count})
      else (some .timeOut,emptyLocalsHOLFinite {source with clock:=0}) := by
  classical
  induction count generalizing source with
  | zero=>
    have test:=loop_test source 0 small n
    simp only [Nat.lt_irrefl,↓reduceIte] at test
    rw [body_shape,evaluateHOLFiniteState_seq_line780,loop,evaluateHOLFiniteState_while_total,test]
    simp [returnZero,evaluateHOLFiniteState_return,evalHOLExact,toExact,scans,result,
      shapeOfHOLExact,sizeOfShapeWithContextHOL]
  | succ count ih=>
    have test:=loop_test source (count+1) small n
    simp only [show 0<count+1 from by omega,↓reduceIte] at test
    by_cases exhausted : source.clock=0
    · rw [body_shape,evaluateHOLFiniteState_seq_line780,loop,evaluateHOLFiniteState_while_total,test]
      have positive : 0<scans contents (count+1):=by
        simp only [scans]; split_ifs <;> omega
      simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide),if_pos exhausted]
      simp only [exhausted,if_neg (show ¬scans contents (count+1)≤0 by omega)]
      have same : source={source with clock:=0}:=by
        exact (show source={source with clock:=source.clock} from rfl).trans
          (congrArg (fun clock:Nat=>{source with clock:=clock}) exhausted)
      rw [←same]
      simp only [if_pos (show (1#64 : BitVec 64)≠0 by decide)]
    · let entry:=decClockHOLFinite source
      have bodyRun:=body_step entry pointer contents (count+1) (by omega) p n
        (mapped count (by omega)) (image count (by omega))
      simp only [Nat.add_sub_cancel] at bodyRun
      by_cases zero : contents count=0#64
      · let next:=bind entry "n" (BitVec.ofNat 64 count)
        have nextP : next.locals.lookup (ofString "p")=some (.val (.word pointer)):=
          (bind_lookup_other entry "n" "p" _ (by decide)).trans p
        have nextN : next.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))):=
          bind_lookup_same entry "n" _
        have nextImage : Image next pointer contents count:=by
          intro index inside
          exact image index (by omega)
        have nextMapped : ∀ index,index<count→ next.memaddrs (slot pointer index):=by
          intro index inside
          exact mapped index (by omega)
        have tailRun:=ih next (by omega) nextP nextN nextImage nextMapped
        have recurrence : evaluateHOLFiniteState source body=evaluateHOLFiniteState next body:=by
          rw [body_shape,evaluateHOLFiniteState_seq_line780,loop,evaluateHOLFiniteState_while_total,test]
          simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide),if_neg exhausted]
          rw [bodyRun,if_pos zero,WitnessRadix.StateSteps.fixed_clock entry next none (by rfl)]
          simp only [if_pos (show (1#64 : BitVec 64)≠0 by decide)]
          rw [evaluateHOLFiniteState_seq_line780]
        rw [recurrence,tailRun]
        have funded : scans contents count≤next.clock ↔ scans contents count+1≤source.clock:=by
          change scans contents count≤source.clock-1 ↔ scans contents count+1≤source.clock
          omega
        simp only [scans,if_pos zero,result,funded]
        split_ifs <;> simp only [next,entry,WitnessRadix.QueryBranch.bind,setVarHOLFinite,decClockHOLFinite,emptyLocalsHOLFinite] <;> congr 2 <;> omega
      · rw [body_shape,evaluateHOLFiniteState_seq_line780,loop,evaluateHOLFiniteState_while_total,test]
        simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide),if_neg exhausted]
        rw [bodyRun,if_neg zero,WitnessRadix.StateSteps.fixed_clock entry (emptyLocalsHOLFinite entry)
          (some (.returned (.val (.word (BitVec.ofNat 64 (count+1)))))) (by rfl)]
        simp [scans,result,zero,exhausted,entry,decClockHOLFinite,emptyLocalsHOLFinite]

/-- All outcomes of the real mapped scan spend at most its initial digit count. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (small : count≤16)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→ source.memaddrs (slot pointer index)) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤count := by
  rw [execute source pointer contents count small p n image mapped]
  have scansBound:=scans_bound contents count
  split_ifs
  · change source.clock-(source.clock-scans contents count)≤count
    omega
  · change source.clock-0≤count
    omega

/-- An actual normal return supplies its own funding, exact length and frame. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (small : count≤16)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→ source.memaddrs (slot pointer index)) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    scans contents count≤source.clock ∧ returned=.val (.word (BitVec.ofNat 64 (result contents count))) ∧
      post=emptyLocalsHOLFinite {source with clock:=source.clock-scans contents count} := by
  rw [execute source pointer contents count small p n image mapped] at normal
  by_cases funded : scans contents count≤source.clock
  · rw [if_pos funded] at normal
    exact ⟨funded,by simpa using (congrArg Prod.fst normal).symm,(congrArg Prod.snd normal).symm⟩
  · simp only [if_neg funded,Prod.mk.injEq,Option.some.injEq] at normal
    cases normal.1

/-- Trimming the leading zero cells does not change the represented number. -/
theorem trimmed_number (contents : Nat→ BitVec 64) (count : Nat) :
    number contents (result contents count)=number contents count := by
  induction count with
  | zero=>rfl
  | succ count ih=>
    by_cases zero : contents count=0#64
    · simpa [result,zero,number] using ih
    · simp only [result,if_neg zero]

theorem positive_length (contents : Nat→ BitVec 64) (count : Nat) (positive : 0<number contents count) :
    0<result contents count := by
  by_contra zero
  have all:=(result_zero contents count).1 (by omega)
  have vanished:=number_zero contents count all
  omega

/-- Real scalar ABI and current physical image price the scoped caller. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (small : count≤16)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 count))])
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→ source.memaddrs (slot pointer index))
    (tailBound : ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "digits_len") arguments continuation)).2.clock≤
      count+tailPrice+1 := by
  obtain ⟨callee,called,pCell,nCell⟩:=word_pair_environment source.code.lookup (ofString "digits_len")
    (ofString "p") (ofString "n") body .one pointer (BitVec.ofNat 64 count) (by decide) (original_code source.code installed)
  exact ClockCost.scoped_current source (ofString name) .one (ofString "digits_len") arguments _ body continuation callee .one count tailPrice args called
    (body_cost (callEntryStateHOLFinite source callee) pointer contents count small pCell nCell image mapped) tailBound

/-- A funded actual caller returns the real length and resumes with its exact
scan charge. Early returns need only their actual number of scans. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (small : count≤16)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 count))])
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→ source.memaddrs (slot pointer index))
    (enough : scans contents count+1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "digits_len") arguments continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-scans contents count}
        name (BitVec.ofNat 64 (result contents count))) continuation
       (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,pCell,nCell⟩:=word_pair_environment source.code.lookup (ofString "digits_len")
    (ofString "p") (ofString "n") body .one pointer (BitVec.ofNat 64 count) (by decide) (original_code source.code installed)
  have run:=execute (callEntryStateHOLFinite source callee) pointer contents count small pCell nCell image mapped
  rw [if_pos (show scans contents count≤(callEntryStateHOLFinite source callee).clock from by
    change scans contents count≤source.clock-1;omega)] at run
  exact CallNormal.pure_return_execute source _ name (ofString "digits_len") arguments _ body continuation callee
    (BitVec.ofNat 64 (result contents count)) (scans contents count) args called (by omega) run rfl

/-- A real normally returning child supplies the exact caller continuation.
The caller's own call tick is charged separately by the scoped-call rules. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (small : count≤16)
    (installed : OriginalCode.Installed source.code)
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→ source.memaddrs (slot pointer index))
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "digits_len")
      [.val (.word pointer),.val (.word (BitVec.ofNat 64 count))]=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    scans contents count≤source.clock-1 ∧ returned=.val (.word (BitVec.ofNat 64 (result contents count))) ∧
      CallNormal.continuationEntry source target name returned=
        bind {source with clock:=source.clock-1-scans contents count} name (BitVec.ofNat 64 (result contents count)) := by
  obtain ⟨expected,lookup,pCell,nCell⟩:=word_pair_environment source.code.lookup (ofString "digits_len")
    (ofString "p") (ofString "n") body .one pointer (BitVec.ofNat 64 count) (by decide) (original_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at pCell nCell
  rw [bodyEq] at run
  obtain ⟨funded,result,post⟩:=body_normal (callEntryStateHOLFinite source callee) target pointer contents count small pCell nCell image mapped returned run
  refine ⟨funded,result,?_⟩
  simp only [CallNormal.continuationEntry,result,post]
  rfl

end InitECandidate.Solver.Input.UDivMod.WideDigits.Length

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.result_bound
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.scans_bound
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.result_zero
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.result_leading
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.result_suffix
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.body_shape
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.body_step

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.body_cost

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.body_normal

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.trimmed_number

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.positive_length

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.call_cost

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.call_execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.resume

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def words (contents : Nat→ BitVec 64) : Quad:=fun index=>
  contents (2*index.val) ||| (contents (2*index.val+1)<<<(32:Nat))

theorem pair_number (low high : BitVec 64) (lowSmall : low.toNat<2^32) (highSmall : high.toNat<2^32) :
    (low ||| (high<<<(32:Nat))).toNat=low.toNat+2^32*high.toNat := by
  have shifted : (high<<<(32:Nat)).toNat=2^32*high.toNat:=by
    rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mod_eq_of_lt (by nlinarith)]
    omega
  rw [BitVec.toNat_or,shifted,Nat.or_comm]
  exact (Nat.two_pow_add_eq_or_of_lt (i:=32) lowSmall high.toNat).symm.trans (by omega)

theorem words_number (contents : Nat→ BitVec 64) (small : ∀ index,index<8→ (contents index).toNat<2^32) :
    quadNumber (words contents)=number contents 8 := by
  change (contents 0 ||| contents 1<<<(32:Nat)).toNat+2^64*(contents 2 ||| contents 3<<<(32:Nat)).toNat+
    2^128*(contents 4 ||| contents 5<<<(32:Nat)).toNat+2^192*(contents 6 ||| contents 7<<<(32:Nat)).toNat=number contents 8
  rw [pair_number _ _ (small 0 (by decide)) (small 1 (by decide)),
    pair_number _ _ (small 2 (by decide)) (small 3 (by decide)),
    pair_number _ _ (small 4 (by decide)) (small 5 (by decide)),
    pair_number _ _ (small 6 (by decide)) (small 7 (by decide))]
  simp only [number]
  omega

theorem digit_inverse (value : Quad) : words (digit value)=value := by
  funext index
  obtain ⟨index,inside⟩:=index
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3:=by omega
  rcases cases with rfl|rfl|rfl|rfl
  · apply BitVec.eq_of_toNat_eq
    have joined:=pair_number (digit value 0) (digit value 1)
      (digit_small value _ (by decide)) (digit_small value _ (by decide))
    have split:=half_number (value 0)
    change (digit value 0 ||| digit value 1<<<(32:Nat)).toNat=(value 0).toNat
    simp only [digit] at joined ⊢
    omega
  · apply BitVec.eq_of_toNat_eq
    have joined:=pair_number (digit value 2) (digit value 3)
      (digit_small value _ (by decide)) (digit_small value _ (by decide))
    have split:=half_number (value 1)
    change (digit value 2 ||| digit value 3<<<(32:Nat)).toNat=(value 1).toNat
    simp only [digit] at joined ⊢
    omega
  · apply BitVec.eq_of_toNat_eq
    have joined:=pair_number (digit value 4) (digit value 5)
      (digit_small value _ (by decide)) (digit_small value _ (by decide))
    have split:=half_number (value 2)
    change (digit value 4 ||| digit value 5<<<(32:Nat)).toNat=(value 2).toNat
    simp only [digit] at joined ⊢
    omega
  · apply BitVec.eq_of_toNat_eq
    have joined:=pair_number (digit value 6) (digit value 7)
      (digit_small value _ (by decide)) (digit_small value _ (by decide))
    have split:=half_number (value 3)
    change (digit value 6 ||| digit value 7<<<(32:Nat)).toNat=(value 3).toNat
    simp only [digit] at joined ⊢
    omega

def body : ProgHOL 64:=match Guest.Software.guestFn_digits_to_u256 with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "p",.one)]
def limb (index : Nat) : ExpHOL 64:=.op .or [.load .one (ToDigits.destination (2*index)),
  .shift .lsl (.load .one (ToDigits.destination (2*index+1))) (.const 32#64)]
def expression : ExpHOL 64:=.rstruct [limb 0,limb 1,limb 2,limb 3]

theorem body_shape : body=.return expression := by
  simp [body,Guest.Software.guestFn_digits_to_u256,progToHOL,expToHOL,shapeToHOL,expression,limb,ToDigits.destination,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "digits_to_u256")=some (formals,body,RlpWrite.U256Value.tupleShape) := by
  have checked:=OriginalCode.indexed code installed 59 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_digits_to_u256) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,RlpWrite.U256Value.tupleShape,
    Guest.Software.guestFn_digits_to_u256,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

private theorem limb_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→ BitVec 64)
    (index : Fin 4) (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index)) :
    eval source (limb index.val)=some (.val (.word (words contents index))) := by
  have loInside : 2*index.val<8:=by omega
  have hiInside : 2*index.val+1<8:=by omega
  have lo:=Witness.load_word_read source (ToDigits.destination (2*index.val)) _ _
    (ToDigits.destination_read source pointer _ p) (mapped _ loInside) (image _ loInside)
  have hi:=Witness.load_word_read source (ToDigits.destination (2*index.val+1)) _ _
    (ToDigits.destination_read source pointer _ p) (mapped _ hiInside) (image _ hiInside)
  simp only [eval] at lo hi ⊢
  rw [limb,evalHOLExact]
  simp only [evalListHOLExact]
  rw [lo,evalHOLExact,hi]
  simp [evalHOLExact,words,valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL,OrOp.or]

/-- The original read/OR/shift return reconstructs the actual physical digits,
changes no nonlocal state and spends no body source ticks. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→ BitVec 64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index)) :
    evaluateHOLFiniteState source body=
      (some (.returned (RlpWrite.U256Value.tuple (words contents))),emptyLocalsHOLFinite source) := by
  classical
  have lo:=limb_read source pointer contents 0 p image mapped
  have mid:=limb_read source pointer contents 1 p image mapped
  have high:=limb_read source pointer contents 2 p image mapped
  have top:=limb_read source pointer contents 3 p image mapped
  simp only [eval] at lo mid high top
  change evalHOLExact source.toExact (limb 0)=_ at lo
  change evalHOLExact source.toExact (limb 1)=_ at mid
  change evalHOLExact source.toExact (limb 2)=_ at high
  change evalHOLExact source.toExact (limb 3)=_ at top
  rw [body_shape,evaluateHOLFiniteState_return,expression,evalHOLExact]
  simp only [evalListHOLExact]
  rw [lo,mid,high,top]
  simp [RlpWrite.U256Value.tuple,shapeOfHOLExact,sizeOfShapeWithContextHOL]

theorem body_cost (code) : ClockCost.Bound code body 0 := by
  rw [body_shape]
  exact ClockCost.returned code _

theorem call_cost (code) (installed : OriginalCode.Installed code) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (tailBound : ClockCost.Bound code continuation tailPrice) :
    ClockCost.Bound code (.decCall (ofString name) RlpWrite.U256Value.tupleShape (ofString "digits_to_u256") arguments continuation) (tailPrice+1) := by
  simpa only [Nat.zero_add] using ClockCost.scoped_body code (ofString name) RlpWrite.U256Value.tupleShape
    (ofString "digits_to_u256") arguments continuation formals body RlpWrite.U256Value.tupleShape 0 tailPrice
    (original_code code installed) (body_cost code) tailBound

/-- Actual unary scalar ABI with the genuine four-word return shape. -/
theorem environment (codeFn : MlS→ Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer : BitVec 64)
    (code : codeFn (ofString "digits_to_u256")=some (formals,body,RlpWrite.U256Value.tupleShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "digits_to_u256") [.val (.word pointer)]=some (body,callee,RlpWrite.U256Value.tupleShape) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) := by
  let rawLocals : MlS→ Option (ValueHOL 64):=fun name=>if name=ofString "p" then some (.val (.word pointer)) else none
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word pointer)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word pointer)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=by
    simp [formals,shapeOfHOLExact,shapeEqHOL_eq_true]
  have raw : lookupCodeHOLExact codeFn (ofString "digits_to_u256") [.val (.word pointer)]=
      some (body,rawLocals,RlpWrite.U256Value.tupleShape):=by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [rawLocals]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→ BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word pointer)])
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index))
    (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) RlpWrite.U256Value.tupleShape (ofString "digits_to_u256") arguments continuation)=
      (let output:=evaluateHOLFiniteState (setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple (words contents))
        {source with clock:=source.clock-1}) continuation
       (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,pCell⟩:=environment source.code.lookup pointer (original_code source.code installed)
  have run:=execute (callEntryStateHOLFinite source callee) pointer contents pCell image mapped
  exact CallNormal.return_execute source _ name RlpWrite.U256Value.tupleShape (ofString "digits_to_u256") arguments _
    body continuation callee RlpWrite.U256Value.tupleShape (RlpWrite.U256Value.tuple (words contents)) args called enough run
    (by simp [RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true])

/-- The actual normal child run determines the reconstructed value and the
unchanged physical caller state with its one-call decrement. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64)
    (contents : Nat→ BitVec 64) (installed : OriginalCode.Installed source.code)
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index))
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "digits_to_u256") [.val (.word pointer)]=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    returned=RlpWrite.U256Value.tuple (words contents) ∧
      CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple (words contents)) {source with clock:=source.clock-1} := by
  obtain ⟨expected,lookup,pCell⟩:=environment source.code.lookup pointer (original_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at pCell
  rw [bodyEq] at run
  have completed:=execute (callEntryStateHOLFinite source callee) pointer contents pCell image mapped
  have actualEq:=run.symm.trans completed
  have result : returned=RlpWrite.U256Value.tuple (words contents):=by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst actualEq
  have targetEq : target=emptyLocalsHOLFinite (callEntryStateHOLFinite source callee):=congrArg Prod.snd actualEq
  refine ⟨result,?_⟩
  simp only [CallNormal.continuationEntry,result,targetEq]
  rfl

end InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.pair_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.words_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.digit_inverse
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.body_shape
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.body_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.call_cost

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.environment

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.call_execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.resume

namespace InitECandidate.Solver.Input.UDivMod.Div64By32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A funded real scalar divider caller returns the genuine quotient and
remainder and resumes its actual continuation after33source ticks. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (high low divisor : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word high),.val (.word low),.val (.word divisor)])
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat) (lowSmall : low.toNat<2^32)
    (enough : 33≤source.clock) :
    ∃ q r,q.toNat=(high.toNat*2^32+low.toNat)/divisor.toNat ∧
      r.toNat=(high.toNat*2^32+low.toNat)%divisor.toNat ∧ q.toNat<2^32 ∧ r.toNat<divisor.toNat ∧
      evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "div64by32") arguments continuation)=
        (let output:=evaluateHOLFiniteState (setVarHOLFinite (ofString name) (pairValue q r)
          {source with clock:=source.clock-33}) continuation
         (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,highCell,lowCell,divisorCell⟩:=word_triple_environment source.code.lookup (ofString "div64by32")
    (ofString "hi") (ofString "lo") (ofString "d") body returnShape high low divisor (by decide) (by decide) (by decide)
    (original_code source.code installed)
  obtain ⟨target,initialQ,initialR,setup,clock,frame,arithmetic⟩:=setup_execute (callEntryStateHOLFinite source callee)
    high low divisor highCell lowCell divisorCell (by change 32≤source.clock-1;omega)
  rw [←body_shape] at setup
  obtain ⟨q,r,result,funded,clock,frame,quotient,remainder,qSmall,rSmall⟩:=body_normal_digits
    (callEntryStateHOLFinite source callee) target high low divisor highCell lowCell divisorCell
    divisorSmall highSmall lowSmall _ setup
  rw [result] at setup
  have targetClock : target.clock=source.clock-33:=by
    change target.clock=source.clock-1-32 at clock
    simpa only [Nat.sub_sub] using clock
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) frame
  change {target with locals:=source.locals}={source with clock:=target.clock} at callerFrame
  have canonical : {target with locals:=source.locals}={source with clock:=source.clock-33}:=
    callerFrame.trans (congrArg (fun remaining : Nat=>{source with clock:=remaining}) targetClock)
  have actual:=CallNormal.return_execute source target name returnShape (ofString "div64by32") arguments _ body continuation
    callee returnShape (pairValue q r) args called (by omega) setup
    (by simp [pairValue,returnShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  refine ⟨q,r,quotient,remainder,qSmall,rSmall,?_⟩
  simpa only [CallNormal.continuationEntry,canonical] using actual

end InitECandidate.Solver.Input.UDivMod.Div64By32

#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.call_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Single
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_divmnu with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "q",.one),(ofString "r",.one),(ofString "u",.one),
  (ofString "m",.one),(ofString "v",.one),(ofString "n",.one)]
def oneTest : ExpHOL 64:=.cmp .equal (localVar "n") (.const 1#64)
def previous : ExpHOL 64:=.op .sub [localVar "j",.const 1#64]
def address (name : String) : ExpHOL 64:=.op .add [localVar name,.panop .mul [localVar "j",.const 8#64]]
def arguments : List (ExpHOL 64):=[localVar "k",.load .one (address "u"),localVar "d"]
def quotientExpression : ExpHOL 64:=.rfield 0 (localVar "qr")
def remainderExpression : ExpHOL 64:=.rfield 1 (localVar "qr")
def tail : ProgHOL 64:=.seq (.store (address "q") quotientExpression)
  (.assign .local (ofString "k") remainderExpression)
def stepCall : ProgHOL 64:=.decCall (ofString "qr") returnShape (ofString "div64by32") arguments tail
def loopBody : ProgHOL 64:=.seq (.assign .local (ofString "j") previous) stepCall
def loopTest : ExpHOL 64:=.cmp .lower (.const 0#64) (localVar "j")
def loop : ProgHOL 64:=.while loopTest loopBody
def finish : ProgHOL 64:=.seq (.store (localVar "r") (localVar "k")) (.return (.const 0#64))
def initialized : ProgHOL 64:=.seq (.assign .local (ofString "j") (localVar "m")) (.seq loop finish)
def oneBranch : ProgHOL 64:=.dec (ofString "d") .one (.load .one (localVar "v"))
  (.dec (ofString "k") .one (.const 0#64) initialized)
def otherBranch : ProgHOL 64:=match body with
  | .dec _ _ _ (.dec _ _ _ (.seq _ rest))=>rest | _=>.skip

theorem body_shape : body=.dec (ofString "i") .one (.const 0#64)
    (.dec (ofString "j") .one (.const 0#64) (.seq (.ite oneTest oneBranch .skip) otherBranch)) := by
  simp only [body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    otherBranch,oneBranch,initialized,loop,loopTest,loopBody,stepCall,arguments,tail,finish,previous,address,
    quotientExpression,remainderExpression,returnShape,oneTest,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "divmnu")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 61 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_divmnu) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_divmnu,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

private theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64)
    (index : Nat) (p : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source (address name)=some (.val (.word (slot pointer index))) := by
  simp [eval,address,localVar,evalHOLExact,evalListHOLExact,toExact,p,j,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,Nat.mul_comm]

private theorem previous_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (index+1))))) :
    eval source previous=some (.val (.word (BitVec.ofNat 64 index))) := by
  have subtraction:=BitVec.ofNat_sub_ofNat_of_le (w:=64) (index+1) 1 (by decide) (by omega)
  simp [eval,previous,localVar,evalHOLExact,evalListHOLExact,toExact,j,valueIsWord,valueWord,wordOpHOL,wordOp,subtraction]

def next (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) (q r : BitVec 64) :=
  let indexed:=bind source "j" (BitVec.ofNat 64 index)
  let entry:=setVarHOLFinite (ofString "qr") (pairValue q r) {indexed with clock:=source.clock-33}
  restore indexed "qr" (bind {entry with memory:=StoreWord.put source.memory (slot pointer index) q} "k" r)

private theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer q r old : BitVec 64) (index : Nat)
    (qCell : source.locals.lookup (ofString "q")=some (.val (.word pointer)))
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))))
    (k : source.locals.lookup (ofString "k")=some (.val (.word old)))
    (qr : source.locals.lookup (ofString "qr")=some (pairValue q r)) (mapped : source.memaddrs (slot pointer index)) :
    evaluateHOLFiniteState source tail=(none,bind {source with memory:=StoreWord.put source.memory (slot pointer index) q} "k" r) := by
  have first : eval source quotientExpression=some (.val (.word q)):=by
    simp [eval,quotientExpression,localVar,evalHOLExact,toExact,qr,pairValue]
  have second : eval {source with memory:=StoreWord.put source.memory (slot pointer index) q} remainderExpression=some (.val (.word r)):=by
    simp [eval,remainderExpression,localVar,evalHOLExact,toExact,qr,pairValue]
  have stored:=StoreWord.execute source (address "q") quotientExpression _ q (address_read source "q" pointer index qCell j) first mapped
  rw [tail,evaluateHOLFiniteState_seq_line780,stored]
  exact StateSteps.assign_execute _ "k" remainderExpression old r k second

private theorem tuple_lookup_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (q r : BitVec 64)
    (different : ofString name≠ofString "qr") :
    (setVarHOLFinite (ofString "qr") (pairValue q r) source).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  change (if ofString "qr"==ofString name then some (pairValue q r) else source.locals.lookup (ofString name))=_
  simp [Ne.symm different]

private theorem tuple_lookup_same (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r : BitVec 64) :
    (setVarHOLFinite (ofString "qr") (pairValue q r) source).locals.lookup (ofString "qr")=some (pairValue q r) := by
  change (if ofString "qr"==ofString "qr" then some (pairValue q r) else source.locals.lookup (ofString "qr"))=_
  simp

/-- The real loop body decrements the index, divides one current input digit,
stores the genuine quotient digit and carries the genuine next remainder. -/
theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer uPointer high low divisor : BitVec 64)
    (index : Nat) (installed : OriginalCode.Installed source.code)
    (qCell : source.locals.lookup (ofString "q")=some (.val (.word qPointer)))
    (uCell : source.locals.lookup (ofString "u")=some (.val (.word uPointer)))
    (jCell : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (index+1)))))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word high)))
    (dCell : source.locals.lookup (ofString "d")=some (.val (.word divisor)))
    (inputMapped : source.memaddrs (slot uPointer index)) (input : source.memory (slot uPointer index)=.word low)
    (outputMapped : source.memaddrs (slot qPointer index))
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat) (lowSmall : low.toNat<2^32)
    (enough : 33≤source.clock) :
    ∃ quotient remainder,quotient.toNat=(high.toNat*2^32+low.toNat)/divisor.toNat ∧
      remainder.toNat=(high.toNat*2^32+low.toNat)%divisor.toNat ∧ quotient.toNat<2^32 ∧ remainder.toNat<divisor.toNat ∧
      evaluateHOLFiniteState source loopBody=(none,next source qPointer index quotient remainder) := by
  classical
  let indexed:=bind source "j" (BitVec.ofNat 64 index)
  have jRead : indexed.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))):=bind_lookup_same _ _ _
  have qRead : indexed.locals.lookup (ofString "q")=some (.val (.word qPointer)):=
    (bind_lookup_other source "j" "q" _ (by decide)).trans qCell
  have uRead : indexed.locals.lookup (ofString "u")=some (.val (.word uPointer)):=
    (bind_lookup_other source "j" "u" _ (by decide)).trans uCell
  have kRead : indexed.locals.lookup (ofString "k")=some (.val (.word high)):=
    (bind_lookup_other source "j" "k" _ (by decide)).trans kCell
  have dRead : indexed.locals.lookup (ofString "d")=some (.val (.word divisor)):=
    (bind_lookup_other source "j" "d" _ (by decide)).trans dCell
  have loaded:=Witness.load_word_read indexed (address "u") _ low (address_read indexed "u" uPointer index uRead jRead) inputMapped input
  simp only [eval] at loaded
  have readK : evalHOLExact indexed.toExact (localVar "k")=some (.val (.word high)):=by
    simp [localVar,evalHOLExact,toExact,kRead]
  have readD : evalHOLExact indexed.toExact (localVar "d")=some (.val (.word divisor)):=by
    simp [localVar,evalHOLExact,toExact,dRead]
  have args : evalListHOLFinite indexed (h:=fun address=>Classical.propDecidable (indexed.memaddrs address)) arguments=
      some [.val (.word high),.val (.word low),.val (.word divisor)]:=by
    simp only [arguments,evalListHOLFinite,evalListHOLExact]
    rw [readK,loaded,readD]
  obtain ⟨quotient,remainder,quotientEq,remainderEq,qSmall,rSmall,call⟩:=Div64By32.call_execute indexed high low divisor "qr" arguments tail
    installed args divisorSmall highSmall lowSmall enough
  let entered:=setVarHOLFinite (ofString "qr") (pairValue quotient remainder) {indexed with clock:=source.clock-33}
  have enteredQ : entered.locals.lookup (ofString "q")=some (.val (.word qPointer)):=
    (tuple_lookup_other _ "q" _ _ (by decide)).trans qRead
  have enteredJ : entered.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))):=
    (tuple_lookup_other _ "j" _ _ (by decide)).trans jRead
  have enteredK : entered.locals.lookup (ofString "k")=some (.val (.word high)):=
    (tuple_lookup_other _ "k" _ _ (by decide)).trans kRead
  have tailRun:=tail_execute entered qPointer quotient remainder high index enteredQ enteredJ enteredK (tuple_lookup_same _ _ _) outputMapped
  have realCall : evaluateHOLFiniteState indexed stepCall=(none,next source qPointer index quotient remainder):=by
    rw [stepCall,call]
    change (let output:=evaluateHOLFiniteState entered tail; (output.1,restore indexed "qr" output.2))=_
    rw [tailRun]
    rfl
  refine ⟨quotient,remainder,quotientEq,remainderEq,qSmall,rSmall,?_⟩
  rw [loopBody,evaluateHOLFiniteState_seq_line780,
    StateSteps.assign_execute source "j" previous _ _ jCell (previous_read source index jCell)]
  exact realCall

/-- The digit step writes precisely one quotient slot and spends33source
call/body ticks; all other physical fields survive. -/
theorem next_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) (q r : BitVec 64) :
    {next source pointer index q r with locals:=source.locals}=
      {source with memory:=StoreWord.put source.memory (slot pointer index) q,clock:=source.clock-33} := by
  rfl

theorem next_index (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) (q r : BitVec 64) :
    (next source pointer index q r).locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))) := by
  unfold next
  rw [restore_lookup_other _ _ "qr" "j" (by decide),bind_lookup_other _ "k" "j" _ (by decide)]
  rw [tuple_lookup_other _ "j" _ _ (by decide)]
  exact bind_lookup_same _ _ _

theorem next_remainder (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) (q r : BitVec 64) :
    (next source pointer index q r).locals.lookup (ofString "k")=some (.val (.word r)) := by
  unfold next
  rw [restore_lookup_other _ _ "qr" "k" (by decide)]
  exact bind_lookup_same _ _ _

theorem next_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) (q r : BitVec 64) (name : String)
    (notJ : ofString name≠ofString "j") (notK : ofString name≠ofString "k") (notQr : ofString name≠ofString "qr") :
    (next source pointer index q r).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  unfold next
  rw [restore_lookup_other _ _ "qr" name notQr,bind_lookup_other _ "k" name _ (Ne.symm notK),tuple_lookup_other _ name _ _ notQr]
  exact bind_lookup_other _ "j" name _ (Ne.symm notJ)

private theorem loop_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (small : count≤16)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 count)))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) loopTest=
      some (.val (.word (if 0<count then 1#64 else 0#64))) := by
  have encoded : (BitVec.ofNat 64 count).toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [finite_eval]
  simp [eval,loopTest,localVar,evalHOLExact,toExact,j,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,encoded]

private theorem number_congr (left right : Nat→ BitVec 64) (count : Nat)
    (agree : ∀ index,index<count→ left index=right index) : number left count=number right count := by
  induction count with
  | zero=>rfl
  | succ count ih=>rw [number,number,agree count (by omega),ih (by intro index inside;exact agree index (by omega))]

structure LoopResult (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer : BitVec 64)
    (contents : Nat→ BitVec 64) (divisor high : BitVec 64) (count : Nat) (quotient : Nat→ BitVec 64) (remainder : BitVec 64) : Prop where
  run : evaluateHOLFiniteState source loop=(none,target)
  state : target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-34*count}
  image : Image target qPointer quotient count
  digits : ∀ index,index<count→ (quotient index).toNat<2^32
  small : remainder.toNat<divisor.toNat
  value : divisor.toNat*number quotient count+remainder.toNat=high.toNat*2^(32*count)+number contents count
  index : target.locals.lookup (ofString "j")=some (.val (.word 0#64))
  carry : target.locals.lookup (ofString "k")=some (.val (.word remainder))
  other : ∀ name : String,ofString name≠ofString "j"→ ofString name≠ofString "k"→ ofString name≠ofString "qr"→
    target.locals.lookup (ofString name)=source.locals.lookup (ofString name)
  away : ∀ query,(∀ index,index<count→ query≠slot qPointer index)→ target.memory query=source.memory query

/-- Full physical one-digit division loop: actual quotient stores, exact
natural division identity, carried remainder and protected-memory frame. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer uPointer high divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (small : count≤16)
    (installed : OriginalCode.Installed source.code)
    (qCell : source.locals.lookup (ofString "q")=some (.val (.word qPointer)))
    (uCell : source.locals.lookup (ofString "u")=some (.val (.word uPointer)))
    (jCell : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 count))))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word high)))
    (dCell : source.locals.lookup (ofString "d")=some (.val (.word divisor)))
    (image : Image source uPointer contents count)
    (inputMapped : ∀ index,index<count→ source.memaddrs (slot uPointer index))
    (outputMapped : ∀ index,index<count→ source.memaddrs (slot qPointer index))
    (separate : ∀ inputIndex,inputIndex<count→ ∀ outputIndex,outputIndex<count→ slot uPointer inputIndex≠slot qPointer outputIndex)
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat)
    (digitsSmall : ∀ index,index<count→ (contents index).toNat<2^32)
    (enough : 34*count≤source.clock) :
    ∃ target quotient remainder,LoopResult source target qPointer contents divisor high count quotient remainder := by
  classical
  induction count generalizing source high with
  | zero=>
    have test:=loop_test source 0 small jCell
    simp only [Nat.lt_irrefl,↓reduceIte] at test
    refine ⟨source,(fun _=>0#64),high,⟨?_,by simp,?_,?_,highSmall,by simp [number],jCell,kCell,?_,?_⟩⟩
    · rw [loop,evaluateHOLFiniteState_while_total,test]
      simp
    · intro index inside;omega
    · intro index inside;omega
    · intros;rfl
    · intros;rfl
  | succ count ih=>
    let entry:=decClockHOLFinite source
    obtain ⟨digit,carry,quotientEq,remainderEq,digitSmall,carrySmall,bodyRun⟩:=body_execute entry qPointer uPointer high (contents count) divisor count installed
      qCell uCell jCell kCell dCell (inputMapped count (by omega)) (image count (by omega)) (outputMapped count (by omega))
      divisorSmall highSmall (digitsSmall count (by omega)) (by change 33≤source.clock-1;omega)
    let middle:=next entry qPointer count digit carry
    have middleState : middle={source with locals:=middle.locals,memory:=StoreWord.put source.memory (slot qPointer count) digit,clock:=source.clock-34}:=by
      have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=middle.locals})
        (next_frame entry qPointer count digit carry)
      change middle={source with locals:=middle.locals,memory:=StoreWord.put source.memory (slot qPointer count) digit,clock:=source.clock-1-33} at frame
      simpa only [Nat.sub_sub] using frame
    have middleClock : middle.clock=source.clock-34:=congrArg PanSemStateFiniteExact.clock middleState
    have middleCode : middle.code=source.code:=rfl
    have middleMemory : middle.memory=StoreWord.put source.memory (slot qPointer count) digit:=congrArg PanSemStateFiniteExact.memory middleState
    have middleImage : Image middle uPointer contents count:=by
      intro index inside
      rw [middleMemory,StoreWord.put,if_neg (separate index (by omega) count (by omega))]
      exact image index (by omega)
    have midQ : middle.locals.lookup (ofString "q")=some (.val (.word qPointer)):=
      (next_other entry qPointer count digit carry "q" (by decide) (by decide) (by decide)).trans qCell
    have midU : middle.locals.lookup (ofString "u")=some (.val (.word uPointer)):=
      (next_other entry qPointer count digit carry "u" (by decide) (by decide) (by decide)).trans uCell
    have midD : middle.locals.lookup (ofString "d")=some (.val (.word divisor)):=
      (next_other entry qPointer count digit carry "d" (by decide) (by decide) (by decide)).trans dCell
    have midInput : ∀ index,index<count→ middle.memaddrs (slot uPointer index):=by
      intro index inside
      exact inputMapped index (by omega)
    have midOutput : ∀ index,index<count→ middle.memaddrs (slot qPointer index):=by
      intro index inside
      exact outputMapped index (by omega)
    obtain ⟨target,tailDigits,finalR,tailRun⟩:=ih middle carry (by omega) (by rw [middleCode];exact installed)
      midQ midU (next_index entry qPointer count digit carry) (next_remainder entry qPointer count digit carry) midD
      middleImage midInput midOutput (by intro i hi j hj;exact separate i (by omega) j (by omega)) carrySmall
      (by intro index inside;exact digitsSmall index (by omega)) (by rw [middleClock];omega)
    let finalDigits : Nat→ BitVec 64:=fun index=>if index=count then digit else tailDigits index
    have lowNumber : number finalDigits count=number tailDigits count:=number_congr finalDigits tailDigits count
      (by intro index inside;simp only [finalDigits,if_neg (show index≠count by omega)])
    have test:=loop_test source (count+1) small jCell
    simp only [show 0<count+1 from by omega,↓reduceIte] at test
    refine ⟨target,finalDigits,finalR,⟨?_,?_,?_,?_,tailRun.small,?_,tailRun.index,tailRun.carry,?_,?_⟩⟩
    · rw [loop,evaluateHOLFiniteState_while_total,test]
      simp only [if_neg (show source.clock≠0 by omega)]
      rw [bodyRun,StateSteps.fixed_clock entry middle none (by change middle.clock≤source.clock-1;omega)]
      simp only [if_pos (show (1#64 : BitVec 64)≠0 by decide)]
      exact tailRun.run
    · have frame:=tailRun.state
      rw [middleState] at frame
      change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-34-34*count} at frame
      simpa only [Nat.sub_sub,show 34+34*count=34*(count+1) by omega] using frame
    · intro index inside
      by_cases last : index=count
      · subst index
        have kept:=tailRun.away (slot qPointer count) (by
          intro index inside hit
          have same:=slot_injective qPointer count index (by omega) (by omega) hit
          omega)
        rw [kept,middleMemory]
        simp [StoreWord.put,finalDigits]
      · simpa only [finalDigits,if_neg last] using tailRun.image index (by omega)
    · intro index inside
      by_cases last : index=count
      · simpa only [finalDigits,if_pos last] using digitSmall
      · simpa only [finalDigits,if_neg last] using tailRun.digits index (by omega)
    · have step : divisor.toNat*digit.toNat+carry.toNat=high.toNat*2^32+(contents count).toNat:=by
        rw [quotientEq,remainderEq]
        exact Nat.div_add_mod _ _
      have scaled:=congrArg (fun value:Nat=>value*2^(32*count)) step
      have power : 2^(32*(count+1))=2^32*2^(32*count):=by
        rw [show 32*(count+1)=32+32*count by omega,Nat.pow_add]
      have tailValue:=tailRun.value
      rw [number,lowNumber]
      simp only [finalDigits,if_pos rfl]
      rw [number,power]
      nlinarith [scaled,tailValue]
    · intro name notJ notK notQr
      exact (tailRun.other name notJ notK notQr).trans (next_other entry qPointer count digit carry name notJ notK notQr)
    · intro query outside
      rw [tailRun.away query (by intro index inside;exact outside index (by omega)),middleMemory,
        StoreWord.put,if_neg (outside count (by omega))]

theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer uPointer high divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (small : count≤16)
    (installed : OriginalCode.Installed source.code)
    (qCell : source.locals.lookup (ofString "q")=some (.val (.word qPointer)))
    (uCell : source.locals.lookup (ofString "u")=some (.val (.word uPointer)))
    (jCell : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 count))))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word high)))
    (dCell : source.locals.lookup (ofString "d")=some (.val (.word divisor)))
    (image : Image source uPointer contents count)
    (inputMapped : ∀ index,index<count→ source.memaddrs (slot uPointer index))
    (outputMapped : ∀ index,index<count→ source.memaddrs (slot qPointer index))
    (separate : ∀ inputIndex,inputIndex<count→ ∀ outputIndex,outputIndex<count→ slot uPointer inputIndex≠slot qPointer outputIndex)
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat)
    (digitsSmall : ∀ index,index<count→ (contents index).toNat<2^32)
    : source.clock-(evaluateHOLFiniteState source loop).2.clock≤34*count := by
  by_cases enough : 34*count≤source.clock
  · obtain ⟨target,quotient,remainder,checked⟩:=loop_execute source qPointer uPointer high divisor contents count small installed
      qCell uCell jCell kCell dCell image inputMapped outputMapped separate divisorSmall highSmall digitsSmall enough
    rw [checked.run]
    have clock:=congrArg PanSemStateFiniteExact.clock checked.state
    change target.clock=source.clock-34*count at clock
    change source.clock-target.clock≤34*count
    omega
  · omega

theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer uPointer high divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (small : count≤16)
    (installed : OriginalCode.Installed source.code)
    (qCell : source.locals.lookup (ofString "q")=some (.val (.word qPointer)))
    (uCell : source.locals.lookup (ofString "u")=some (.val (.word uPointer)))
    (jCell : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 count))))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word high)))
    (dCell : source.locals.lookup (ofString "d")=some (.val (.word divisor)))
    (image : Image source uPointer contents count)
    (inputMapped : ∀ index,index<count→ source.memaddrs (slot uPointer index))
    (outputMapped : ∀ index,index<count→ source.memaddrs (slot qPointer index))
    (separate : ∀ inputIndex,inputIndex<count→ ∀ outputIndex,outputIndex<count→ slot uPointer inputIndex≠slot qPointer outputIndex)
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat)
    (digitsSmall : ∀ index,index<count→ (contents index).toNat<2^32)
    (normal : evaluateHOLFiniteState source loop=(none,post)) :
    ∃ quotient remainder,34*count≤source.clock ∧ LoopResult source post qPointer contents divisor high count quotient remainder := by
  let fundedSource:={source with clock:=34*count}
  obtain ⟨baseTarget,baseQ,baseR,base⟩:=loop_execute fundedSource qPointer uPointer high divisor contents count small installed
    qCell uCell jCell kCell dCell image inputMapped outputMapped separate divisorSmall highSmall digitsSmall (by rfl)
  have zero : baseTarget.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock base.state
    change baseTarget.clock=34*count-34*count at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget post loop (34*count) none none base.run zero (by decide) normal (by decide)).1
  obtain ⟨target,quotient,remainder,checked⟩:=loop_execute source qPointer uPointer high divisor contents count small installed
    qCell uCell jCell kCell dCell image inputMapped outputMapped separate divisorSmall highSmall digitsSmall funded
  have same : post=target:=congrArg Prod.snd (normal.symm.trans checked.run)
  exact ⟨quotient,remainder,funded,same.symm ▸ checked⟩

/-- The real quotient image and carried word are the ordinary natural quotient
and remainder; the physical execution itself supplies the conservation law. -/
theorem LoopResult.division {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {qPointer : BitVec 64}
    {contents quotient : Nat→ BitVec 64} {divisor high remainder : BitVec 64} {count : Nat}
    (checked : LoopResult source target qPointer contents divisor high count quotient remainder) :
    number quotient count=(high.toNat*2^(32*count)+number contents count)/divisor.toNat ∧
      remainder.toNat=(high.toNat*2^(32*count)+number contents count)%divisor.toNat := by
  have positive : 0<divisor.toNat:=by have small:=checked.small;omega
  constructor
  · rw [←checked.value,Nat.mul_add_div positive,Nat.div_eq_of_lt checked.small,Nat.add_zero]
  · rw [←checked.value,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt checked.small]

/-- Current initialized buffers and divisor, independent of caller locals. -/
structure Buffers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) : Prop where
  small : count≤16
  installed : OriginalCode.Installed source.code
  image : Image source uPointer contents count
  inputMapped : ∀ index,index<count→ source.memaddrs (slot uPointer index)
  outputMapped : ∀ index,index<count→ source.memaddrs (slot qPointer index)
  separate : ∀ inputIndex,inputIndex<count→ ∀ outputIndex,outputIndex<count→ slot uPointer inputIndex≠slot qPointer outputIndex
  remainderSeparate : ∀ index,index<count→ rPointer≠slot qPointer index
  divisorMapped : source.memaddrs vPointer
  divisorCell : source.memory vPointer=.word divisor
  remainderMapped : source.memaddrs rPointer
  divisorSmall : divisor.toNat<2^32
  positive : 0<divisor.toNat
  digitsSmall : ∀ index,index<count→ (contents index).toNat<2^32

/-- Actual one-digit function argument bindings and its physical buffers. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) extends Buffers source qPointer rPointer uPointer vPointer divisor contents count : Prop where
  qCell : source.locals.lookup (ofString "q")=some (.val (.word (qPointer)))
  rCell : source.locals.lookup (ofString "r")=some (.val (.word (rPointer)))
  uCell : source.locals.lookup (ofString "u")=some (.val (.word (uPointer)))
  vCell : source.locals.lookup (ofString "v")=some (.val (.word (vPointer)))
  mCell : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count)))
  nCell : source.locals.lookup (ofString "n")=some (.val (.word (1#64)))

theorem Buffers.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {qPointer rPointer uPointer vPointer divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat}
    (checked : Buffers source qPointer rPointer uPointer vPointer divisor contents count) (clock : Nat) :
    Buffers {source with clock:=clock} qPointer rPointer uPointer vPointer divisor contents count := by
  exact ⟨checked.small,
    checked.installed,
    checked.image,
    checked.inputMapped,
    checked.outputMapped,
    checked.separate,
    checked.remainderSeparate,
    checked.divisorMapped,
    checked.divisorCell,
    checked.remainderMapped,
    checked.divisorSmall,
    checked.positive,
    checked.digitsSmall⟩

theorem Buffers.withLocals {source : PanSemStateFiniteExact 64 Guest.HostMemory} {qPointer rPointer uPointer vPointer divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat}
    (checked : Buffers source qPointer rPointer uPointer vPointer divisor contents count) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    Buffers {source with locals:=locals} qPointer rPointer uPointer vPointer divisor contents count := by
  exact ⟨checked.small,
    checked.installed,
    checked.image,
    checked.inputMapped,
    checked.outputMapped,
    checked.separate,
    checked.remainderSeparate,
    checked.divisorMapped,
    checked.divisorCell,
    checked.remainderMapped,
    checked.divisorSmall,
    checked.positive,
    checked.digitsSmall⟩

theorem Entry.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {qPointer rPointer uPointer vPointer divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat}
    (checked : Entry source qPointer rPointer uPointer vPointer divisor contents count) (clock : Nat) :
    Entry {source with clock:=clock} qPointer rPointer uPointer vPointer divisor contents count := by
  exact ⟨checked.toBuffers.withClock clock,checked.qCell,
    checked.rCell,
    checked.uCell,
    checked.vCell,
    checked.mCell,
    checked.nCell⟩

theorem Entry.bindWord {source : PanSemStateFiniteExact 64 Guest.HostMemory} {qPointer rPointer uPointer vPointer divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat}
    (checked : Entry source qPointer rPointer uPointer vPointer divisor contents count) (name : String) (word : BitVec 64)
    (allowed : name="i" ∨ name="j" ∨ name="d" ∨ name="k") :
    Entry (bind source name word) qPointer rPointer uPointer vPointer divisor contents count := by
  exact ⟨checked.toBuffers.withLocals (bind source name word).locals,(bind_lookup_other source name "q" word (by rcases allowed with rfl|rfl|rfl|rfl <;> decide)).trans checked.qCell,
    (bind_lookup_other source name "r" word (by rcases allowed with rfl|rfl|rfl|rfl <;> decide)).trans checked.rCell,
    (bind_lookup_other source name "u" word (by rcases allowed with rfl|rfl|rfl|rfl <;> decide)).trans checked.uCell,
    (bind_lookup_other source name "v" word (by rcases allowed with rfl|rfl|rfl|rfl <;> decide)).trans checked.vCell,
    (bind_lookup_other source name "m" word (by rcases allowed with rfl|rfl|rfl|rfl <;> decide)).trans checked.mCell,
    (bind_lookup_other source name "n" word (by rcases allowed with rfl|rfl|rfl|rfl <;> decide)).trans checked.nCell⟩

structure BranchResult (program : ProgHOL 64) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (qPointer rPointer divisor : BitVec 64) (contents : Nat→ BitVec 64) (count : Nat)
    (quotient : Nat→ BitVec 64) (remainder : BitVec 64) : Prop where
  run : evaluateHOLFiniteState source program=(some (.returned (.val (.word 0#64))),target)
  state : target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-34*count}
  image : Image target qPointer quotient count
  digits : ∀ index,index<count→ (quotient index).toNat<2^32
  remainderCell : target.memory rPointer=.word remainder
  quotientEq : number quotient count=number contents count/divisor.toNat
  remainderEq : remainder.toNat=number contents count%divisor.toNat
  small : remainder.toNat<divisor.toNat
  away : ∀ query,(∀ index,index<count→ query≠slot qPointer index)→ query≠rPointer→ target.memory query=source.memory query

/-- The actual one-digit branch initializes the real loop, writes its final
remainder and returns0 through both genuine lexical declarations. -/
theorem branch_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Entry source qPointer rPointer uPointer vPointer divisor contents count)
    (oldJ : BitVec 64) (jCell : source.locals.lookup (ofString "j")=some (.val (.word oldJ))) (enough : 34*count≤source.clock) :
    ∃ target quotient remainder,BranchResult oneBranch source target qPointer rPointer divisor contents count quotient remainder := by
  classical
  let dEntry:=bind source "d" divisor
  let kEntry:=bind dEntry "k" 0#64
  let indexed:=bind kEntry "j" (BitVec.ofNat 64 count)
  have dModel:=checked.bindWord "d" divisor (by simp)
  have kModel:=dModel.bindWord "k" 0#64 (by simp)
  have indexedModel:=kModel.bindWord "j" (BitVec.ofNat 64 count) (by simp)
  have kJ : kEntry.locals.lookup (ofString "j")=some (.val (.word oldJ)):=
    (bind_lookup_other dEntry "k" "j" _ (by decide)).trans ((bind_lookup_other source "d" "j" _ (by decide)).trans jCell)
  have indexedK : indexed.locals.lookup (ofString "k")=some (.val (.word 0#64)):=
    (bind_lookup_other kEntry "j" "k" _ (by decide)).trans (bind_lookup_same dEntry "k" _)
  have indexedD : indexed.locals.lookup (ofString "d")=some (.val (.word divisor)):=
    (bind_lookup_other kEntry "j" "d" _ (by decide)).trans ((bind_lookup_other dEntry "k" "d" _ (by decide)).trans (bind_lookup_same source "d" _))
  obtain ⟨loopTarget,quotient,remainder,checkedLoop⟩:=loop_execute indexed qPointer uPointer 0#64 divisor contents count checked.small checked.installed
    indexedModel.qCell indexedModel.uCell (bind_lookup_same kEntry "j" _) indexedK indexedD indexedModel.image
    indexedModel.inputMapped indexedModel.outputMapped indexedModel.separate checked.divisorSmall checked.positive checked.digitsSmall enough
  have rLocal : loopTarget.locals.lookup (ofString "r")=some (.val (.word rPointer)):=
    (checkedLoop.other "r" (by decide) (by decide) (by decide)).trans indexedModel.rCell
  have rRead : eval loopTarget (localVar "r")=some (.val (.word rPointer)):=by
    simp [eval,localVar,evalHOLExact,toExact,rLocal]
  have kRead : eval loopTarget (localVar "k")=some (.val (.word remainder)):=by
    simp [eval,localVar,evalHOLExact,toExact,checkedLoop.carry]
  have mappedR : loopTarget.memaddrs rPointer:=by
    have domain:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memaddrs) checkedLoop.state
    change loopTarget.memaddrs=indexed.memaddrs at domain
    rw [domain]
    exact checked.remainderMapped
  let stored:={loopTarget with memory:=StoreWord.put loopTarget.memory rPointer remainder}
  have storedRun:=StoreWord.execute loopTarget (localVar "r") (localVar "k") rPointer remainder rRead kRead mappedR
  have returnRun : evaluateHOLFiniteState stored (.return (.const 0#64))=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite stored):=by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have finished : evaluateHOLFiniteState loopTarget finish=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite stored):=by
    rw [finish,evaluateHOLFiniteState_seq_line780,storedRun]
    exact returnRun
  have mLocal : kEntry.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count))):=kModel.mCell
  have mRead : eval kEntry (localVar "m")=some (.val (.word (BitVec.ofNat 64 count))):=by
    simp [eval,localVar,evalHOLExact,toExact,mLocal]
  have initializedRun : evaluateHOLFiniteState kEntry initialized=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite stored):=by
    rw [initialized,evaluateHOLFiniteState_seq_line780,
      StateSteps.assign_execute kEntry "j" (localVar "m") oldJ (BitVec.ofNat 64 count) kJ mRead]
    change evaluateHOLFiniteState indexed (.seq loop finish)=_
    rw [evaluateHOLFiniteState_seq_line780,checkedLoop.run]
    exact finished
  have declaredK:=ScalarScope.declare_execute dEntry (emptyLocalsHOLFinite stored) "k" (.const 0#64) 0#64 initialized _ rfl initializedRun
  have vRead : eval source (localVar "v")=some (.val (.word vPointer)):=by
    simp [eval,localVar,evalHOLExact,toExact,checked.vCell]
  have dRead:=Witness.load_word_read source (localVar "v") vPointer divisor vRead checked.divisorMapped checked.divisorCell
  have declaredD:=ScalarScope.declare_execute source (restore dEntry "k" (emptyLocalsHOLFinite stored)) "d"
    (.load .one (localVar "v")) divisor (.dec (ofString "k") .one (.const 0#64) initialized) _ dRead declaredK
  let target:=restore source "d" (restore dEntry "k" (emptyLocalsHOLFinite stored))
  refine ⟨target,quotient,remainder,⟨?_,?_,?_,checkedLoop.digits,?_,?_,?_,checkedLoop.small,?_⟩⟩
  · exact declaredD
  · have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals,memory:=target.memory}) checkedLoop.state
    change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-34*count} at frame
    exact frame
  · intro index inside
    change StoreWord.put loopTarget.memory rPointer remainder (slot qPointer index)=.word (quotient index)
    rw [StoreWord.put,if_neg (Ne.symm (checked.remainderSeparate index inside))]
    exact checkedLoop.image index inside
  · change StoreWord.put loopTarget.memory rPointer remainder rPointer=.word remainder
    simp [StoreWord.put]
  · simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.zero_mul,Nat.zero_add] using checkedLoop.division.1
  · simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.zero_mul,Nat.zero_add] using checkedLoop.division.2
  · intro query outside notR
    change StoreWord.put loopTarget.memory rPointer remainder query=source.memory query
    rw [StoreWord.put,if_neg notR]
    exact checkedLoop.away query outside

/-- Complete unchanged divmnu execution on its genuine one-digit path,
including both outer declarations and the branch's early function return. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Entry source qPointer rPointer uPointer vPointer divisor contents count)
    (enough : 34*count≤source.clock) :
    ∃ target quotient remainder,BranchResult body source target qPointer rPointer divisor contents count quotient remainder := by
  classical
  let iEntry:=bind source "i" 0#64
  let jEntry:=bind iEntry "j" 0#64
  have iModel:=checked.bindWord "i" 0#64 (by simp)
  have jModel:=iModel.bindWord "j" 0#64 (by simp)
  obtain ⟨branchTarget,quotient,remainder,result⟩:=branch_execute jEntry qPointer rPointer uPointer vPointer divisor contents count
    jModel 0#64 (bind_lookup_same iEntry "j" _) enough
  have nLocal : jEntry.locals.lookup (ofString "n")=some (.val (.word 1#64)):=jModel.nCell
  have tested : evalHOLExact jEntry.toExact oneTest=some (.val (.word 1#64)):=by
    simp [oneTest,localVar,evalHOLExact,toExact,nLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  let selected : ProgHOL 64:=.seq (.ite oneTest oneBranch .skip) otherBranch
  have selectedRun : evaluateHOLFiniteState jEntry selected=(some (.returned (.val (.word 0#64))),branchTarget):=by
    change evaluateHOLFiniteState jEntry (.seq (.ite oneTest oneBranch .skip) otherBranch)=_
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,tested]
    simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)]
    rw [result.run]
  have declaredJ:=ScalarScope.declare_execute iEntry branchTarget "j" (.const 0#64) 0#64 selected _ rfl selectedRun
  have declaredI:=ScalarScope.declare_execute source (restore iEntry "j" branchTarget) "i" (.const 0#64) 0#64
    (.dec (ofString "j") .one (.const 0#64) selected) _ rfl declaredJ
  let target:=restore source "i" (restore iEntry "j" branchTarget)
  refine ⟨target,quotient,remainder,⟨?_,?_,result.image,result.digits,result.remainderCell,
    result.quotientEq,result.remainderEq,result.small,result.away⟩⟩
  · rw [body_shape]
    exact declaredI
  · have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals}) result.state
    change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-34*count} at frame
    exact frame

/-- All outcomes of the original one-digit function path spend at most544
body ticks at16digits, including failed/short-clock executions. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Entry source qPointer rPointer uPointer vPointer divisor contents count) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤34*count := by
  by_cases enough : 34*count≤source.clock
  · obtain ⟨target,quotient,remainder,result⟩:=execute source qPointer rPointer uPointer vPointer divisor contents count checked enough
    rw [result.run]
    have clock:=congrArg PanSemStateFiniteExact.clock result.state
    change target.clock=source.clock-34*count at clock
    change source.clock-target.clock≤34*count
    omega
  · omega

/-- The actual normal function return derives its funding, real quotient
image and remainder store; it cannot assume a later successful execution. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Entry source qPointer rPointer uPointer vPointer divisor contents count)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ quotient remainder,34*count≤source.clock ∧ returned=.val (.word 0#64) ∧
      BranchResult body source post qPointer rPointer divisor contents count quotient remainder := by
  let fundedSource:={source with clock:=34*count}
  obtain ⟨baseTarget,baseQ,baseR,base⟩:=execute fundedSource qPointer rPointer uPointer vPointer divisor contents count
    (checked.withClock (34*count)) (by rfl)
  have zero : baseTarget.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock base.state
    change baseTarget.clock=34*count-34*count at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget post body (34*count) _ _ base.run zero
    (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)).1
  obtain ⟨target,quotient,remainder,result⟩:=execute source qPointer rPointer uPointer vPointer divisor contents count checked funded
  have same:=normal.symm.trans result.run
  have returnedEq : returned=.val (.word 0#64):=by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst same
  have postEq : post=target:=congrArg Prod.snd same
  exact ⟨quotient,remainder,funded,returnedEq,postEq.symm ▸ result⟩

def values (qPointer rPointer uPointer vPointer : BitVec 64) (count : Nat) : List (ValueHOL 64):=
  [.val (.word qPointer),.val (.word rPointer),.val (.word uPointer),.val (.word (BitVec.ofNat 64 count)),.val (.word vPointer),.val (.word 1#64)]

private def rawLocals (qPointer rPointer uPointer vPointer : BitVec 64) (count : Nat) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "n" then some (.val (.word 1#64)) else
  if name=ofString "v" then some (.val (.word vPointer)) else
  if name=ofString "m" then some (.val (.word (BitVec.ofNat 64 count))) else
  if name=ofString "u" then some (.val (.word uPointer)) else
  if name=ofString "r" then some (.val (.word rPointer)) else
  if name=ofString "q" then some (.val (.word qPointer)) else none

/-- The actual six-scalar signature establishes every one-digit callee
argument, independently of the caller's local variable names. -/
theorem environment (codeFn : MlS→ Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (qPointer rPointer uPointer vPointer : BitVec 64) (count : Nat)
    (code : codeFn (ofString "divmnu")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "divmnu") (values qPointer rPointer uPointer vPointer count)=some (body,callee,.one) ∧
      callee.lookup (ofString "q")=some (.val (.word qPointer)) ∧
      callee.lookup (ofString "r")=some (.val (.word rPointer)) ∧
      callee.lookup (ofString "u")=some (.val (.word uPointer)) ∧
      callee.lookup (ofString "v")=some (.val (.word vPointer)) ∧
      callee.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count))) ∧
      callee.lookup (ofString "n")=some (.val (.word 1#64)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values qPointer rPointer uPointer vPointer count).length ∧
      ((formals.zip (values qPointer rPointer uPointer vPointer count)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=by
    exact ⟨by decide,rfl,by simp [formals,values,shapeOfHOLExact,shapeEqHOL_eq_true]⟩
  have raw : lookupCodeHOLExact codeFn (ofString "divmnu") (values qPointer rPointer uPointer vPointer count)=
      some (body,rawLocals qPointer rPointer uPointer vPointer count,.one):=by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [locals];simp [rawLocals,ofString]

private theorem callee_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Buffers source qPointer rPointer uPointer vPointer divisor contents count)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (qCell : callee.lookup (ofString "q")=some (.val (.word qPointer)))
    (rCell : callee.lookup (ofString "r")=some (.val (.word rPointer)))
    (uCell : callee.lookup (ofString "u")=some (.val (.word uPointer)))
    (vCell : callee.lookup (ofString "v")=some (.val (.word vPointer)))
    (mCell : callee.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count))))
    (nCell : callee.lookup (ofString "n")=some (.val (.word 1#64))) :
    Entry (callEntryStateHOLFinite source callee) qPointer rPointer uPointer vPointer divisor contents count := by
  exact ⟨(checked.withLocals callee).withClock (source.clock-1),qCell,rCell,uCell,vCell,mCell,nCell⟩

/-- The genuine ignored-result caller costs at most545source ticks for16
input digits, including the function's real early return and short clocks. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Buffers source qPointer rPointer uPointer vPointer divisor contents count)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (values qPointer rPointer uPointer vPointer count)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "divmnu") arguments)).2.clock≤34*count+1 := by
  obtain ⟨callee,called,qCell,rCell,uCell,vCell,mCell,nCell⟩:=environment source.code.lookup qPointer rPointer uPointer vPointer count
    (original_code source.code checked.installed)
  have actual:=callee_entry source qPointer rPointer uPointer vPointer divisor contents count checked callee qCell rCell uCell vCell mCell nCell
  exact ClockCost.call_current source (some none) (ofString "divmnu") arguments _ body callee .one (34*count) args called
    (body_cost (callEntryStateHOLFinite source callee) qPointer rPointer uPointer vPointer divisor contents count actual)

structure CallerResult (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (arguments : List (ExpHOL 64)) (quotient : Nat→ BitVec 64) (remainder : BitVec 64) : Prop where
  run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "divmnu") arguments)=(none,post)
  state : post={source with memory:=post.memory,clock:=source.clock-(34*count+1)}
  image : Image post qPointer quotient count
  digits : ∀ index,index<count→ (quotient index).toNat<2^32
  remainderCell : post.memory rPointer=.word remainder
  quotientEq : number quotient count=number contents count/divisor.toNat
  remainderEq : remainder.toNat=number contents count%divisor.toNat
  small : remainder.toNat<divisor.toNat
  away : ∀ query,(∀ index,index<count→ query≠slot qPointer index)→ query≠rPointer→ post.memory query=source.memory query

/-- The real ignored-result call returns the exact quotient/remainder memory
and canonical caller state after its actual one-digit execution. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Buffers source qPointer rPointer uPointer vPointer divisor contents count)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (values qPointer rPointer uPointer vPointer count)) (enough : 34*count+1≤source.clock) :
    ∃ post quotient remainder,CallerResult source post qPointer rPointer divisor contents count arguments quotient remainder := by
  obtain ⟨callee,called,qCell,rCell,uCell,vCell,mCell,nCell⟩:=environment source.code.lookup qPointer rPointer uPointer vPointer count
    (original_code source.code checked.installed)
  have actual:=callee_entry source qPointer rPointer uPointer vPointer divisor contents count checked callee qCell rCell uCell vCell mCell nCell
  obtain ⟨target,quotient,remainder,result⟩:=execute (callEntryStateHOLFinite source callee) qPointer rPointer uPointer vPointer divisor contents count actual
    (by change 34*count≤source.clock-1;omega)
  let post:={target with locals:=source.locals}
  have calledRun:=evaluateHOLFiniteState_call_return_caller_locals source none (ofString "divmnu") arguments _ body callee .one
    (.val (.word 0#64)) target args called (by omega) result.run (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨post,quotient,remainder,⟨calledRun,?_,result.image,result.digits,result.remainderCell,
    result.quotientEq,result.remainderEq,result.small,result.away⟩⟩
  have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) result.state
  change post={source with memory:=post.memory,clock:=source.clock-1-34*count} at frame
  simpa only [Nat.sub_sub,show 1+34*count=34*count+1 by omega] using frame

/-- A genuine normal caller derives its own complete funding and physical
quotient/remainder result from the same actual callee execution. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Buffers source qPointer rPointer uPointer vPointer divisor contents count)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (values qPointer rPointer uPointer vPointer count))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "divmnu") arguments)=(none,post)) :
    ∃ quotient remainder,34*count+1≤source.clock ∧ CallerResult source post qPointer rPointer divisor contents count arguments quotient remainder := by
  obtain ⟨callee,called,qCell,rCell,uCell,vCell,mCell,nCell⟩:=environment source.code.lookup qPointer rPointer uPointer vPointer count
    (original_code source.code checked.installed)
  obtain ⟨callFunded,target,returned,bodyRun⟩:=CallNormal.ignored_callee_return source post (ofString "divmnu") arguments _ body callee .one args called normal
  have actual:=callee_entry source qPointer rPointer uPointer vPointer divisor contents count checked callee qCell rCell uCell vCell mCell nCell
  obtain ⟨childQ,childR,childFunded,returnedEq,childResult⟩:=body_normal (callEntryStateHOLFinite source callee) target
    qPointer rPointer uPointer vPointer divisor contents count actual returned bodyRun
  have funded : 34*count+1≤source.clock:=by
    change 34*count≤source.clock-1 at childFunded
    omega
  obtain ⟨expected,quotient,remainder,result⟩:=call_execute source qPointer rPointer uPointer vPointer divisor contents count checked arguments args funded
  have same : post=expected:=congrArg Prod.snd (normal.symm.trans result.run)
  exact ⟨quotient,remainder,funded,same.symm ▸ result⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Single

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.body_shape
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.original_code

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.body_execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.next_frame

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.next_index

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.next_remainder

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.next_other

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.loop_execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.loop_cost

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.loop_normal

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.LoopResult.division

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.Entry.withClock

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.Entry.bindWord

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.branch_execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.body_cost

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.body_normal

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.Buffers.withClock

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.Buffers.withLocals

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.environment

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.call_cost

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.call_execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.call_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

inductive Buffer where | normalizedNumerator | normalizedDivisor | quotient | remainder | numerator | divisor

def offset : Buffer→ Nat
  | .normalizedNumerator=>0 | .normalizedDivisor=>144 | .quotient=>216
  | .remainder=>352 | .numerator=>424 | .divisor=>560

def count : Buffer→ Nat
  | .normalizedNumerator=>17 | .quotient=>16 | .numerator=>16 | _=>8

def pointer (base : BitVec 64) (buffer : Buffer) : BitVec 64:=base+BitVec.ofNat 64 (offset buffer)

structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) : Prop where
  global : source.globals.lookup (ofString "u256_ws")=some (.val (.word base))
  domain : source.memaddrs=InitE.ordinaryDomain
  arena : AllocatedBytes.Arena base 640
  aligned : base.toNat%8=0

theorem fits (buffer : Buffer) : offset buffer+8*count buffer≤640 := by cases buffer <;> decide

theorem aligned (buffer : Buffer) : offset buffer%8=0 := by cases buffer <;> decide

theorem slot_flat (base : BitVec 64) (buffer : Buffer) (index : Nat) :
    slot (pointer base buffer) index=base+BitVec.ofNat 64 (offset buffer+8*index) := by
  simp only [slot,pointer,BitVec.ofNat_add,BitVec.add_assoc]

theorem buffer_arena (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : Context source base) (buffer : Buffer) : AllocatedBytes.Arena (pointer base buffer) (8*count buffer) :=
  AllocatedBytes.Arena.subrange base 640 (offset buffer) (8*count buffer) context.arena (fits buffer)

theorem buffer_aligned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : Context source base) (buffer : Buffer) : (pointer base buffer).toNat%8=0 := by
  have inside:=fits buffer
  have number:=byteAddress_toNat base (offset buffer) (by have upper:=context.arena.upper;omega)
  change (pointer base buffer).toNat=base.toNat+offset buffer at number
  rw [number,Nat.add_mod,context.aligned,aligned]

theorem slot_number (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : Context source base) (buffer : Buffer) (index : Nat) (inside : index<count buffer) :
    (slot (pointer base buffer) index).toNat=base.toNat+offset buffer+8*index := by
  have extent:=fits buffer
  rw [slot_flat]
  have number:=byteAddress_toNat base (offset buffer+8*index) (by have upper:=context.arena.upper;omega)
  change (base+BitVec.ofNat 64 (offset buffer+8*index)).toNat=base.toNat+(offset buffer+8*index) at number
  simpa only [Nat.add_assoc] using number

theorem slot_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : Context source base) (buffer : Buffer) (index : Nat) (inside : index<count buffer) :
    source.memaddrs (slot (pointer base buffer) index) := by
  have extent:=fits buffer
  rw [slot_flat]
  exact AllocatedBytes.word_mapped source base 640 (offset buffer+8*index) context.domain context.arena (by omega)
    context.aligned (by rw [Nat.add_mod,aligned];omega)

/-- Distinct actual workspace arrays have disjoint word slots, including
all16quotient slots and the seventeenth normalized numerator word. -/
theorem separate (base : BitVec 64) (left right : Buffer) (different : left≠right)
    (i j : Nat) (leftInside : i<count left) (rightInside : j<count right) :
    slot (pointer base left) i≠slot (pointer base right) j := by
  intro hit
  rw [slot_flat,slot_flat] at hit
  have words : BitVec.ofNat 64 (offset left+8*i)=BitVec.ofNat 64 (offset right+8*j):=(BitVec.add_right_inj base).mp hit
  have numbers:=congrArg BitVec.toNat words
  have leftFits:=fits left
  have rightFits:=fits right
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at numbers
  cases left <;> cases right <;> simp only [offset,count] at * <;> first | exact different rfl | omega

/-- Main's actually derived pointer supplies the fixed mapped workspace.
Startup separately establishes the allocation and its persistent heap extent. -/
theorem current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (global : source.globals.lookup (ofString "u256_ws")=some (.val (.word 2701134824#64)))
    (domain : source.memaddrs=InitE.ordinaryDomain) : Context source 2701134824#64 :=
  ⟨global,domain,⟨by decide,by decide⟩,by decide⟩

/-- Current workspace geometry derives the one-digit divider's real entry
buffers once conversion has established its actual digit images. -/
theorem single_buffers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (context : Context source base) (installed : OriginalCode.Installed source.code)
    (contents : Nat→ BitVec 64) (length : Nat) (small : length≤16)
    (image : Image source (pointer base .numerator) contents length)
    (divisorCell : source.memory (pointer base .divisor)=.word divisor)
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (digitsSmall : ∀ index,index<length→ (contents index).toNat<2^32) :
    Single.Buffers source (pointer base .quotient) (pointer base .remainder) (pointer base .numerator) (pointer base .divisor)
      divisor contents length := by
  refine ⟨small,installed,image,?_,?_,?_,?_,?_,divisorCell,?_,divisorSmall,positive,digitsSmall⟩
  · intro index inside
    exact slot_mapped source base context .numerator index (by change index<16;omega)
  · intro index inside
    exact slot_mapped source base context .quotient index (by change index<16;omega)
  · intro inputIndex inputInside outputIndex outputInside
    exact separate base .numerator .quotient (by intro impossible;cases impossible) inputIndex outputIndex
      (by change inputIndex<16;omega) (by change outputIndex<16;omega)
  · intro index inside
    simpa only [slot,Nat.mul_zero,show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using
      separate base .remainder .quotient (by intro impossible;cases impossible) 0 index (by decide) (by change index<16;omega)
  · simpa only [slot,Nat.mul_zero,show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using slot_mapped source base context .divisor 0 (by decide)
  · simpa only [slot,Nat.mul_zero,show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using slot_mapped source base context .remainder 0 (by decide)

end InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.fits
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.aligned
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.slot_flat
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.buffer_arena
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.buffer_aligned
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.slot_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.slot_mapped
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.separate
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.current
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Workspace.single_buffers

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Clear
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def address (name : String) : ExpHOL 64:=.op .add [localVar name,.panop .mul [localVar "i",.const 8#64]]
def increment : ExpHOL 64:=.op .add [localVar "i",.const 1#64]
def body (name : String) : ProgHOL 64:=.seq (.store (address name) (.const 0#64)) (.assign .local (ofString "i") increment)
def test (limit : Nat) : ExpHOL 64:=.cmp .lower (localVar "i") (.const (BitVec.ofNat 64 limit))
def loop (name : String) (limit : Nat) : ProgHOL 64:=.while (test limit) (body name)
def divmodBody : ProgHOL 64:=match Guest.Software.guestFn_digits_divmod with | .function fn=>progToHOL fn.body | _=>.skip

private def findLoop (limit : Nat) : ProgHOL 64→ Option (ProgHOL 64)
  | .while condition body=>
    match condition with
    | .cmp .lower (.var .local name) (.const bound)=>
      if name=ofString "i" ∧ bound=BitVec.ofNat 64 limit then some (.while condition body) else findLoop limit body
    | _=>findLoop limit body
  | .seq first rest=>(findLoop limit first).orElse (fun _=>findLoop limit rest)
  | .dec _ _ _ rest=>findLoop limit rest
  | .decCall _ _ _ _ rest=>findLoop limit rest
  | .ite _ yes no=>(findLoop limit yes).orElse (fun _=>findLoop limit no)
  | _=>none

theorem quotient_literal : findLoop 16 divmodBody=some (loop "q" 16) := by
  simp [findLoop,divmodBody,Guest.Software.guestFn_digits_divmod,progToHOL,expToHOL,shapeToHOL,
    loop,test,body,address,increment,localVar]

theorem remainder_literal : findLoop 8 divmodBody=some (loop "r" 8) := by
  simp [findLoop,divmodBody,Guest.Software.guestFn_digits_divmod,progToHOL,expToHOL,shapeToHOL,
    loop,test,body,address,increment,localVar]

def memory (initial : BitVec 64→ HolWordLab 64) (pointer : BitVec 64) (index : Nat) : Nat→ (BitVec 64→ HolWordLab 64)
  | 0=>initial
  | rounds+1=>memory (StoreWord.put initial (slot pointer index) 0#64) pointer (index+1) rounds

theorem memory_preserves_zero (initial : BitVec 64→ HolWordLab 64) (pointer query : BitVec 64) (index rounds : Nat)
    (zero : initial query=.word 0#64) : memory initial pointer index rounds query=.word 0#64 := by
  induction rounds generalizing initial index with
  | zero=>exact zero
  | succ rounds ih=>
    rw [memory]
    apply ih
    by_cases same : query=slot pointer index
    · simp [StoreWord.put,same]
    · simpa only [StoreWord.put,if_neg same] using zero

theorem memory_cell (initial : BitVec 64→ HolWordLab 64) (pointer : BitVec 64) (first rounds index : Nat)
    (lower : first≤index) (upper : index<first+rounds) : memory initial pointer first rounds (slot pointer index)=.word 0#64 := by
  induction rounds generalizing initial first with
  | zero=>omega
  | succ rounds ih=>
    rw [memory]
    by_cases current : index=first
    · subst index
      apply memory_preserves_zero
      simp [StoreWord.put]
    · exact ih _ (first+1) (by omega) (by omega)

theorem memory_away (initial : BitVec 64→ HolWordLab 64) (pointer query : BitVec 64) (first rounds : Nat)
    (away : ∀ index,first≤index→ index<first+rounds→ query≠slot pointer index) :
    memory initial pointer first rounds query=initial query := by
  induction rounds generalizing initial first with
  | zero=>rfl
  | succ rounds ih=>
    rw [memory,ih _ (first+1) (by intro index lower upper;exact away index (by omega) (by omega)),
      StoreWord.put,if_neg (away first (by omega) (by omega))]

def bodyPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) :=
  bind {source with memory:=StoreWord.put source.memory (slot pointer index) 0#64} "i" (BitVec.ofNat 64 (index+1))

def after (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) : Nat→ PanSemStateFiniteExact 64 Guest.HostMemory
  | 0=>source
  | rounds+1=>after (bodyPost (decClockHOLFinite source) pointer index) pointer (index+1) rounds

private theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64) (index : Nat)
    (p : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source (address name)=some (.val (.word (slot pointer index))) := by
  simp [eval,address,localVar,evalHOLExact,evalListHOLExact,toExact,p,i,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,Nat.mul_comm]

theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64) (index : Nat)
    (p : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (mapped : source.memaddrs (slot pointer index)) :
    evaluateHOLFiniteState source (body name)=(none,bodyPost source pointer index) := by
  have read : eval {source with memory:=StoreWord.put source.memory (slot pointer index) 0#64} increment=
      some (.val (.word (BitVec.ofNat 64 (index+1)))):=by
    simp [eval,increment,localVar,evalHOLExact,evalListHOLExact,toExact,i,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have stored:=StoreWord.execute source (address name) (.const 0#64) (slot pointer index) 0#64 (address_read source name pointer index p i) rfl mapped
  rw [body,evaluateHOLFiniteState_seq_line780,stored]
  exact StateSteps.assign_execute _ "i" increment _ _ i read

theorem after_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    after source pointer index rounds={source with
      locals:=(after source pointer index rounds).locals,
      memory:=memory source.memory pointer index rounds,clock:=source.clock-rounds} := by
  induction rounds generalizing source index with
  | zero=>simp [after,memory]
  | succ rounds ih=>
    rw [after,ih]
    simp only [bodyPost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,decClockHOLFinite,memory]
    congr 1
    omega

theorem after_index (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    (after source pointer index rounds).locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+rounds)))) := by
  induction rounds generalizing source index with
  | zero=>simpa only [after,Nat.add_zero] using i
  | succ rounds ih=>
    rw [after]
    have checked:=ih (bodyPost (decClockHOLFinite source) pointer index) (index+1) (bind_lookup_same _ _ _)
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using checked

theorem after_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat)
    (name : String) (notI : ofString "i"≠ofString name) :
    (after source pointer index rounds).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  induction rounds generalizing source index with
  | zero=>rfl
  | succ rounds ih=>
    rw [after,ih]
    exact bind_lookup_other _ "i" name _ notI

private theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index limit : Nat)
    (small : limit≤16) (inside : index≤limit)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (test limit)=
      some (.val (.word (if index<limit then 1#64 else 0#64))) := by
  have indexNumber : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have limitNumber : (BitVec.ofNat 64 limit).toNat=limit:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [finite_eval]
  simp [eval,test,localVar,evalHOLExact,toExact,i,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,indexNumber,limitNumber]

/-- Complete actual counted clearing loop, including its final test and the
exact zero-store/counter/clock state. There is no incoming-content premise. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64)
    (limit index rounds : Nat) (small : limit≤16) (finish : index+rounds=limit)
    (p : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (notI : ofString "i"≠ofString name)
    (mapped : ∀ slotIndex,slotIndex<limit→ source.memaddrs (slot pointer slotIndex)) (enough : rounds≤source.clock) :
    evaluateHOLFiniteState source (loop name limit)=(none,after source pointer index rounds) := by
  classical
  induction rounds generalizing source index with
  | zero=>
    have read:=test_read source index limit small (by omega) i
    rw [if_neg (show ¬index<limit by omega)] at read
    rw [loop,evaluateHOLFiniteState_while_total,read]
    simp [after]
  | succ rounds ih=>
    let entry:=decClockHOLFinite source
    let next:=bodyPost entry pointer index
    have bodyRun:=body_execute entry name pointer index p i (mapped index (by omega))
    have nextP : next.locals.lookup (ofString name)=some (.val (.word pointer)):=
      (bind_lookup_other _ "i" name _ notI).trans p
    have nextI : next.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))):=bind_lookup_same _ _ _
    have tailRun:=ih next (index+1) (by omega) nextP nextI mapped (by change rounds≤source.clock-1;omega)
    have read:=test_read source index limit small (by omega) i
    rw [if_pos (show index<limit by omega)] at read
    rw [loop,evaluateHOLFiniteState_while_total,read]
    simp only [if_neg (show source.clock≠0 by omega)]
    rw [bodyRun,StateSteps.fixed_clock entry next none (by rfl)]
    simp only [if_pos (show (1#64 : BitVec 64)≠0 by decide)]
    exact tailRun

/-- The real loop's all-outcome allowance includes every short-clock case. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64)
    (limit index : Nat) (small : limit≤16) (inside : index≤limit)
    (p : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (notI : ofString "i"≠ofString name)
    (mapped : ∀ slotIndex,slotIndex<limit→ source.memaddrs (slot pointer slotIndex)) :
    source.clock-(evaluateHOLFiniteState source (loop name limit)).2.clock≤limit-index := by
  by_cases enough : limit-index≤source.clock
  · have run:=loop_execute source name pointer limit index (limit-index) small (by omega) p i notI mapped enough
    rw [run]
    have clock:=congrArg PanSemStateFiniteExact.clock (after_state source pointer index (limit-index))
    change (after source pointer index (limit-index)).clock=source.clock-(limit-index) at clock
    change source.clock-(after source pointer index (limit-index)).clock≤limit-index
    omega
  · omega

/-- A normally completed real loop derives its own required clock and exact
post-state, rather than assuming future clearing succeeded. -/
theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64)
    (limit index : Nat) (small : limit≤16) (inside : index≤limit)
    (p : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (notI : ofString "i"≠ofString name)
    (mapped : ∀ slotIndex,slotIndex<limit→ source.memaddrs (slot pointer slotIndex))
    (normal : evaluateHOLFiniteState source (loop name limit)=(none,post)) :
    limit-index≤source.clock ∧ post=after source pointer index (limit-index) := by
  let base:={source with clock:=limit-index}
  let target:=after base pointer index (limit-index)
  have baseRun:=loop_execute base name pointer limit index (limit-index) small (by omega) p i notI mapped (by rfl)
  have zero : target.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock (after_state base pointer index (limit-index))
    change target.clock=(limit-index)-(limit-index) at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source target post (loop name limit) (limit-index) none none
    baseRun zero (by decide) normal (by decide)).1
  have expected:=loop_execute source name pointer limit index (limit-index) small (by omega) p i notI mapped funded
  exact ⟨funded,congrArg Prod.snd (normal.symm.trans expected)⟩

/-- Each real full clear leaves its entire initialized zero image. -/
theorem after_image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat) :
    Image (after source pointer 0 length) pointer (fun _=>0#64) length := by
  have written:=congrArg PanSemStateFiniteExact.memory (after_state source pointer 0 length)
  change (after source pointer 0 length).memory=memory source.memory pointer 0 length at written
  intro index inside
  rw [written]
  exact memory_cell source.memory pointer 0 length index (by omega) (by omega)

theorem after_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (length : Nat)
    (away : ∀ index,index<length→ query≠slot pointer index) :
    (after source pointer 0 length).memory query=source.memory query := by
  have written:=congrArg PanSemStateFiniteExact.memory (after_state source pointer 0 length)
  change (after source pointer 0 length).memory=memory source.memory pointer 0 length at written
  rw [written]
  exact memory_away source.memory pointer query 0 length (by intro index lower upper;exact away index (by omega))

theorem after_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base pointer : BitVec 64) (length : Nat)
    (context : Workspace.Context source base) : Workspace.Context (after source pointer 0 length) base := by
  have state:=after_state source pointer 0 length
  refine ⟨?_,?_,context.arena,context.aligned⟩
  · rw [state]
    exact context.global
  · rw [state]
    exact context.domain

/-- Clearing one real workspace buffer retains every initialized cell of
any distinct buffer, including the future numerator and divisor reads. -/
theorem after_workspace_image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (cleared other : Workspace.Buffer) (different : other≠cleared) (contents : Nat→ BitVec 64) (length : Nat)
    (small : length≤Workspace.count other) (image : Image source (Workspace.pointer base other) contents length) :
    Image (after source (Workspace.pointer base cleared) 0 (Workspace.count cleared)) (Workspace.pointer base other) contents length := by
  intro index inside
  exact (after_away source (Workspace.pointer base cleared) (slot (Workspace.pointer base other) index) (Workspace.count cleared)
    (by intro written writtenInside;exact Workspace.separate base other cleared different index written (by omega) writtenInside)).trans
    (image index inside)

end InitECandidate.Solver.Input.UDivMod.WideDigits.Clear

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.quotient_literal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.remainder_literal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.memory_preserves_zero
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.memory_cell
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.memory_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.body_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.after_state
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.after_index
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.after_other

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.loop_execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.loop_cost

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.loop_normal

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.after_image

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.after_away

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.after_context

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.after_workspace_image

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual tail-return form used by digits_divmod, with the exact physical
reconstruction and its one caller tick. -/
theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→ BitVec 64)
    (arguments : List (ExpHOL 64)) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word pointer)])
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index))
    (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.call none (ofString "digits_to_u256") arguments)=
      (some (.returned (RlpWrite.U256Value.tuple (words contents))),emptyLocalsHOLFinite {source with clock:=source.clock-1}) := by
  obtain ⟨callee,called,pCell⟩:=environment source.code.lookup pointer (original_code source.code installed)
  have run:=execute (callEntryStateHOLFinite source callee) pointer contents pCell image mapped
  have actual:=evaluateHOLFiniteState_call_return_none source (RlpWrite.U256Value.tuple (words contents)) (ofString "digits_to_u256") arguments _
    body callee RlpWrite.U256Value.tupleShape (emptyLocalsHOLFinite (callEntryStateHOLFinite source callee)) args called (by omega) run
    (by simp [RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  exact actual

theorem tail_cost (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call none (ofString "digits_to_u256") arguments) 1 := by
  exact ClockCost.call_body code none (ofString "digits_to_u256") arguments formals body RlpWrite.U256Value.tupleShape 0
    (original_code code installed) (body_cost code)

/-- A real returning tail call derives its own funding and exact value/state;
the physical reads come from the same incoming image. -/
theorem tail_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→ BitVec 64)
    (arguments : List (ExpHOL 64)) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word pointer)])
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→ source.memaddrs (slot pointer index))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (.call none (ofString "digits_to_u256") arguments)=(some (.returned returned),post)) :
    1≤source.clock ∧ returned=RlpWrite.U256Value.tuple (words contents) ∧ post=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
  obtain ⟨callee,called,pCell⟩:=environment source.code.lookup pointer (original_code source.code installed)
  have enough : 1≤source.clock:=by
    by_contra short
    have zero : source.clock=0:=by omega
    rw [evaluateHOLFiniteState_call] at normal
    simp only [args,called,if_pos zero] at normal
    cases normal
  have expected:=tail_execute source pointer contents arguments installed args image mapped enough
  have same:=normal.symm.trans expected
  exact ⟨enough,by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst same,
    congrArg Prod.snd same⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.tail_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.tail_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.ToWords.tail_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Single
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def remainderDigits (remainder : BitVec 64) (index : Nat) : BitVec 64:=if index=0 then remainder else 0#64
def remainderWords (remainder : BitVec 64) : Quad:=fun index=>if index=0 then remainder else 0#64

theorem remainder_reconstruction (remainder : BitVec 64) : ToWords.words (remainderDigits remainder)=remainderWords remainder := by
  funext index
  obtain ⟨index,inside⟩:=index
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3:=by omega
  rcases cases with rfl|rfl|rfl|rfl <;> simp [ToWords.words,remainderDigits,remainderWords]

theorem remainder_number (remainder : BitVec 64) : quadNumber (remainderWords remainder)=remainder.toNat := by
  simp [quadNumber,remainderWords]

def padded (quotient : Nat→ BitVec 64) (length index : Nat) : BitVec 64:=if index<length then quotient index else 0#64

theorem padded_number (quotient : Nat→ BitVec 64) (length width : Nat) (small : length≤width) :
    number (padded quotient length) width=number quotient length := by
  induction width with
  | zero=>
    have empty : length=0:=by omega
    subst length
    rfl
  | succ width ih=>
    by_cases lower : length≤width
    · rw [number,ih lower]
      simp [padded,show ¬width<length by omega]
    · have same : length=width+1:=by omega
      subst length
      exact number_congr (padded quotient (width+1)) quotient (width+1) (by
        intro index inside;simp only [padded,if_pos inside])

/-- The actual divider preserves the already-zero higher remainder cells;
its genuine final store supplies the low digit. -/
theorem CallerResult.remainder_image {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor remainder : BitVec 64}
    {contents quotient : Nat→ BitVec 64} {length : Nat} {arguments : List (ExpHOL 64)}
    (result : CallerResult source post (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) divisor contents length arguments quotient remainder)
    (small : length≤16) (zero : Image source (Workspace.pointer base .remainder) (fun _=>0#64) 8) :
    Image post (Workspace.pointer base .remainder) (remainderDigits remainder) 8 := by
  intro index inside
  by_cases first : index=0
  · subst index
    simpa [slot,remainderDigits] using result.remainderCell
  · have notQ : ∀ written,written<length→ slot (Workspace.pointer base .remainder) index≠slot (Workspace.pointer base .quotient) written:=by
      intro written writtenInside
      exact Workspace.separate base .remainder .quotient (by intro impossible;cases impossible) index written
        (by change index<8;exact inside) (by change written<16;omega)
    have notR : slot (Workspace.pointer base .remainder) index≠Workspace.pointer base .remainder:=by
      intro hit
      have equal : slot (Workspace.pointer base .remainder) index=slot (Workspace.pointer base .remainder) 0:=by simpa [slot] using hit
      exact first (slot_injective _ index 0 (by omega) (by decide) equal)
    rw [result.away _ notQ notR]
    simpa only [remainderDigits,if_neg first] using zero index inside

/-- The real quotient prefix and the old cleared suffix form the full
sixteen-word scratch image used by subsequent reconstruction. -/
theorem CallerResult.quotient_image {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor remainder : BitVec 64}
    {contents quotient : Nat→ BitVec 64} {length : Nat} {arguments : List (ExpHOL 64)}
    (result : CallerResult source post (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) divisor contents length arguments quotient remainder)
    (zero : Image source (Workspace.pointer base .quotient) (fun _=>0#64) 16) :
    Image post (Workspace.pointer base .quotient) (padded quotient length) 16 := by
  intro index inside
  by_cases written : index<length
  · simpa only [padded,if_pos written] using result.image index written
  · have notQ : ∀ earlier,earlier<length→ slot (Workspace.pointer base .quotient) index≠slot (Workspace.pointer base .quotient) earlier:=by
      intro earlier earlierInside hit
      have same:=slot_injective (Workspace.pointer base .quotient) index earlier inside (by omega) hit
      omega
    have notR : slot (Workspace.pointer base .quotient) index≠Workspace.pointer base .remainder:=by
      simpa only [slot,Nat.mul_zero,show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using
        Workspace.separate base .quotient .remainder (by intro impossible;cases impossible) index 0 inside (by decide)
    rw [result.away _ notQ notR]
    simpa only [padded,if_neg written] using zero index inside

/-- For the actual eight-digit u256 path, reconstruction of the written
quotient digits gives the exact natural quotient rather than a word oracle. -/
theorem CallerResult.quotient_number {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor remainder : BitVec 64}
    {contents quotient : Nat→ BitVec 64} {length : Nat} {arguments : List (ExpHOL 64)}
    (result : CallerResult source post (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) divisor contents length arguments quotient remainder)
    (small : length≤8) :
    quadNumber (ToWords.words (padded quotient length))=number contents length/divisor.toNat := by
  have digits : ∀ index,index<8→ (padded quotient length index).toNat<2^32:=by
    intro index inside
    by_cases before : index<length
    · simpa only [padded,if_pos before] using result.digits index before
    · simp [padded,before]
  rw [ToWords.words_number _ digits,padded_number quotient length 8 small]
  exact result.quotientEq

end InitECandidate.Solver.Input.UDivMod.WideDigits.Single

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.remainder_reconstruction
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.remainder_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.padded_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.CallerResult.remainder_image
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.CallerResult.quotient_image
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.CallerResult.quotient_number

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Single
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def wideArguments : List (ExpHOL 64):=[localVar "q",localVar "r",localVar "u",localVar "mm",localVar "v",localVar "n"]
def returnArguments : List (ExpHOL 64):=[localVar "r"]
def afterClearing (arguments : List (ExpHOL 64)) : ProgHOL 64:=
  .seq (.call (some (none,none)) (ofString "divmnu") arguments) (.call none (ofString "digits_to_u256") returnArguments)

private def findTail : ProgHOL 64→ Option (ProgHOL 64)
  | .seq (.call destination function arguments) rest=>
    if function=ofString "divmnu" then some (.seq (.call destination function arguments) rest) else findTail rest
  | .seq first rest=>(findTail first).orElse (fun _=>findTail rest)
  | .dec _ _ _ rest=>findTail rest
  | .decCall _ _ _ _ rest=>findTail rest
  | .ite _ yes no=>(findTail yes).orElse (fun _=>findTail no)
  | _=>none

theorem literal_tail : findTail Clear.divmodBody=some (afterClearing wideArguments) := by
  simp [findTail,Clear.divmodBody,Guest.Software.guestFn_digits_divmod,progToHOL,expToHOL,shapeToHOL,
    afterClearing,wideArguments,returnArguments,localVar]
  all_goals decide

/-- All outcomes of the real post-clearing tail include both actual calls. -/
theorem after_clearing_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer rPointer uPointer vPointer divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (length : Nat) (checked : Buffers source qPointer rPointer uPointer vPointer divisor contents length)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (values qPointer rPointer uPointer vPointer length)) :
    source.clock-(evaluateHOLFiniteState source (afterClearing arguments)).2.clock≤34*length+2 := by
  simpa only [afterClearing,Nat.add_assoc] using ClockCost.sequence_current source
    (.call (some (none,none)) (ofString "divmnu") arguments) (.call none (ofString "digits_to_u256") returnArguments)
    (34*length+1) 1 (call_cost source qPointer rPointer uPointer vPointer divisor contents length checked arguments args)
    (ToWords.tail_cost source.code checked.installed returnArguments)

private theorem result_context {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor remainder : BitVec 64}
    {contents quotient : Nat→ BitVec 64} {length : Nat} {arguments : List (ExpHOL 64)}
    (context : Workspace.Context source base)
    (result : CallerResult source post (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) divisor contents length arguments quotient remainder) :
    Workspace.Context post base := by
  refine ⟨?_,?_,context.arena,context.aligned⟩
  · rw [result.state]
    exact context.global
  · rw [result.state]
    exact context.domain

private theorem result_return_arguments {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor remainder : BitVec 64}
    {contents quotient : Nat→ BitVec 64} {length : Nat} {arguments : List (ExpHOL 64)}
    (result : CallerResult source post (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) divisor contents length arguments quotient remainder)
    (rLocal : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder)))) :
    evalListHOLFinite post (h:=fun query=>Classical.propDecidable (post.memaddrs query)) returnArguments=
      some [.val (.word (Workspace.pointer base .remainder))] := by
  have afterR : post.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))):=by
    rw [result.state]
    exact rLocal
  simp [returnArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,afterR]

/-- The original actual divmnu call and subsequent tail reconstruction return
the physical one-digit remainder in a real four-word value. -/
theorem after_clearing_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (contents : Nat→ BitVec 64) (length : Nat) (small : length≤16)
    (image : Image source (Workspace.pointer base .numerator) contents length)
    (divisorCell : source.memory (Workspace.pointer base .divisor)=.word divisor)
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (digitsSmall : ∀ index,index<length→ (contents index).toNat<2^32)
    (zero : Image source (Workspace.pointer base .remainder) (fun _=>0#64) 8)
    (rLocal : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (values (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) (Workspace.pointer base .numerator) (Workspace.pointer base .divisor) length))
    (enough : 34*length+2≤source.clock) :
    ∃ middle quotient remainder,
      CallerResult source middle (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) divisor contents length arguments quotient remainder ∧
      evaluateHOLFiniteState source (afterClearing arguments)=
        (some (.returned (RlpWrite.U256Value.tuple (remainderWords remainder))),emptyLocalsHOLFinite {middle with clock:=middle.clock-1}) := by
  have checked:=Workspace.single_buffers source base divisor context installed contents length small image divisorCell divisorSmall positive digitsSmall
  obtain ⟨middle,quotient,remainder,result⟩:=call_execute source (Workspace.pointer base .quotient) (Workspace.pointer base .remainder)
    (Workspace.pointer base .numerator) (Workspace.pointer base .divisor) divisor contents length checked arguments args (by omega)
  have nextContext:=result_context context result
  have nextCode : OriginalCode.Installed middle.code:=by rw [result.state];exact installed
  have middleClock:=congrArg PanSemStateFiniteExact.clock result.state
  change middle.clock=source.clock-(34*length+1) at middleClock
  have tailRun:=ToWords.tail_execute middle (Workspace.pointer base .remainder) (remainderDigits remainder) returnArguments nextCode
    (result_return_arguments result rLocal) (result.remainder_image small zero)
    (by intro index inside;exact Workspace.slot_mapped middle base nextContext .remainder index inside) (by omega)
  rw [remainder_reconstruction] at tailRun
  refine ⟨middle,quotient,remainder,result,?_⟩
  rw [afterClearing,evaluateHOLFiniteState_seq_line780,result.run]
  exact tailRun

theorem after_clearing_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (contents : Nat→ BitVec 64) (length : Nat) (small : length≤16)
    (image : Image source (Workspace.pointer base .numerator) contents length)
    (divisorCell : source.memory (Workspace.pointer base .divisor)=.word divisor)
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (digitsSmall : ∀ index,index<length→ (contents index).toNat<2^32)
    (zero : Image source (Workspace.pointer base .remainder) (fun _=>0#64) 8)
    (rLocal : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (values (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) (Workspace.pointer base .numerator) (Workspace.pointer base .divisor) length))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (afterClearing arguments)=(some (.returned returned),post)) :
    ∃ middle quotient remainder,
      CallerResult source middle (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) divisor contents length arguments quotient remainder ∧
      34*length+2≤source.clock ∧ returned=RlpWrite.U256Value.tuple (remainderWords remainder) ∧
      post=emptyLocalsHOLFinite {middle with clock:=middle.clock-1} ∧
      quadNumber (remainderWords remainder)=number contents length%divisor.toNat := by
  have checked:=Workspace.single_buffers source base divisor context installed contents length small image divisorCell divisorSmall positive digitsSmall
  have safe : LocalPrefix (ofString "unused") (.call (some (none,none)) (ofString "divmnu") arguments):=
    .call none (ofString "divmnu") arguments (by intro name impossible;cases impossible)
  rw [afterClearing] at normal
  obtain ⟨middle,divisionRun,returnRun⟩:=sequence_returned source post
    (.call (some (none,none)) (ofString "divmnu") arguments) (.call none (ofString "digits_to_u256") returnArguments)
    returned (safe.summary_full source).2.1 normal
  obtain ⟨quotient,remainder,divisionFunded,result⟩:=call_normal source middle (Workspace.pointer base .quotient) (Workspace.pointer base .remainder)
    (Workspace.pointer base .numerator) (Workspace.pointer base .divisor) divisor contents length checked arguments args divisionRun
  have nextContext:=result_context context result
  have nextCode : OriginalCode.Installed middle.code:=by rw [result.state];exact installed
  obtain ⟨returnFunded,returnedEq,postEq⟩:=ToWords.tail_normal middle post (Workspace.pointer base .remainder) (remainderDigits remainder)
    returnArguments nextCode (result_return_arguments result rLocal) (result.remainder_image small zero)
    (by intro index inside;exact Workspace.slot_mapped middle base nextContext .remainder index inside) returned returnRun
  rw [remainder_reconstruction] at returnedEq
  have middleClock:=congrArg PanSemStateFiniteExact.clock result.state
  change middle.clock=source.clock-(34*length+1) at middleClock
  exact ⟨middle,quotient,remainder,result,by omega,returnedEq,postEq,(remainder_number remainder).trans result.remainderEq⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Single

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.literal_tail
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.after_clearing_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.after_clearing_execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Single.after_clearing_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Clear
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem after_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    after source pointer index rounds={source with
      locals:=(after source pointer index rounds).locals,
      memory:=(after source pointer index rounds).memory,clock:=source.clock-rounds} := by
  have frame:=after_state source pointer index rounds
  have written:=congrArg PanSemStateFiniteExact.memory frame
  change (after source pointer index rounds).memory=memory source.memory pointer index rounds at written
  rw [←written] at frame
  exact frame

end InitECandidate.Solver.Input.UDivMod.WideDigits.Clear

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64:=Clear.divmodBody
def lessTest : ExpHOL 64:=.cmp .lower (localVar "mm") (localVar "n")
def underflowArguments : List (ExpHOL 64):=[localVar "u"]
def guard : ProgHOL 64:=.ite lessTest (.call none (ofString "digits_to_u256") underflowArguments) .skip
def resetIndex : ProgHOL 64:=.assign .local (ofString "i") (.const 0#64)
def afterQuotient : ProgHOL 64:=.seq guard (.seq resetIndex (.seq (Clear.loop "r" 8) (Single.afterClearing Single.wideArguments)))
def afterCounts : ProgHOL 64:=.dec (ofString "i") .one (.const 0#64) (.seq (Clear.loop "q" 16) afterQuotient)
def price (length : Nat) : Nat:=if length=0 then 17 else 34*length+26

private def findCounts : ProgHOL 64→ Option (ProgHOL 64)
  | .dec name shape expression rest=>
    if name=ofString "i" then some (.dec name shape expression rest) else findCounts rest
  | .decCall _ _ _ _ rest=>findCounts rest
  | .seq first rest=>(findCounts first).orElse (fun _=>findCounts rest)
  | .ite _ yes no=>(findCounts yes).orElse (fun _=>findCounts no)
  | _=>none

theorem literal_counts : findCounts body=some afterCounts := by
  simp [findCounts,body,Clear.divmodBody,Guest.Software.guestFn_digits_divmod,progToHOL,expToHOL,shapeToHOL,
    afterCounts,afterQuotient,guard,lessTest,underflowArguments,resetIndex,Clear.loop,Clear.test,Clear.body,Clear.address,Clear.increment,
    Single.afterClearing,Single.wideArguments,Single.returnArguments,localVar,
    show ofString "q"≠ofString "i" by decide,show ofString "r"≠ofString "i" by decide,show ofString "v"≠ofString "i" by decide]

/-- Facts after the actual two length calls on the one-digit-divisor path.
The zero case retains the real eight cells read by its early return. -/
structure Scanned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (length : Nat) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  small : length≤16
  q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))
  r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder)))
  u : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator)))
  v : source.locals.lookup (ofString "v")=some (.val (.word (Workspace.pointer base .divisor)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 1#64))
  mm : source.locals.lookup (ofString "mm")=some (.val (.word (BitVec.ofNat 64 length)))
  image : Image source (Workspace.pointer base .numerator) contents length
  divisorCell : source.memory (Workspace.pointer base .divisor)=.word divisor
  divisorSmall : divisor.toNat<2^32
  positive : 0<divisor.toNat
  digitsSmall : ∀ index,index<length→ (contents index).toNat<2^32
  zeroCase : length=0→ Image source (Workspace.pointer base .numerator) (fun _=>0#64) 8

theorem Scanned.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {length : Nat} (checked : Scanned source base divisor contents length) (clock : Nat) :
    Scanned {source with clock:=clock} base divisor contents length :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,checked.small,
    checked.q,checked.r,checked.u,checked.v,checked.n,checked.mm,checked.image,checked.divisorCell,
    checked.divisorSmall,checked.positive,checked.digitsSmall,checked.zeroCase⟩

theorem Scanned.bindIndex {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {length : Nat} (checked : Scanned source base divisor contents length) (word : BitVec 64) :
    Scanned (bind source "i" word) base divisor contents length := by
  refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,checked.small,
    ?_,?_,?_,?_,?_,?_,checked.image,checked.divisorCell,checked.divisorSmall,checked.positive,checked.digitsSmall,checked.zeroCase⟩
  · exact (bind_lookup_other source "i" "q" _ (by decide)).trans checked.q
  · exact (bind_lookup_other source "i" "r" _ (by decide)).trans checked.r
  · exact (bind_lookup_other source "i" "u" _ (by decide)).trans checked.u
  · exact (bind_lookup_other source "i" "v" _ (by decide)).trans checked.v
  · exact (bind_lookup_other source "i" "n" _ (by decide)).trans checked.n
  · exact (bind_lookup_other source "i" "mm" _ (by decide)).trans checked.mm

/-- The actual clear preserves every scanned argument and future input read
when its workspace buffer differs from the numerator and divisor arrays. -/
theorem Scanned.afterClear {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {length : Nat} (checked : Scanned source base divisor contents length)
    (cleared : Workspace.Buffer) (notNumerator : Workspace.Buffer.numerator≠cleared) (notDivisor : Workspace.Buffer.divisor≠cleared) :
    Scanned (Clear.after source (Workspace.pointer base cleared) 0 (Workspace.count cleared)) base divisor contents length := by
  let pointer:=Workspace.pointer base cleared
  let target:=Clear.after source pointer 0 (Workspace.count cleared)
  have state:=Clear.after_state source pointer 0 (Workspace.count cleared)
  have code:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.code) state
  change target.code=source.code at code
  have targetCode : OriginalCode.Installed target.code:=by rw [code];exact checked.installed
  have divisorAway : ∀ index,index<Workspace.count cleared→ Workspace.pointer base .divisor≠slot pointer index:=by
    intro index inside
    simpa only [slot,Nat.mul_zero,show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using
      Workspace.separate base .divisor cleared notDivisor 0 index (by decide) inside
  have divisorKept:=Clear.after_away source pointer (Workspace.pointer base .divisor) (Workspace.count cleared) divisorAway
  refine ⟨Clear.after_context source base pointer (Workspace.count cleared) checked.context,targetCode,checked.small,
    ?_,?_,?_,?_,?_,?_,?_,divisorKept.trans checked.divisorCell,checked.divisorSmall,checked.positive,checked.digitsSmall,?_⟩
  · exact (Clear.after_other source pointer 0 _ "q" (by decide)).trans checked.q
  · exact (Clear.after_other source pointer 0 _ "r" (by decide)).trans checked.r
  · exact (Clear.after_other source pointer 0 _ "u" (by decide)).trans checked.u
  · exact (Clear.after_other source pointer 0 _ "v" (by decide)).trans checked.v
  · exact (Clear.after_other source pointer 0 _ "n" (by decide)).trans checked.n
  · exact (Clear.after_other source pointer 0 _ "mm" (by decide)).trans checked.mm
  · exact Clear.after_workspace_image source base cleared .numerator notNumerator contents length checked.small checked.image
  · intro zero
    exact Clear.after_workspace_image source base cleared .numerator notNumerator (fun _=>0#64) 8 (by decide) (checked.zeroCase zero)

private theorem guard_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (length : Nat) (checked : Scanned source base divisor contents length) :
    eval source lessTest=some (.val (.word (if length=0 then 1#64 else 0#64))) := by
  have encoded : (BitVec.ofNat 64 length).toNat=length:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=checked.small;omega)]
  have nLocal:=checked.n
  have mmLocal:=checked.mm
  simp [eval,lessTest,localVar,evalHOLExact,toExact,nLocal,mmLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,encoded]

private theorem wide_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (length : Nat) (checked : Scanned source base divisor contents length) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Single.wideArguments=
      some (Single.values (Workspace.pointer base .quotient) (Workspace.pointer base .remainder) (Workspace.pointer base .numerator)
        (Workspace.pointer base .divisor) length) := by
  have qLocal:=checked.q
  have rLocal:=checked.r
  have uLocal:=checked.u
  have vLocal:=checked.v
  have nLocal:=checked.n
  have mmLocal:=checked.mm
  simp [Single.wideArguments,Single.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
    qLocal,rLocal,uLocal,vLocal,nLocal,mmLocal]

theorem price_lower (length : Nat) : 16≤price length := by
  by_cases zero : length=0 <;> simp [price,zero] <;> omega

theorem price_upper (length : Nat) : price length≤34*length+26 := by
  by_cases zero : length=0 <;> simp [price,zero]

structure Result (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (length : Nat) (quotient : Nat→ BitVec 64) (remainder : BitVec 64) : Prop where
  run : evaluateHOLFiniteState source afterCounts=(some (.returned (RlpWrite.U256Value.tuple (Single.remainderWords remainder))),target)
  state : target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-price length}
  quotientImage : Image target (Workspace.pointer base .quotient) (Single.padded quotient length) 16
  digits : ∀ index,index<length→ (quotient index).toNat<2^32
  quotientEq : number quotient length=number contents length/divisor.toNat
  remainderEq : remainder.toNat=number contents length%divisor.toNat
  small : remainder.toNat<divisor.toNat
  away : ∀ query,(∀ index,index<16→ query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .remainder) index)→ target.memory query=source.memory query

set_option maxHeartbeats 800000 in
/-- Exact execution of the real post-scan wrapper, including its early
zero-numerator return and the positive division branch. -/
theorem after_counts_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (length : Nat) (checked : Scanned source base divisor contents length)
    (enough : price length≤source.clock) :
    ∃ target quotient remainder,Result source target base divisor contents length quotient remainder := by
  classical
  let indexed:=bind source "i" 0#64
  have indexedModel : Scanned indexed base divisor contents length:=checked.bindIndex 0#64
  let qPointer:=Workspace.pointer base .quotient
  let rPointer:=Workspace.pointer base .remainder
  let qCleared:=Clear.after indexed qPointer 0 16
  have qRun:=Clear.loop_execute indexed "q" qPointer 16 0 16 (by decide) rfl indexedModel.q (bind_lookup_same _ _ _) (by decide)
    (by intro index inside;exact Workspace.slot_mapped indexed base indexedModel.context .quotient index inside)
    (by change 16≤source.clock;exact Nat.le_trans (price_lower length) enough)
  have qModel : Scanned qCleared base divisor contents length:=indexedModel.afterClear .quotient
    (by intro impossible;cases impossible) (by intro impossible;cases impossible)
  have qFrame : qCleared={source with locals:=qCleared.locals,memory:=qCleared.memory,clock:=source.clock-16}:=
    Clear.after_frame indexed qPointer 0 16
  have qClock : qCleared.clock=source.clock-16:=congrArg PanSemStateFiniteExact.clock qFrame
  have qIndex : qCleared.locals.lookup (ofString "i")=some (.val (.word 16#64)):=by
    simpa using Clear.after_index indexed qPointer 0 16 (bind_lookup_same _ _ _)
  have qZero : Image qCleared qPointer (fun _=>0#64) 16:=Clear.after_image indexed qPointer 16
  have qAway : ∀ query,(∀ index,index<16→ query≠slot qPointer index)→ qCleared.memory query=source.memory query:=by
    intro query outside
    exact Clear.after_away indexed qPointer query 16 outside
  have qDefinition : qCleared=Clear.after indexed qPointer 0 16:=rfl
  rw [←qDefinition] at qRun
  clear_value qCleared
  by_cases zero : length=0
  · subst length
    have uArgs : evalListHOLFinite qCleared (h:=fun query=>Classical.propDecidable (qCleared.memaddrs query)) underflowArguments=
        some [.val (.word (Workspace.pointer base .numerator))]:=by
      have uLocal:=qModel.u
      simp [underflowArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,uLocal]
    have returned:=ToWords.tail_execute qCleared (Workspace.pointer base .numerator) (fun _=>0#64) underflowArguments qModel.installed
      uArgs (qModel.zeroCase rfl)
      (by intro index inside;exact Workspace.slot_mapped qCleared base qModel.context .numerator index (by change index<16;omega))
      (by
        have funded : 17≤source.clock:=by simpa [price] using enough
        omega)
    have zeroWords : ToWords.words (fun _=>0#64)=Single.remainderWords 0#64:=by
      funext index
      simp [ToWords.words,Single.remainderWords]
    rw [zeroWords] at returned
    let inner:=emptyLocalsHOLFinite {qCleared with clock:=qCleared.clock-1}
    have guardRun : evaluateHOLFiniteState qCleared guard=(some (.returned (RlpWrite.U256Value.tuple (Single.remainderWords 0#64))),inner):=by
      have tested:=guard_read qCleared base divisor contents 0 qModel
      simp only [eval,if_pos rfl] at tested
      rw [guard,evaluateHOLFiniteState_ite,tested]
      simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)]
      exact returned
    have continued : evaluateHOLFiniteState qCleared afterQuotient=
        (some (.returned (RlpWrite.U256Value.tuple (Single.remainderWords 0#64))),inner):=by
      rw [afterQuotient,evaluateHOLFiniteState_seq_line780,guardRun]
    have indexedRun : evaluateHOLFiniteState indexed (.seq (Clear.loop "q" 16) afterQuotient)=
        (some (.returned (RlpWrite.U256Value.tuple (Single.remainderWords 0#64))),inner):=by
      rw [evaluateHOLFiniteState_seq_line780,qRun]
      exact continued
    have declared:=ScalarScope.declare_execute source inner "i" (.const 0#64) 0#64 (.seq (Clear.loop "q" 16) afterQuotient) _ rfl indexedRun
    let target:=restore source "i" inner
    refine ⟨target,(fun _=>0#64),0#64,⟨?_,?_,?_,by intro index inside;omega,by simp [number],by simp [number],checked.positive,?_⟩⟩
    · exact declared
    · have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals,memory:=target.memory,clock:=state.clock-1}) qFrame
      change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-16-1} at frame
      change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-17}
      simpa only [Nat.sub_sub] using frame
    · intro index inside
      change qCleared.memory (slot qPointer index)=.word (Single.padded (fun _=>0#64) 0 index)
      simpa [Single.padded] using qZero index inside
    · intro query outsideQ outsideR
      exact qAway query outsideQ
  · have funded : 34*length+26≤source.clock:=by simpa only [price,if_neg zero] using enough
    let reset:=bind qCleared "i" 0#64
    have resetModel : Scanned reset base divisor contents length:=qModel.bindIndex 0#64
    let rCleared:=Clear.after reset rPointer 0 8
    have rRun:=Clear.loop_execute reset "r" rPointer 8 0 8 (by decide) rfl resetModel.r (bind_lookup_same _ _ _) (by decide)
      (by intro index inside;exact Workspace.slot_mapped reset base resetModel.context .remainder index inside)
      (by change 8≤qCleared.clock;omega)
    have rModel : Scanned rCleared base divisor contents length:=resetModel.afterClear .remainder
      (by intro impossible;cases impossible) (by intro impossible;cases impossible)
    have rFrame : rCleared={qCleared with locals:=rCleared.locals,memory:=rCleared.memory,clock:=qCleared.clock-8}:=
      Clear.after_frame reset rPointer 0 8
    have rClock : rCleared.clock=source.clock-24:=by
      have clock:=congrArg PanSemStateFiniteExact.clock rFrame
      change rCleared.clock=qCleared.clock-8 at clock
      omega
    have rZero : Image rCleared rPointer (fun _=>0#64) 8:=Clear.after_image reset rPointer 8
    have rQuotient : Image rCleared qPointer (fun _=>0#64) 16:=
      Clear.after_workspace_image reset base .remainder .quotient (by intro impossible;cases impossible) (fun _=>0#64) 16 (by decide) qZero
    have rAway : ∀ query,(∀ index,index<8→ query≠slot rPointer index)→ rCleared.memory query=qCleared.memory query:=by
      intro query outside
      exact Clear.after_away reset rPointer query 8 outside
    have rDefinition : rCleared=Clear.after reset rPointer 0 8:=rfl
    rw [←rDefinition] at rRun
    clear_value rCleared
    obtain ⟨middle,quotient,remainder,result,tailRun⟩:=Single.after_clearing_execute rCleared base divisor rModel.context rModel.installed
      contents length rModel.small rModel.image rModel.divisorCell rModel.divisorSmall rModel.positive rModel.digitsSmall
      rZero rModel.r Single.wideArguments (wide_arguments rCleared base divisor contents length rModel) (by omega)
    let inner:=emptyLocalsHOLFinite {middle with clock:=middle.clock-1}
    have guardRun : evaluateHOLFiniteState qCleared guard=(none,qCleared):=by
      have tested:=guard_read qCleared base divisor contents length qModel
      simp only [eval,if_neg zero] at tested
      rw [guard,evaluateHOLFiniteState_ite,tested]
      simp
    have resetRun : evaluateHOLFiniteState qCleared resetIndex=(none,reset):=
      StateSteps.assign_execute qCleared "i" (.const 0#64) 16#64 0#64 qIndex rfl
    have continued : evaluateHOLFiniteState qCleared afterQuotient=
        (some (.returned (RlpWrite.U256Value.tuple (Single.remainderWords remainder))),inner):=by
      rw [afterQuotient,evaluateHOLFiniteState_seq_line780,guardRun]
      change evaluateHOLFiniteState qCleared (.seq resetIndex (.seq (Clear.loop "r" 8) (Single.afterClearing Single.wideArguments)))=_
      rw [evaluateHOLFiniteState_seq_line780,resetRun]
      change evaluateHOLFiniteState reset (.seq (Clear.loop "r" 8) (Single.afterClearing Single.wideArguments))=_
      rw [evaluateHOLFiniteState_seq_line780,rRun]
      exact tailRun
    have indexedRun : evaluateHOLFiniteState indexed (.seq (Clear.loop "q" 16) afterQuotient)=
        (some (.returned (RlpWrite.U256Value.tuple (Single.remainderWords remainder))),inner):=by
      rw [evaluateHOLFiniteState_seq_line780,qRun]
      exact continued
    have declared:=ScalarScope.declare_execute source inner "i" (.const 0#64) 0#64 (.seq (Clear.loop "q" 16) afterQuotient) _ rfl indexedRun
    let target:=restore source "i" inner
    refine ⟨target,quotient,remainder,⟨?_,?_,?_,result.digits,result.quotientEq,result.remainderEq,result.small,?_⟩⟩
    · exact declared
    · have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals,memory:=target.memory,clock:=state.clock-1}) result.state
      change target={rCleared with locals:=target.locals,memory:=target.memory,clock:=rCleared.clock-(34*length+1)-1} at frame
      rw [rFrame,qFrame] at frame
      change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-16-8-(34*length+1)-1} at frame
      have subtract : source.clock-16-8-(34*length+1)-1=source.clock-(34*length+26):=by omega
      simpa only [price,if_neg zero,subtract] using frame
    · exact result.quotient_image rQuotient
    · intro query outsideQ outsideR
      change middle.memory query=source.memory query
      rw [result.away query (by intro index inside;exact outsideQ index (by have small:=checked.small;omega))
        (by simpa [slot] using outsideR 0 (by decide))]
      exact (rAway query outsideR).trans (qAway query outsideQ)


/-- Every outcome of the actual post-scan wrapper spends at most its
length-dependent allowance, including an insufficient incoming clock. -/
theorem after_counts_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (length : Nat) (checked : Scanned source base divisor contents length) :
    source.clock-(evaluateHOLFiniteState source afterCounts).2.clock≤price length := by
  by_cases enough : price length≤source.clock
  · obtain ⟨target,quotient,remainder,result⟩:=after_counts_execute source base divisor contents length checked enough
    rw [result.run]
    have clock:=congrArg PanSemStateFiniteExact.clock result.state
    change target.clock=source.clock-price length at clock
    change source.clock-target.clock≤price length
    omega
  · omega

/-- A real normal return supplies its own funding, numerical remainder,
full quotient image, and complete memory frame. -/
theorem after_counts_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (length : Nat) (checked : Scanned source base divisor contents length)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCounts=(some (.returned returned),post)) :
    ∃ quotient remainder,price length≤source.clock ∧
      returned=RlpWrite.U256Value.tuple (Single.remainderWords remainder) ∧
      Result source post base divisor contents length quotient remainder := by
  obtain ⟨baseTarget,baseQ,baseR,baseResult⟩:=after_counts_execute {source with clock:=price length}
    base divisor contents length (checked.withClock (price length)) (by rfl)
  have zero : baseTarget.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock baseResult.state
    change baseTarget.clock=price length-price length at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget post afterCounts (price length) _ _ baseResult.run zero
    (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)).1
  obtain ⟨target,quotient,remainder,result⟩:=after_counts_execute source base divisor contents length checked funded
  have output:=normal.symm.trans result.run
  have same : post=target:=congrArg Prod.snd output
  have value : returned=RlpWrite.U256Value.tuple (Single.remainderWords remainder):=by
    have values:=congrArg Prod.fst output
    cases values
    rfl
  exact ⟨quotient,remainder,funded,value,same.symm ▸ result⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.literal_counts
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.Scanned.withClock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.Scanned.bindIndex
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.Scanned.afterClear

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Clear.after_frame

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.price_lower

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.price_upper

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.after_counts_execute

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.after_counts_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.after_counts_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def workspaceAddress (buffer : Workspace.Buffer) : ExpHOL 64:=
  .op .add [.var .global (ofString "u256_ws"),.const (BitVec.ofNat 64 (Workspace.offset buffer))]
def convertArguments : List (ExpHOL 64):=[localVar "v",localVar "d"]
def divisorLengthArguments : List (ExpHOL 64):=[localVar "v",.const 8#64]
def numeratorLengthArguments : List (ExpHOL 64):=[localVar "u",localVar "m"]
def afterDivisorLength : ProgHOL 64:=
  .decCall (ofString "mm") .one (ofString "digits_len") numeratorLengthArguments afterCounts
def afterConversion : ProgHOL 64:=
  .decCall (ofString "n") .one (ofString "digits_len") divisorLengthArguments afterDivisorLength
def setupDivisor : ProgHOL 64:=
  .seq (.call (some (none,none)) (ofString "u256_to_digits") convertArguments) afterConversion

theorem body_shape : body=
    .dec (ofString "q") .one (workspaceAddress .quotient)
      (.dec (ofString "r") .one (workspaceAddress .remainder)
        (.dec (ofString "v") .one (workspaceAddress .divisor) setupDivisor)) := by
  simp [body,Clear.divmodBody,Guest.Software.guestFn_digits_divmod,progToHOL,expToHOL,shapeToHOL,
    workspaceAddress,Workspace.offset,setupDivisor,convertArguments,afterConversion,divisorLengthArguments,
    afterDivisorLength,numeratorLengthArguments,afterCounts,afterQuotient,guard,lessTest,underflowArguments,resetIndex,
    Clear.loop,Clear.test,Clear.body,Clear.address,Clear.increment,Single.afterClearing,Single.wideArguments,Single.returnArguments,localVar]

theorem workspace_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : Workspace.Context source base) (buffer : Workspace.Buffer) :
    eval source (workspaceAddress buffer)=some (.val (.word (Workspace.pointer base buffer))) := by
  have global:=context.global
  simp [eval,workspaceAddress,Workspace.pointer,evalHOLExact,evalListHOLExact,toExact,global,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem single_divisor_digits (divisor : BitVec 64) (small : divisor.toNat<2^32) (index : Nat) (inside : index<8) :
    digit (Single.remainderWords divisor) index=Single.remainderDigits divisor index := by
  have masked : divisor &&& 4294967295#64=divisor:=by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    exact (Nat.and_two_pow_sub_one_eq_mod divisor.toNat 32).trans (Nat.mod_eq_of_lt small)
  have shifted : divisor>>>(32:Nat)=0#64:=by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt small
  have choices : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7:=by omega
  rcases choices with h|h|h|h|h|h|h|h <;> subst index <;> simp [digit,Single.remainderWords,Single.remainderDigits,masked,shifted]

theorem single_divisor_length (divisor : BitVec 64) (small : divisor.toNat<2^32) (positive : 0<divisor.toNat) :
    Length.result (digit (Single.remainderWords divisor)) 8=1 ∧
      Length.scans (digit (Single.remainderWords divisor)) 8=8 := by
  have nonzero : divisor≠0#64:=by intro zero;subst divisor;exact Nat.lt_irrefl 0 positive
  have values : ∀ index,index<8→ digit (Single.remainderWords divisor) index=Single.remainderDigits divisor index:=
    single_divisor_digits divisor small
  simp [Length.result,Length.scans,values,Single.remainderDigits,nonzero]

end InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.body_shape
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.workspace_read
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.single_divisor_digits
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.single_divisor_length

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Physical arguments after the real q/r/v pointer declarations. At least
8 actual numerator cells are retained for the real early-return read. -/
structure Prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  eight : 8≤count
  small : count≤16
  q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))
  r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder)))
  u : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator)))
  v : source.locals.lookup (ofString "v")=some (.val (.word (Workspace.pointer base .divisor)))
  m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count)))
  d : source.locals.lookup (ofString "d")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor))
  image : Image source (Workspace.pointer base .numerator) contents count
  divisorSmall : divisor.toNat<2^32
  positive : 0<divisor.toNat
  digitsSmall : ∀ index,index<count→ (contents index).toNat<2^32

theorem Prepared.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat} (checked : Prepared source base divisor contents count) (clock : Nat) :
    Prepared {source with clock:=clock} base divisor contents count :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
    checked.eight,checked.small,checked.q,checked.r,checked.u,checked.v,checked.m,checked.d,checked.image,
    checked.divisorSmall,checked.positive,checked.digitsSmall⟩

theorem Prepared.bindScan {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat} (checked : Prepared source base divisor contents count)
    (name : String) (word : BitVec 64) (allowed : name="n" ∨ name="mm") :
    Prepared (bind source name word) base divisor contents count := by
  rcases allowed with rfl|rfl <;>
    refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
      checked.eight,checked.small,?_,?_,?_,?_,?_,?_,checked.image,checked.divisorSmall,checked.positive,checked.digitsSmall⟩ <;>
    first
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.q
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.r
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.u
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.v
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.m
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.d

/-- The actual converter constructs the divisor image while protecting every
numerator slot through the derived workspace-buffer separation. -/
theorem Prepared.convert {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat} (checked : Prepared source base divisor contents count) :
    Prepared (ToDigits.callerPost source (Workspace.pointer base .divisor) (Single.remainderWords divisor)) base divisor contents count ∧
      Image (ToDigits.callerPost source (Workspace.pointer base .divisor) (Single.remainderWords divisor))
        (Workspace.pointer base .divisor) (Single.remainderDigits divisor) 8 := by
  constructor
  · refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
      checked.eight,checked.small,checked.q,checked.r,checked.u,checked.v,checked.m,checked.d,?_,
      checked.divisorSmall,checked.positive,checked.digitsSmall⟩
    intro index inside
    rw [ToDigits.caller_away source (Workspace.pointer base .divisor) (slot (Workspace.pointer base .numerator) index)
      (Single.remainderWords divisor) (by
        intro other otherInside
        exact Workspace.separate base .numerator .divisor (by intro impossible;cases impossible)
          index other (by change index<16;have small:=checked.small;omega) otherInside)]
    exact checked.image index inside
  · intro index inside
    rw [←single_divisor_digits divisor checked.divisorSmall index inside]
    exact ToDigits.caller_image source (Workspace.pointer base .divisor) (Single.remainderWords divisor) index inside

/-- The real scanned length and retained input image supply all post-scan
conditions, including the eight actual zero cells used by the early return. -/
theorem Prepared.scanned {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat} (checked : Prepared source base divisor contents count)
    (divisorImage : Image source (Workspace.pointer base .divisor) (Single.remainderDigits divisor) 8)
    (n : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (mm : source.locals.lookup (ofString "mm")=some (.val (.word (BitVec.ofNat 64 (Length.result contents count))))) :
    Scanned source base divisor contents (Length.result contents count) := by
  have bound:=Length.result_bound contents count
  have small:=checked.small
  refine ⟨checked.context,checked.installed,by omega,checked.q,checked.r,checked.u,checked.v,n,mm,?_,?_,
    checked.divisorSmall,checked.positive,?_,?_⟩
  · intro index inside
    exact checked.image index (by omega)
  · have cell:=divisorImage 0 (by decide)
    simpa [slot,Single.remainderDigits] using cell
  · intro index inside
    exact checked.digitsSmall index (by omega)
  · intro zero index inside
    rw [checked.image index (by have eight:=checked.eight;omega)]
    congr 1
    exact (Length.result_zero contents count).1 zero index (by have eight:=checked.eight;omega)

def wholePrice (contents : Nat→ BitVec 64) (count : Nat) : Nat:=11+Length.scans contents count+price (Length.result contents count)

theorem wholePrice_upper (contents : Nat→ BitVec 64) (count : Nat) : wholePrice contents count≤35*count+37 := by
  have scans:=Length.scans_bound contents count
  have length:=Length.result_bound contents count
  have rest:=price_upper (Length.result contents count)
  unfold wholePrice
  omega

end InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.Prepared.withClock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.Prepared.bindScan
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.Prepared.convert
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.Prepared.scanned
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.wholePrice_upper

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure WrapperResult (program : ProgHOL 64) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base divisor : BitVec 64) (contents : Nat→ BitVec 64) (count : Nat)
    (quotient : Nat→ BitVec 64) (remainder : BitVec 64) : Prop where
  run : evaluateHOLFiniteState source program=(some (.returned (RlpWrite.U256Value.tuple (Single.remainderWords remainder))),target)
  state : target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-wholePrice contents count}
  quotientImage : Image target (Workspace.pointer base .quotient) (Single.padded quotient (Length.result contents count)) 16
  digits : ∀ index,index<Length.result contents count→ (quotient index).toNat<2^32
  quotientEq : number quotient (Length.result contents count)=number contents count/divisor.toNat
  remainderEq : remainder.toNat=number contents count%divisor.toNat
  small : remainder.toNat<divisor.toNat
  away : ∀ query,(∀ index,index<16→ query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .remainder) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .divisor) index)→ target.memory query=source.memory query

/-- Both actual mapped scans feed the real post-scan wrapper. The divisor
conversion and all calls are executed, rather than supplied as future facts. -/
theorem setup_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Prepared source base divisor contents count)
    (enough : wholePrice contents count≤source.clock) :
    ∃ target quotient remainder,WrapperResult setupDivisor source target base divisor contents count quotient remainder := by
  have funded : 11+Length.scans contents count+price (Length.result contents count)≤source.clock:=enough
  let converted:=ToDigits.callerPost source (Workspace.pointer base .divisor) (Single.remainderWords divisor)
  obtain ⟨convertedModel,divisorImage⟩:=checked.convert
  have convertArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) convertArguments=
      some [.val (.word (Workspace.pointer base .divisor)),RlpWrite.U256Value.tuple (Single.remainderWords divisor)]:=by
    have vLocal:=checked.v
    have dLocal:=checked.d
    simp [convertArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,vLocal,dLocal]
  have convertedRun:=ToDigits.call_execute source (Workspace.pointer base .divisor) (Single.remainderWords divisor) convertArguments
    checked.installed convertArgs (by intro index inside;exact Workspace.slot_mapped source base checked.context .divisor index inside) (by omega)
  have divLength:=single_divisor_length divisor checked.divisorSmall checked.positive
  let nEntry:=bind {converted with clock:=converted.clock-1-8} "n" 1#64
  have nModel : Prepared nEntry base divisor contents count:=
    (convertedModel.withClock (converted.clock-1-8)).bindScan "n" 1#64 (Or.inl rfl)
  let mmEntry:=bind {nEntry with clock:=nEntry.clock-1-Length.scans contents count} "mm" (BitVec.ofNat 64 (Length.result contents count))
  have mmModel : Prepared mmEntry base divisor contents count:=
    (nModel.withClock (nEntry.clock-1-Length.scans contents count)).bindScan "mm" _ (Or.inr rfl)
  have mmN : mmEntry.locals.lookup (ofString "n")=some (.val (.word 1#64)):=by
    exact (bind_lookup_other _ "mm" "n" _ (by decide)).trans (bind_lookup_same _ _ _)
  have scanned : Scanned mmEntry base divisor contents (Length.result contents count):=
    mmModel.scanned divisorImage mmN (bind_lookup_same _ _ _)
  have convertedClock : converted.clock=source.clock-1:=rfl
  have nClock : nEntry.clock=source.clock-10:=by
    change converted.clock-1-8=source.clock-10
    omega
  have mmClock : mmEntry.clock=source.clock-(11+Length.scans contents count):=by
    change nEntry.clock-1-Length.scans contents count=source.clock-(11+Length.scans contents count)
    omega
  obtain ⟨inner,quotient,remainder,result⟩:=after_counts_execute mmEntry base divisor contents (Length.result contents count) scanned (by omega)
  have mmArgs : evalListHOLFinite nEntry (h:=fun query=>Classical.propDecidable (nEntry.memaddrs query)) numeratorLengthArguments=
      some [.val (.word (Workspace.pointer base .numerator)),.val (.word (BitVec.ofNat 64 count))]:=by
    have uLocal:=nModel.u
    have mLocal:=nModel.m
    simp [numeratorLengthArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,uLocal,mLocal]
  have mmRun:=Length.call_execute nEntry (Workspace.pointer base .numerator) contents count checked.small "mm"
    numeratorLengthArguments afterCounts nModel.installed mmArgs nModel.image
    (by intro index inside;exact Workspace.slot_mapped nEntry base nModel.context .numerator index (by change index<16;have small:=checked.small;omega)) (by omega)
  change evaluateHOLFiniteState nEntry afterDivisorLength=
    (let output:=evaluateHOLFiniteState mmEntry afterCounts;(output.1,restore nEntry "mm" output.2)) at mmRun
  rw [result.run] at mmRun
  have nArgs : evalListHOLFinite converted (h:=fun query=>Classical.propDecidable (converted.memaddrs query)) divisorLengthArguments=
      some [.val (.word (Workspace.pointer base .divisor)),.val (.word 8#64)]:=by
    have vLocal : converted.locals.lookup (ofString "v")=some (.val (.word (Workspace.pointer base .divisor))):=convertedModel.v
    simp [divisorLengthArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,vLocal]
  have nRun:=Length.call_execute converted (Workspace.pointer base .divisor) (digit (Single.remainderWords divisor)) 8 (by decide) "n"
    divisorLengthArguments afterDivisorLength convertedModel.installed nArgs (ToDigits.caller_image source _ _)
    (by intro index inside;exact Workspace.slot_mapped converted base convertedModel.context .divisor index inside) (by rw [divLength.2];omega)
  rw [divLength.1,divLength.2] at nRun
  change evaluateHOLFiniteState converted afterConversion=
    (let output:=evaluateHOLFiniteState nEntry afterDivisorLength;(output.1,restore converted "n" output.2)) at nRun
  rw [mmRun] at nRun
  let target:=restore converted "n" (restore nEntry "mm" inner)
  refine ⟨target,quotient,remainder,⟨?_,?_,result.quotientImage,result.digits,?_,?_,result.small,?_⟩⟩
  · rw [setupDivisor,evaluateHOLFiniteState_seq_line780,convertedRun]
    exact nRun
  · have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals}) result.state
    change target={source with
      locals:=target.locals,memory:=target.memory,
      clock:=source.clock-1-1-8-1-Length.scans contents count-price (Length.result contents count)} at frame
    have subtract : source.clock-1-1-8-1-Length.scans contents count-price (Length.result contents count)=source.clock-wholePrice contents count:=by
      unfold wholePrice
      omega
    simpa only [subtract] using frame
  · simpa only [Length.trimmed_number] using result.quotientEq
  · simpa only [Length.trimmed_number] using result.remainderEq
  · intro query outsideQ outsideR outsideV
    exact (result.away query outsideQ outsideR).trans
      (ToDigits.caller_away source (Workspace.pointer base .divisor) query (Single.remainderWords divisor) outsideV)

end InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.setup_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual function-entry arguments and physical workspace, before any
pointer initialization, conversion, scan, clearing or division. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  eight : 8≤count
  small : count≤16
  u : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator)))
  m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count)))
  d : source.locals.lookup (ofString "d")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor))
  image : Image source (Workspace.pointer base .numerator) contents count
  divisorSmall : divisor.toNat<2^32
  positive : 0<divisor.toNat
  digitsSmall : ∀ index,index<count→ (contents index).toNat<2^32

theorem Entry.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat} (checked : Entry source base divisor contents count) (clock : Nat) :
    Entry {source with clock:=clock} base divisor contents count :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
    checked.eight,checked.small,checked.u,checked.m,checked.d,checked.image,checked.divisorSmall,checked.positive,checked.digitsSmall⟩

theorem Entry.bindPointer {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→ BitVec 64} {count : Nat} (checked : Entry source base divisor contents count)
    (name : String) (word : BitVec 64) (allowed : name="q" ∨ name="r" ∨ name="v") :
    Entry (bind source name word) base divisor contents count := by
  rcases allowed with rfl|rfl|rfl <;>
    refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
      checked.eight,checked.small,?_,?_,?_,checked.image,checked.divisorSmall,checked.positive,checked.digitsSmall⟩ <;>
    first
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.u
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.m
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.d

/-- The unchanged complete digits_divmod function on its actual one-digit
path, including all pointer declarations and the original early return. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Entry source base divisor contents count)
    (enough : wholePrice contents count≤source.clock) :
    ∃ target quotient remainder,WrapperResult body source target base divisor contents count quotient remainder := by
  let qEntry:=bind source "q" (Workspace.pointer base .quotient)
  have qModel : Entry qEntry base divisor contents count:=checked.bindPointer "q" _ (Or.inl rfl)
  let rEntry:=bind qEntry "r" (Workspace.pointer base .remainder)
  have rModel : Entry rEntry base divisor contents count:=qModel.bindPointer "r" _ (Or.inr (Or.inl rfl))
  let vEntry:=bind rEntry "v" (Workspace.pointer base .divisor)
  have vModel : Entry vEntry base divisor contents count:=rModel.bindPointer "v" _ (Or.inr (Or.inr rfl))
  have qCell : vEntry.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))):=
    (bind_lookup_other _ "v" "q" _ (by decide)).trans
      ((bind_lookup_other _ "r" "q" _ (by decide)).trans (bind_lookup_same _ _ _))
  have rCell : vEntry.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))):=
    (bind_lookup_other _ "v" "r" _ (by decide)).trans (bind_lookup_same _ _ _)
  have prepared : Prepared vEntry base divisor contents count:=
    ⟨vModel.context,vModel.installed,vModel.eight,vModel.small,qCell,rCell,vModel.u,bind_lookup_same _ _ _,
      vModel.m,vModel.d,vModel.image,vModel.divisorSmall,vModel.positive,vModel.digitsSmall⟩
  obtain ⟨inner,quotient,remainder,result⟩:=setup_execute vEntry base divisor contents count prepared enough
  have vRun:=ScalarScope.declare_execute rEntry inner "v" (workspaceAddress .divisor) (Workspace.pointer base .divisor)
    setupDivisor _ (workspace_read rEntry base rModel.context .divisor) result.run
  have rRun:=ScalarScope.declare_execute qEntry (restore rEntry "v" inner) "r" (workspaceAddress .remainder) (Workspace.pointer base .remainder)
    (.dec (ofString "v") .one (workspaceAddress .divisor) setupDivisor) _ (workspace_read qEntry base qModel.context .remainder) vRun
  have qRun:=ScalarScope.declare_execute source (restore qEntry "r" (restore rEntry "v" inner)) "q" (workspaceAddress .quotient) (Workspace.pointer base .quotient)
    (.dec (ofString "r") .one (workspaceAddress .remainder) (.dec (ofString "v") .one (workspaceAddress .divisor) setupDivisor)) _
    (workspace_read source base checked.context .quotient) rRun
  let target:=restore source "q" (restore qEntry "r" (restore rEntry "v" inner))
  refine ⟨target,quotient,remainder,⟨?_,?_,result.quotientImage,result.digits,result.quotientEq,result.remainderEq,result.small,result.away⟩⟩
  · rw [body_shape]
    exact qRun
  · have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals}) result.state
    exact frame

/-- Uniform source-clock charge, including every short-clock outcome. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Entry source base divisor contents count) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤wholePrice contents count := by
  by_cases enough : wholePrice contents count≤source.clock
  · obtain ⟨target,quotient,remainder,result⟩:=execute source base divisor contents count checked enough
    rw [result.run]
    have clock:=congrArg PanSemStateFiniteExact.clock result.state
    change target.clock=source.clock-wholePrice contents count at clock
    change source.clock-target.clock≤wholePrice contents count
    omega
  · omega

/-- A genuine returned execution derives its own funding and full physical
quotient/remainder contract from the actual entry state. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Entry source base divisor contents count)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ quotient remainder,wholePrice contents count≤source.clock ∧
      returned=RlpWrite.U256Value.tuple (Single.remainderWords remainder) ∧
      WrapperResult body source post base divisor contents count quotient remainder := by
  obtain ⟨baseTarget,baseQ,baseR,baseResult⟩:=execute {source with clock:=wholePrice contents count}
    base divisor contents count (checked.withClock (wholePrice contents count)) (by rfl)
  have zero : baseTarget.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock baseResult.state
    change baseTarget.clock=wholePrice contents count-wholePrice contents count at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget post body (wholePrice contents count) _ _ baseResult.run zero
    (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)).1
  obtain ⟨target,quotient,remainder,result⟩:=execute source base divisor contents count checked funded
  have output:=normal.symm.trans result.run
  have same : post=target:=congrArg Prod.snd output
  have value : returned=RlpWrite.U256Value.tuple (Single.remainderWords remainder):=by
    have values:=congrArg Prod.fst output
    cases values
    rfl
  exact ⟨quotient,remainder,funded,value,same.symm ▸ result⟩

theorem WrapperResult.quotient_number {program : ProgHOL 64} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base divisor remainder : BitVec 64} {contents quotient : Nat→ BitVec 64} {count : Nat}
    (result : WrapperResult program source target base divisor contents count quotient remainder)
    (small : Length.result contents count≤8) :
    quadNumber (ToWords.words (Single.padded quotient (Length.result contents count)))=number contents count/divisor.toNat := by
  have digits : ∀ index,index<8→ (Single.padded quotient (Length.result contents count) index).toNat<2^32:=by
    intro index inside
    by_cases before : index<Length.result contents count
    · simpa only [Single.padded,if_pos before] using result.digits index before
    · simp [Single.padded,before]
  rw [ToWords.words_number _ digits,Single.padded_number quotient (Length.result contents count) 8 small]
  exact result.quotientEq

end InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.Entry.withClock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.Entry.bindPointer
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.body_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.body_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.WrapperResult.quotient_number

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Length
/-- A descending leading-zero scan and its returned length share the same
initial digit range; they cannot both independently use its full width. -/
theorem scans_result_bound (contents : Nat→ BitVec 64) (count : Nat) : scans contents count+result contents count≤count+1 := by
  induction count with
  | zero=>simp [scans,result]
  | succ count ih=>
    by_cases zero : contents count=0#64
    · simp only [scans,result,if_pos zero]
      omega
    · simp only [scans,result,if_neg zero]
      omega
end InitECandidate.Solver.Input.UDivMod.WideDigits.Length

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem wholePrice_tight (contents : Nat→ BitVec 64) (count : Nat) : wholePrice contents count≤34*count+38 := by
  have shared:=Length.scans_result_bound contents count
  have length:=Length.result_bound contents count
  have rest:=price_upper (Length.result contents count)
  unfold wholePrice
  omega

def formals : List (MlS×ShapeHOL):=[(ofString "u",.one),(ofString "m",.one),(ofString "d",RlpWrite.U256Value.tupleShape)]
def values (pointer : BitVec 64) (count : Nat) (divisor : BitVec 64) : List (ValueHOL 64):=
  [.val (.word pointer),.val (.word (BitVec.ofNat 64 count)),RlpWrite.U256Value.tuple (Single.remainderWords divisor)]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "digits_divmod")=some (formals,body,RlpWrite.U256Value.tupleShape) := by
  have checked:=OriginalCode.indexed code installed 62 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_digits_divmod) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Clear.divmodBody,RlpWrite.U256Value.tupleShape,
    Guest.Software.guestFn_digits_divmod,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

private def rawLocals (pointer : BitVec 64) (count : Nat) (divisor : BitVec 64) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "d" then some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)) else
  if name=ofString "m" then some (.val (.word (BitVec.ofNat 64 count))) else
  if name=ofString "u" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS→ Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (pointer : BitVec 64) (count : Nat) (divisor : BitVec 64)
    (code : codeFn (ofString "digits_divmod")=some (formals,body,RlpWrite.U256Value.tupleShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "digits_divmod") (values pointer count divisor)=some (body,callee,RlpWrite.U256Value.tupleShape) ∧
      callee.lookup (ofString "u")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count))) ∧
      callee.lookup (ofString "d")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer count divisor).length ∧
      ((formals.zip (values pointer count divisor)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=by
    simp [formals,values,RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "u"≠ofString "m" by decide,show ofString "u"≠ofString "d" by decide,show ofString "m"≠ofString "d" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "digits_divmod") (values pointer count divisor)=
      some (body,rawLocals pointer count divisor,RlpWrite.U256Value.tupleShape):=by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "u"≠ofString "d" by decide,show ofString "u"≠ofString "m" by decide]
  · simp [rawLocals,show ofString "m"≠ofString "d" by decide]
  · simp [rawLocals]

/-- Caller-side physical inputs contain no callee locals or future outcomes. -/
structure Buffers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  eight : 8≤count
  small : count≤16
  image : Image source (Workspace.pointer base .numerator) contents count
  divisorSmall : divisor.toNat<2^32
  positive : 0<divisor.toNat
  digitsSmall : ∀ index,index<count→ (contents index).toNat<2^32

private theorem callee_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Buffers source base divisor contents count)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (u : callee.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))))
    (m : callee.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count))))
    (d : callee.lookup (ofString "d")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor))) :
    Entry (callEntryStateHOLFinite source callee) base divisor contents count :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
    checked.eight,checked.small,u,m,d,checked.image,checked.divisorSmall,checked.positive,checked.digitsSmall⟩

/-- Actual mixed scalar/quad arguments price every call form, including
short clocks. At the original u256 width this is at most311source ticks. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Buffers source base divisor contents count)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (values (Workspace.pointer base .numerator) count divisor)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "digits_divmod") arguments)).2.clock≤wholePrice contents count+1 := by
  obtain ⟨callee,called,u,m,d⟩:=environment source.code.lookup (Workspace.pointer base .numerator) count divisor
    (original_code source.code checked.installed)
  have actual:=callee_entry source base divisor contents count checked callee u m d
  exact ClockCost.call_current source destination (ofString "digits_divmod") arguments _ body callee RlpWrite.U256Value.tupleShape
    (wholePrice contents count) args called (body_cost (callEntryStateHOLFinite source callee) base divisor contents count actual)

/-- A real child return supplies the exact physical result and restored
caller continuation. The scoped-call rule charges its separate call tick. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Buffers source base divisor contents count) (name : String)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "digits_divmod") (values (Workspace.pointer base .numerator) count divisor)=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    ∃ quotient remainder,wholePrice contents count≤source.clock-1 ∧
      returned=RlpWrite.U256Value.tuple (Single.remainderWords remainder) ∧
      WrapperResult body (callEntryStateHOLFinite source callee) target base divisor contents count quotient remainder ∧
      CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple (Single.remainderWords remainder))
          {source with memory:=target.memory,clock:=source.clock-1-wholePrice contents count} := by
  obtain ⟨expected,lookup,u,m,d⟩:=environment source.code.lookup (Workspace.pointer base .numerator) count divisor
    (original_code source.code checked.installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at u m d
  rw [bodyEq] at run
  have entry:=callee_entry source base divisor contents count checked callee u m d
  obtain ⟨quotient,remainder,funded,returnedEq,result⟩:=body_normal (callEntryStateHOLFinite source callee) target base divisor contents count entry returned run
  refine ⟨quotient,remainder,funded,returnedEq,result,?_⟩
  have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) result.state
  change {target with locals:=source.locals}={source with memory:=target.memory,clock:=source.clock-1-wholePrice contents count} at frame
  rw [CallNormal.continuationEntry,returnedEq,frame]

end InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Length.scans_result_bound
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.wholePrice_tight
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.environment
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.call_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.resume


namespace InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem body_cost_eight (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (checked : Entry source base divisor contents 8) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤310 := by
  have cost:=body_cost source base divisor contents 8 checked
  have bound:=wholePrice_tight contents 8
  omega

theorem call_cost_eight (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (checked : Buffers source base divisor contents 8)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (values (Workspace.pointer base .numerator) 8 divisor)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "digits_divmod") arguments)).2.clock≤311 := by
  have cost:=call_cost source base divisor contents 8 checked destination arguments args
  have bound:=wholePrice_tight contents 8
  omega

end InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.body_cost_eight
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.call_cost_eight

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual caller state immediately before binding the returned remainder. -/
structure CallerResult (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (quotient : Nat→ BitVec 64) (remainder : BitVec 64) : Prop where
  state : post={source with memory:=post.memory,clock:=source.clock-1-wholePrice contents count}
  quotientImage : Image post (Workspace.pointer base .quotient) (Single.padded quotient (Length.result contents count)) 16
  digits : ∀ index,index<Length.result contents count→ (quotient index).toNat<2^32
  quotientEq : number quotient (Length.result contents count)=number contents count/divisor.toNat
  remainderEq : remainder.toNat=number contents count%divisor.toNat
  small : remainder.toNat<divisor.toNat
  away : ∀ query,(∀ index,index<16→ query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .remainder) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .divisor) index)→ post.memory query=source.memory query

/-- Execute the actual scoped call and install its real four-word remainder
before evaluating an arbitrary original continuation. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (checked : Buffers source base divisor contents count)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (values (Workspace.pointer base .numerator) count divisor))
    (enough : wholePrice contents count+1≤source.clock) :
    ∃ post quotient remainder,CallerResult source post base divisor contents count quotient remainder ∧
      evaluateHOLFiniteState source (.decCall (ofString name) RlpWrite.U256Value.tupleShape (ofString "digits_divmod") arguments continuation)=
        (let output:=evaluateHOLFiniteState (setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple (Single.remainderWords remainder)) post) continuation;
          (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,u,m,d⟩:=environment source.code.lookup (Workspace.pointer base .numerator) count divisor
    (original_code source.code checked.installed)
  have actual:=callee_entry source base divisor contents count checked callee u m d
  obtain ⟨target,quotient,remainder,result⟩:=execute (callEntryStateHOLFinite source callee) base divisor contents count actual
    (by change wholePrice contents count≤source.clock-1;omega)
  let post:={target with locals:=source.locals}
  have caller:=CallNormal.return_execute source target name RlpWrite.U256Value.tupleShape (ofString "digits_divmod") arguments _
    body continuation callee RlpWrite.U256Value.tupleShape (RlpWrite.U256Value.tuple (Single.remainderWords remainder)) args called (by omega) result.run
    (by simp [RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  refine ⟨post,quotient,remainder,⟨?_,result.quotientImage,result.digits,result.quotientEq,result.remainderEq,result.small,result.away⟩,caller⟩
  exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) result.state

theorem CallerResult.quotient_number {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base divisor remainder : BitVec 64} {contents quotient : Nat→ BitVec 64} {count : Nat}
    (result : CallerResult source post base divisor contents count quotient remainder)
    (small : Length.result contents count≤8) :
    quadNumber (ToWords.words (Single.padded quotient (Length.result contents count)))=number contents count/divisor.toNat := by
  have digits : ∀ index,index<8→ (Single.padded quotient (Length.result contents count) index).toNat<2^32:=by
    intro index inside
    by_cases before : index<Length.result contents count
    · simpa only [Single.padded,if_pos before] using result.digits index before
    · simp [Single.padded,before]
  rw [ToWords.words_number _ digits,Single.padded_number quotient (Length.result contents count) 8 small]
  exact result.quotientEq

end InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.call_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.DivMod.CallerResult.quotient_number

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def pairValue (quotient remainder : Quad) : ValueHOL 64:=.rStruct
  [.val (.word (quotient 0)),.val (.word (quotient 1)),.val (.word (quotient 2)),.val (.word (quotient 3)),
   .val (.word (remainder 0)),.val (.word (remainder 1)),.val (.word (remainder 2)),.val (.word (remainder 3))]
def finish : ProgHOL 64:=.return (.rstruct
  [.rfield 0 (localVar "q"),.rfield 1 (localVar "q"),.rfield 2 (localVar "q"),.rfield 3 (localVar "q"),
   .rfield 0 (localVar "r"),.rfield 1 (localVar "r"),.rfield 2 (localVar "r"),.rfield 3 (localVar "r")])
def quotientArguments : List (ExpHOL 64):=[DivMod.workspaceAddress .quotient]
def afterDivision : ProgHOL 64:=.decCall (ofString "q") RlpWrite.U256Value.tupleShape (ofString "digits_to_u256") quotientArguments finish
def divisionArguments : List (ExpHOL 64):=[localVar "u",.const 8#64,localVar "b"]
def numeratorArguments : List (ExpHOL 64):=[localVar "u",localVar "a"]
def slowTail : ProgHOL 64:=.seq (.call (some (none,none)) (ofString "u256_to_digits") numeratorArguments)
  (.decCall (ofString "r") RlpWrite.U256Value.tupleShape (ofString "digits_divmod") divisionArguments afterDivision)

theorem finish_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (quotient remainder : Quad)
    (q : source.locals.lookup (ofString "q")=some (RlpWrite.U256Value.tuple quotient))
    (r : source.locals.lookup (ofString "r")=some (RlpWrite.U256Value.tuple remainder)) :
    evaluateHOLFiniteState source finish=(some (.returned (pairValue quotient remainder)),emptyLocalsHOLFinite source) := by
  simp [finish,pairValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,q,r,
    RlpWrite.U256Value.tuple,shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.finish_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Result (program : ProgHOL 64) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (a : Quad) (divisor : BitVec 64) (quotient remainder : Quad)
    (spent : Nat:=DivMod.wholePrice (digit a) 8+3) : Prop where
  run : evaluateHOLFiniteState source program=(some (.returned (pairValue quotient remainder)),target)
  state : target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-spent}
  quotientEq : quadNumber quotient=quadNumber a/divisor.toNat
  remainderEq : quadNumber remainder=quadNumber a%divisor.toNat
  small : quadNumber remainder<divisor.toNat
  away : ∀ query,(∀ index,index<16→ query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .remainder) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .divisor) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .numerator) index)→ target.memory query=source.memory query

/-- Execute the original wide u256 division tail: convert the numerator,
call the real divider, reconstruct its quotient, and return all eight words. -/
theorem slow_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (uLocal : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (enough : DivMod.wholePrice (digit a) 8+3≤source.clock) :
    ∃ target quotient remainder,Result slowTail source target base a divisor quotient remainder := by
  let converted:=ToDigits.callerPost source (Workspace.pointer base .numerator) a
  have convertArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) numeratorArguments=
      some [.val (.word (Workspace.pointer base .numerator)),RlpWrite.U256Value.tuple a]:=by
    simp [numeratorArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,uLocal,aLocal]
  have convertedRun:=ToDigits.call_execute source (Workspace.pointer base .numerator) a numeratorArguments installed convertArgs
    (by intro index inside;exact Workspace.slot_mapped source base context .numerator index (by change index<16;omega)) (by omega)
  have convertedContext : Workspace.Context converted base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  have checked : DivMod.Buffers converted base divisor (digit a) 8:=
    ⟨convertedContext,installed,by decide,by decide,ToDigits.caller_image source _ a,divisorSmall,positive,digit_small a⟩
  have divisionArgs : evalListHOLFinite converted (h:=fun query=>Classical.propDecidable (converted.memaddrs query)) divisionArguments=
      some (DivMod.values (Workspace.pointer base .numerator) 8 divisor):=by
    have u : converted.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))):=uLocal
    have b : converted.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)):=bLocal
    simp [divisionArguments,DivMod.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,u,b]
  have convertedClock : converted.clock=source.clock-1:=rfl
  obtain ⟨post,quotient,remainder,result,divisionRun⟩:=DivMod.call_execute converted base divisor (digit a) 8 checked "r"
    divisionArguments afterDivision divisionArgs (by change DivMod.wholePrice (digit a) 8+1≤converted.clock;omega)
  let rEntry:=setVarHOLFinite (ofString "r") (RlpWrite.U256Value.tuple (Single.remainderWords remainder)) post
  have postContext : Workspace.Context post base:=⟨by rw [result.state];exact context.global,
    by rw [result.state];exact context.domain,context.arena,context.aligned⟩
  have rContext : Workspace.Context rEntry base:=⟨postContext.global,postContext.domain,postContext.arena,postContext.aligned⟩
  have postCode : OriginalCode.Installed post.code:=by rw [result.state];exact installed
  have rCode : OriginalCode.Installed rEntry.code:=postCode
  have postClock:=congrArg PanSemStateFiniteExact.clock result.state
  change post.clock=converted.clock-1-DivMod.wholePrice (digit a) 8 at postClock
  have rClock : rEntry.clock=source.clock-2-DivMod.wholePrice (digit a) 8:=by
    change post.clock=source.clock-2-DivMod.wholePrice (digit a) 8
    omega
  have quotientArgs : evalListHOLFinite rEntry (h:=fun query=>Classical.propDecidable (rEntry.memaddrs query)) quotientArguments=
      some [.val (.word (Workspace.pointer base .quotient))]:=by
    have address:=DivMod.workspace_read rEntry base rContext .quotient
    simp only [eval] at address
    simpa only [quotientArguments,evalListHOLFinite,evalListHOLExact,address] using
      (show some [.val (.word (Workspace.pointer base .quotient))]=some [.val (.word (Workspace.pointer base .quotient))] from rfl)
  let qWords:=ToWords.words (Single.padded quotient (Length.result (digit a) 8))
  let qEntry:=setVarHOLFinite (ofString "q") (RlpWrite.U256Value.tuple qWords) {rEntry with clock:=rEntry.clock-1}
  have qCell : qEntry.locals.lookup (ofString "q")=some (RlpWrite.U256Value.tuple qWords):=by
    simp [qEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have rCell : qEntry.locals.lookup (ofString "r")=some (RlpWrite.U256Value.tuple (Single.remainderWords remainder)):=by
    simp [qEntry,rEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,show ofString "q"≠ofString "r" by decide,show ofString "r"≠ofString "q" by decide]
  have finishRun:=finish_execute qEntry qWords (Single.remainderWords remainder) qCell rCell
  have quotientRun:=ToWords.call_execute rEntry (Workspace.pointer base .quotient) (Single.padded quotient (Length.result (digit a) 8)) "q"
    quotientArguments finish rCode quotientArgs (by intro index inside;exact result.quotientImage index (by omega))
    (by intro index inside;exact Workspace.slot_mapped rEntry base rContext .quotient index (by change index<16;omega)) (by change 1≤rEntry.clock;omega)
  change evaluateHOLFiniteState rEntry afterDivision=
    (let output:=evaluateHOLFiniteState qEntry finish;(output.1,restore rEntry "q" output.2)) at quotientRun
  rw [finishRun] at quotientRun
  change evaluateHOLFiniteState converted (.decCall (ofString "r") RlpWrite.U256Value.tupleShape (ofString "digits_divmod") divisionArguments afterDivision)=
    (let output:=evaluateHOLFiniteState rEntry afterDivision;(output.1,restore converted "r" output.2)) at divisionRun
  rw [quotientRun] at divisionRun
  let target:=restore converted "r" (restore rEntry "q" (emptyLocalsHOLFinite qEntry))
  refine ⟨target,qWords,Single.remainderWords remainder,⟨?_,?_,?_,?_,?_,?_⟩⟩
  · rw [slowTail,evaluateHOLFiniteState_seq_line780,convertedRun]
    exact divisionRun
  · have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
        locals:=target.locals,clock:=state.clock-1}) result.state
    change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-1-1-DivMod.wholePrice (digit a) 8-1} at frame
    have subtract : source.clock-1-1-DivMod.wholePrice (digit a) 8-1=source.clock-(DivMod.wholePrice (digit a) 8+3):=by omega
    simpa only [subtract] using frame
  · simpa only [digits_number] using result.quotient_number (Length.result_bound (digit a) 8)
  · rw [Single.remainder_number,result.remainderEq,digits_number]
  · simpa only [Single.remainder_number] using result.small
  · intro query outsideQ outsideR outsideV outsideU
    exact (result.away query outsideQ outsideR outsideV).trans (ToDigits.caller_away source (Workspace.pointer base .numerator) query a outsideU)

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.slow_tail_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_u256_divmod with | .function fn=>progToHOL fn.body | _=>.skip
def slowBranch : ProgHOL 64:=.dec (ofString "u") .one (DivMod.workspaceAddress .numerator) slowTail

private def findSlow : ProgHOL 64→ Option (ProgHOL 64)
  | .dec name shape expression rest=>if name=ofString "u" then some (.dec name shape expression rest) else findSlow rest
  | .decCall _ _ _ _ rest=>findSlow rest
  | .seq first rest=>(findSlow first).orElse (fun _=>findSlow rest)
  | .ite _ yes no=>(findSlow yes).orElse (fun _=>findSlow no)
  | _=>none

theorem literal_slow : findSlow body=some slowBranch := by
  simp [findSlow,body,Guest.Software.guestFn_u256_divmod,progToHOL,expToHOL,shapeToHOL,
    slowBranch,slowTail,numeratorArguments,divisionArguments,afterDivision,quotientArguments,finish,
    DivMod.workspaceAddress,Workspace.offset,localVar,RlpWrite.U256Value.tupleShape]

/-- Include the actual numerator-pointer declaration of the original wide
branch; its returned quotient/remainder follow from the real memory path. -/
theorem slow_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (enough : DivMod.wholePrice (digit a) 8+3≤source.clock) :
    ∃ target quotient remainder,Result slowBranch source target base a divisor quotient remainder := by
  let ready:=bind source "u" (Workspace.pointer base .numerator)
  have nextContext : Workspace.Context ready base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  obtain ⟨inner,quotient,remainder,result⟩:=slow_tail_execute ready base divisor a nextContext installed
    ((bind_lookup_other source "u" "a" _ (by decide)).trans aLocal)
    ((bind_lookup_other source "u" "b" _ (by decide)).trans bLocal)
    (bind_lookup_same _ _ _) divisorSmall positive enough
  let target:=restore source "u" inner
  have declared:=ScalarScope.declare_execute source inner "u" (DivMod.workspaceAddress .numerator) (Workspace.pointer base .numerator)
    slowTail _ (DivMod.workspace_read source base context .numerator) result.run
  refine ⟨target,quotient,remainder,⟨declared,?_,result.quotientEq,result.remainderEq,result.small,result.away⟩⟩
  exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals}) result.state

/-- The entire actual wide branch costs at most313source clocks with a
one-digit divisor, independently of every short-clock outcome. -/
theorem slow_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat) :
    source.clock-(evaluateHOLFiniteState source slowBranch).2.clock≤313 := by
  have bound:=DivMod.wholePrice_tight (digit a) 8
  by_cases enough : DivMod.wholePrice (digit a) 8+3≤source.clock
  · obtain ⟨target,quotient,remainder,result⟩:=slow_execute source base divisor a context installed aLocal bLocal divisorSmall positive enough
    rw [result.run]
    have clock:=congrArg PanSemStateFiniteExact.clock result.state
    change target.clock=source.clock-(DivMod.wholePrice (digit a) 8+3) at clock
    change source.clock-target.clock≤313
    omega
  · omega

/-- A real normal return derives this wide branch's funding, exact eight
returned words, natural quotient/remainder and physical write frame. -/
theorem slow_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source slowBranch=(some (.returned returned),post)) :
    ∃ quotient remainder,DivMod.wholePrice (digit a) 8+3≤source.clock ∧
      returned=pairValue quotient remainder ∧ Result slowBranch source post base a divisor quotient remainder := by
  let price:=DivMod.wholePrice (digit a) 8+3
  have nextContext : Workspace.Context {source with clock:=price} base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  obtain ⟨baseTarget,baseQ,baseR,baseResult⟩:=slow_execute {source with clock:=price} base divisor a nextContext installed aLocal bLocal divisorSmall positive (by rfl)
  have zero : baseTarget.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock baseResult.state
    change baseTarget.clock=price-price at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget post slowBranch price _ _ baseResult.run zero
    (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)).1
  obtain ⟨target,quotient,remainder,result⟩:=slow_execute source base divisor a context installed aLocal bLocal divisorSmall positive funded
  have output:=normal.symm.trans result.run
  have same : post=target:=congrArg Prod.snd output
  have value : returned=pairValue quotient remainder:=by
    have values:=congrArg Prod.fst output
    cases values
    rfl
  exact ⟨quotient,remainder,funded,value,same.symm ▸ result⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.literal_slow
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.slow_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.slow_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.slow_normal

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real64-round branch selected after the actual magnitude comparison
has exact funding and a complete read-only numerical result. -/
theorem body_execute_large (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (positive : 0<b.toNat) (small : b.toNat≤2^63) (large : b.toNat≤a.toNat) (enough : 64≤source.clock) :
    ∃ target q r,evaluateHOLFiniteState source body=(some (.returned (pairValue q r)),target) ∧
      target={source with locals:=target.locals,clock:=source.clock-64} ∧
      q.toNat=a.toNat/b.toNat ∧ r.toNat=a.toNat%b.toNat := by
  have nonzero : b≠0#64:=by intro zero;subst b;exact Nat.lt_irrefl 0 positive
  have zeroRead : eval source zeroTest=some (.val (.word 0#64)):=by
    simp [eval,zeroTest,localVar,evalHOLExact,toExact,bLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  have smallRead : eval source smallTest=some (.val (.word 0#64)):=by
    simp [eval,smallTest,localVar,evalHOLExact,toExact,aLocal,bLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,
      show ¬a.toNat<b.toNat by omega]
  simp only [eval] at zeroRead smallRead
  have zeroRun : evaluateHOLFiniteState source zeroGuard=(none,source):=by
    rw [zeroGuard,evaluateHOLFiniteState_ite,zeroRead]
    simp
  have smallRun : evaluateHOLFiniteState source smallGuard=(none,source):=by
    rw [smallGuard,evaluateHOLFiniteState_ite,smallRead]
    simp
  obtain ⟨target,q,r,run,clock,frame,numeric⟩:=setup_execute source a b aLocal bLocal enough
  refine ⟨target,q,r,?_,?_,(numeric small positive).1,(numeric small positive).2⟩
  · rw [body_shape,evaluateHOLFiniteState_seq_line780,zeroRun]
    change evaluateHOLFiniteState source (.seq smallGuard setupProgram)=_
    rw [evaluateHOLFiniteState_seq_line780,smallRun]
    exact run
  · have full:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals,clock:=target.clock}) frame
    change target={source with locals:=target.locals,clock:=target.clock} at full
    rw [clock] at full
    exact full

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.body_execute_large

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def zeroWords : Quad:=fun _=>0#64
def upperZero (a : Quad) : Prop:=a 1=0#64 ∧ a 2=0#64 ∧ a 3=0#64
instance (a : Quad) : Decidable (upperZero a):=inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def fullPrice (a : Quad) (divisor : BitVec 64) : Nat:=
  if quadNumber a<divisor.toNat then 1 else if upperZero a then 66 else DivMod.wholePrice (digit a) 8+4

def zeroTest : ExpHOL 64:=.cmp .equal (.op .or [.rfield 0 (localVar "b"),.rfield 1 (localVar "b"),.rfield 2 (localVar "b"),.rfield 3 (localVar "b")]) (.const 0#64)
def zeroGuard : ProgHOL 64:=.ite zeroTest (.return (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64,.const 0#64,.const 0#64,.const 0#64,.const 0#64])) .skip
def lessTest : ExpHOL 64:=.cmp .equal (localVar "lt") (.const 1#64)
def lessReturn : ProgHOL 64:=.return (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64,
  .rfield 0 (localVar "a"),.rfield 1 (localVar "a"),.rfield 2 (localVar "a"),.rfield 3 (localVar "a")])
def lessGuard : ProgHOL 64:=.ite lessTest lessReturn .skip
def scalarTest : ExpHOL 64:=.cmp .equal (.op .or
  [.rfield 1 (localVar "a"),.rfield 2 (localVar "a"),.rfield 3 (localVar "a"),
   .rfield 1 (localVar "b"),.rfield 2 (localVar "b"),.rfield 3 (localVar "b")]) (.const 0#64)
def scalarFinish : ProgHOL 64:=.return (.rstruct [.rfield 0 (localVar "qr"),.const 0#64,.const 0#64,.const 0#64,
  .rfield 1 (localVar "qr"),.const 0#64,.const 0#64,.const 0#64])
def scalarArguments : List (ExpHOL 64):=[.rfield 0 (localVar "a"),.rfield 0 (localVar "b")]
def scalarBranch : ProgHOL 64:=.decCall (ofString "qr") UDivMod.returnShape (ofString "udivmod") scalarArguments scalarFinish
def scalarGuard : ProgHOL 64:=.ite scalarTest scalarBranch .skip
def afterComparison : ProgHOL 64:=.seq lessGuard (.seq scalarGuard slowBranch)
def comparisonArguments : List (ExpHOL 64):=[localVar "a",localVar "b"]
def afterZero : ProgHOL 64:=.decCall (ofString "lt") .one (ofString "u256_lt") comparisonArguments afterComparison

theorem body_shape : body=.seq zeroGuard afterZero := by
  simp [body,Guest.Software.guestFn_u256_divmod,progToHOL,expToHOL,shapeToHOL,zeroGuard,zeroTest,afterZero,
    comparisonArguments,afterComparison,lessGuard,lessTest,lessReturn,scalarGuard,scalarTest,scalarBranch,scalarArguments,
    scalarFinish,slowBranch,slowTail,numeratorArguments,divisionArguments,afterDivision,quotientArguments,finish,
    DivMod.workspaceAddress,Workspace.offset,localVar,RlpWrite.U256Value.tupleShape,UDivMod.returnShape]

theorem fullPrice_upper (a : Quad) (divisor : BitVec 64) : fullPrice a divisor≤314 := by
  have wide:=DivMod.wholePrice_tight (digit a) 8
  unfold fullPrice
  split_ifs <;> omega

theorem upperZero_number (a : Quad) (zero : upperZero a) : quadNumber a=(a 0).toNat := by
  simp [quadNumber,zero.1,zero.2.1,zero.2.2]

theorem less_return_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a : Quad)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a)) :
    evaluateHOLFiniteState source lessReturn=(some (.returned (pairValue zeroWords a)),emptyLocalsHOLFinite source) := by
  simp [lessReturn,pairValue,zeroWords,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,aLocal,
    RlpWrite.U256Value.tuple,shapeOfHOLExact,sizeOfShapeWithContextHOL]

theorem scalar_finish_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r : BitVec 64)
    (qr : source.locals.lookup (ofString "qr")=some (UDivMod.pairValue q r)) :
    evaluateHOLFiniteState source scalarFinish=(some (.returned (pairValue (Single.remainderWords q) (Single.remainderWords r))),emptyLocalsHOLFinite source) := by
  simp [scalarFinish,pairValue,Single.remainderWords,UDivMod.pairValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,qr,
    shapeOfHOLExact,sizeOfShapeWithContextHOL]

private theorem zero_guard_none (source : PanSemStateFiniteExact 64 Guest.HostMemory) (divisor : BitVec 64)
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (positive : 0<divisor.toNat) : evaluateHOLFiniteState source zeroGuard=(none,source) := by
  have nonzero : divisor≠0#64:=by intro zero;subst divisor;exact Nat.lt_irrefl 0 positive
  have folded : OrOp.or divisor (OrOp.or (0#64) (OrOp.or (0#64) (OrOp.or 0#64 0#64)))=divisor:=by
    change divisor ||| (0#64 ||| (0#64 ||| (0#64 ||| 0#64)))=divisor
    simp
  have test : eval source zeroTest=some (.val (.word 0#64)):=by
    simp [folded,eval,zeroTest,localVar,evalHOLExact,evalListHOLExact,toExact,bLocal,RlpWrite.U256Value.tuple,Single.remainderWords,
      valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  simp only [eval] at test
  rw [zeroGuard,evaluateHOLFiniteState_ite,test]
  simp

private theorem scalar_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a : Quad) (divisor : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor))) :
    eval source scalarTest=some (.val (.word (if upperZero a then 1#64 else 0#64))) := by
  have condition : OrOp.or (a 1) (OrOp.or (a 2) (OrOp.or (a 3) (OrOp.or (0#64) (OrOp.or (0#64) (OrOp.or 0#64 0#64)))))=0#64 ↔ upperZero a:=by
    change a 1 ||| (a 2 ||| (a 3 ||| (0#64 ||| (0#64 ||| (0#64 ||| 0#64)))))=0#64 ↔ a 1=0#64 ∧ a 2=0#64 ∧ a 3=0#64
    simp [BitVec.or_eq_zero_iff]
  by_cases upper : upperZero a
  · have zero:=condition.mpr upper
    simp [eval,scalarTest,localVar,evalHOLExact,evalListHOLExact,toExact,aLocal,bLocal,RlpWrite.U256Value.tuple,Single.remainderWords,
      valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero,upper]
  · have nonzero : ¬OrOp.or (a 1) (OrOp.or (a 2) (OrOp.or (a 3) (OrOp.or (0#64) (OrOp.or (0#64) (OrOp.or 0#64 0#64)))))=0#64:=
      fun zero=>upper (condition.mp zero)
    simp [eval,scalarTest,localVar,evalHOLExact,evalListHOLExact,toExact,aLocal,bLocal,RlpWrite.U256Value.tuple,Single.remainderWords,
      valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero,upper]

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.body_shape
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.fullPrice_upper
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.upperZero_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.less_return_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.scalar_finish_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem scalar_execute_small63 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat≤2^63) (positive : 0<divisor.toNat) (upper : upperZero a)
    (large : divisor.toNat≤quadNumber a) (enough : 65≤source.clock) :
    ∃ target quotient remainder,Result scalarBranch source target base a divisor quotient remainder 65 := by
  have valueA:=upperZero_number a upper
  obtain ⟨callee,called,aCell,bCell⟩:=UDivMod.environment source.code.lookup (a 0) divisor (UDivMod.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) scalarArguments=
      some (UDivMod.values (a 0) divisor):=by
    simp [scalarArguments,UDivMod.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,aLocal,bLocal,
      RlpWrite.U256Value.tuple,Single.remainderWords]
  obtain ⟨child,q,r,childRun,childFrame,qEq,rEq⟩:=UDivMod.body_execute_large (callEntryStateHOLFinite source callee) (a 0) divisor
    aCell bCell positive (by omega) (by omega) (by change 64≤source.clock-1;omega)
  let ready:=setVarHOLFinite (ofString "qr") (UDivMod.pairValue q r) {source with clock:=source.clock-65}
  have qrCell : ready.locals.lookup (ofString "qr")=some (UDivMod.pairValue q r):=by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have finishRun:=scalar_finish_execute ready q r qrCell
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) childFrame
  change {child with locals:=source.locals}={source with clock:=source.clock-1-64} at callerFrame
  have sub : source.clock-1-64=source.clock-65:=by omega
  rw [sub] at callerFrame
  have actual:=CallNormal.return_execute source child "qr" UDivMod.returnShape (ofString "udivmod") scalarArguments _
    UDivMod.body scalarFinish callee UDivMod.returnShape (UDivMod.pairValue q r) args called (by omega) childRun
    (by simp [UDivMod.pairValue,UDivMod.returnShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  rw [CallNormal.continuationEntry,callerFrame] at actual
  change evaluateHOLFiniteState source scalarBranch=(let output:=evaluateHOLFiniteState ready scalarFinish;(output.1,restore source "qr" output.2)) at actual
  rw [finishRun] at actual
  let target:=restore source "qr" (emptyLocalsHOLFinite ready)
  refine ⟨target,Single.remainderWords q,Single.remainderWords r,⟨actual,rfl,?_,?_,?_,?_⟩⟩
  · rw [Single.remainder_number,valueA]
    exact qEq
  · rw [Single.remainder_number,valueA]
    exact rEq
  · rw [Single.remainder_number,rEq]
    exact Nat.mod_lt _ positive
  · intro query outsideQ outsideR outsideV outsideU
    rfl


theorem scalar_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat) (upper : upperZero a)
    (large : divisor.toNat≤quadNumber a) (enough : 65≤source.clock) :
    ∃ target quotient remainder,Result scalarBranch source target base a divisor quotient remainder 65 := by
  exact scalar_execute_small63 source base divisor a installed aLocal bLocal (by omega) positive upper large enough

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.scalar_execute_small63
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.scalar_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem fullPrice_positive (a : Quad) (divisor : BitVec 64) : 1≤fullPrice a divisor := by
  unfold fullPrice
  split_ifs <;> omega

private theorem comparison_value (a : Quad) (divisor : BitVec 64) :
    GasBudget.U256LessThan.resultWord a (Single.remainderWords divisor)=if quadNumber a<divisor.toNat then 1#64 else 0#64 := by
  by_cases lower : quadNumber a<divisor.toNat
  · rw [if_pos lower]
    apply (GasBudget.U256LessThan.resultWord_one_iff_number_lt a (Single.remainderWords divisor)).mpr
    change quadNumber a<quadNumber (Single.remainderWords divisor)
    rwa [Single.remainder_number]
  · rw [if_neg lower]
    apply (GasBudget.U256LessThan.resultWord_zero_iff_number_le a (Single.remainderWords divisor)).mpr
    change quadNumber (Single.remainderWords divisor)≤quadNumber a
    rw [Single.remainder_number]
    omega

/-- After the real comparison, the unchanged guards select the early return,
scalar division or the already checked wide branch. -/
theorem after_comparison_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (ltLocal : source.locals.lookup (ofString "lt")=some (.val (.word (GasBudget.U256LessThan.resultWord a (Single.remainderWords divisor)))))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (enough : fullPrice a divisor-1≤source.clock) :
    ∃ target quotient remainder,Result afterComparison source target base a divisor quotient remainder (fullPrice a divisor-1) := by
  have tested : eval source lessTest=some (.val (.word (if quadNumber a<divisor.toNat then 1#64 else 0#64))):=by
    have read:=ltLocal
    rw [comparison_value] at read
    by_cases lower : quadNumber a<divisor.toNat <;>
      simp [eval,lessTest,localVar,evalHOLExact,toExact,read,lower,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at tested
  by_cases lower : quadNumber a<divisor.toNat
  · have price : fullPrice a divisor-1=0:=by simp [fullPrice,lower]
    have returned:=less_return_execute source a aLocal
    have guardRun : evaluateHOLFiniteState source lessGuard=(some (.returned (pairValue zeroWords a)),emptyLocalsHOLFinite source):=by
      rw [lessGuard,evaluateHOLFiniteState_ite,tested,if_pos lower]
      simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)]
      exact returned
    refine ⟨emptyLocalsHOLFinite source,zeroWords,a,⟨?_,?_,?_,?_,lower,?_⟩⟩
    · rw [afterComparison,evaluateHOLFiniteState_seq_line780,guardRun]
    · simp only [price,Nat.sub_zero]
      rfl
    · rw [Nat.div_eq_of_lt lower]
      simp [quadNumber,zeroWords]
    · exact (Nat.mod_eq_of_lt lower).symm
    · intro query outsideQ outsideR outsideV outsideU
      rfl
  · have guardRun : evaluateHOLFiniteState source lessGuard=(none,source):=by
      rw [lessGuard,evaluateHOLFiniteState_ite,tested,if_neg lower]
      simp
    have scalarRead:=scalar_test_read source a divisor aLocal bLocal
    simp only [eval] at scalarRead
    by_cases upper : upperZero a
    · have price : fullPrice a divisor-1=65:=by simp [fullPrice,lower,upper]
      obtain ⟨target,quotient,remainder,result⟩:=scalar_execute source base divisor a installed aLocal bLocal divisorSmall positive upper (by omega)
        (by rwa [price] at enough)
      have scalarRun : evaluateHOLFiniteState source scalarGuard=(some (.returned (pairValue quotient remainder)),target):=by
        rw [scalarGuard,evaluateHOLFiniteState_ite,scalarRead,if_pos upper]
        simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)]
        exact result.run
      refine ⟨target,quotient,remainder,⟨?_,?_,result.quotientEq,result.remainderEq,result.small,result.away⟩⟩
      · rw [afterComparison,evaluateHOLFiniteState_seq_line780,guardRun]
        change evaluateHOLFiniteState source (.seq scalarGuard slowBranch)=_
        rw [evaluateHOLFiniteState_seq_line780,scalarRun]
      · simpa only [price] using result.state
    · have price : fullPrice a divisor-1=DivMod.wholePrice (digit a) 8+3:=by simp [fullPrice,lower,upper]
      obtain ⟨target,quotient,remainder,result⟩:=slow_execute source base divisor a context installed aLocal bLocal divisorSmall positive
        (by rwa [price] at enough)
      have scalarRun : evaluateHOLFiniteState source scalarGuard=(none,source):=by
        rw [scalarGuard,evaluateHOLFiniteState_ite,scalarRead,if_neg upper]
        simp
      refine ⟨target,quotient,remainder,⟨?_,?_,result.quotientEq,result.remainderEq,result.small,result.away⟩⟩
      · rw [afterComparison,evaluateHOLFiniteState_seq_line780,guardRun]
        change evaluateHOLFiniteState source (.seq scalarGuard slowBranch)=_
        rw [evaluateHOLFiniteState_seq_line780,scalarRun]
        exact result.run
      · simpa only [price] using result.state

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.fullPrice_positive
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.after_comparison_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The complete unchanged u256_divmod function for an actual positive
one-digit divisor: zero guard, real comparison and both division routes. -/
theorem full_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (enough : fullPrice a divisor≤source.clock) :
    ∃ target quotient remainder,Result body source target base a divisor quotient remainder (fullPrice a divisor) := by
  have pricePositive:=fullPrice_positive a divisor
  let compared:=bind {source with clock:=source.clock-1} "lt" (GasBudget.U256LessThan.resultWord a (Single.remainderWords divisor))
  have nextContext : Workspace.Context compared base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  obtain ⟨inner,quotient,remainder,result⟩:=after_comparison_execute compared base divisor a nextContext installed
    ((bind_lookup_other _ "lt" "a" _ (by decide)).trans aLocal)
    ((bind_lookup_other _ "lt" "b" _ (by decide)).trans bLocal)
    (bind_lookup_same _ _ _) divisorSmall positive (by change fullPrice a divisor-1≤source.clock-1;omega)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) comparisonArguments=
      some [RlpWrite.U256Value.tuple a,RlpWrite.U256Value.tuple (Single.remainderWords divisor)]:=by
    simp [comparisonArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,aLocal,bLocal]
  obtain ⟨callee,called,aCell,bCell⟩:=GasBudget.U256LessThan.environment source.code.lookup a (Single.remainderWords divisor)
    (GasBudget.U256LessThan.original_code source.code installed)
  let childEntry:=callEntryStateHOLFinite source callee
  have childRun:=GasBudget.U256LessThan.execute childEntry a (Single.remainderWords divisor) aCell bCell
  have actual:=CallNormal.pure_return_execute source (emptyLocalsHOLFinite childEntry) "lt" (ofString "u256_lt") comparisonArguments _
    GasBudget.U256LessThan.body afterComparison callee (GasBudget.U256LessThan.resultWord a (Single.remainderWords divisor)) 0
    args called (by omega) childRun rfl
  simp only [Nat.sub_zero] at actual
  change evaluateHOLFiniteState source afterZero=(let output:=evaluateHOLFiniteState compared afterComparison;(output.1,restore source "lt" output.2)) at actual
  rw [result.run] at actual
  let target:=restore source "lt" inner
  refine ⟨target,quotient,remainder,⟨?_,?_,result.quotientEq,result.remainderEq,result.small,result.away⟩⟩
  · rw [body_shape,evaluateHOLFiniteState_seq_line780,zero_guard_none source divisor bLocal positive]
    exact actual
  · have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals}) result.state
    change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-1-(fullPrice a divisor-1)} at frame
    have subtract : source.clock-1-(fullPrice a divisor-1)=source.clock-fullPrice a divisor:=by omega
    simpa only [subtract] using frame

/-- All outcomes of the complete original one-digit-divisor function path,
including every insufficient clock, cost at most314source ticks. -/
theorem full_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤314 := by
  have bound:=fullPrice_upper a divisor
  by_cases enough : fullPrice a divisor≤source.clock
  · obtain ⟨target,quotient,remainder,result⟩:=full_execute source base divisor a context installed aLocal bLocal divisorSmall positive enough
    rw [result.run]
    have clock:=congrArg PanSemStateFiniteExact.clock result.state
    change target.clock=source.clock-fullPrice a divisor at clock
    change source.clock-target.clock≤314
    omega
  · omega

/-- An actual normal full-function return supplies funding, exact natural
quotient/remainder and the same concrete eight-word output and write frame. -/
theorem full_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ quotient remainder,fullPrice a divisor≤source.clock ∧ returned=pairValue quotient remainder ∧
      Result body source post base a divisor quotient remainder (fullPrice a divisor) := by
  have nextContext : Workspace.Context {source with clock:=fullPrice a divisor} base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  obtain ⟨baseTarget,baseQ,baseR,baseResult⟩:=full_execute {source with clock:=fullPrice a divisor} base divisor a nextContext installed aLocal bLocal divisorSmall positive (by rfl)
  have zero : baseTarget.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock baseResult.state
    change baseTarget.clock=fullPrice a divisor-fullPrice a divisor at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget post body (fullPrice a divisor) _ _ baseResult.run zero
    (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)).1
  obtain ⟨target,quotient,remainder,result⟩:=full_execute source base divisor a context installed aLocal bLocal divisorSmall positive funded
  have output:=normal.symm.trans result.run
  have same : post=target:=congrArg Prod.snd output
  have value : returned=pairValue quotient remainder:=by
    have values:=congrArg Prod.fst output
    cases values
    rfl
  exact ⟨quotient,remainder,funded,value,same.symm ▸ result⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.full_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.full_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.full_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure QuotientResult (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (a : Quad) (divisor : BitVec 64) (quotient : Quad) : Prop where
  run : evaluateHOLFiniteState source GasBudget.U256Division.divBody=(some (.returned (RlpWrite.U256Value.tuple quotient)),target)
  state : target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-(fullPrice a divisor+1)}
  quotientEq : quadNumber quotient=quadNumber a/divisor.toNat
  away : ∀ query,(∀ index,index<16→ query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .remainder) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .divisor) index)→
    (∀ index,index<8→ query≠slot (Workspace.pointer base .numerator) index)→ target.memory query=source.memory query

/-- The original u256_div wrapper calls the real complete u256_divmod and
extracts its actual quotient; no mathematical-division return is assumed. -/
theorem divide_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (enough : fullPrice a divisor+1≤source.clock) :
    ∃ target quotient,QuotientResult source target base a divisor quotient := by
  obtain ⟨callee,called,aCell,bCell⟩:=RlpWrite.U256Value.pair_environment source.code.lookup (ofString "u256_divmod") body
    GasBudget.U256Division.shapeEight a (Single.remainderWords divisor) (GasBudget.U256Division.divmod_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have entryContext : Workspace.Context entry base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  obtain ⟨child,quotient,remainder,result⟩:=full_execute entry base divisor a entryContext installed aCell bCell divisorSmall positive
    (by change fullPrice a divisor≤source.clock-1;omega)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) GasBudget.U256Division.divArguments=
      some [RlpWrite.U256Value.tuple a,RlpWrite.U256Value.tuple (Single.remainderWords divisor)]:=by
    simp [GasBudget.U256Division.divArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,aLocal,bLocal]
  let ready:=CallNormal.continuationEntry source child "qr" (pairValue quotient remainder)
  have qrCell : ready.locals.lookup (ofString "qr")=some (pairValue quotient remainder):=by
    simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have returned : evaluateHOLFiniteState ready GasBudget.U256Division.divReturn=
      (some (.returned (RlpWrite.U256Value.tuple quotient)),emptyLocalsHOLFinite ready):=by
    simp [GasBudget.U256Division.divReturn,GasBudget.U256Division.quotientExpression,pairValue,evaluateHOLFiniteState_return,
      evalHOLExact,evalListHOLExact,toExact,localVar,qrCell,RlpWrite.U256Value.tuple,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have actual:=CallNormal.return_execute source child "qr" GasBudget.U256Division.shapeEight (ofString "u256_divmod") GasBudget.U256Division.divArguments _
    body GasBudget.U256Division.divReturn callee GasBudget.U256Division.shapeEight (pairValue quotient remainder) args called (by omega) result.run
    (by simp [pairValue,GasBudget.U256Division.shapeEight,shapeOfHOLExact,shapeEqHOL_eq_true])
  change evaluateHOLFiniteState source (.decCall (ofString "qr") GasBudget.U256Division.shapeEight (ofString "u256_divmod") GasBudget.U256Division.divArguments GasBudget.U256Division.divReturn)=
    (let output:=evaluateHOLFiniteState ready GasBudget.U256Division.divReturn;(output.1,restore source "qr" output.2)) at actual
  rw [returned,←GasBudget.U256Division.div_shape] at actual
  let target:=restore source "qr" (emptyLocalsHOLFinite ready)
  refine ⟨target,quotient,⟨actual,?_,result.quotientEq,result.away⟩⟩
  have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals}) result.state
  change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-1-fullPrice a divisor} at frame
  have sub : source.clock-1-fullPrice a divisor=source.clock-(fullPrice a divisor+1):=by omega
  simpa only [sub] using frame

theorem divide_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat) :
    source.clock-(evaluateHOLFiniteState source GasBudget.U256Division.divBody).2.clock≤315 := by
  have bound:=fullPrice_upper a divisor
  by_cases enough : fullPrice a divisor+1≤source.clock
  · obtain ⟨target,quotient,result⟩:=divide_execute source base divisor a context installed aLocal bLocal divisorSmall positive enough
    rw [result.run]
    have clock:=congrArg PanSemStateFiniteExact.clock result.state
    change target.clock=source.clock-(fullPrice a divisor+1) at clock
    change source.clock-target.clock≤315
    omega
  · omega

theorem divide_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source GasBudget.U256Division.divBody=(some (.returned returned),post)) :
    ∃ quotient,fullPrice a divisor+1≤source.clock ∧ returned=RlpWrite.U256Value.tuple quotient ∧
      QuotientResult source post base a divisor quotient := by
  have nextContext : Workspace.Context {source with clock:=fullPrice a divisor+1} base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  obtain ⟨baseTarget,baseQ,baseResult⟩:=divide_execute {source with clock:=fullPrice a divisor+1} base divisor a nextContext installed aLocal bLocal divisorSmall positive (by rfl)
  have zero : baseTarget.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock baseResult.state
    change baseTarget.clock=(fullPrice a divisor+1)-(fullPrice a divisor+1) at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget post GasBudget.U256Division.divBody (fullPrice a divisor+1) _ _ baseResult.run zero
    (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)).1
  obtain ⟨target,quotient,result⟩:=divide_execute source base divisor a context installed aLocal bLocal divisorSmall positive funded
  have output:=normal.symm.trans result.run
  have same : post=target:=congrArg Prod.snd output
  have value : returned=RlpWrite.U256Value.tuple quotient:=by
    have values:=congrArg Prod.fst output
    cases values
    rfl
  exact ⟨quotient,funded,value,same.symm ▸ result⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.divide_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.divide_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.divide_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual two-quad arguments price all original u256_div call forms. -/
theorem divide_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [RlpWrite.U256Value.tuple a,RlpWrite.U256Value.tuple (Single.remainderWords divisor)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "u256_div") arguments)).2.clock≤316 := by
  obtain ⟨callee,called,aCell,bCell⟩:=RlpWrite.U256Value.pair_environment source.code.lookup (ofString "u256_div") GasBudget.U256Division.divBody
    RlpWrite.U256Value.tupleShape a (Single.remainderWords divisor) (GasBudget.U256Division.div_code source.code installed)
  have entryContext : Workspace.Context (callEntryStateHOLFinite source callee) base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  exact ClockCost.call_current source destination (ofString "u256_div") arguments _ GasBudget.U256Division.divBody callee RlpWrite.U256Value.tupleShape 315
    args called (divide_cost (callEntryStateHOLFinite source callee) base divisor a entryContext installed aCell bCell divisorSmall positive)

/-- The actual assigned call used by Taylor derives its own funding,
canonical next accumulator, natural division and complete physical frame. -/
theorem divide_assigned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat)
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [RlpWrite.U256Value.tuple a,RlpWrite.U256Value.tuple (Single.remainderWords divisor)])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "u256_div") arguments)=(none,post)) :
    ∃ quotient,fullPrice a divisor+2≤source.clock ∧
      post=setVarHOLFinite name (RlpWrite.U256Value.tuple quotient)
        {source with memory:=post.memory,clock:=source.clock-(fullPrice a divisor+2)} ∧
      quadNumber quotient=quadNumber a/divisor.toNat ∧
      (∀ query,(∀ index,index<16→ query≠slot (Workspace.pointer base .quotient) index)→
        (∀ index,index<8→ query≠slot (Workspace.pointer base .remainder) index)→
        (∀ index,index<8→ query≠slot (Workspace.pointer base .divisor) index)→
        (∀ index,index<8→ query≠slot (Workspace.pointer base .numerator) index)→ post.memory query=source.memory query) := by
  obtain ⟨callFunded,values,actual,callee,shape,target,returned,actualArgs,called,childRun,typed,postEq⟩:=
    CallNormal.local_data source post name (ofString "u256_div") arguments normal
  have valuesEq : values=[RlpWrite.U256Value.tuple a,RlpWrite.U256Value.tuple (Single.remainderWords divisor)]:=
    Option.some.inj (actualArgs.symm.trans args)
  subst values
  obtain ⟨expected,lookup,aCell,bCell⟩:=RlpWrite.U256Value.pair_environment source.code.lookup (ofString "u256_div") GasBudget.U256Division.divBody
    RlpWrite.U256Value.tupleShape a (Single.remainderWords divisor) (GasBudget.U256Division.div_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=GasBudget.U256Division.divBody:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at aCell bCell
  rw [bodyEq] at childRun
  have entryContext : Workspace.Context (callEntryStateHOLFinite source callee) base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  obtain ⟨quotient,childFunded,returnedEq,result⟩:=divide_normal (callEntryStateHOLFinite source callee) target base divisor a
    entryContext installed aCell bCell divisorSmall positive returned childRun
  have funded : fullPrice a divisor+2≤source.clock:=by
    change fullPrice a divisor+1≤source.clock-1 at childFunded
    omega
  have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) result.state
  change {target with locals:=source.locals}={source with memory:=target.memory,clock:=source.clock-1-(fullPrice a divisor+1)} at frame
  have subtract : source.clock-1-(fullPrice a divisor+1)=source.clock-(fullPrice a divisor+2):=by omega
  rw [subtract] at frame
  have memory : post.memory=target.memory:=by rw [postEq];rfl
  refine ⟨quotient,funded,?_,result.quotientEq,?_⟩
  · have canonical : post=setVarHOLFinite name (RlpWrite.U256Value.tuple quotient)
        {source with memory:=target.memory,clock:=source.clock-(fullPrice a divisor+2)}:=by
      rw [postEq,returnedEq,frame]
    rw [←memory] at canonical
    exact canonical
  · intro query outsideQ outsideR outsideV outsideU
    rw [memory]
    exact result.away query outsideQ outsideR outsideV outsideU

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.divide_call_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256.divide_assigned_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def address (name : String) (index : ExpHOL 64) : ExpHOL 64:=.op .add [localVar name,.panop .mul [index,.const 8#64]]
def inputAddress : ExpHOL 64:=address "un" (.op .add [localVar "i",localVar "j"])
def divisorAddress : ExpHOL 64:=address "vn" (localVar "i")
def productExpression : ExpHOL 64:=.panop .mul [localVar "qhat",.load .one divisorAddress]
def residualExpression : ExpHOL 64:=.op .sub [.op .sub [.load .one inputAddress,localVar "k"],.op .and [localVar "p",.const 4294967295#64]]
def lowExpression : ExpHOL 64:=.op .and [localVar "t",.const 4294967295#64]
def carryExpression : ExpHOL 64:=.op .sub [.shift .lsr (localVar "p") (.const 32#64),.shift .asr (localVar "t") (.const 32#64)]
def increment : ExpHOL 64:=.op .add [localVar "i",.const 1#64]
def updates : ProgHOL 64:=.seq (.store inputAddress lowExpression)
  (.seq (.assign .local (ofString "k") carryExpression) (.assign .local (ofString "i") increment))
def step : ProgHOL 64:=.dec (ofString "p") .one productExpression (.dec (ofString "t") .one residualExpression updates)
def test : ExpHOL 64:=.cmp .lower (localVar "i") (localVar "n")
def loop : ProgHOL 64:=.while test step

private def findStep : ProgHOL 64→ Option (ProgHOL 64)
  | .while condition contents=>
    match condition with
    | .cmp .lower (.var .local index) (.var .local bound)=>
      if index=ofString "i" ∧ bound=ofString "n" then some contents else findStep contents
    | _=>findStep contents
  | .dec _ _ _ rest=>findStep rest
  | .decCall _ _ _ _ rest=>findStep rest
  | .seq first rest=>(findStep first).orElse (fun _=>findStep rest)
  | .ite _ yes no=>(findStep yes).orElse (fun _=>findStep no)
  | _=>none

theorem literal_step : findStep Single.body=some step := by
  simp [findStep,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    step,updates,productExpression,residualExpression,lowExpression,carryExpression,increment,inputAddress,divisorAddress,address,localVar]

private theorem divisor_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat)
    (v : source.locals.lookup (ofString "vn")=some (.val (.word pointer)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source divisorAddress=some (.val (.word (slot pointer index))) := by
  simp [eval,divisorAddress,address,localVar,evalHOLExact,evalListHOLExact,toExact,v,i,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,Nat.mul_comm]

private theorem input_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index position : Nat)
    (u : source.locals.lookup (ofString "un")=some (.val (.word pointer)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position)))) :
    eval source inputAddress=some (.val (.word (slot pointer (index+position)))) := by
  simp [eval,inputAddress,address,localVar,evalHOLExact,evalListHOLExact,toExact,u,i,j,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,BitVec.ofNat_add,Nat.mul_comm]

private theorem binary_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (operator : BinOp) (left right : ExpHOL 64) (a b result : BitVec 64)
    (leftRead : eval source left=some (.val (.word a))) (rightRead : eval source right=some (.val (.word b)))
    (computed : wordOpHOL operator [a,b]=some result) :
    eval source (.op operator [left,right])=some (.val (.word result)) := by
  simp only [eval] at leftRead rightRead ⊢
  rw [evalHOLExact]
  simp [evalListHOLExact,leftRead,rightRead,valueIsWord,valueWord,computed]

private theorem multiply_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (left right : ExpHOL 64) (a b : BitVec 64)
    (leftRead : eval source left=some (.val (.word a))) (rightRead : eval source right=some (.val (.word b))) :
    eval source (.panop .mul [left,right])=some (.val (.word (a*b))) := by
  simp only [eval] at leftRead rightRead ⊢
  rw [evalHOLExact]
  simp [evalListHOLExact,leftRead,rightRead,valueIsWord,valueWord,panOpHOL]

private theorem shifted_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (operator : Shift) (expression : ExpHOL 64) (word result : BitVec 64)
    (read : eval source expression=some (.val (.word word))) (computed : wordShiftHOL operator word 32=some result) :
    eval source (.shift operator expression (.const 32#64))=some (.val (.word result)) := by
  simp only [eval] at read ⊢
  rw [evalHOLExact]
  simp [read,evalHOLExact,computed]

/-- The real inner body has no calls or loops; source clocks are unchanged. -/
theorem step_cost (code) : ClockCost.Bound code step 0 := by
  unfold step updates
  exact ClockCost.declared code _ _ _ _ 0 (ClockCost.declared code _ _ _ _ 0
    (ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _)
      (ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _) (ClockCost.assign code _ _))))

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.literal_step
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.step_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) : Prop where
  context : Workspace.Context source base
  indexSmall : index<2
  inside : index+position<17
  u : source.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator)))
  v : source.locals.lookup (ofString "vn")=some (.val (.word (Workspace.pointer base .normalizedDivisor)))
  i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position)))
  q : source.locals.lookup (ofString "qhat")=some (.val (.word quotient))
  k : source.locals.lookup (ofString "k")=some (.val (.word carry))
  input : source.memory (slot (Workspace.pointer base .normalizedNumerator) (index+position))=.word cell
  divisorCell : source.memory (slot (Workspace.pointer base .normalizedDivisor) index)=.word divisor
  cellSmall : cell.toNat<4294967296
  carrySmall : carry.toNat<4294967296
  quotientSmall : quotient.toNat<4294967296
  divisorSmall : divisor.toNat<4294967296

theorem Entry.bindTemporary {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {index position : Nat}
    {quotient carry cell divisor : BitVec 64} (checked : Entry source base index position quotient carry cell divisor)
    (name : String) (word : BitVec 64) (allowed : name="p" ∨ name="t") :
    Entry (bind source name word) base index position quotient carry cell divisor := by
  rcases allowed with rfl|rfl <;>
    refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.indexSmall,checked.inside,
      ?_,?_,?_,?_,?_,?_,checked.input,checked.divisorCell,checked.cellSmall,checked.carrySmall,checked.quotientSmall,checked.divisorSmall⟩ <;>
    first
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.u
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.v
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.i
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.j
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.q
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.k

private theorem local_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64)
    (cell : source.locals.lookup (ofString name)=some (.val (.word word))) : eval source (localVar name)=some (.val (.word word)) := by
  simp [eval,localVar,evalHOLExact,toExact,cell]

private theorem product_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) (checked : Entry source base index position quotient carry cell divisor) :
    eval source productExpression=some (.val (.word (quotient*divisor))) := by
  have mapped:=Workspace.slot_mapped source base checked.context .normalizedDivisor index (by change index<8;have h:=checked.indexSmall;omega)
  have loaded:=Witness.load_word_read source divisorAddress _ divisor (divisor_address_read source _ index checked.v checked.i) mapped checked.divisorCell
  exact multiply_read source (localVar "qhat") (.load .one divisorAddress) quotient divisor (local_read source "qhat" quotient checked.q) loaded

private theorem residual_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) (checked : Entry source base index position quotient carry cell divisor)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (quotient*divisor)))) :
    eval source residualExpression=some (.val (.word (TwoDigitSubtract.residual cell carry (quotient*divisor)))) := by
  have mapped:=Workspace.slot_mapped source base checked.context .normalizedNumerator (index+position) checked.inside
  have loaded:=Witness.load_word_read source inputAddress _ cell (input_address_read source _ index position checked.u checked.i checked.j) mapped checked.input
  have first:=binary_read source .sub (.load .one inputAddress) (localVar "k") cell carry (cell-carry)
    loaded (local_read source "k" carry checked.k) rfl
  have masked:=binary_read source .and (localVar "p") (.const 4294967295#64) (quotient*divisor) 4294967295#64 ((quotient*divisor) &&& 4294967295#64)
    (local_read source "p" _ p) rfl rfl
  exact binary_read source .sub _ _ _ _ _ first masked rfl

def updatePost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) :=
  bind (bind {source with
    memory:=StoreWord.put source.memory (slot (Workspace.pointer base .normalizedNumerator) (index+position))
      (TwoDigitSubtract.low cell carry (quotient*divisor))} "k" (TwoDigitSubtract.nextCarry cell carry (quotient*divisor))) "i" (BitVec.ofNat 64 (index+1))

def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) :=
  let pEntry:=bind source "p" (quotient*divisor)
  let tEntry:=bind pEntry "t" (TwoDigitSubtract.residual cell carry (quotient*divisor))
  restore source "p" (restore pEntry "t" (updatePost tEntry base index position quotient carry cell divisor))

private theorem updates_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) (checked : Entry source base index position quotient carry cell divisor)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (quotient*divisor))))
    (t : source.locals.lookup (ofString "t")=some (.val (.word (TwoDigitSubtract.residual cell carry (quotient*divisor))))) :
    evaluateHOLFiniteState source updates=(none,updatePost source base index position quotient carry cell divisor) := by
  let product:=quotient*divisor
  let rest:=TwoDigitSubtract.residual cell carry product
  let stored:={source with memory:=StoreWord.put source.memory (slot (Workspace.pointer base .normalizedNumerator) (index+position)) (TwoDigitSubtract.low cell carry product)}
  have lowRead : eval source lowExpression=some (.val (.word (TwoDigitSubtract.low cell carry product))):=
    binary_read source .and (localVar "t") (.const 4294967295#64) rest 4294967295#64 _ (local_read source "t" _ t) rfl rfl
  have storedRun:=StoreWord.execute source inputAddress lowExpression _ _ (input_address_read source _ index position checked.u checked.i checked.j) lowRead
    (Workspace.slot_mapped source base checked.context .normalizedNumerator (index+position) checked.inside)
  have left:=shifted_read stored .lsr (localVar "p") product (product>>>(32:Nat)) (local_read stored "p" _ p) rfl
  have right:=shifted_read stored .asr (localVar "t") rest (rest.sshiftRight 32) (local_read stored "t" _ t) rfl
  have carryRead : eval stored carryExpression=some (.val (.word (TwoDigitSubtract.nextCarry cell carry product))):=
    binary_read stored .sub _ _ _ _ _ left right rfl
  let carried:=bind stored "k" (TwoDigitSubtract.nextCarry cell carry product)
  have iCell : carried.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=
    (bind_lookup_other stored "k" "i" _ (by decide)).trans checked.i
  have nextRead : eval carried increment=some (.val (.word (BitVec.ofNat 64 (index+1)))):=by
    simp [eval,increment,localVar,evalHOLExact,evalListHOLExact,toExact,iCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  rw [updates,evaluateHOLFiniteState_seq_line780,storedRun]
  change evaluateHOLFiniteState stored (.seq (.assign .local (ofString "k") carryExpression) (.assign .local (ofString "i") increment))=_
  rw [evaluateHOLFiniteState_seq_line780,StateSteps.assign_execute stored "k" carryExpression carry _ checked.k carryRead]
  exact StateSteps.assign_execute carried "i" increment _ _ iCell nextRead

/-- Execute the original p/t declarations, real mapped load/store, signed
carry update and index increment, including their actual lexical restores. -/
theorem step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) (checked : Entry source base index position quotient carry cell divisor) :
    evaluateHOLFiniteState source step=(none,post source base index position quotient carry cell divisor) := by
  let pEntry:=bind source "p" (quotient*divisor)
  have pModel : Entry pEntry base index position quotient carry cell divisor:=checked.bindTemporary "p" _ (Or.inl rfl)
  let tEntry:=bind pEntry "t" (TwoDigitSubtract.residual cell carry (quotient*divisor))
  have tModel : Entry tEntry base index position quotient carry cell divisor:=pModel.bindTemporary "t" _ (Or.inr rfl)
  have pCell : tEntry.locals.lookup (ofString "p")=some (.val (.word (quotient*divisor))):=
    (bind_lookup_other pEntry "t" "p" _ (by decide)).trans (bind_lookup_same _ _ _)
  have run:=updates_execute tEntry base index position quotient carry cell divisor tModel pCell (bind_lookup_same _ _ _)
  have tRun:=ScalarScope.declare_execute pEntry (updatePost tEntry base index position quotient carry cell divisor) "t" residualExpression
    (TwoDigitSubtract.residual cell carry (quotient*divisor)) updates none (residual_read pEntry base index position quotient carry cell divisor pModel (bind_lookup_same _ _ _)) run
  exact ScalarScope.declare_execute source _ "p" productExpression (quotient*divisor) (.dec (ofString "t") .one residualExpression updates) none
    (product_read source base index position quotient carry cell divisor checked) tRun

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.Entry.bindTemporary
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.step_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem restore_memory (saved state : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (memory : BitVec 64→HolWordLab 64) :
    restore saved name {state with memory:=memory}={restore saved name state with memory:=memory} := rfl

/-- Restoring p/t leaves exactly the actual memory store and i/k updates. -/
theorem post_canonical (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) :
    post source base index position quotient carry cell divisor=updatePost source base index position quotient carry cell divisor := by
  unfold post updatePost
  dsimp only
  rw [restore_bind_other _ _ "t" "i" _ (by decide),restore_bind_other _ _ "t" "k" _ (by decide),
    restore_bind_other _ _ "p" "i" _ (by decide),restore_bind_other _ _ "p" "k" _ (by decide)]
  simp only [restore_memory,restore_bound]
  rfl

theorem post_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) :
    post source base index position quotient carry cell divisor={source with
      locals:=(post source base index position quotient carry cell divisor).locals,
      memory:=StoreWord.put source.memory (slot (Workspace.pointer base .normalizedNumerator) (index+position)) (TwoDigitSubtract.low cell carry (quotient*divisor))} := by
  rw [post_canonical]
  rfl

theorem post_index (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) :
    (post source base index position quotient carry cell divisor).locals.lookup (ofString "i")=
      some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
  rw [post_canonical]
  exact bind_lookup_same _ _ _

theorem post_carry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) :
    (post source base index position quotient carry cell divisor).locals.lookup (ofString "k")=
      some (.val (.word (TwoDigitSubtract.nextCarry cell carry (quotient*divisor)))) := by
  rw [post_canonical]
  exact (bind_lookup_other _ "i" "k" _ (by decide)).trans (bind_lookup_same _ _ _)

theorem post_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) (name : String) (notI : ofString name≠ofString "i") (notK : ofString name≠ofString "k") :
    (post source base index position quotient carry cell divisor).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  rw [post_canonical]
  exact (bind_lookup_other _ "i" name _ (Ne.symm notI)).trans (bind_lookup_other _ "k" name _ (Ne.symm notK))

theorem post_written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) :
    (post source base index position quotient carry cell divisor).memory (slot (Workspace.pointer base .normalizedNumerator) (index+position))=
      .word (TwoDigitSubtract.low cell carry (quotient*divisor)) := by
  rw [post_canonical]
  simp [updatePost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,StoreWord.put]

theorem post_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor query : BitVec 64)
    (outside : query≠slot (Workspace.pointer base .normalizedNumerator) (index+position)) :
    (post source base index position quotient carry cell divisor).memory query=source.memory query := by
  rw [post_canonical]
  simp only [updatePost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,StoreWord.put,if_neg outside]

theorem step_arithmetic (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index position : Nat)
    (quotient carry cell divisor : BitVec 64) (checked : Entry source base index position quotient carry cell divisor) :
    evaluateHOLFiniteState source step=(none,post source base index position quotient carry cell divisor) ∧
      (TwoDigitSubtract.low cell carry (quotient*divisor)).toNat<4294967296 ∧
      (TwoDigitSubtract.nextCarry cell carry (quotient*divisor)).toNat<4294967296 ∧
      cell.toNat+4294967296*(TwoDigitSubtract.nextCarry cell carry (quotient*divisor)).toNat=
        (TwoDigitSubtract.low cell carry (quotient*divisor)).toNat+quotient.toNat*divisor.toNat+carry.toNat :=
  ⟨step_execute source base index position quotient carry cell divisor checked,
    TwoDigitSubtract.product_digit cell carry quotient divisor checked.cellSmall checked.carrySmall checked.quotientSmall checked.divisorSmall⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.post_canonical
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.post_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.post_index
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.post_carry
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.post_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.post_written
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.post_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.step_arithmetic

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The two actual input/divisor words needed by the n=2 subtraction loop. -/
structure PairEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) : Prop where
  first : Entry source base 0 position quotient 0#64 low divisorLow
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  nextInside : 1+position<17
  middleCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (1+position))=.word middle
  highCell : source.memory (slot (Workspace.pointer base .normalizedDivisor) 1)=.word divisorHigh
  middleSmall : middle.toNat<4294967296
  highSmall : divisorHigh.toNat<4294967296

theorem Entry.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {index position : Nat}
    {quotient carry cell divisor : BitVec 64} (checked : Entry source base index position quotient carry cell divisor) (clock : Nat) :
    Entry {source with clock:=clock} base index position quotient carry cell divisor :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    checked.indexSmall,checked.inside,checked.u,checked.v,checked.i,checked.j,checked.q,checked.k,
    checked.input,checked.divisorCell,checked.cellSmall,checked.carrySmall,checked.quotientSmall,checked.divisorSmall⟩

theorem PairEntry.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {position : Nat}
    {quotient low middle divisorLow divisorHigh : BitVec 64}
    (checked : PairEntry source base position quotient low middle divisorLow divisorHigh) (clock : Nat) :
    PairEntry {source with clock:=clock} base position quotient low middle divisorLow divisorHigh :=
  ⟨checked.first.withClock clock,checked.n,checked.nextInside,checked.middleCell,checked.highCell,checked.middleSmall,checked.highSmall⟩

private theorem slots_different (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : Workspace.Context source base) (left right : Nat) (leftInside : left<17) (rightInside : right<17) (different : left≠right) :
    slot (Workspace.pointer base .normalizedNumerator) left≠slot (Workspace.pointer base .normalizedNumerator) right := by
  intro hit
  have number:=congrArg BitVec.toNat hit
  rw [Workspace.slot_number source base context .normalizedNumerator left leftInside,
    Workspace.slot_number source base context .normalizedNumerator right rightInside] at number
  omega

private theorem next_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) (checked : PairEntry source base position quotient low middle divisorLow divisorHigh) :
    Entry (post source base 0 position quotient 0#64 low divisorLow) base 1 position quotient
      (TwoDigitSubtract.nextCarry low 0#64 (quotient*divisorLow)) middle divisorHigh := by
  have arithmetic:=TwoDigitSubtract.product_digit low 0#64 quotient divisorLow checked.first.cellSmall (by decide)
    checked.first.quotientSmall checked.first.divisorSmall
  refine ⟨⟨checked.first.context.global,checked.first.context.domain,checked.first.context.arena,checked.first.context.aligned⟩,
    by decide,checked.nextInside,?_,?_,?_,?_,?_,?_,?_,?_,checked.middleSmall,arithmetic.2.1,checked.first.quotientSmall,checked.highSmall⟩
  · exact (post_other source base 0 position quotient 0#64 low divisorLow "un" (by decide) (by decide)).trans checked.first.u
  · exact (post_other source base 0 position quotient 0#64 low divisorLow "vn" (by decide) (by decide)).trans checked.first.v
  · exact post_index source base 0 position quotient 0#64 low divisorLow
  · exact (post_other source base 0 position quotient 0#64 low divisorLow "j" (by decide) (by decide)).trans checked.first.j
  · exact (post_other source base 0 position quotient 0#64 low divisorLow "qhat" (by decide) (by decide)).trans checked.first.q
  · exact post_carry source base 0 position quotient 0#64 low divisorLow
  · exact (post_away source base 0 position quotient 0#64 low divisorLow _
      (slots_different source base checked.first.context (1+position) (0+position) checked.nextInside checked.first.inside (by omega))).trans checked.middleCell
  · exact (post_away source base 0 position quotient 0#64 low divisorLow _
      (Workspace.separate base .normalizedDivisor .normalizedNumerator (by intro same;cases same) 1 (0+position) (by decide) checked.first.inside)).trans checked.highCell

/-- Exact final state of the original two iterations, including both loop ticks. -/
def pairPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) :=
  let first:=post (decClockHOLFinite source) base 0 position quotient 0#64 low divisorLow
  post (decClockHOLFinite first) base 1 position quotient (TwoDigitSubtract.nextCarry low 0#64 (quotient*divisorLow)) middle divisorHigh

private theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (small : index≤2)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=
      some (.val (.word (if index<2 then 1#64 else 0#64))) := by
  have indexNumber : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [finite_eval]
  simp [eval,test,localVar,evalHOLExact,toExact,i,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,indexNumber]

theorem pairPost_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) :
    pairPost source base position quotient low middle divisorLow divisorHigh={source with
      locals:=(pairPost source base position quotient low middle divisorLow divisorHigh).locals,
      memory:=StoreWord.put (StoreWord.put source.memory (slot (Workspace.pointer base .normalizedNumerator) (0+position))
        (TwoDigitSubtract.low low 0#64 (quotient*divisorLow)))
        (slot (Workspace.pointer base .normalizedNumerator) (1+position))
        (TwoDigitSubtract.low middle (TwoDigitSubtract.nextCarry low 0#64 (quotient*divisorLow)) (quotient*divisorHigh)),
      clock:=source.clock-2} := by
  simp only [pairPost,post_canonical,updatePost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,decClockHOLFinite]
  congr 1

private theorem while_next (source next final : PanSemStateFiniteExact 64 Guest.HostMemory)
    (condition : ExpHOL 64) (contents : ProgHOL 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) condition=some (.val (.word 1#64)))
    (paid : source.clock≠0)
    (bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) contents=(none,next))
    (tailRun : evaluateHOLFiniteState next (.while condition contents)=(none,final)) :
    evaluateHOLFiniteState source (.while condition contents)=(none,final) := by
  have clock:=evaluateHOLFiniteState_clock_le (decClockHOLFinite source) contents
  rw [bodyRun] at clock
  rw [evaluateHOLFiniteState_while_total,read]
  simp only [if_neg paid,if_pos (show (1#64 : BitVec 64)≠0 by decide)]
  rw [bodyRun,StateSteps.fixed_clock (decClockHOLFinite source) next none clock]
  exact tailRun

private theorem while_done (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (condition : ExpHOL 64) (contents : ProgHOL 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) condition=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source (.while condition contents)=(none,source) := by
  rw [evaluateHOLFiniteState_while_total,read]
  rfl

/-- Both real iterations, and the final false guard, execute from actual cells. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) (checked : PairEntry source base position quotient low middle divisorLow divisorHigh)
    (enough : 2≤source.clock) :
    evaluateHOLFiniteState source loop=(none,pairPost source base position quotient low middle divisorLow divisorHigh) := by
  let first:=post (decClockHOLFinite source) base 0 position quotient 0#64 low divisorLow
  let second:=pairPost source base position quotient low middle divisorLow divisorHigh
  have firstRun : evaluateHOLFiniteState (decClockHOLFinite source) step=(none,first):=
    step_execute (decClockHOLFinite source) base 0 position quotient 0#64 low divisorLow (checked.first.withClock _)
  have nextModel : Entry first base 1 position quotient (TwoDigitSubtract.nextCarry low 0#64 (quotient*divisorLow)) middle divisorHigh:=
    next_entry (decClockHOLFinite source) base position quotient low middle divisorLow divisorHigh (checked.withClock _)
  have firstN : first.locals.lookup (ofString "n")=some (.val (.word 2#64)):=
    (post_other (decClockHOLFinite source) base 0 position quotient 0#64 low divisorLow "n" (by decide) (by decide)).trans checked.n
  have secondRun : evaluateHOLFiniteState (decClockHOLFinite first) step=(none,second):=
    step_execute (decClockHOLFinite first) base 1 position quotient (TwoDigitSubtract.nextCarry low 0#64 (quotient*divisorLow)) middle divisorHigh (nextModel.withClock _)
  have secondI : second.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 2))):=
    post_index (decClockHOLFinite first) base 1 position quotient (TwoDigitSubtract.nextCarry low 0#64 (quotient*divisorLow)) middle divisorHigh
  have secondN : second.locals.lookup (ofString "n")=some (.val (.word 2#64)):=
    (post_other (decClockHOLFinite first) base 1 position quotient (TwoDigitSubtract.nextCarry low 0#64 (quotient*divisorLow)) middle divisorHigh "n" (by decide) (by decide)).trans firstN
  have read0:=test_read source 0 (by decide) checked.first.i checked.n
  have read1:=test_read first 1 (by decide) nextModel.i firstN
  have read2:=test_read second 2 (by decide) secondI secondN
  simp only [Nat.reduceLT,↓reduceIte] at read0 read1 read2
  have finish : evaluateHOLFiniteState second loop=(none,second):=while_done second test step read2
  have firstClock : first.clock=source.clock-1:=rfl
  have tailRun : evaluateHOLFiniteState first loop=(none,second):=
    while_next first second second test step read1 (by omega) secondRun finish
  exact while_next source first second test step read0 (by omega) firstRun tailRun

/-- The all-outcome source allowance includes short-clock timeout executions. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) (checked : PairEntry source base position quotient low middle divisorLow divisorHigh) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤2 := by
  by_cases enough : 2≤source.clock
  · rw [loop_execute source base position quotient low middle divisorLow divisorHigh checked enough]
    have clock:=congrArg PanSemStateFiniteExact.clock (pairPost_frame source base position quotient low middle divisorLow divisorHigh)
    change (pairPost source base position quotient low middle divisorLow divisorHigh).clock=source.clock-2 at clock
    change source.clock-(pairPost source base position quotient low middle divisorLow divisorHigh).clock≤2
    omega
  · omega

/-- An actual normal return derives both required loop ticks and its real stores. -/
theorem loop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) (checked : PairEntry source base position quotient low middle divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source loop=(none,target)) :
    2≤source.clock ∧ target=pairPost source base position quotient low middle divisorLow divisorHigh := by
  let baseSource:={source with clock:=2}
  let baseTarget:=pairPost baseSource base position quotient low middle divisorLow divisorHigh
  have baseRun:=loop_execute baseSource base position quotient low middle divisorLow divisorHigh (checked.withClock 2) (by rfl)
  have zero : baseTarget.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock (pairPost_frame baseSource base position quotient low middle divisorLow divisorHigh)
    change baseTarget.clock=2-2 at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget target loop 2 none none baseRun zero (by decide) normal (by decide)).1
  have expected:=loop_execute source base position quotient low middle divisorLow divisorHigh checked funded
  exact ⟨funded,congrArg Prod.snd (normal.symm.trans expected)⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.Entry.withClock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.PairEntry.withClock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.pairPost_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.loop_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.loop_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.loop_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem pairPost_carry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) :
    (pairPost source base position quotient low middle divisorLow divisorHigh).locals.lookup (ofString "k")=
      some (.val (.word (TwoDigitSubtract.secondCarry low middle quotient divisorLow divisorHigh))) :=
  post_carry _ base 1 position quotient _ middle divisorHigh

theorem pairPost_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) (name : String) (notI : ofString name≠ofString "i") (notK : ofString name≠ofString "k") :
    (pairPost source base position quotient low middle divisorLow divisorHigh).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  unfold pairPost
  exact (post_other _ base 1 position quotient _ middle divisorHigh name notI notK).trans
    (post_other _ base 0 position quotient 0#64 low divisorLow name notI notK)

theorem pairPost_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh query : BitVec 64)
    (outsideLow : query≠slot (Workspace.pointer base .normalizedNumerator) (0+position))
    (outsideMiddle : query≠slot (Workspace.pointer base .normalizedNumerator) (1+position)) :
    (pairPost source base position quotient low middle divisorLow divisorHigh).memory query=source.memory query := by
  unfold pairPost
  exact (post_away _ base 1 position quotient _ middle divisorHigh query outsideMiddle).trans
    (post_away _ base 0 position quotient 0#64 low divisorLow query outsideLow)

theorem pairPost_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) (checked : PairEntry source base position quotient low middle divisorLow divisorHigh) :
    (pairPost source base position quotient low middle divisorLow divisorHigh).memory (slot (Workspace.pointer base .normalizedNumerator) (0+position))=
      .word (TwoDigitSubtract.firstLow low quotient divisorLow) ∧
    (pairPost source base position quotient low middle divisorLow divisorHigh).memory (slot (Workspace.pointer base .normalizedNumerator) (1+position))=
      .word (TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh) := by
  let first:=post (decClockHOLFinite source) base 0 position quotient 0#64 low divisorLow
  refine ⟨?_,post_written (decClockHOLFinite first) base 1 position quotient _ middle divisorHigh⟩
  exact (post_away (decClockHOLFinite first) base 1 position quotient _ middle divisorHigh _
    (slots_different source base checked.first.context (0+position) (1+position) checked.first.inside checked.nextInside (by omega))).trans
    (post_written (decClockHOLFinite source) base 0 position quotient 0#64 low divisorLow)

/-- A genuine normal subtraction-loop return, with its actual corrected
quotient, has the real remainder cells and the exact top carry. Connecting
quotient correction to that quotient premise remains the surrounding caller's job. -/
theorem loop_remainder (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle top divisorLow divisorHigh : BitVec 64) (checked : PairEntry source base position quotient low middle divisorLow divisorHigh)
    (positive : 0<TwoDigitSubtract.divisorNumber divisorLow divisorHigh)
    (exactQuotient : quotient.toNat=TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source loop=(none,target)) :
    2≤source.clock ∧
      target.locals.lookup (ofString "k")=some (.val (.word top)) ∧
      target.memory (slot (Workspace.pointer base .normalizedNumerator) (0+position))=.word (TwoDigitSubtract.firstLow low quotient divisorLow) ∧
      target.memory (slot (Workspace.pointer base .normalizedNumerator) (1+position))=.word (TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh) ∧
      (TwoDigitSubtract.firstLow low quotient divisorLow).toNat+4294967296*(TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh).toNat=
        TwoDigitSubtract.window low middle top%TwoDigitSubtract.divisorNumber divisorLow divisorHigh := by
  obtain ⟨funded,rfl⟩:=loop_normal source target base position quotient low middle divisorLow divisorHigh checked normal
  have arithmetic:=TwoDigitSubtract.pair_from_quotient low middle top quotient divisorLow divisorHigh
    checked.first.cellSmall checked.middleSmall checked.first.quotientSmall checked.first.divisorSmall checked.highSmall positive exactQuotient
  have carry:=pairPost_carry source base position quotient low middle divisorLow divisorHigh
  rw [arithmetic.1] at carry
  have cells:=pairPost_cells source base position quotient low middle divisorLow divisorHigh checked
  exact ⟨funded,carry,cells.1,cells.2,arithmetic.2.2⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.pairPost_carry
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.pairPost_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.pairPost_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.pairPost_cells
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.loop_remainder

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def topAddress : ExpHOL 64:=address "un" (.op .add [localVar "j",localVar "n"])
def quotientAddress : ExpHOL 64:=address "q" (localVar "j")
def difference : ExpHOL 64:=.op .sub [localVar "ujn",localVar "k"]
def negativeTest : ExpHOL 64:=.cmp .less (localVar "tt") (.const 0#64)
def keep : ProgHOL 64:=.seq (.store quotientAddress (localVar "qhat")) (.store topAddress (localVar "tt"))

private def findFinish : ProgHOL 64→Option (ProgHOL 64)
  | .dec name shape (.op .sub [.var .local high,.var .local carry]) rest=>
    if name=ofString "tt" ∧ high=ofString "ujn" ∧ carry=ofString "k" then
      some (.dec name shape (.op .sub [.var .local high,.var .local carry]) rest) else findFinish rest
  | .dec _ _ _ rest=>findFinish rest
  | .seq first rest=>(findFinish first).orElse (fun _=>findFinish rest)
  | .ite _ yes no=>(findFinish yes).orElse (fun _=>findFinish no)
  | .while _ contents=>findFinish contents
  | .decCall _ _ _ _ rest=>findFinish rest
  | _=>none

/-- The original tt declaration and complete original add-back conditional. -/
def finish : ProgHOL 64:=(findFinish Single.body).getD .skip

set_option maxRecDepth 100000 in
theorem finish_shape : ∃ addBack,finish=.dec (ofString "tt") .one difference (.ite negativeTest addBack keep) := by
  simp [finish,findFinish,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    topAddress,quotientAddress,address,difference,negativeTest,keep,localVar]

structure FinishEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient top : BitVec 64) : Prop where
  context : Workspace.Context source base
  inside : position+2<17
  un : source.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator)))
  q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))
  j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  qhat : source.locals.lookup (ofString "qhat")=some (.val (.word quotient))
  ujn : source.locals.lookup (ofString "ujn")=some (.val (.word top))
  k : source.locals.lookup (ofString "k")=some (.val (.word top))

private theorem quotient_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (position : Nat)
    (q : source.locals.lookup (ofString "q")=some (.val (.word pointer)))
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position)))) :
    eval source quotientAddress=some (.val (.word (slot pointer position))) := by
  simp [eval,quotientAddress,address,localVar,evalHOLExact,evalListHOLExact,toExact,q,j,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,Nat.mul_comm]

private theorem top_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (position : Nat)
    (un : source.locals.lookup (ofString "un")=some (.val (.word pointer)))
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position))))
    (n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))) :
    eval source topAddress=some (.val (.word (slot pointer (position+2)))) := by
  simp [eval,topAddress,address,localVar,evalHOLExact,evalListHOLExact,toExact,un,j,n,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,BitVec.ofNat_add,Nat.mul_comm]

def finishPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat) (quotient : BitVec 64) :=
  {source with
    memory:=StoreWord.put (StoreWord.put source.memory (slot (Workspace.pointer base .quotient) position) quotient)
      (slot (Workspace.pointer base .normalizedNumerator) (position+2)) 0#64}

/-- Equal actual top and carry select the original nonnegative branch,
store the real qhat digit and zero the normalized top word. -/
theorem finish_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient top : BitVec 64) (checked : FinishEntry source base position quotient top) :
    evaluateHOLFiniteState source finish=(none,finishPost source base position quotient) := by
  let entered:=bind source "tt" 0#64
  have differenceRead : eval source difference=some (.val (.word 0#64)):=by
    simp [eval,difference,localVar,evalHOLExact,evalListHOLExact,toExact,checked.ujn,checked.k,valueIsWord,valueWord,wordOpHOL,wordOp]
  have tt : entered.locals.lookup (ofString "tt")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have negativeRead : eval entered negativeTest=some (.val (.word 0#64)):=by
    simp [eval,negativeTest,localVar,evalHOLExact,toExact,tt,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess]
  have qhat : entered.locals.lookup (ofString "qhat")=some (.val (.word quotient)):=
    (bind_lookup_other source "tt" "qhat" _ (by decide)).trans checked.qhat
  have q : entered.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))):=
    (bind_lookup_other source "tt" "q" _ (by decide)).trans checked.q
  have j : entered.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position))):=
    (bind_lookup_other source "tt" "j" _ (by decide)).trans checked.j
  have un : entered.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator))):=
    (bind_lookup_other source "tt" "un" _ (by decide)).trans checked.un
  have n : entered.locals.lookup (ofString "n")=some (.val (.word 2#64)):=
    (bind_lookup_other source "tt" "n" _ (by decide)).trans checked.n
  let first:={entered with memory:=StoreWord.put entered.memory (slot (Workspace.pointer base .quotient) position) quotient}
  have firstRun:=StoreWord.execute entered quotientAddress (localVar "qhat") _ quotient
    (quotient_address_read entered _ position q j) (local_read entered "qhat" quotient qhat)
    (Workspace.slot_mapped source base checked.context .quotient position (by change position<16;have h:=checked.inside;omega))
  have secondRun:=StoreWord.execute first topAddress (localVar "tt") _ 0#64
    (top_address_read first _ position un j n) (local_read first "tt" 0#64 tt)
    (Workspace.slot_mapped source base checked.context .normalizedNumerator (position+2) checked.inside)
  have stores : evaluateHOLFiniteState entered keep=(none,finishPost entered base position quotient):=by
    rw [keep,StateSteps.next_sequence entered first _ _ firstRun (by rfl)]
    exact secondRun
  obtain ⟨addBack,shape⟩:=finish_shape
  have branchRun : evaluateHOLFiniteState entered (.ite negativeTest addBack keep)=(none,finishPost entered base position quotient):=by
    simp only [eval] at negativeRead
    rw [evaluateHOLFiniteState_ite,negativeRead]
    exact stores
  have declared:=ScalarScope.declare_execute source (finishPost entered base position quotient) "tt" difference 0#64
    (.ite negativeTest addBack keep) none differenceRead branchRun
  rw [shape,declared]
  change (none,restore source "tt" (finishPost entered base position quotient))=(none,finishPost source base position quotient)
  congr 1
  unfold finishPost
  rw [restore_memory,restore_bound]
  rfl

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.finish_shape
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.finish_execute

namespace InitECandidate.Solver.Input.UDivMod.QhatCorrection
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real correction loop changes only qhat/rhat/again caller bindings. -/
theorem loop_other (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notQ : ofString name≠ofString "qhat") (notR : ofString name≠ofString "rhat") (notAgain : ofString name≠ofString "again")
    (normal : evaluateHOLFiniteState source loop=(none,post)) :
    post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  have safe : LocalPrefix (ofString name) loop:=by
    unfold loop body branch correct
    exact .loop _ (.seq (.assign _ _ notAgain) (.ite _
      (.ite _ (.seq (.assign _ _ notQ) (.seq (.assign _ _ notR) (.assign _ _ notAgain))) .skip) .skip))
  have kept:=(safe.summary_full source).1
  rw [normal] at kept
  exact kept rfl

end InitECandidate.Solver.Input.UDivMod.QhatCorrection

#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.loop_other

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual normalized two-digit window, independently of the current
quotient estimate or the temporary carry/index bindings. -/
structure Window (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) : Prop where
  context : Workspace.Context source base
  inside : position+2<17
  un : source.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator)))
  vn : source.locals.lookup (ofString "vn")=some (.val (.word (Workspace.pointer base .normalizedDivisor)))
  q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))
  j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  ujn : source.locals.lookup (ofString "ujn")=some (.val (.word top))
  i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))
  lowCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (0+position))=.word low
  middleCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (1+position))=.word middle
  topCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (position+2))=.word top
  divisorLowCell : source.memory (slot (Workspace.pointer base .normalizedDivisor) 0)=.word divisorLow
  divisorHighCell : source.memory (slot (Workspace.pointer base .normalizedDivisor) 1)=.word divisorHigh
  lowSmall : low.toNat<4294967296
  middleSmall : middle.toNat<4294967296
  divisorLowSmall : divisorLow.toNat<4294967296
  divisorHighSmall : divisorHigh.toNat<4294967296
  divisorHighLarge : 2147483648≤divisorHigh.toNat

theorem Window.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {position : Nat}
    {low middle top divisorLow divisorHigh : BitVec 64} (checked : Window source base position low middle top divisorLow divisorHigh) (clock : Nat) :
    Window {source with clock:=clock} base position low middle top divisorLow divisorHigh :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    checked.inside,checked.un,checked.vn,checked.q,checked.j,checked.n,checked.ujn,checked.i,
    checked.lowCell,checked.middleCell,checked.topCell,checked.divisorLowCell,checked.divisorHighCell,
    checked.lowSmall,checked.middleSmall,checked.divisorLowSmall,checked.divisorHighSmall,checked.divisorHighLarge⟩

private theorem Window.after_correction {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {position : Nat}
    {low middle top divisorLow divisorHigh : BitVec 64} (checked : Window source base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source QhatCorrection.loop=(none,target)) :
    Window target base position low middle top divisorLow divisorHigh := by
  have frame:=QhatCorrection.loop_frame source.code source rfl
  rw [normal] at frame
  have memory:=LocalEffects.memory_of_erase source target frame
  have globals : target.globals=source.globals:=by
    have projected:=congrArg PanSemStateFiniteExact.globals frame
    exact projected
  have domain : target.memaddrs=source.memaddrs:=by
    have projected:=congrArg PanSemStateFiniteExact.memaddrs frame
    exact projected
  refine ⟨⟨?_,domain.trans checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    checked.inside,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,checked.lowSmall,checked.middleSmall,
    checked.divisorLowSmall,checked.divisorHighSmall,checked.divisorHighLarge⟩
  · rw [globals];exact checked.context.global
  · exact (QhatCorrection.loop_other source target "un" (by decide) (by decide) (by decide) normal).trans checked.un
  · exact (QhatCorrection.loop_other source target "vn" (by decide) (by decide) (by decide) normal).trans checked.vn
  · exact (QhatCorrection.loop_other source target "q" (by decide) (by decide) (by decide) normal).trans checked.q
  · exact (QhatCorrection.loop_other source target "j" (by decide) (by decide) (by decide) normal).trans checked.j
  · exact (QhatCorrection.loop_other source target "n" (by decide) (by decide) (by decide) normal).trans checked.n
  · exact (QhatCorrection.loop_other source target "ujn" (by decide) (by decide) (by decide) normal).trans checked.ujn
  · obtain ⟨old,cell⟩:=checked.i
    exact ⟨old,(QhatCorrection.loop_other source target "i" (by decide) (by decide) (by decide) normal).trans cell⟩
  · rw [memory];exact checked.lowCell
  · rw [memory];exact checked.middleCell
  · rw [memory];exact checked.topCell
  · rw [memory];exact checked.divisorLowCell
  · rw [memory];exact checked.divisorHighCell

def subtractionEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=bind (bind source "k" 0#64) "i" 0#64

private theorem initialize_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notI : ofString name≠ofString "i") (notK : ofString name≠ofString "k") :
    (subtractionEntry source).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "i" name _ (Ne.symm notI)).trans (bind_lookup_other _ "k" name _ (Ne.symm notK))

private theorem Window.enter_pair {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {position : Nat}
    {low middle top divisorLow divisorHigh : BitVec 64} (checked : Window source base position low middle top divisorLow divisorHigh)
    (quotient : BitVec 64) (qhat : source.locals.lookup (ofString "qhat")=some (.val (.word quotient))) (small : quotient.toNat<4294967296) :
    PairEntry (subtractionEntry source) base position quotient low middle divisorLow divisorHigh := by
  refine ⟨⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    by decide,by have h:=checked.inside;omega,?_,?_,?_,?_,?_,?_,checked.lowCell,checked.divisorLowCell,
    checked.lowSmall,by decide,small,checked.divisorLowSmall⟩,?_,by have h:=checked.inside;omega,
    checked.middleCell,checked.divisorHighCell,checked.middleSmall,checked.divisorHighSmall⟩
  · exact (initialize_other source "un" (by decide) (by decide)).trans checked.un
  · exact (initialize_other source "vn" (by decide) (by decide)).trans checked.vn
  · exact bind_lookup_same _ _ _
  · exact (initialize_other source "j" (by decide) (by decide)).trans checked.j
  · exact (initialize_other source "qhat" (by decide) (by decide)).trans qhat
  · exact (bind_lookup_other _ "i" "k" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact (initialize_other source "n" (by decide) (by decide)).trans checked.n

def initialized : ProgHOL 64:=.dec (ofString "k") .one (.const 0#64)
  (.seq (.assign .local (ofString "i") (.const 0#64)) (.seq loop finish))
def initializedPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) :=
  restore source "k" (finishPost (pairPost (subtractionEntry source) base position quotient low middle divisorLow divisorHigh) base position quotient)

/-- Actual k declaration, i reset, both subtraction iterations and original
post-subtraction conditional. The quotient is the current entry binding. -/
theorem initialized_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (qhat : source.locals.lookup (ofString "qhat")=some (.val (.word quotient))) (small : quotient.toNat<4294967296)
    (exactQuotient : quotient.toNat=TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh)
    (enough : 2≤source.clock) :
    evaluateHOLFiniteState source initialized=(none,initializedPost source base position quotient low middle divisorLow divisorHigh) := by
  let entered:=subtractionEntry source
  let subtracted:=pairPost entered base position quotient low middle divisorLow divisorHigh
  have pairModel : PairEntry entered base position quotient low middle divisorLow divisorHigh:=checked.enter_pair quotient qhat small
  have loopRun : evaluateHOLFiniteState entered loop=(none,subtracted):=loop_execute entered base position quotient low middle divisorLow divisorHigh pairModel enough
  have positive : 0<TwoDigitSubtract.divisorNumber divisorLow divisorHigh:=by
    have large:=checked.divisorHighLarge
    unfold TwoDigitSubtract.divisorNumber
    omega
  have arithmetic:=TwoDigitSubtract.pair_from_quotient low middle top quotient divisorLow divisorHigh
    checked.lowSmall checked.middleSmall small checked.divisorLowSmall checked.divisorHighSmall positive exactQuotient
  have carry:=pairPost_carry entered base position quotient low middle divisorLow divisorHigh
  rw [arithmetic.1] at carry
  have finishModel : FinishEntry subtracted base position quotient top:=by
    refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
      checked.inside,?_,?_,?_,?_,?_,?_,carry⟩
    · exact (pairPost_other entered base position quotient low middle divisorLow divisorHigh "un" (by decide) (by decide)).trans pairModel.first.u
    · exact (pairPost_other entered base position quotient low middle divisorLow divisorHigh "q" (by decide) (by decide)).trans
        ((initialize_other source "q" (by decide) (by decide)).trans checked.q)
    · exact (pairPost_other entered base position quotient low middle divisorLow divisorHigh "j" (by decide) (by decide)).trans pairModel.first.j
    · exact (pairPost_other entered base position quotient low middle divisorLow divisorHigh "n" (by decide) (by decide)).trans pairModel.n
    · exact (pairPost_other entered base position quotient low middle divisorLow divisorHigh "qhat" (by decide) (by decide)).trans pairModel.first.q
    · exact (pairPost_other entered base position quotient low middle divisorLow divisorHigh "ujn" (by decide) (by decide)).trans
        ((initialize_other source "ujn" (by decide) (by decide)).trans checked.ujn)
  have finishRun:=finish_execute subtracted base position quotient top finishModel
  have tailRun : evaluateHOLFiniteState entered (.seq loop finish)=(none,finishPost subtracted base position quotient):=by
    rw [evaluateHOLFiniteState_seq_line780,loopRun]
    exact finishRun
  obtain ⟨old,i⟩:=checked.i
  have enteredI : (bind source "k" 0#64).locals.lookup (ofString "i")=some (.val (.word old)):=
    (bind_lookup_other _ "k" "i" _ (by decide)).trans i
  have reset:=StateSteps.assign_execute (bind source "k" 0#64) "i" (.const 0#64) old 0#64 enteredI rfl
  have bodyRun : evaluateHOLFiniteState (bind source "k" 0#64) (.seq (.assign .local (ofString "i") (.const 0#64)) (.seq loop finish))=
      (none,finishPost subtracted base position quotient):=by
    rw [evaluateHOLFiniteState_seq_line780,reset]
    exact tailRun
  exact ScalarScope.declare_execute source _ "k" (.const 0#64) 0#64 _ none rfl bodyRun

/-- Every outcome of the complete initialized subtraction phase costs≤2. -/
theorem initialized_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (qhat : source.locals.lookup (ofString "qhat")=some (.val (.word quotient))) (small : quotient.toNat<4294967296)
    (exactQuotient : quotient.toNat=TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh) :
    source.clock-(evaluateHOLFiniteState source initialized).2.clock≤2 := by
  by_cases enough : 2≤source.clock
  · rw [initialized_execute source base position quotient low middle top divisorLow divisorHigh checked qhat small exactQuotient enough]
    change source.clock-((source.clock-1)-1)≤2
    omega
  · omega

/-- A real normal phase derives its own funding and exact initialized endpoint. -/
theorem initialized_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (qhat : source.locals.lookup (ofString "qhat")=some (.val (.word quotient))) (small : quotient.toNat<4294967296)
    (exactQuotient : quotient.toNat=TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source initialized=(none,target)) :
    2≤source.clock ∧ target=initializedPost source base position quotient low middle divisorLow divisorHigh := by
  let baseSource:={source with clock:=2}
  let baseTarget:=initializedPost baseSource base position quotient low middle divisorLow divisorHigh
  have baseRun:=initialized_execute baseSource base position quotient low middle top divisorLow divisorHigh (checked.withClock 2) qhat small exactQuotient (by rfl)
  have zero : baseTarget.clock=0:=rfl
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget target initialized 2 none none baseRun zero (by decide) normal (by decide)).1
  have expected:=initialized_execute source base position quotient low middle top divisorLow divisorHigh checked qhat small exactQuotient funded
  exact ⟨funded,congrArg Prod.snd (normal.symm.trans expected)⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.Window.withClock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.initialized_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.initialized_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.initialized_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def corrected : ProgHOL 64:=.seq QhatCorrection.loop initialized

private def findCorrected : ProgHOL 64→Option (ProgHOL 64)
  | .seq (.while condition contents) rest=>
    match condition with
    | .cmp .equal (.var .local name) (.const word)=>
      if name=ofString "again" ∧ word=1#64 then some (.seq (.while condition contents) rest)
      else (findCorrected contents).orElse (fun _=>findCorrected rest)
    | _=>(findCorrected contents).orElse (fun _=>findCorrected rest)
  | .dec _ _ _ rest=>findCorrected rest
  | .seq first rest=>(findCorrected first).orElse (fun _=>findCorrected rest)
  | .ite _ yes no=>(findCorrected yes).orElse (fun _=>findCorrected no)
  | .while _ contents=>findCorrected contents
  | .decCall _ _ _ _ rest=>findCorrected rest
  | _=>none

set_option maxRecDepth 100000 in
/-- The whole original correction/subtraction/store phase inside again's scope. -/
theorem literal_corrected : findCorrected Single.body=some corrected := by
  simp [findCorrected,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    corrected,QhatCorrection.loop,QhatCorrection.test,QhatCorrection.body,QhatCorrection.branch,QhatCorrection.correct,
    QhatCorrection.roomTest,QhatCorrection.estimateTest,QhatCorrection.leftEstimate,QhatCorrection.rightEstimate,
    QhatCorrection.quotientExpression,QhatCorrection.remainderExpression,initialized,loop,test,step,updates,
    productExpression,residualExpression,lowExpression,carryExpression,increment,inputAddress,divisorAddress,
    finish,findFinish,topAddress,quotientAddress,address,difference,negativeTest,keep,localVar]

/-- An actual correction-loop return supplies the current exact quotient
and retains the same physical normalized window for the subtraction phase. -/
private theorem correction_result (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (q r low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (ready : QhatCorrection.Bindings source q r 1#64 divisorHigh divisorLow low) (small : q.toNat<4294967296)
    (estimate : q.toNat*divisorHigh.toNat+r.toNat=top.toNat*4294967296+middle.toNat)
    (upper : TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh≤q.toNat)
    (normal : evaluateHOLFiniteState source QhatCorrection.loop=(none,target)) :
    ∃ quotient,Window target base position low middle top divisorLow divisorHigh ∧
      target.locals.lookup (ofString "qhat")=some (.val (.word quotient)) ∧ quotient.toNat<4294967296 ∧
      quotient.toNat=TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh := by
  have numerator : (q.toNat*divisorHigh.toNat+r.toNat)*4294967296+low.toNat=TwoDigitSubtract.window low middle top:=by
    rw [estimate]
    unfold TwoDigitSubtract.window
    ring
  have denominator : divisorHigh.toNat*4294967296+divisorLow.toNat=TwoDigitSubtract.divisorNumber divisorLow divisorHigh:=by
    unfold TwoDigitSubtract.divisorNumber
    ring
  have initialUpper : ((q.toNat*divisorHigh.toNat+r.toNat)*4294967296+low.toNat)/(divisorHigh.toNat*4294967296+divisorLow.toNat)≤q.toNat:=by
    rw [numerator,denominator]
    exact upper
  obtain ⟨quotient,remainder,corrections,count,postReady,number,remaining,remainingSmall,frame⟩:=
    QhatCorrection.normal_digit source target q r divisorHigh divisorLow low ready checked.divisorHighLarge checked.divisorHighSmall
      small checked.divisorLowSmall checked.lowSmall initialUpper normal
  rw [numerator,denominator] at number
  exact ⟨quotient,checked.after_correction normal,postReady.qCell,by omega,number⟩

/-- Every outcome of the literal correction/subtraction/store phase costs≤5
source ticks. Its exact quotient is derived from the real correction run. -/
theorem corrected_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (q r low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (ready : QhatCorrection.Bindings source q r 1#64 divisorHigh divisorLow low) (small : q.toNat<4294967296)
    (estimate : q.toNat*divisorHigh.toNat+r.toNat=top.toNat*4294967296+middle.toNat)
    (upper : TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh≤q.toNat) :
    source.clock-(evaluateHOLFiniteState source corrected).2.clock≤5 := by
  have front:=QhatCorrection.loop_cost source q r 1#64 divisorHigh divisorLow low ready checked.divisorHighLarge checked.divisorHighSmall
  have forward:=evaluateHOLFiniteState_clock_le source QhatCorrection.loop
  rw [corrected,evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source QhatCorrection.loop=output at front forward ⊢
  obtain ⟨result,middleState⟩:=output
  cases result with
  | none=>
    obtain ⟨quotient,nextModel,qhat,qSmall,exactQuotient⟩:=correction_result source middleState base position q r low middle top divisorLow divisorHigh
      checked ready small estimate upper computed
    have back:=initialized_cost middleState base position quotient low middle top divisorLow divisorHigh nextModel qhat qSmall exactQuotient
    have lastForward:=evaluateHOLFiniteState_clock_le middleState initialized
    change source.clock-(evaluateHOLFiniteState middleState initialized).2.clock≤5
    change source.clock-middleState.clock≤3 at front
    change middleState.clock≤source.clock at forward
    omega
  | some result=>
    change source.clock-middleState.clock≤5
    change source.clock-middleState.clock≤3 at front
    omega

def digitMemory (memory : BitVec 64→HolWordLab 64) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) : BitVec 64→HolWordLab 64:=
  StoreWord.put (StoreWord.put
    (StoreWord.put (StoreWord.put memory (slot (Workspace.pointer base .normalizedNumerator) (0+position))
      (TwoDigitSubtract.firstLow low quotient divisorLow))
      (slot (Workspace.pointer base .normalizedNumerator) (1+position))
      (TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh))
    (slot (Workspace.pointer base .quotient) position) quotient)
    (slot (Workspace.pointer base .normalizedNumerator) (position+2)) 0#64

theorem initializedPost_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) :
    initializedPost source base position quotient low middle divisorLow divisorHigh={source with
      locals:=(initializedPost source base position quotient low middle divisorLow divisorHigh).locals,
      memory:=digitMemory source.memory base position quotient low middle divisorLow divisorHigh,
      clock:=source.clock-2} := by
  simp only [initializedPost,finishPost,pairPost,post_canonical,updatePost,subtractionEntry,restore,
    WitnessRadix.QueryBranch.bind,setVarHOLFinite,decClockHOLFinite,digitMemory,TwoDigitSubtract.firstLow,TwoDigitSubtract.secondLow,TwoDigitSubtract.firstCarry]
  congr 1

/-- A real normal original phase derives its quotient, exact remainder
arithmetic and four physical stores from the same actual correction run. -/
theorem corrected_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (q r low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (ready : QhatCorrection.Bindings source q r 1#64 divisorHigh divisorLow low) (small : q.toNat<4294967296)
    (estimate : q.toNat*divisorHigh.toNat+r.toNat=top.toNat*4294967296+middle.toNat)
    (upper : TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh≤q.toNat)
    (normal : evaluateHOLFiniteState source corrected=(none,target)) :
    ∃ quotient,quotient.toNat<4294967296 ∧
      quotient.toNat=TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
      (TwoDigitSubtract.firstLow low quotient divisorLow).toNat+4294967296*(TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh).toNat=
        TwoDigitSubtract.window low middle top%TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
      target.memory=digitMemory source.memory base position quotient low middle divisorLow divisorHigh ∧
      target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock} ∧
      source.clock-target.clock≤5 := by
  obtain ⟨middleState,front,back⟩:=sequence_none source target QhatCorrection.loop initialized normal
  obtain ⟨quotient,nextModel,qhat,qSmall,exactQuotient⟩:=correction_result source middleState base position q r low middle top divisorLow divisorHigh
    checked ready small estimate upper front
  obtain ⟨funded,endpoint⟩:=initialized_normal middleState target base position quotient low middle top divisorLow divisorHigh nextModel qhat qSmall exactQuotient back
  have physical:=initializedPost_frame middleState base position quotient low middle divisorLow divisorHigh
  have frame:=QhatCorrection.loop_frame source.code source rfl
  rw [front] at frame
  have memory:=LocalEffects.memory_of_erase source middleState frame
  have written : target.memory=digitMemory source.memory base position quotient low middle divisorLow divisorHigh:=by
    rw [endpoint]
    have projected:=congrArg PanSemStateFiniteExact.memory physical
    change (initializedPost middleState base position quotient low middle divisorLow divisorHigh).memory=
      digitMemory middleState.memory base position quotient low middle divisorLow divisorHigh at projected
    rw [projected,memory]
  have static : target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock}:=by
    rw [endpoint]
    have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
      {state with
        locals:=(initializedPost middleState base position quotient low middle divisorLow divisorHigh).locals,
        memory:=(initializedPost middleState base position quotient low middle divisorLow divisorHigh).memory,
        clock:=(initializedPost middleState base position quotient low middle divisorLow divisorHigh).clock}) frame
    exact projected
  have positive : 0<TwoDigitSubtract.divisorNumber divisorLow divisorHigh:=by
    have large:=checked.divisorHighLarge
    unfold TwoDigitSubtract.divisorNumber
    omega
  have arithmetic:=TwoDigitSubtract.pair_from_quotient low middle top quotient divisorLow divisorHigh checked.lowSmall checked.middleSmall qSmall
    checked.divisorLowSmall checked.divisorHighSmall positive exactQuotient
  have cost:=corrected_cost source base position q r low middle top divisorLow divisorHigh checked ready small estimate upper
  rw [normal] at cost
  exact ⟨quotient,qSmall,exactQuotient,arithmetic.2.2,written,static,cost⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.literal_corrected
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.corrected_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.initializedPost_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.corrected_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def test : ExpHOL 64:=.cmp .notLower (localVar "ujn") (localVar "vtop")
def remainderExpression : ExpHOL 64:=.op .sub [
  .op .or [.shift .lsl (localVar "ujn") (.const 32#64),localVar "ujn1"],
  .panop .mul [localVar "qhat",localVar "vtop"]]
def maximum : ProgHOL 64:=.seq (.assign .local (ofString "qhat") (.const 4294967295#64))
  (.assign .local (ofString "rhat") remainderExpression)
def arguments : List (ExpHOL 64):=[localVar "ujn",localVar "ujn1",localVar "vtop"]
def updates : ProgHOL 64:=.seq (.assign .local (ofString "qhat") (.rfield 0 (localVar "qr")))
  (.assign .local (ofString "rhat") (.rfield 1 (localVar "qr")))
def scalar : ProgHOL 64:=.decCall (ofString "qr") returnShape (ofString "div64by32") arguments updates
def program : ProgHOL 64:=.ite test maximum scalar

def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r : BitVec 64) (paid : Nat) :=
  bind (bind {source with clock:=source.clock-paid} "qhat" q) "rhat" r

def maxRemainder (top middle divisorHigh : BitVec 64) : BitVec 64:=
  ((top<<<(32:Nat)) ||| middle)-(4294967295#64*divisorHigh)

private def findEstimate : ProgHOL 64→Option (ProgHOL 64)
  | .ite condition yes no=>
    match condition with
    | .cmp .notLower (.var .local high) (.var .local divisor)=>
      if high=ofString "ujn" ∧ divisor=ofString "vtop" then some (.ite condition yes no)
      else (findEstimate yes).orElse (fun _=>findEstimate no)
    | _=>(findEstimate yes).orElse (fun _=>findEstimate no)
  | .dec _ _ _ rest=>findEstimate rest
  | .seq first rest=>(findEstimate first).orElse (fun _=>findEstimate rest)
  | .while _ contents=>findEstimate contents
  | .decCall _ _ _ _ rest=>findEstimate rest
  | _=>none

set_option maxRecDepth 100000 in
theorem literal_program : findEstimate Single.body=some program := by
  simp [findEstimate,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    program,test,maximum,remainderExpression,scalar,arguments,updates,returnShape,localVar]

structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) : Prop where
  window : Subtract.Window source base position low middle top divisorLow divisorHigh
  installed : OriginalCode.Installed source.code
  middleCell : source.locals.lookup (ofString "ujn1")=some (.val (.word middle))
  lowCell : source.locals.lookup (ofString "ujn2")=some (.val (.word low))
  highCell : source.locals.lookup (ofString "vtop")=some (.val (.word divisorHigh))
  secondCell : source.locals.lookup (ofString "vsec")=some (.val (.word divisorLow))
  qhat : source.locals.lookup (ofString "qhat")=some (.val (.word 0#64))
  rhat : source.locals.lookup (ofString "rhat")=some (.val (.word 0#64))
  digitRange : TwoDigitSubtract.window low middle top<TwoDigitSubtract.divisorNumber divisorLow divisorHigh*4294967296

private theorem Entry.topSmall {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {position : Nat}
    {low middle top divisorLow divisorHigh : BitVec 64} (checked : Entry source base position low middle top divisorLow divisorHigh) :
    top.toNat<4294967296 := by
  have highSmall:=checked.window.divisorHighSmall
  have lowSmall:=checked.window.divisorLowSmall
  have range:=checked.digitRange
  unfold TwoDigitSubtract.window TwoDigitSubtract.divisorNumber at range
  omega

private theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (top divisorHigh : BitVec 64)
    (topCell : source.locals.lookup (ofString "ujn")=some (.val (.word top)))
    (highCell : source.locals.lookup (ofString "vtop")=some (.val (.word divisorHigh))) :
    eval source test=some (.val (.word (if divisorHigh.toNat≤top.toNat then 1#64 else 0#64))) := by
  simp [eval,test,localVar,evalHOLExact,toExact,topCell,highCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,Nat.not_lt]

private theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (top middle divisorHigh : BitVec 64)
    (topCell : source.locals.lookup (ofString "ujn")=some (.val (.word top)))
    (middleCell : source.locals.lookup (ofString "ujn1")=some (.val (.word middle)))
    (highCell : source.locals.lookup (ofString "vtop")=some (.val (.word divisorHigh))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word top),.val (.word middle),.val (.word divisorHigh)] := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,topCell,middleCell,highCell]

/-- The actual maximum-digit branch is straight line and retains its exact
wrapped remainder word without any clock premise. -/
theorem maximum_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (top middle divisorHigh : BitVec 64)
    (topCell : source.locals.lookup (ofString "ujn")=some (.val (.word top)))
    (middleCell : source.locals.lookup (ofString "ujn1")=some (.val (.word middle)))
    (highCell : source.locals.lookup (ofString "vtop")=some (.val (.word divisorHigh)))
    (qhat : source.locals.lookup (ofString "qhat")=some (.val (.word 0#64)))
    (rhat : source.locals.lookup (ofString "rhat")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source maximum=(none,post source 4294967295#64 (maxRemainder top middle divisorHigh) 0) := by
  let entered:=bind source "qhat" 4294967295#64
  have topRead : entered.locals.lookup (ofString "ujn")=some (.val (.word top)):=
    (bind_lookup_other _ "qhat" "ujn" _ (by decide)).trans topCell
  have middleRead : entered.locals.lookup (ofString "ujn1")=some (.val (.word middle)):=
    (bind_lookup_other _ "qhat" "ujn1" _ (by decide)).trans middleCell
  have highRead : entered.locals.lookup (ofString "vtop")=some (.val (.word divisorHigh)):=
    (bind_lookup_other _ "qhat" "vtop" _ (by decide)).trans highCell
  have qRead : entered.locals.lookup (ofString "qhat")=some (.val (.word 4294967295#64)):=bind_lookup_same _ _ _
  have rRead : entered.locals.lookup (ofString "rhat")=some (.val (.word 0#64)):=
    (bind_lookup_other _ "qhat" "rhat" _ (by decide)).trans rhat
  have remainderRead : eval entered remainderExpression=some (.val (.word (maxRemainder top middle divisorHigh))):=by
    simp [eval,remainderExpression,maxRemainder,localVar,evalHOLExact,evalListHOLExact,toExact,topRead,middleRead,highRead,qRead,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,OrOp.or]
  rw [maximum,evaluateHOLFiniteState_seq_line780,StateSteps.assign_execute source "qhat" (.const 4294967295#64) 0#64 4294967295#64 qhat rfl]
  simpa only [post,Nat.sub_zero] using StateSteps.assign_execute entered "rhat" remainderExpression 0#64 _ rRead remainderRead

private theorem updates_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r : BitVec 64)
    (qhat : source.locals.lookup (ofString "qhat")=some (.val (.word 0#64)))
    (rhat : source.locals.lookup (ofString "rhat")=some (.val (.word 0#64)))
    (qr : source.locals.lookup (ofString "qr")=some (pairValue q r)) :
    evaluateHOLFiniteState source updates=(none,bind (bind source "qhat" q) "rhat" r) := by
  have qRead : eval source (.rfield 0 (localVar "qr"))=some (.val (.word q)):=by
    simp [eval,localVar,evalHOLExact,toExact,qr,pairValue]
  let entered:=bind source "qhat" q
  have qrNext : entered.locals.lookup (ofString "qr")=some (pairValue q r):=
    (bind_lookup_other _ "qhat" "qr" _ (by decide)).trans qr
  have rNext : entered.locals.lookup (ofString "rhat")=some (.val (.word 0#64)):=
    (bind_lookup_other _ "qhat" "rhat" _ (by decide)).trans rhat
  have rRead : eval entered (.rfield 1 (localVar "qr"))=some (.val (.word r)):=by
    simp [eval,localVar,evalHOLExact,toExact,qrNext,pairValue]
  rw [updates,evaluateHOLFiniteState_seq_line780,StateSteps.assign_execute source "qhat" _ 0#64 q qhat qRead]
  exact StateSteps.assign_execute entered "rhat" _ 0#64 r rNext rRead

private theorem restore_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (value : ValueHOL 64) :
    restore source name (setVarHOLFinite (ofString name) value source)=source := by
  dsimp only [restore,setVarHOLFinite]
  congr 1
  apply HolFiniteMapExact.ext
  funext query
  cases old : source.locals.lookup (ofString name) <;> by_cases atName : query=ofString name
  all_goals first
    | subst query
      simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.update,HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq,FUPDATE,FUPDATE_HOL,FDOMSUB_HOL,old]
    | simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.update,HolFiniteMapExact.updateEq,
        HolFiniteMapExact.eraseEq,FUPDATE,FUPDATE_HOL,FDOMSUB_HOL,old,atName,Ne.symm atName]

private theorem scalar_restored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r : BitVec 64) :
    restore source "qr" (bind (bind (setVarHOLFinite (ofString "qr") (pairValue q r) {source with clock:=source.clock-33}) "qhat" q) "rhat" r)=post source q r 33 := by
  rw [restore_bind_other _ _ "qr" "rhat" _ (by decide),restore_bind_other _ _ "qr" "qhat" _ (by decide)]
  have saved : restore source "qr" (setVarHOLFinite (ofString "qr") (pairValue q r) {source with clock:=source.clock-33})={source with clock:=source.clock-33}:=
    restore_value {source with clock:=source.clock-33} "qr" (pairValue q r)
  rw [saved]
  rfl

/-- The original scoped scalar estimate calls the checked32-round divider,
assigns both actual returned words and restores the real qr binding. -/
theorem scalar_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (top middle divisorHigh : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (topCell : source.locals.lookup (ofString "ujn")=some (.val (.word top)))
    (middleCell : source.locals.lookup (ofString "ujn1")=some (.val (.word middle)))
    (highCell : source.locals.lookup (ofString "vtop")=some (.val (.word divisorHigh)))
    (qhat : source.locals.lookup (ofString "qhat")=some (.val (.word 0#64)))
    (rhat : source.locals.lookup (ofString "rhat")=some (.val (.word 0#64)))
    (divisorSmall : divisorHigh.toNat<4294967296) (highSmall : top.toNat<divisorHigh.toNat) (middleSmall : middle.toNat<4294967296)
    (enough : 33≤source.clock) :
    ∃ q r,q.toNat=(top.toNat*4294967296+middle.toNat)/divisorHigh.toNat ∧
      r.toNat=(top.toNat*4294967296+middle.toNat)%divisorHigh.toNat ∧ q.toNat<4294967296 ∧ r.toNat<divisorHigh.toNat ∧
      evaluateHOLFiniteState source scalar=(none,post source q r 33) := by
  have args:=arguments_read source top middle divisorHigh topCell middleCell highCell
  obtain ⟨q,r,quotient,remainder,qSmall,rSmall,actual⟩:=Div64By32.call_execute source top middle divisorHigh "qr" arguments updates
    installed args divisorSmall highSmall middleSmall enough
  let entered:=setVarHOLFinite (ofString "qr") (pairValue q r) {source with clock:=source.clock-33}
  have qZero : entered.locals.lookup (ofString "qhat")=some (.val (.word 0#64)):=
    (Single.tuple_lookup_other _ "qhat" q r (by decide)).trans qhat
  have rZero : entered.locals.lookup (ofString "rhat")=some (.val (.word 0#64)):=
    (Single.tuple_lookup_other _ "rhat" q r (by decide)).trans rhat
  have updatesRun:=updates_execute entered q r qZero rZero (Single.tuple_lookup_same _ q r)
  refine ⟨q,r,quotient,remainder,qSmall,rSmall,?_⟩
  rw [scalar,actual]
  change (let output:=evaluateHOLFiniteState entered updates;(output.1,restore source "qr" output.2))=_
  rw [updatesRun]
  dsimp only
  rw [scalar_restored]

end InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.literal_program
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.maximum_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.scalar_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual normal scoped estimate derives its own33ticks and actual two
returned digits before assigning and restoring the caller's qr scope. -/
theorem scalar_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (top middle divisorHigh : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (topCell : source.locals.lookup (ofString "ujn")=some (.val (.word top)))
    (middleCell : source.locals.lookup (ofString "ujn1")=some (.val (.word middle)))
    (highCell : source.locals.lookup (ofString "vtop")=some (.val (.word divisorHigh)))
    (qhat : source.locals.lookup (ofString "qhat")=some (.val (.word 0#64)))
    (rhat : source.locals.lookup (ofString "rhat")=some (.val (.word 0#64)))
    (divisorSmall : divisorHigh.toNat<4294967296) (highSmall : top.toNat<divisorHigh.toNat) (middleSmall : middle.toNat<4294967296)
    (normal : evaluateHOLFiniteState source scalar=(none,target)) :
    ∃ q r,33≤source.clock ∧ q.toNat=(top.toNat*4294967296+middle.toNat)/divisorHigh.toNat ∧
      r.toNat=(top.toNat*4294967296+middle.toNat)%divisorHigh.toNat ∧ q.toNat<4294967296 ∧ r.toNat<divisorHigh.toNat ∧
      target=post source q r 33 := by
  have args:=arguments_read source top middle divisorHigh topCell middleCell highCell
  obtain ⟨callee,called,highLocal,middleLocal,divisorLocal⟩:=word_triple_environment source.code.lookup (ofString "div64by32")
    (ofString "hi") (ofString "lo") (ofString "d") Div64By32.body returnShape top middle divisorHigh (by decide) (by decide) (by decide)
    (Div64By32.original_code source.code installed)
  obtain ⟨positive,calleePost,returned,inner,bodyRun,shape,remaining,endpoint⟩:=CallNormal.scoped_none source target "qr" returnShape (ofString "div64by32")
    arguments _ Div64By32.body updates callee returnShape args called normal
  obtain ⟨q,r,value,paid,quotient,remainder,qSmall,rSmall,canonical⟩:=Div64By32.resume source calleePost "qr" top middle divisorHigh
    installed divisorSmall highSmall middleSmall Div64By32.body callee returnShape called returned bodyRun
  rw [canonical] at remaining
  let entered:=setVarHOLFinite (ofString "qr") (pairValue q r) {source with clock:=source.clock-33}
  have qZero : entered.locals.lookup (ofString "qhat")=some (.val (.word 0#64)):=
    (Single.tuple_lookup_other _ "qhat" q r (by decide)).trans qhat
  have rZero : entered.locals.lookup (ofString "rhat")=some (.val (.word 0#64)):=
    (Single.tuple_lookup_other _ "rhat" q r (by decide)).trans rhat
  have expected:=updates_execute entered q r qZero rZero (Single.tuple_lookup_same _ q r)
  have innerEq : inner=bind (bind entered "qhat" q) "rhat" r:=congrArg Prod.snd (remaining.symm.trans expected)
  rw [innerEq,scalar_restored] at endpoint
  exact ⟨q,r,paid,quotient,remainder,qSmall,rSmall,endpoint⟩

/-- Both real branches include every stopped/short-clock outcome. -/
theorem program_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Entry source base position low middle top divisorLow divisorHigh) :
    source.clock-(evaluateHOLFiniteState source program).2.clock≤33 := by
  have tested:=test_read source top divisorHigh checked.window.ujn checked.highCell
  simp only [eval] at tested
  rw [program,evaluateHOLFiniteState_ite,tested]
  by_cases take : divisorHigh.toNat≤top.toNat
  · rw [if_pos take]
    simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)]
    rw [maximum_execute source top middle divisorHigh checked.window.ujn checked.middleCell checked.highCell checked.qhat checked.rhat]
    change source.clock-(source.clock-0)≤33
    omega
  · rw [if_neg take]
    simp only [if_pos (show (0#64 : BitVec 64)=0 by rfl)]
    have updatesBound : ClockCost.Bound source.code updates 0:=ClockCost.sequence source.code _ _ 0 0 (ClockCost.assign source.code _ _) (ClockCost.assign source.code _ _)
    exact Div64By32.call_cost source top middle divisorHigh "qr" arguments updates 0 checked.installed
      (arguments_read source top middle divisorHigh checked.window.ujn checked.middleCell checked.highCell) updatesBound

/-- Actual normal estimate returns supply conservation and an upper estimate
for the three-digit/two-digit window, with no future correction premise. -/
theorem program_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Entry source base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source program=(none,target)) :
    ∃ q r paid,paid≤33 ∧ paid≤source.clock ∧ target=post source q r paid ∧ q.toNat<4294967296 ∧
      q.toNat*divisorHigh.toNat+r.toNat=top.toNat*4294967296+middle.toNat ∧
      TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh≤q.toNat := by
  have tested:=test_read source top divisorHigh checked.window.ujn checked.highCell
  simp only [eval] at tested
  rw [program,evaluateHOLFiniteState_ite,tested] at normal
  by_cases take : divisorHigh.toNat≤top.toNat
  · rw [if_pos take] at normal
    simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)] at normal
    have expected:=maximum_execute source top middle divisorHigh checked.window.ujn checked.middleCell checked.highCell checked.qhat checked.rhat
    have endpoint:=congrArg Prod.snd (normal.symm.trans expected)
    have range : (top.toNat*4294967296+middle.toNat)*4294967296+low.toNat<
        (divisorHigh.toNat*4294967296+divisorLow.toNat)*4294967296:=by
      have bound:=checked.digitRange
      unfold TwoDigitSubtract.window TwoDigitSubtract.divisorNumber at bound
      omega
    obtain ⟨balance,upper⟩:=QhatCorrection.max_initial_upper top middle low divisorHigh divisorLow checked.topSmall checked.window.middleSmall checked.window.divisorHighSmall take range
    change 4294967295*divisorHigh.toNat+(maxRemainder top middle divisorHigh).toNat=top.toNat*4294967296+middle.toNat at balance
    have numerator : (4294967295*divisorHigh.toNat+(maxRemainder top middle divisorHigh).toNat)*4294967296+low.toNat=TwoDigitSubtract.window low middle top:=by
      rw [balance]
      unfold TwoDigitSubtract.window
      ring
    have denominator : divisorHigh.toNat*4294967296+divisorLow.toNat=TwoDigitSubtract.divisorNumber divisorLow divisorHigh:=by
      unfold TwoDigitSubtract.divisorNumber
      ring
    change ((4294967295*divisorHigh.toNat+(maxRemainder top middle divisorHigh).toNat)*4294967296+low.toNat)/
      (divisorHigh.toNat*4294967296+divisorLow.toNat)≤4294967295 at upper
    rw [numerator,denominator] at upper
    exact ⟨4294967295#64,maxRemainder top middle divisorHigh,0,by omega,by omega,endpoint,by decide,balance,upper⟩
  · rw [if_neg take] at normal
    simp only [if_pos (show (0#64 : BitVec 64)=0 by rfl)] at normal
    obtain ⟨q,r,paid,quotient,remainder,qSmall,rSmall,endpoint⟩:=scalar_normal source target top middle divisorHigh checked.installed
      checked.window.ujn checked.middleCell checked.highCell checked.qhat checked.rhat checked.window.divisorHighSmall (by omega) checked.window.middleSmall normal
    have split:=Nat.mod_add_div (top.toNat*4294967296+middle.toNat) divisorHigh.toNat
    rw [←quotient,←remainder,Nat.mul_comm divisorHigh.toNat q.toNat] at split
    have balance : q.toNat*divisorHigh.toNat+r.toNat=top.toNat*4294967296+middle.toNat:=by omega
    have upper:=QhatCorrection.initial_upper q r divisorHigh divisorLow low rSmall checked.window.lowSmall
    have numerator : (q.toNat*divisorHigh.toNat+r.toNat)*4294967296+low.toNat=TwoDigitSubtract.window low middle top:=by
      rw [balance]
      unfold TwoDigitSubtract.window
      ring
    have denominator : divisorHigh.toNat*4294967296+divisorLow.toNat=TwoDigitSubtract.divisorNumber divisorLow divisorHigh:=by
      unfold TwoDigitSubtract.divisorNumber
      ring
    rw [numerator,denominator] at upper
    exact ⟨q,r,33,by omega,paid,endpoint,qSmall,balance,upper⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.scalar_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.program_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.program_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem Window.bind_estimate {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {position : Nat}
    {low middle top divisorLow divisorHigh : BitVec 64} (checked : Window source base position low middle top divisorLow divisorHigh)
    (name : String) (word : BitVec 64) (allowed : name="qhat" ∨ name="rhat" ∨ name="again") :
    Window (bind source name word) base position low middle top divisorLow divisorHigh := by
  rcases allowed with rfl|rfl|rfl <;>
    refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
      checked.inside,?_,?_,?_,?_,?_,?_,?_,checked.lowCell,checked.middleCell,checked.topCell,
      checked.divisorLowCell,checked.divisorHighCell,checked.lowSmall,checked.middleSmall,
      checked.divisorLowSmall,checked.divisorHighSmall,checked.divisorHighLarge⟩ <;>
    first
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.un
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.vn
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.q
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.j
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.n
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.ujn
    | obtain ⟨old,cell⟩:=checked.i
      exact ⟨old,(bind_lookup_other _ _ _ _ (by decide)).trans cell⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem post_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r : BitVec 64) (paid : Nat) (name : String)
    (notQ : ofString name≠ofString "qhat") (notR : ofString name≠ofString "rhat") :
    (post source q r paid).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "rhat" name _ (Ne.symm notR)).trans (bind_lookup_other _ "qhat" name _ (Ne.symm notQ))

def afterEstimate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r : BitVec 64) (paid : Nat) :=bind (post source q r paid) "again" 1#64

private theorem entry_after_estimate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Entry source base position low middle top divisorLow divisorHigh) (q r : BitVec 64) (paid : Nat) :
    Subtract.Window (afterEstimate source q r paid) base position low middle top divisorLow divisorHigh ∧
      QhatCorrection.Bindings (afterEstimate source q r paid) q r 1#64 divisorHigh divisorLow low := by
  have window : Subtract.Window (afterEstimate source q r paid) base position low middle top divisorLow divisorHigh:=
    (((checked.window.withClock (source.clock-paid)).bind_estimate "qhat" q (Or.inl rfl)).bind_estimate "rhat" r (Or.inr (Or.inl rfl))).bind_estimate "again" 1#64 (Or.inr (Or.inr rfl))
  refine ⟨window,?_,?_,bind_lookup_same _ _ _,?_,?_,?_⟩
  · exact (bind_lookup_other _ "again" "qhat" _ (by decide)).trans
      ((bind_lookup_other _ "rhat" "qhat" _ (by decide)).trans (bind_lookup_same _ _ _))
  · exact (bind_lookup_other _ "again" "rhat" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact (bind_lookup_other _ "again" "vtop" _ (by decide)).trans
      ((post_other source q r paid "vtop" (by decide) (by decide)).trans checked.highCell)
  · exact (bind_lookup_other _ "again" "vsec" _ (by decide)).trans
      ((post_other source q r paid "vsec" (by decide) (by decide)).trans checked.secondCell)
  · exact (bind_lookup_other _ "again" "ujn2" _ (by decide)).trans
      ((post_other source q r paid "ujn2" (by decide) (by decide)).trans checked.lowCell)

def continuation : ProgHOL 64:=.dec (ofString "again") .one (.const 1#64) Subtract.corrected
def phase : ProgHOL 64:=.seq program continuation

private def findPhase : ProgHOL 64→Option (ProgHOL 64)
  | .seq (.ite condition yes no) rest=>
    match condition with
    | .cmp .notLower (.var .local high) (.var .local divisor)=>
      if high=ofString "ujn" ∧ divisor=ofString "vtop" then some (.seq (.ite condition yes no) rest)
      else ((findPhase yes).orElse (fun _=>findPhase no)).orElse (fun _=>findPhase rest)
    | _=>((findPhase yes).orElse (fun _=>findPhase no)).orElse (fun _=>findPhase rest)
  | .dec _ _ _ rest=>findPhase rest
  | .seq first rest=>(findPhase first).orElse (fun _=>findPhase rest)
  | .ite _ yes no=>(findPhase yes).orElse (fun _=>findPhase no)
  | .while _ contents=>findPhase contents
  | .decCall _ _ _ _ rest=>findPhase rest
  | _=>none

set_option maxRecDepth 100000 in
/-- The original estimate followed by its real again/correction/subtraction scope. -/
theorem literal_phase : findPhase Single.body=some phase := by
  simp [findPhase,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    phase,program,test,maximum,remainderExpression,scalar,arguments,updates,returnShape,continuation,
    Subtract.corrected,QhatCorrection.loop,QhatCorrection.test,QhatCorrection.body,QhatCorrection.branch,QhatCorrection.correct,
    QhatCorrection.roomTest,QhatCorrection.estimateTest,QhatCorrection.leftEstimate,QhatCorrection.rightEstimate,
    QhatCorrection.quotientExpression,QhatCorrection.remainderExpression,Subtract.initialized,Subtract.loop,Subtract.test,Subtract.step,Subtract.updates,
    Subtract.productExpression,Subtract.residualExpression,Subtract.lowExpression,Subtract.carryExpression,Subtract.increment,Subtract.inputAddress,Subtract.divisorAddress,
    Subtract.finish,Subtract.findFinish,Subtract.topAddress,Subtract.quotientAddress,Subtract.address,Subtract.difference,Subtract.negativeTest,Subtract.keep,localVar]

/-- Complete original per-digit estimate/correction/subtraction/stores,
including every stopped outcome and every short-clock prefix. -/
theorem phase_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Entry source base position low middle top divisorLow divisorHigh) :
    source.clock-(evaluateHOLFiniteState source phase).2.clock≤38 := by
  have front:=program_cost source base position low middle top divisorLow divisorHigh checked
  have forward:=evaluateHOLFiniteState_clock_le source program
  rw [phase,evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source program=output at front forward ⊢
  obtain ⟨result,middleState⟩:=output
  cases result with
  | none=>
    obtain ⟨q,r,paid,price,funded,endpoint,qSmall,balance,upper⟩:=program_normal source middleState base position low middle top divisorLow divisorHigh checked computed
    subst middleState
    obtain ⟨window,ready⟩:=entry_after_estimate source base position low middle top divisorLow divisorHigh checked q r paid
    have correctedCost:=Subtract.corrected_cost (afterEstimate source q r paid) base position q r low middle top divisorLow divisorHigh window ready qSmall balance upper
    have back:=ClockCost.declared_current (post source q r paid) "again" (.const 1#64) 1#64 Subtract.corrected 5 rfl correctedCost
    change (source.clock-paid)-(evaluateHOLFiniteState (post source q r paid) continuation).2.clock≤5 at back
    have lastForward:=evaluateHOLFiniteState_clock_le (post source q r paid) continuation
    change source.clock-(evaluateHOLFiniteState (post source q r paid) continuation).2.clock≤38
    change source.clock-(post source q r paid).clock≤33 at front
    change (post source q r paid).clock≤source.clock at forward
    omega
  | some result=>
    change source.clock-middleState.clock≤38
    change source.clock-middleState.clock≤33 at front
    omega

/-- A genuine normal original digit phase derives the exact quotient,
remainder and four real stores without assuming a future helper result. -/
theorem phase_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Entry source base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source phase=(none,target)) :
    ∃ quotient,quotient.toNat<4294967296 ∧
      quotient.toNat=TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
      (TwoDigitSubtract.firstLow low quotient divisorLow).toNat+4294967296*(TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh).toNat=
        TwoDigitSubtract.window low middle top%TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
      target.memory=Subtract.digitMemory source.memory base position quotient low middle divisorLow divisorHigh ∧
      target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock} ∧
      source.clock-target.clock≤38 := by
  obtain ⟨middleState,front,back⟩:=sequence_none source target program continuation normal
  obtain ⟨q,r,paid,price,funded,endpoint,qSmall,balance,upper⟩:=program_normal source middleState base position low middle top divisorLow divisorHigh checked front
  subst middleState
  obtain ⟨window,ready⟩:=entry_after_estimate source base position low middle top divisorLow divisorHigh checked q r paid
  obtain ⟨inner,remaining,restored⟩:=ScalarScope.declare_trace (post source q r paid) target "again" (.const 1#64) 1#64 Subtract.corrected none rfl back
  obtain ⟨quotient,quotientSmall,quotientNumber,remainder,written,static,cost⟩:=Subtract.corrected_normal (afterEstimate source q r paid) inner base position q r low middle top divisorLow divisorHigh
    window ready qSmall balance upper remaining
  have targetMemory : target.memory=Subtract.digitMemory source.memory base position quotient low middle divisorLow divisorHigh:=by
    rw [restored]
    exact written
  have targetStatic : target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock}:=by
    rw [restored]
    have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
      {state with
        locals:=(restore (post source q r paid) "again" inner).locals,
        memory:=(restore (post source q r paid) "again" inner).memory,
        clock:=(restore (post source q r paid) "again" inner).clock}) static
    exact projected
  have totalCost:=phase_cost source base position low middle top divisorLow divisorHigh checked
  rw [normal] at totalCost
  exact ⟨quotient,quotientSmall,quotientNumber,remainder,targetMemory,targetStatic,totalCost⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.literal_phase
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.phase_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.phase_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The four actual stores retain both low remainder cells, the quotient
digit and the zero top word. Actual workspace geometry proves nonaliasing. -/
theorem digitMemory_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) (context : Workspace.Context source base) (inside : position+2<17) :
    digitMemory source.memory base position quotient low middle divisorLow divisorHigh (slot (Workspace.pointer base .normalizedNumerator) (0+position))=
      .word (TwoDigitSubtract.firstLow low quotient divisorLow) ∧
    digitMemory source.memory base position quotient low middle divisorLow divisorHigh (slot (Workspace.pointer base .normalizedNumerator) (1+position))=
      .word (TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh) ∧
    digitMemory source.memory base position quotient low middle divisorLow divisorHigh (slot (Workspace.pointer base .quotient) position)=.word quotient ∧
    digitMemory source.memory base position quotient low middle divisorLow divisorHigh (slot (Workspace.pointer base .normalizedNumerator) (position+2))=.word 0#64 := by
  have lowTop:=slots_different source base context (0+position) (position+2) (by omega) inside (by omega)
  have lowMiddle:=slots_different source base context (0+position) (1+position) (by omega) (by omega) (by omega)
  have middleTop:=slots_different source base context (1+position) (position+2) (by omega) inside (by omega)
  have lowQ:=Workspace.separate base .normalizedNumerator .quotient (by intro same;cases same) (0+position) position (by change 0+position<17;omega) (by change position<16;omega)
  have middleQ:=Workspace.separate base .normalizedNumerator .quotient (by intro same;cases same) (1+position) position (by change 1+position<17;omega) (by change position<16;omega)
  have qTop:=Workspace.separate base .quotient .normalizedNumerator (by intro same;cases same) position (position+2) (by change position<16;omega) inside
  refine ⟨?_,?_,?_,?_⟩
  · simp only [digitMemory,StoreWord.put,if_neg lowTop,if_neg lowQ,if_neg lowMiddle,if_pos rfl,ite_true]
  · simp only [digitMemory,StoreWord.put,if_neg middleTop,if_neg middleQ,if_pos rfl,ite_true]
  · simp only [digitMemory,StoreWord.put,if_neg qTop,if_pos rfl,ite_true]
  · simp only [digitMemory,StoreWord.put,if_pos rfl,ite_true]

/-- Every word outside the four real digit stores is unchanged. -/
theorem digitMemory_away (memory : BitVec 64→HolWordLab 64) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh query : BitVec 64)
    (outsideLow : query≠slot (Workspace.pointer base .normalizedNumerator) (0+position))
    (outsideMiddle : query≠slot (Workspace.pointer base .normalizedNumerator) (1+position))
    (outsideQ : query≠slot (Workspace.pointer base .quotient) position)
    (outsideTop : query≠slot (Workspace.pointer base .normalizedNumerator) (position+2)) :
    digitMemory memory base position quotient low middle divisorLow divisorHigh query=memory query := by
  simp only [digitMemory,StoreWord.put,if_neg outsideTop,if_neg outsideQ,if_neg outsideMiddle,if_neg outsideLow]

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.digitMemory_cells
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.digitMemory_away

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Normalized
open Flapjack

def incoming (contents : Nat→BitVec 64) (bits : Nat) : Nat→BitVec 64
  | 0=>0#64
  | count+1=>Normalize.high (contents count) bits

def digit (contents : Nat→BitVec 64) (bits : Nat) : Nat→BitVec 64
  | 0=>Normalize.first (contents 0) bits
  | index+1=>Normalize.digit (contents (index+1)) (contents index) bits

def extended (contents : Nat→BitVec 64) (bits length index : Nat) : BitVec 64:=
  if index<length then digit contents bits index else incoming contents bits length

/-- The actual incoming carry and actual normalized digit conserve one
source digit, including the original separate first-word store. -/
private theorem digit_balance (contents : Nat→BitVec 64) (bits index : Nat) (bitsSmall : bits≤31)
    (small : ∀ current,current≤index→(contents current).toNat<4294967296) :
    (digit contents bits index).toNat<4294967296 ∧
      (digit contents bits index).toNat+4294967296*(incoming contents bits (index+1)).toNat=
        (contents index).toNat*2^bits+(incoming contents bits index).toNat := by
  cases index with
  | zero=>
    simpa only [digit,incoming,BitVec.toNat_zero,Nat.add_zero] using Normalize.first_balance (contents 0) bits bitsSmall (small 0 (by omega))
  | succ index=>
    exact Normalize.digit_balance (contents (index+1)) (contents index) bits bitsSmall (small (index+1) (by omega)) (small index (by omega))

/-- Telescoping the actual32-bit carry equations proves that a normalized
prefix plus its outgoing carry is exactly the original prefix times2^s. -/
theorem prefix_number (contents : Nat→BitVec 64) (bits count : Nat) (bitsSmall : bits≤31)
    (small : ∀ index,index<count→(contents index).toNat<4294967296) :
    number (digit contents bits) count+2^(32*count)*(incoming contents bits count).toNat=
      number contents count*2^bits := by
  induction count with
  | zero=>simp [number,incoming]
  | succ count ih=>
    have prior:=ih (by intro index inside;exact small index (by omega))
    have step:=digit_balance contents bits count bitsSmall (by intro index inside;exact small index (by omega))
    have power : 2^(32*(count+1))=2^(32*count)*4294967296:=by
      rw [Nat.mul_add,Nat.mul_one,Nat.pow_add]
    rw [number,number,power]
    calc
      _=number (digit contents bits) count+2^(32*count)*
          ((digit contents bits count).toNat+4294967296*(incoming contents bits (count+1)).toNat):=by ring
      _=number (digit contents bits) count+2^(32*count)*
          ((contents count).toNat*2^bits+(incoming contents bits count).toNat):=by rw [step.2]
      _=(number (digit contents bits) count+2^(32*count)*(incoming contents bits count).toNat)+
          2^(32*count)*(contents count).toNat*2^bits:=by ring
      _=number contents count*2^bits+2^(32*count)*(contents count).toNat*2^bits:=by rw [prior]
      _=_:=by ring

/-- The seventeenth possible normalized numerator word is the real outgoing
carry, not an assumed zero. The complete array represents U*2^s exactly. -/
theorem extended_number (contents : Nat→BitVec 64) (bits length : Nat) (bitsSmall : bits≤31)
    (small : ∀ index,index<length→(contents index).toNat<4294967296) :
    number (extended contents bits length) (length+1)=number contents length*2^bits := by
  have prefixEq : number (extended contents bits length) length=number (digit contents bits) length:=
    Single.number_congr _ _ length (by intro index inside;exact if_pos inside)
  rw [number,prefixEq]
  have last : extended contents bits length length=incoming contents bits length:=by simp [extended]
  rw [last]
  exact prefix_number contents bits length bitsSmall small

/-- Every actually normalized word, including the extra numerator carry,
is a32-bit digit. -/
theorem extended_small (contents : Nat→BitVec 64) (bits length index : Nat) (bitsSmall : bits≤31)
    (small : ∀ current,current<length→(contents current).toNat<4294967296) (inside : index≤length) :
    (extended contents bits length index).toNat<4294967296 := by
  by_cases ordinary : index<length
  · rw [extended,if_pos ordinary]
    exact (digit_balance contents bits index bitsSmall (by intro current bound;exact small current (by omega))).1
  · have last : index=length:=by omega
    subst index
    rw [extended,if_neg (by omega)]
    cases length with
    | zero=>
      change (0#64 : BitVec 64).toNat<4294967296
      decide
    | succ length=>
      have high:=Normalize.high_bound (contents length) bits bitsSmall (small length (by omega))
      have factorBound : 2^bits≤2147483648:=Nat.pow_le_pow_right (by decide) bitsSmall
      change (Normalize.high (contents length) bits).toNat<4294967296
      omega

/-- The real nlz32 upper bound removes the divisor's outgoing carry, so its
stored n-word normalized image already represents D*2^s exactly. -/
theorem divisor_number (contents : Nat→BitVec 64) (bits length : Nat) (bitsSmall : bits≤31) (positive : 0<length)
    (small : ∀ index,index<length→(contents index).toNat<4294967296)
    (leading : (contents (length-1)).toNat*2^bits<4294967296) :
    number (digit contents bits) length=number contents length*2^bits := by
  have noCarry : incoming contents bits length=0#64:=by
    cases length with
    | zero=>omega
    | succ length=>
      exact Normalize.high_zero (contents length) bits bitsSmall (by simpa only [Nat.add_sub_cancel] using leading)
  have total:=prefix_number contents bits length bitsSmall small
  rw [noCarry,BitVec.toNat_zero,Nat.mul_zero,Nat.add_zero] at total
  exact total

end InitECandidate.Solver.Input.UDivMod.WideDigits.Normalized

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalized.prefix_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalized.extended_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalized.extended_small
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalized.divisor_number

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def previous : ExpHOL 64:=.op .sub [localVar "i",.const 1#64]
def remaining : ExpHOL 64:=.op .sub [.const 32#64,localVar "s"]
def address (name : String) (index : ExpHOL 64) : ExpHOL 64:=.op .add [localVar name,.panop .mul [index,.const 8#64]]
def expression (input : String) : ExpHOL 64:=.op .and [
  .op .or [.shift .lsl (.load .one (address input (localVar "i"))) (localVar "s"),
    .shift .lsr (.load .one (address input previous)) remaining],.const 4294967295#64]
def body (input output : String) : ProgHOL 64:=.seq (.store (address output (localVar "i")) (expression input))
  (.assign .local (ofString "i") previous)
def test : ExpHOL 64:=.cmp .lower (.const 0#64) (localVar "i")
def loop (input output : String) : ProgHOL 64:=.while test (body input output)

private def findLoop (wanted : MlS) : ProgHOL 64→Option (ProgHOL 64)
  | .while condition contents=>
    match condition,contents with
    | .cmp .lower (.const zero) (.var .local index),.seq (.store (.op .add [.var .local name,offset]) value) rest=>
      if zero=0#64 ∧ index=ofString "i" ∧ name=wanted then some (.while condition contents) else findLoop wanted contents
    | _,_=>findLoop wanted contents
  | .dec _ _ _ rest=>findLoop wanted rest
  | .seq first rest=>(findLoop wanted first).orElse (fun _=>findLoop wanted rest)
  | .ite _ yes no=>(findLoop wanted yes).orElse (fun _=>findLoop wanted no)
  | .decCall _ _ _ _ rest=>findLoop wanted rest
  | _=>none

set_option maxRecDepth 100000 in
theorem divisor_literal : findLoop (ofString "vn") Single.body=some (loop "v" "vn") := by
  simp [findLoop,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    loop,test,body,expression,address,previous,remaining,localVar]

set_option maxRecDepth 100000 in
theorem numerator_literal : findLoop (ofString "un") Single.body=some (loop "u" "un") := by
  have different : ofString "vn"≠ofString "un":=by decide
  simp [findLoop,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    loop,test,body,expression,address,previous,remaining,localVar,different]

structure Buffers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input output : BitVec 64) (contents : Nat→BitVec 64) (length : Nat) : Prop where
  small : length≤16
  image : Image source input contents length
  inputMapped : ∀ index,index<length→source.memaddrs (slot input index)
  outputMapped : ∀ index,index<length→source.memaddrs (slot output index)
  separate : ∀ inputIndex,inputIndex<length→∀ outputIndex,outputIndex<length→slot input inputIndex≠slot output outputIndex

structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits index : Nat) : Prop where
  buffers : Buffers source input output contents length
  inside : index<length
  bitsSmall : bits≤31
  inputCell : source.locals.lookup (ofString inputName)=some (.val (.word input))
  outputCell : source.locals.lookup (ofString outputName)=some (.val (.word output))
  s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits)))
  i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  notInput : ofString "i"≠ofString inputName
  notOutput : ofString "i"≠ofString outputName

private theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64) (index : Nat)
    (cell : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source (address name (localVar "i"))=some (.val (.word (slot pointer index))) := by
  simp [eval,address,localVar,evalHOLExact,evalListHOLExact,toExact,cell,i,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,Nat.mul_comm]

private theorem previous_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (positive : 0<index)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source previous=some (.val (.word (BitVec.ofNat 64 (index-1)))) := by
  have difference:=BitVec.ofNat_sub_ofNat_of_le (w:=64) index 1 (by decide) positive
  simp [eval,previous,localVar,evalHOLExact,evalListHOLExact,toExact,i,valueIsWord,valueWord,wordOpHOL,wordOp,difference]

private theorem previous_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64) (index : Nat) (positive : 0<index)
    (cell : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source (address name previous)=some (.val (.word (slot pointer (index-1)))) := by
  have prev:=previous_read source index positive i
  simp only [eval] at prev
  simp [eval,address,localVar,evalHOLExact,evalListHOLExact,toExact,cell,prev,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,Nat.mul_comm]

private theorem remaining_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bits : Nat) (small : bits≤31)
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits)))) :
    eval source remaining=some (.val (.word (BitVec.ofNat 64 (32-bits)))) := by
  have difference:=BitVec.ofNat_sub_ofNat_of_le (w:=64) 32 bits (by omega) (by omega)
  simp [eval,remaining,localVar,evalHOLExact,evalListHOLExact,toExact,s,valueIsWord,valueWord,wordOpHOL,wordOp,difference]

private theorem shift_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (operator : Shift) (value amount : ExpHOL 64) (word shift result : BitVec 64)
    (readValue : eval source value=some (.val (.word word))) (readAmount : eval source amount=some (.val (.word shift)))
    (computed : wordShiftHOL operator word shift.toNat=some result) :
    eval source (.shift operator value amount)=some (.val (.word result)) := by
  simp only [eval] at readValue readAmount ⊢
  rw [evalHOLExact]
  simp [readValue,readAmount,computed]

private theorem expression_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits index : Nat) (checked : Entry source inputName outputName input output contents length bits index) (positive : 0<index) :
    eval source (expression inputName)=some (.val (.word (Normalized.digit contents bits index))) := by
  have current:=Witness.load_word_read source (address inputName (localVar "i")) _ (contents index)
    (address_read source inputName input index checked.inputCell checked.i) (checked.buffers.inputMapped index checked.inside) (checked.buffers.image index checked.inside)
  have previousInside : index-1<length:=by have inside:=checked.inside;omega
  have prev:=Witness.load_word_read source (address inputName previous) _ (contents (index-1))
    (previous_address_read source inputName input index positive checked.inputCell checked.i)
    (checked.buffers.inputMapped (index-1) previousInside) (checked.buffers.image (index-1) previousInside)
  have bitsNumber : (BitVec.ofNat 64 bits).toNat=bits:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=checked.bitsSmall;omega)]
  have restNumber : (BitVec.ofNat 64 (32-bits)).toNat=32-bits:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have left:=shift_read source .lsl (.load .one (address inputName (localVar "i"))) (localVar "s") (contents index) (BitVec.ofNat 64 bits) ((contents index)<<<bits)
    current (Subtract.local_read source "s" _ checked.s) (by simp [wordShiftHOL,bitsNumber,show bits<64 from by have small:=checked.bitsSmall;omega])
  have right:=shift_read source .lsr (.load .one (address inputName previous)) remaining (contents (index-1)) (BitVec.ofNat 64 (32-bits)) (Normalize.high (contents (index-1)) bits)
    prev (remaining_read source bits checked.bitsSmall checked.s) (by simp [wordShiftHOL,restNumber,Normalize.high,show 32-bits<64 from by omega])
  have joined:=Subtract.binary_read source .or _ _ _ _ (((contents index)<<<bits) ||| Normalize.high (contents (index-1)) bits) left right (by simp [wordOpHOL,wordOp,OrOp.or])
  have masked:=Subtract.binary_read source .and _ (.const 4294967295#64) _ 4294967295#64 (Normalize.digit (contents index) (contents (index-1)) bits) joined rfl rfl
  change eval source (expression inputName)=some (.val (.word (Normalize.digit (contents index) (contents (index-1)) bits))) at masked
  have same : Normalize.digit (contents index) (contents (index-1)) bits=Normalized.digit contents bits index:=by
    cases index with
    | zero=>omega
    | succ index=>rfl
  rw [←same]
  exact masked

def bodyPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits index : Nat) :=
  bind {source with memory:=StoreWord.put source.memory (slot pointer index) (Normalized.digit contents bits index)} "i" (BitVec.ofNat 64 (index-1))

/-- Exact original two-load, shift/or/mask/store and counter decrement. -/
theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits index : Nat) (checked : Entry source inputName outputName input output contents length bits index) (positive : 0<index) :
    evaluateHOLFiniteState source (body inputName outputName)=(none,bodyPost source output contents bits index) := by
  have stored:=StoreWord.execute source (address outputName (localVar "i")) (expression inputName) _ (Normalized.digit contents bits index)
    (address_read source outputName output index checked.outputCell checked.i) (expression_read source inputName outputName input output contents length bits index checked positive)
    (checked.buffers.outputMapped index checked.inside)
  rw [body,evaluateHOLFiniteState_seq_line780,stored]
  exact StateSteps.assign_execute _ "i" previous _ _ checked.i (previous_read _ index positive checked.i)

/-- The literal normalization step has no calls or inner loops. -/
theorem body_cost (code) (input output : String) : ClockCost.Bound code (body input output) 0 :=
  ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.assign code _ _)

end InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.divisor_literal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.numerator_literal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.body_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.body_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current allocated workspace geometry supplies actual input/output slots
and their separation; no future normalization run is assumed. -/
theorem workspace_buffers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : Workspace.Context source base) (input output : Workspace.Buffer) (different : input≠output)
    (contents : Nat→BitVec 64) (length : Nat) (small : length≤16)
    (inputInside : length≤Workspace.count input) (outputInside : length≤Workspace.count output)
    (image : Image source (Workspace.pointer base input) contents length) :
    Buffers source (Workspace.pointer base input) (Workspace.pointer base output) contents length := by
  refine ⟨small,image,?_,?_,?_⟩
  · intro index inside
    exact Workspace.slot_mapped source base context input index (by omega)
  · intro index inside
    exact Workspace.slot_mapped source base context output index (by omega)
  · intro inputIndex iInside outputIndex oInside
    exact Workspace.separate base input output different inputIndex outputIndex (by omega) (by omega)

private theorem Entry.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {inputName outputName : String} {input output : BitVec 64}
    {contents : Nat→BitVec 64} {length bits index : Nat} (checked : Entry source inputName outputName input output contents length bits index) (clock : Nat) :
    Entry {source with clock:=clock} inputName outputName input output contents length bits index :=
  ⟨⟨checked.buffers.small,checked.buffers.image,checked.buffers.inputMapped,checked.buffers.outputMapped,checked.buffers.separate⟩,
    checked.inside,checked.bitsSmall,checked.inputCell,checked.outputCell,checked.s,checked.i,checked.notInput,checked.notOutput⟩

private theorem Entry.next {source : PanSemStateFiniteExact 64 Guest.HostMemory} {inputName outputName : String} {input output : BitVec 64}
    {contents : Nat→BitVec 64} {length bits index : Nat} (checked : Entry source inputName outputName input output contents length bits index) :
    Entry (bodyPost source output contents bits index) inputName outputName input output contents length bits (index-1) := by
  refine ⟨⟨checked.buffers.small,?_,checked.buffers.inputMapped,checked.buffers.outputMapped,checked.buffers.separate⟩,
    by have inside:=checked.inside;omega,checked.bitsSmall,?_,?_,?_,bind_lookup_same _ _ _,checked.notInput,checked.notOutput⟩
  · intro current inside
    have separate:=checked.buffers.separate current inside index checked.inside
    simp only [bodyPost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,StoreWord.put,if_neg separate]
    exact checked.buffers.image current inside
  · exact (bind_lookup_other _ "i" inputName _ checked.notInput).trans checked.inputCell
  · exact (bind_lookup_other _ "i" outputName _ checked.notOutput).trans checked.outputCell
  · exact (bind_lookup_other _ "i" "s" _ (by decide)).trans checked.s

def memory (initial : BitVec 64→HolWordLab 64) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits index : Nat) : Nat→(BitVec 64→HolWordLab 64)
  | 0=>initial
  | rounds+1=>memory (StoreWord.put initial (slot pointer index) (Normalized.digit contents bits index)) pointer contents bits (index-1) rounds

def after (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits index : Nat) : Nat→PanSemStateFiniteExact 64 Guest.HostMemory
  | 0=>source
  | rounds+1=>after (bodyPost (decClockHOLFinite source) pointer contents bits index) pointer contents bits (index-1) rounds

theorem after_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits index rounds : Nat) :
    after source pointer contents bits index rounds={source with
      locals:=(after source pointer contents bits index rounds).locals,
      memory:=memory source.memory pointer contents bits index rounds,clock:=source.clock-rounds} := by
  induction rounds generalizing source index with
  | zero=>simp [after,memory]
  | succ rounds ih=>
    rw [after,ih]
    simp only [bodyPost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,decClockHOLFinite,memory]
    congr 1
    omega

theorem after_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits index rounds : Nat)
    (name : String) (notI : ofString "i"≠ofString name) :
    (after source pointer contents bits index rounds).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  induction rounds generalizing source index with
  | zero=>rfl
  | succ rounds ih=>
    rw [after,ih]
    exact bind_lookup_other _ "i" name _ notI

theorem after_index (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits index : Nat)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    (after source pointer contents bits index index).locals.lookup (ofString "i")=some (.val (.word 0#64)) := by
  induction index generalizing source with
  | zero=>exact i
  | succ index ih=>
    simp only [after,Nat.add_sub_cancel]
    exact ih _ (bind_lookup_same _ _ _)

private theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (small : index<16)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=
      some (.val (.word (if 0<index then 1#64 else 0#64))) := by
  have indexNumber : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [finite_eval]
  simp [eval,test,localVar,evalHOLExact,toExact,i,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,indexNumber]

/-- Complete original descending normalization loop with its final false
guard. Its input image is retained after every real output store. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits index : Nat) (checked : Entry source inputName outputName input output contents length bits index)
    (enough : index≤source.clock) :
    evaluateHOLFiniteState source (loop inputName outputName)=(none,after source output contents bits index index) := by
  induction index generalizing source with
  | zero=>
    have read:=test_read source 0 (by decide) checked.i
    simp only [Nat.lt_irrefl,ite_false] at read
    exact Subtract.while_done source test (body inputName outputName) read
  | succ index ih=>
    let next:=bodyPost (decClockHOLFinite source) output contents bits (index+1)
    have nextModel : Entry next inputName outputName input output contents length bits index:=(checked.withClock _).next
    have bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) (body inputName outputName)=(none,next):=
      body_execute (decClockHOLFinite source) inputName outputName input output contents length bits (index+1) (checked.withClock _) (by omega)
    have tailRun:=ih next nextModel (by change index≤source.clock-1;omega)
    have read:=test_read source (index+1) (by have a:=checked.inside;have b:=checked.buffers.small;omega) checked.i
    simp only [Nat.zero_lt_succ,ite_true] at read
    exact Subtract.while_next source next _ test (body inputName outputName) read (by omega) bodyRun tailRun

/-- Short-clock outcomes are included in the index-tick source allowance. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits index : Nat) (checked : Entry source inputName outputName input output contents length bits index) :
    source.clock-(evaluateHOLFiniteState source (loop inputName outputName)).2.clock≤index := by
  by_cases enough : index≤source.clock
  · rw [loop_execute source inputName outputName input output contents length bits index checked enough]
    have clock:=congrArg PanSemStateFiniteExact.clock (after_frame source output contents bits index index)
    change (after source output contents bits index index).clock=source.clock-index at clock
    change source.clock-(after source output contents bits index index).clock≤index
    omega
  · omega

/-- A real normal loop derives its own exact funding and physical endpoint. -/
theorem loop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits index : Nat) (checked : Entry source inputName outputName input output contents length bits index)
    (normal : evaluateHOLFiniteState source (loop inputName outputName)=(none,target)) :
    index≤source.clock ∧ target=after source output contents bits index index := by
  let base:={source with clock:=index}
  let final:=after base output contents bits index index
  have baseRun:=loop_execute base inputName outputName input output contents length bits index (checked.withClock index) (by rfl)
  have zero : final.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock (after_frame base output contents bits index index)
    change final.clock=index-index at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source final target (loop inputName outputName) index none none baseRun zero (by decide) normal (by decide)).1
  have expected:=loop_execute source inputName outputName input output contents length bits index checked funded
  exact ⟨funded,congrArg Prod.snd (normal.symm.trans expected)⟩

/-- Full-loop writes affect only positive indices through its initial i. -/
theorem after_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (contents : Nat→BitVec 64) (bits index : Nat)
    (outside : ∀ current,0<current→current≤index→query≠slot pointer current) :
    (after source pointer contents bits index index).memory query=source.memory query := by
  induction index generalizing source with
  | zero=>rfl
  | succ index ih=>
    rw [after]
    simp only [Nat.add_sub_cancel]
    rw [ih _ (by intro current positive inside;exact outside current positive (by omega))]
    simp only [bodyPost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,decClockHOLFinite,StoreWord.put,if_neg (outside (index+1) (by omega) (by omega))]

/-- The actual descending loop writes every required positive-index word. -/
theorem after_written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits index : Nat)
    (small : index<16) (query : Nat) (positive : 0<query) (inside : query≤index) :
    (after source pointer contents bits index index).memory (slot pointer query)=.word (Normalized.digit contents bits query) := by
  induction index generalizing source with
  | zero=>omega
  | succ index ih=>
    rw [after]
    simp only [Nat.add_sub_cancel]
    by_cases last : query=index+1
    · subst query
      rw [after_away _ pointer (slot pointer (index+1)) contents bits index (by
        intro current currentPositive currentInside hit
        have same:=slot_injective pointer (index+1) current small (by omega) hit
        omega)]
      simp [bodyPost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,StoreWord.put]
    · exact ih _ (by omega) (by omega)

end InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.workspace_buffers
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.after_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.after_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.after_index
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.loop_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.loop_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.loop_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.after_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.after_written

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every real source digit remains available after the complete output loop. -/
theorem after_input (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input output : BitVec 64) (contents : Nat→BitVec 64)
    (length bits index : Nat) (buffers : Buffers source input output contents length) (inside : index<length) :
    Image (after source output contents bits index index) input contents length := by
  intro current currentInside
  rw [after_away source output (slot input current) contents bits index (by
    intro written positive bound
    exact buffers.separate current currentInside written (by omega))]
  exact buffers.image current currentInside

/-- The separately stored numerator top word survives the actual loop,
including the seventeenth physical normalized slot when length=16. -/
theorem numerator_top (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (context : Workspace.Context source base)
    (contents : Nat→BitVec 64) (length bits : Nat) (small : length≤16) :
    (after source (Workspace.pointer base .normalizedNumerator) contents bits (length-1) (length-1)).memory
      (slot (Workspace.pointer base .normalizedNumerator) length)=source.memory (slot (Workspace.pointer base .normalizedNumerator) length) := by
  apply after_away
  intro current positive inside
  exact Subtract.slots_different source base context length current (by omega) (by omega) (by omega)

end InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.after_input
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.numerator_top

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def firstExpression (input : String) : ExpHOL 64:=.op .and [
  .shift .lsl (.load .one (localVar input)) (localVar "s"),.const 4294967295#64]
def firstStore (input output : String) : ProgHOL 64:=.store (localVar output) (firstExpression input)
def topExpression (input : String) : ExpHOL 64:=.shift .lsr
  (.load .one (address input (.op .sub [localVar "m",.const 1#64]))) remaining
def topStore (input output : String) : ProgHOL 64:=.store (address output (localVar "m")) (topExpression input)

private def findFirst (wanted : MlS) : ProgHOL 64→Option (ProgHOL 64)
  | .store (.var .local name) (.op .and [.shift .lsl (.load .one (.var .local input)) (.var .local count),.const mask])=>
    if name=wanted then some (.store (.var .local name) (.op .and [.shift .lsl (.load .one (.var .local input)) (.var .local count),.const mask])) else none
  | .dec _ _ _ rest=>findFirst wanted rest
  | .seq first rest=>(findFirst wanted first).orElse (fun _=>findFirst wanted rest)
  | .ite _ yes no=>(findFirst wanted yes).orElse (fun _=>findFirst wanted no)
  | .while _ contents=>findFirst wanted contents
  | .decCall _ _ _ _ rest=>findFirst wanted rest
  | _=>none

private def findTop : ProgHOL 64→Option (ProgHOL 64)
  | .store destination (.shift .lsr value amount)=>some (.store destination (.shift .lsr value amount))
  | .dec _ _ _ rest=>findTop rest
  | .seq first rest=>(findTop first).orElse (fun _=>findTop rest)
  | .ite _ yes no=>(findTop yes).orElse (fun _=>findTop no)
  | .while _ contents=>findTop contents
  | .decCall _ _ _ _ rest=>findTop rest
  | _=>none

set_option maxRecDepth 100000 in
theorem divisor_first_literal : findFirst (ofString "vn") Single.body=some (firstStore "v" "vn") := by
  simp [findFirst,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    firstStore,firstExpression,localVar]

set_option maxRecDepth 100000 in
theorem numerator_first_literal : findFirst (ofString "un") Single.body=some (firstStore "u" "un") := by
  have different : ofString "vn"≠ofString "un":=by decide
  simp [findFirst,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    firstStore,firstExpression,localVar,different]

set_option maxRecDepth 100000 in
theorem numerator_top_literal : findTop Single.body=some (topStore "u" "un") := by
  simp [findTop,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    topStore,topExpression,address,remaining,localVar]

private theorem indexed_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64)
    (indexExpression : ExpHOL 64) (index : Nat)
    (pointerCell : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (indexRead : eval source indexExpression=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source (address name indexExpression)=some (.val (.word (slot pointer index))) := by
  simp only [eval] at indexRead
  simp [eval,address,localVar,evalHOLExact,evalListHOLExact,toExact,pointerCell,indexRead,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    slot,BitVec.ofNat_mul,Nat.mul_comm]

private theorem counter_previous_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (length : Nat) (positive : 0<length)
    (cell : source.locals.lookup (ofString name)=some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source (.op .sub [localVar name,.const 1#64])=some (.val (.word (BitVec.ofNat 64 (length-1)))) := by
  have difference:=BitVec.ofNat_sub_ofNat_of_le (w:=64) length 1 (by decide) positive
  simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,cell,valueIsWord,valueWord,wordOpHOL,wordOp,difference]

/-- The original separate lowest-word store reads the actual input word and
writes its exact masked shift, without spending a source call/loop tick. -/
theorem first_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits : Nat) (buffers : Buffers source input output contents length) (positive : 0<length) (bitsSmall : bits≤31)
    (inputCell : source.locals.lookup (ofString inputName)=some (.val (.word input)))
    (outputCell : source.locals.lookup (ofString outputName)=some (.val (.word output)))
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits)))) :
    evaluateHOLFiniteState source (firstStore inputName outputName)=(none,{source with
      memory:=StoreWord.put source.memory output (Normalize.first (contents 0) bits)}) := by
  have mapped : source.memaddrs input:=by simpa [slot] using buffers.inputMapped 0 positive
  have cell : source.memory input=.word (contents 0):=by simpa [slot] using buffers.image 0 positive
  have loaded:=Witness.load_word_read source (localVar inputName) input (contents 0) (Subtract.local_read source inputName input inputCell) mapped cell
  have bitsNumber : (BitVec.ofNat 64 bits).toNat=bits:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have shifted:=shift_read source .lsl (.load .one (localVar inputName)) (localVar "s") (contents 0) (BitVec.ofNat 64 bits) ((contents 0)<<<bits)
    loaded (Subtract.local_read source "s" _ s) (by simp [wordShiftHOL,bitsNumber,show bits<64 from by omega])
  have masked:=Subtract.binary_read source .and _ (.const 4294967295#64) _ 4294967295#64 (Normalize.first (contents 0) bits) shifted rfl rfl
  exact StoreWord.execute source (localVar outputName) (firstExpression inputName) output _
    (Subtract.local_read source outputName output outputCell) masked (by simpa [slot] using buffers.outputMapped 0 positive)

/-- The original extra UN[m] store loads U[m-1], shifts by32-s and writes
its genuine outgoing carry. The allocated seventeenth slot is admitted. -/
theorem top_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits : Nat) (buffers : Buffers source input output contents length) (positive : 0<length) (bitsSmall : bits≤31)
    (inputCell : source.locals.lookup (ofString inputName)=some (.val (.word input)))
    (outputCell : source.locals.lookup (ofString outputName)=some (.val (.word output)))
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))))
    (m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 length))))
    (topMapped : source.memaddrs (slot output length)) :
    evaluateHOLFiniteState source (topStore inputName outputName)=(none,{source with
      memory:=StoreWord.put source.memory (slot output length) (Normalized.incoming contents bits length)}) := by
  have prevRead:=counter_previous_read source "m" length positive m
  have indexInside : length-1<length:=by omega
  have loaded:=Witness.load_word_read source (address inputName (.op .sub [localVar "m",.const 1#64])) _ (contents (length-1))
    (indexed_address_read source inputName input _ (length-1) inputCell prevRead)
    (buffers.inputMapped (length-1) indexInside) (buffers.image (length-1) indexInside)
  have restNumber : (BitVec.ofNat 64 (32-bits)).toNat=32-bits:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have shifted:=shift_read source .lsr _ remaining (contents (length-1)) (BitVec.ofNat 64 (32-bits)) (Normalize.high (contents (length-1)) bits)
    loaded (remaining_read source bits bitsSmall s) (by simp [wordShiftHOL,restNumber,Normalize.high,show 32-bits<64 from by omega])
  have same : Normalize.high (contents (length-1)) bits=Normalized.incoming contents bits length:=by
    cases length with
    | zero=>omega
    | succ length=>rfl
  rw [same] at shifted
  exact StoreWord.execute source (address outputName (localVar "m")) (topExpression inputName) _ _
    (indexed_address_read source outputName output _ length outputCell (Subtract.local_read source "m" _ m)) shifted topMapped

end InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.divisor_first_literal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.numerator_first_literal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.numerator_top_literal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.first_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.top_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def array (input output counter : String) : ProgHOL 64:=
  .seq (.assign .local (ofString "i") (.op .sub [localVar counter,.const 1#64]))
    (.seq (loop input output) (firstStore input output))

def arrayPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits length : Nat) :=
  let started:=bind source "i" (BitVec.ofNat 64 (length-1))
  let normalized:=after started pointer contents bits (length-1) (length-1)
  {normalized with memory:=StoreWord.put normalized.memory pointer (Normalize.first (contents 0) bits)}

/-- Actual counter initialization, entire descending loop and separate
lowest-word store, with the complete physical input image retained. -/
theorem array_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName counter : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits : Nat) (buffers : Buffers source input output contents length) (positive : 0<length) (bitsSmall : bits≤31)
    (inputCell : source.locals.lookup (ofString inputName)=some (.val (.word input)))
    (outputCell : source.locals.lookup (ofString outputName)=some (.val (.word output)))
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))))
    (count : source.locals.lookup (ofString counter)=some (.val (.word (BitVec.ofNat 64 length))))
    (old : BitVec 64) (i : source.locals.lookup (ofString "i")=some (.val (.word old)))
    (notInput : ofString "i"≠ofString inputName) (notOutput : ofString "i"≠ofString outputName) (enough : length-1≤source.clock) :
    evaluateHOLFiniteState source (array inputName outputName counter)=(none,arrayPost source output contents bits length) := by
  let started:=bind source "i" (BitVec.ofNat 64 (length-1))
  let normalized:=after started output contents bits (length-1) (length-1)
  have model : Entry started inputName outputName input output contents length bits (length-1):=
    ⟨⟨buffers.small,buffers.image,buffers.inputMapped,buffers.outputMapped,buffers.separate⟩,by omega,bitsSmall,
      (bind_lookup_other _ "i" inputName _ notInput).trans inputCell,
      (bind_lookup_other _ "i" outputName _ notOutput).trans outputCell,
      (bind_lookup_other _ "i" "s" _ (by decide)).trans s,bind_lookup_same _ _ _,notInput,notOutput⟩
  have loopRun : evaluateHOLFiniteState started (loop inputName outputName)=(none,normalized):=
    loop_execute started inputName outputName input output contents length bits (length-1) model enough
  have mapped : normalized.memaddrs=source.memaddrs:=by
    have fields:=congrArg PanSemStateFiniteExact.memaddrs (after_frame started output contents bits (length-1) (length-1))
    exact fields
  have nextBuffers : Buffers normalized input output contents length:=by
    refine ⟨buffers.small,after_input started input output contents length bits (length-1) model.buffers (by omega),?_,?_,buffers.separate⟩
    · intro index inside;rw [mapped];exact buffers.inputMapped index inside
    · intro index inside;rw [mapped];exact buffers.outputMapped index inside
  have nextInput : normalized.locals.lookup (ofString inputName)=some (.val (.word input)):=
    (after_other started output contents bits (length-1) (length-1) inputName notInput).trans model.inputCell
  have nextOutput : normalized.locals.lookup (ofString outputName)=some (.val (.word output)):=
    (after_other started output contents bits (length-1) (length-1) outputName notOutput).trans model.outputCell
  have nextS : normalized.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))):=
    (after_other started output contents bits (length-1) (length-1) "s" (by decide)).trans model.s
  have firstRun:=first_execute normalized inputName outputName input output contents length bits nextBuffers positive bitsSmall nextInput nextOutput nextS
  have tailRun : evaluateHOLFiniteState started (.seq (loop inputName outputName) (firstStore inputName outputName))=(none,arrayPost source output contents bits length):=by
    rw [evaluateHOLFiniteState_seq_line780,loopRun]
    exact firstRun
  have reset:=StateSteps.assign_execute source "i" (.op .sub [localVar counter,.const 1#64]) old (BitVec.ofNat 64 (length-1)) i
    (counter_previous_read source counter length positive count)
  rw [array,evaluateHOLFiniteState_seq_line780,reset]
  exact tailRun

theorem arrayPost_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits length : Nat) :
    arrayPost source pointer contents bits length={source with
      locals:=(arrayPost source pointer contents bits length).locals,
      memory:=(arrayPost source pointer contents bits length).memory,clock:=source.clock-(length-1)} := by
  let started:=bind source "i" (BitVec.ofNat 64 (length-1))
  let target:=arrayPost source pointer contents bits length
  have frame:=after_frame started pointer contents bits (length-1) (length-1)
  have clock : target.clock=source.clock-(length-1):=by
    have fields:=congrArg PanSemStateFiniteExact.clock frame
    exact fields
  have static : target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock}:=by
    have fields:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
      {state with locals:=target.locals,memory:=target.memory,clock:=target.clock}) frame
    exact fields
  rw [clock] at static
  exact static

/-- Complete actual normalized output, now including its separate index0 store. -/
theorem arrayPost_image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits length : Nat)
    (positive : 0<length) (small : length≤16) :
    Image (arrayPost source pointer contents bits length) pointer (Normalized.digit contents bits) length := by
  intro index inside
  by_cases zero : index=0
  · subst index
    simp [arrayPost,slot,StoreWord.put,Normalized.digit]
  · have outside : slot pointer index≠pointer:=by
      intro hit
      have same:=slot_injective pointer index 0 (by omega) (by decide) (by simpa [slot] using hit)
      omega
    change StoreWord.put _ pointer _ (slot pointer index)=_
    rw [StoreWord.put,if_neg outside]
    exact after_written _ pointer contents bits (length-1) (by omega) index (by omega) (by omega)

/-- No word outside the complete normalized output range changes. -/
theorem arrayPost_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (contents : Nat→BitVec 64) (bits length : Nat)
    (positive : 0<length) (outside : ∀ index,index<length→query≠slot pointer index) :
    (arrayPost source pointer contents bits length).memory query=source.memory query := by
  have firstOutside : query≠pointer:=by simpa [slot] using outside 0 positive
  change StoreWord.put _ pointer _ query=_
  rw [StoreWord.put,if_neg firstOutside]
  exact after_away _ pointer query contents bits (length-1) (by intro index positive inside;exact outside index (by omega))

/-- Actual normal completion supplies the entire output image and its own
funding; future successful normalization is never an entry premise. -/
theorem array_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName counter : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits : Nat) (buffers : Buffers source input output contents length) (positive : 0<length) (bitsSmall : bits≤31)
    (inputCell : source.locals.lookup (ofString inputName)=some (.val (.word input)))
    (outputCell : source.locals.lookup (ofString outputName)=some (.val (.word output)))
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))))
    (count : source.locals.lookup (ofString counter)=some (.val (.word (BitVec.ofNat 64 length))))
    (old : BitVec 64) (i : source.locals.lookup (ofString "i")=some (.val (.word old)))
    (notInput : ofString "i"≠ofString inputName) (notOutput : ofString "i"≠ofString outputName)
    (normal : evaluateHOLFiniteState source (array inputName outputName counter)=(none,target)) :
    length-1≤source.clock ∧ target=arrayPost source output contents bits length ∧ Image target output (Normalized.digit contents bits) length := by
  let base:={source with clock:=length-1}
  let final:=arrayPost base output contents bits length
  have baseBuffers : Buffers base input output contents length:=⟨buffers.small,buffers.image,buffers.inputMapped,buffers.outputMapped,buffers.separate⟩
  have baseRun:=array_execute base inputName outputName counter input output contents length bits baseBuffers positive bitsSmall inputCell outputCell s count old i notInput notOutput (by rfl)
  have zero : final.clock=0:=by
    have fields:=congrArg PanSemStateFiniteExact.clock (arrayPost_frame base output contents bits length)
    change final.clock=(length-1)-(length-1) at fields
    omega
  have funded:=(ClockCost.normal_from_zero_clock source final target (array inputName outputName counter) (length-1) none none baseRun zero (by decide) normal (by decide)).1
  have expected:=array_execute source inputName outputName counter input output contents length bits buffers positive bitsSmall inputCell outputCell s count old i notInput notOutput funded
  have endpoint : target=arrayPost source output contents bits length:=congrArg Prod.snd (normal.symm.trans expected)
  exact ⟨funded,endpoint,by rw [endpoint];exact arrayPost_image source output contents bits length positive buffers.small⟩

/-- All stopped and short-clock outcomes fit the actual counted loop allowance. -/
theorem array_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName counter : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits : Nat) (buffers : Buffers source input output contents length) (positive : 0<length) (bitsSmall : bits≤31)
    (inputCell : source.locals.lookup (ofString inputName)=some (.val (.word input)))
    (outputCell : source.locals.lookup (ofString outputName)=some (.val (.word output)))
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))))
    (count : source.locals.lookup (ofString counter)=some (.val (.word (BitVec.ofNat 64 length))))
    (old : BitVec 64) (i : source.locals.lookup (ofString "i")=some (.val (.word old)))
    (notInput : ofString "i"≠ofString inputName) (notOutput : ofString "i"≠ofString outputName) :
    source.clock-(evaluateHOLFiniteState source (array inputName outputName counter)).2.clock≤length-1 := by
  by_cases enough : length-1≤source.clock
  · rw [array_execute source inputName outputName counter input output contents length bits buffers positive bitsSmall inputCell outputCell s count old i notInput notOutput enough]
    have fields:=congrArg PanSemStateFiniteExact.clock (arrayPost_frame source output contents bits length)
    change (arrayPost source output contents bits length).clock=source.clock-(length-1) at fields
    change source.clock-(arrayPost source output contents bits length).clock≤length-1
    omega
  · omega

end InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.array_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.arrayPost_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.arrayPost_image
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.arrayPost_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.array_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.array_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem sequence_four (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b c tail : ProgHOL 64) :
    evaluateHOLFiniteState source (.seq a (.seq b (.seq c tail)))=
      evaluateHOLFiniteState source (.seq (.seq a (.seq b c)) tail) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  generalize firstRun : evaluateHOLFiniteState source a=firstResult
  obtain ⟨first,middle⟩:=firstResult
  cases first with
  | some result=>rfl
  | none=>
    generalize secondRun : evaluateHOLFiniteState middle b=secondResult
    obtain ⟨second,next⟩:=secondResult
    cases second with
    | some result=>rfl
    | none=>
      generalize thirdRun : evaluateHOLFiniteState next c=thirdResult
      obtain ⟨third,last⟩:=thirdResult
      cases third <;> rfl

/-- The original right-associated syntax resumes any actual continuation
from the same complete normalized output; no executable is reassociated. -/
theorem array_continue (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName outputName counter : String) (input output : BitVec 64)
    (contents : Nat→BitVec 64) (length bits : Nat) (buffers : Buffers source input output contents length) (positive : 0<length) (bitsSmall : bits≤31)
    (inputCell : source.locals.lookup (ofString inputName)=some (.val (.word input)))
    (outputCell : source.locals.lookup (ofString outputName)=some (.val (.word output)))
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))))
    (count : source.locals.lookup (ofString counter)=some (.val (.word (BitVec.ofNat 64 length))))
    (old : BitVec 64) (i : source.locals.lookup (ofString "i")=some (.val (.word old)))
    (notInput : ofString "i"≠ofString inputName) (notOutput : ofString "i"≠ofString outputName) (enough : length-1≤source.clock)
    (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (.seq (.assign .local (ofString "i") (.op .sub [localVar counter,.const 1#64]))
      (.seq (loop inputName outputName) (.seq (firstStore inputName outputName) continuation)))=
      evaluateHOLFiniteState (arrayPost source output contents bits length) continuation := by
  rw [sequence_four]
  have actual:=array_execute source inputName outputName counter input output contents length bits buffers positive bitsSmall inputCell outputCell s count old i notInput notOutput enough
  change evaluateHOLFiniteState source (.seq (array inputName outputName counter) continuation)=_
  rw [evaluateHOLFiniteState_seq_line780,actual]

end InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.array_continue

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem arrayPost_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits length : Nat)
    (name : String) (notI : ofString "i"≠ofString name) :
    (arrayPost source pointer contents bits length).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (after_other (bind source "i" (BitVec.ofNat 64 (length-1))) pointer contents bits (length-1) (length-1) name notI).trans
    (bind_lookup_other source "i" name _ notI)

theorem arrayPost_index (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (bits length : Nat) :
    (arrayPost source pointer contents bits length).locals.lookup (ofString "i")=some (.val (.word 0#64)) :=
  after_index (bind source "i" (BitVec.ofNat 64 (length-1))) pointer contents bits (length-1) (bind_lookup_same _ _ _)

/-- The same actually allocated workspace remains available at the next block. -/
theorem arrayPost_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base pointer : BitVec 64) (context : Workspace.Context source base)
    (contents : Nat→BitVec 64) (bits length : Nat) : Workspace.Context (arrayPost source pointer contents bits length) base := by
  have frame:=arrayPost_frame source pointer contents bits length
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  change (arrayPost source pointer contents bits length).globals=source.globals at globals
  change (arrayPost source pointer contents bits length).memaddrs=source.memaddrs at domain
  refine ⟨?_,domain.trans context.domain,context.arena,context.aligned⟩
  rw [globals]
  exact context.global

/-- The full numerator array block, including the first-word store, retains
its actual extra carry word even at physical index16. -/
theorem arrayPost_numerator_top (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (context : Workspace.Context source base)
    (contents : Nat→BitVec 64) (length bits : Nat) (positive : 0<length) (small : length≤16) :
    (arrayPost source (Workspace.pointer base .normalizedNumerator) contents bits length).memory
      (slot (Workspace.pointer base .normalizedNumerator) length)=source.memory (slot (Workspace.pointer base .normalizedNumerator) length) := by
  apply arrayPost_away _ _ _ _ _ _ positive
  intro index inside
  exact Subtract.slots_different source base context length index (by omega) (by omega) (by omega)

end InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.arrayPost_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.arrayPost_index
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.arrayPost_context
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.NormalizeLoop.arrayPost_numerator_top

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Real original inputs/pointers at the two-digit normalization entry. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length : Nat) : Prop where
  context : Workspace.Context source base
  large : 2≤length
  small : length≤16
  un : source.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator)))
  vn : source.locals.lookup (ofString "vn")=some (.val (.word (Workspace.pointer base .normalizedDivisor)))
  uCell : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator)))
  vCell : source.locals.lookup (ofString "v")=some (.val (.word (Workspace.pointer base .divisor)))
  m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 length)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))
  uImage : Image source (Workspace.pointer base .numerator) u length
  vImage : Image source (Workspace.pointer base .divisor) v 2
  uSmall : ∀ index,index<length→(u index).toNat<4294967296
  vSmall : ∀ index,index<2→(v index).toNat<4294967296
  leadingPositive : 0<(v 1).toNat

private theorem Entry.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length : Nat}
    (checked : Entry source base u v length) (clock : Nat) : Entry {source with clock:=clock} base u v length :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.large,checked.small,
    checked.un,checked.vn,checked.uCell,checked.vCell,checked.m,checked.n,checked.i,checked.uImage,checked.vImage,checked.uSmall,checked.vSmall,checked.leadingPositive⟩

private theorem Entry.bindS {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length : Nat}
    (checked : Entry source base u v length) (bits : Nat) : Entry (bind source "s" (BitVec.ofNat 64 bits)) base u v length := by
  refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.large,checked.small,
    ?_,?_,?_,?_,?_,?_,?_,checked.uImage,checked.vImage,checked.uSmall,checked.vSmall,checked.leadingPositive⟩
  · exact (bind_lookup_other _ "s" "un" _ (by decide)).trans checked.un
  · exact (bind_lookup_other _ "s" "vn" _ (by decide)).trans checked.vn
  · exact (bind_lookup_other _ "s" "u" _ (by decide)).trans checked.uCell
  · exact (bind_lookup_other _ "s" "v" _ (by decide)).trans checked.vCell
  · exact (bind_lookup_other _ "s" "m" _ (by decide)).trans checked.m
  · exact (bind_lookup_other _ "s" "n" _ (by decide)).trans checked.n
  · obtain ⟨old,cell⟩:=checked.i
    exact ⟨old,(bind_lookup_other _ "s" "i" _ (by decide)).trans cell⟩

private theorem Entry.u_buffers {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length : Nat}
    (checked : Entry source base u v length) :
    NormalizeLoop.Buffers source (Workspace.pointer base .numerator) (Workspace.pointer base .normalizedNumerator) u length :=
  NormalizeLoop.workspace_buffers source base checked.context .numerator .normalizedNumerator (by intro same;cases same)
    u length checked.small checked.small (by change length≤17;have bound:=checked.small;omega) checked.uImage

private theorem Entry.v_buffers {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length : Nat}
    (checked : Entry source base u v length) :
    NormalizeLoop.Buffers source (Workspace.pointer base .divisor) (Workspace.pointer base .normalizedDivisor) v 2 :=
  NormalizeLoop.workspace_buffers source base checked.context .divisor .normalizedDivisor (by intro same;cases same)
    v 2 (by decide) (by decide) (by decide) checked.vImage

private theorem Entry.after_array {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length : Nat}
    (checked : Entry source base u v length) (output : Workspace.Buffer) (contents : Nat→BitVec 64) (bits count : Nat)
    (positive : 0<count) (inside : count≤Workspace.count output) (notU : .numerator≠output) (notV : .divisor≠output) :
    Entry (NormalizeLoop.arrayPost source (Workspace.pointer base output) contents bits count) base u v length := by
  refine ⟨NormalizeLoop.arrayPost_context source base _ checked.context contents bits count,checked.large,checked.small,
    ?_,?_,?_,?_,?_,?_,⟨0#64,NormalizeLoop.arrayPost_index source _ contents bits count⟩,?_,?_,checked.uSmall,checked.vSmall,checked.leadingPositive⟩
  · exact (NormalizeLoop.arrayPost_other source _ contents bits count "un" (by decide)).trans checked.un
  · exact (NormalizeLoop.arrayPost_other source _ contents bits count "vn" (by decide)).trans checked.vn
  · exact (NormalizeLoop.arrayPost_other source _ contents bits count "u" (by decide)).trans checked.uCell
  · exact (NormalizeLoop.arrayPost_other source _ contents bits count "v" (by decide)).trans checked.vCell
  · exact (NormalizeLoop.arrayPost_other source _ contents bits count "m" (by decide)).trans checked.m
  · exact (NormalizeLoop.arrayPost_other source _ contents bits count "n" (by decide)).trans checked.n
  · intro index bound
    rw [NormalizeLoop.arrayPost_away source _ _ contents bits count positive (by
      intro written inRange
      exact Workspace.separate base .numerator output notU index written (by change index<16;have h:=checked.small;omega) (by omega))]
    exact checked.uImage index bound
  · intro index bound
    rw [NormalizeLoop.arrayPost_away source _ _ contents bits count positive (by
      intro written inRange
      exact Workspace.separate base .divisor output notV index written (by change index<8;omega) (by omega))]
    exact checked.vImage index bound

def divisorPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (v : Nat→BitVec 64) (bits : Nat) :=
  NormalizeLoop.arrayPost source (Workspace.pointer base .normalizedDivisor) v bits 2

def topPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat) :=
  let normalized:=divisorPost source base v bits
  {normalized with memory:=StoreWord.put normalized.memory (slot (Workspace.pointer base .normalizedNumerator) length) (Normalized.incoming u bits length)}

def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat) :=
  NormalizeLoop.arrayPost (topPost source base u v length bits) (Workspace.pointer base .normalizedNumerator) u bits length

private theorem Entry.after_divisor {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length : Nat}
    (checked : Entry source base u v length) (bits : Nat) : Entry (divisorPost source base v bits) base u v length :=
  checked.after_array .normalizedDivisor v bits 2 (by decide) (by decide) (by intro same;cases same) (by intro same;cases same)

private theorem Entry.after_top {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length : Nat}
    (checked : Entry source base u v length) (bits : Nat) : Entry (topPost source base u v length bits) base u v length := by
  have previous:=checked.after_divisor bits
  refine ⟨⟨previous.context.global,previous.context.domain,previous.context.arena,previous.context.aligned⟩,previous.large,previous.small,
    previous.un,previous.vn,previous.uCell,previous.vCell,previous.m,previous.n,previous.i,?_,?_,previous.uSmall,previous.vSmall,previous.leadingPositive⟩
  · intro index inside
    have separate:=Workspace.separate base .numerator .normalizedNumerator (by intro same;cases same) index length (by change index<16;have bound:=checked.small;omega) (by change length<17;have bound:=checked.small;omega)
    change StoreWord.put _ _ _ (slot (Workspace.pointer base .numerator) index)=_
    rw [StoreWord.put,if_neg separate]
    exact previous.uImage index inside
  · intro index inside
    have separate:=Workspace.separate base .divisor .normalizedNumerator (by intro same;cases same) index length (by change index<8;omega) (by change length<17;have bound:=checked.small;omega)
    change StoreWord.put _ _ _ (slot (Workspace.pointer base .divisor) index)=_
    rw [StoreWord.put,if_neg separate]
    exact previous.vImage index inside

/-- The original right-associated normalization code after the s call,
with the genuine later vtop/vsec/outer-loop continuation kept explicit. -/
def body (continuation : ProgHOL 64) : ProgHOL 64:=
  .seq (.assign .local (ofString "i") (.op .sub [localVar "n",.const 1#64]))
    (.seq (NormalizeLoop.loop "v" "vn") (.seq (NormalizeLoop.firstStore "v" "vn")
      (.seq (NormalizeLoop.topStore "u" "un")
        (.seq (.assign .local (ofString "i") (.op .sub [localVar "m",.const 1#64]))
          (.seq (NormalizeLoop.loop "u" "un") (.seq (NormalizeLoop.firstStore "u" "un") continuation))))))

/-- Both actual array blocks and the actual intervening top store execute
from the same real input images and retain the original continuation. -/
theorem body_continue (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat)
    (checked : Entry source base u v length) (bitsSmall : bits≤31)
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))))
    (enough : length≤source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (body continuation)=evaluateHOLFiniteState (post source base u v length bits) continuation := by
  let vn:=divisorPost source base v bits
  let top:=topPost source base u v length bits
  let next : ProgHOL 64:=.seq (.assign .local (ofString "i") (.op .sub [localVar "m",.const 1#64]))
    (.seq (NormalizeLoop.loop "u" "un") (.seq (NormalizeLoop.firstStore "u" "un") continuation))
  obtain ⟨old,i⟩:=checked.i
  have vnRun:=NormalizeLoop.array_continue source "v" "vn" "n" (Workspace.pointer base .divisor) (Workspace.pointer base .normalizedDivisor)
    v 2 bits checked.v_buffers (by decide) bitsSmall checked.vCell checked.vn s checked.n old i (by decide) (by decide)
    (by have lower:=checked.large;omega) (.seq (NormalizeLoop.topStore "u" "un") next)
  have vnEntry : Entry vn base u v length:=checked.after_divisor bits
  have sVn : vn.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))):=
    (NormalizeLoop.arrayPost_other source _ v bits 2 "s" (by decide)).trans s
  have topRun : evaluateHOLFiniteState vn (NormalizeLoop.topStore "u" "un")=(none,top):=
    NormalizeLoop.top_execute vn "u" "un" (Workspace.pointer base .numerator) (Workspace.pointer base .normalizedNumerator) u length bits vnEntry.u_buffers
      (by have lower:=checked.large;omega) bitsSmall vnEntry.uCell vnEntry.un sVn vnEntry.m
      (Workspace.slot_mapped vn base vnEntry.context .normalizedNumerator length (by change length<17;have upper:=checked.small;omega))
  have topEntry : Entry top base u v length:=checked.after_top bits
  have topI : top.locals.lookup (ofString "i")=some (.val (.word 0#64)):=NormalizeLoop.arrayPost_index source _ v bits 2
  have clockVn : vn.clock=source.clock-1:=by
    have clock:=congrArg PanSemStateFiniteExact.clock (NormalizeLoop.arrayPost_frame source (Workspace.pointer base .normalizedDivisor) v bits 2)
    exact clock
  have unRun:=NormalizeLoop.array_continue top "u" "un" "m" (Workspace.pointer base .numerator) (Workspace.pointer base .normalizedNumerator)
    u length bits topEntry.u_buffers (by have lower:=checked.large;omega) bitsSmall topEntry.uCell topEntry.un sVn topEntry.m 0#64 topI
    (by decide) (by decide) (by change length-1≤vn.clock;have lower:=checked.large;omega) continuation
  rw [body,vnRun]
  change evaluateHOLFiniteState vn (.seq (NormalizeLoop.topStore "u" "un") next)=_
  rw [evaluateHOLFiniteState_seq_line780,topRun]
  exact unRun

end InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.body_continue

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem Entry.after_post {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length : Nat}
    (checked : Entry source base u v length) (bits : Nat) : Entry (post source base u v length bits) base u v length :=
  (checked.after_top bits).after_array .normalizedNumerator u bits length (by have bound:=checked.large;omega)
    (by change length≤17;have bound:=checked.small;omega) (by intro same;cases same) (by intro same;cases same)

/-- Both complete normalized images and all actual bindings at the real
post-normalization continuation, including nlz32's true shift bounds. -/
structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat) : Prop where
  entry : Entry source base u v length
  bitsSmall : bits≤31
  s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits)))
  i : source.locals.lookup (ofString "i")=some (.val (.word 0#64))
  uImage : Image source (Workspace.pointer base .normalizedNumerator) (Normalized.extended u bits length) (length+1)
  vImage : Image source (Workspace.pointer base .normalizedDivisor) (Normalized.digit v bits) 2
  lower : 2147483648≤(v 1).toNat*2^bits
  upper : (v 1).toNat*2^bits<4294967296

/-- The exact combined physical post-state supplies both normalized images;
all inputs and pointer bindings are retained by the same real stores. -/
theorem post_ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat)
    (checked : Entry source base u v length) (bitsSmall : bits≤31)
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))))
    (lower : 2147483648≤(v 1).toNat*2^bits) (upper : (v 1).toNat*2^bits<4294967296) :
    Ready (post source base u v length bits) base u v length bits := by
  let vn:=divisorPost source base v bits
  let top:=topPost source base u v length bits
  have topEntry : Entry top base u v length:=checked.after_top bits
  have positive : 0<length:=by have bound:=checked.large;omega
  have sVn : vn.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))):=
    (NormalizeLoop.arrayPost_other source _ v bits 2 "s" (by decide)).trans s
  have unImage:=NormalizeLoop.arrayPost_image top (Workspace.pointer base .normalizedNumerator) u bits length positive checked.small
  have vnImage : Image vn (Workspace.pointer base .normalizedDivisor) (Normalized.digit v bits) 2:=
    NormalizeLoop.arrayPost_image source _ v bits 2 (by decide) (by decide)
  refine ⟨checked.after_post bits,bitsSmall,?_,NormalizeLoop.arrayPost_index top _ u bits length,?_,?_,lower,upper⟩
  · exact (NormalizeLoop.arrayPost_other top _ u bits length "s" (by decide)).trans sVn
  · intro index inside
    by_cases ordinary : index<length
    · simpa only [post,top,Normalized.extended,if_pos ordinary] using unImage index ordinary
    · have last : index=length:=by omega
      subst index
      rw [Normalized.extended,if_neg (by omega)]
      have retained:=NormalizeLoop.arrayPost_numerator_top top base topEntry.context u length bits positive checked.small
      have stored : top.memory (slot (Workspace.pointer base .normalizedNumerator) length)=.word (Normalized.incoming u bits length):=by
        simp [top,topPost,StoreWord.put]
      exact retained.trans stored
  · intro index inside
    have kept:=NormalizeLoop.arrayPost_away top (Workspace.pointer base .normalizedNumerator) (slot (Workspace.pointer base .normalizedDivisor) index) u bits length positive (by
      intro written inRange
      exact Workspace.separate base .normalizedDivisor .normalizedNumerator (by intro same;cases same) index written
        (by change index<8;omega) (by change written<17;have bound:=checked.small;omega))
    have separate:=Workspace.separate base .normalizedDivisor .normalizedNumerator (by intro same;cases same) index length
      (by change index<8;omega) (by change length<17;have bound:=checked.small;omega)
    have topSame : top.memory (slot (Workspace.pointer base .normalizedDivisor) index)=vn.memory (slot (Workspace.pointer base .normalizedDivisor) index):=by
      simp only [top,topPost,vn,StoreWord.put,if_neg separate]
    exact kept.trans (topSame.trans (vnImage index inside))

/-- Exact normal clock and unchanged static fields of both normalization arrays. -/
theorem post_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat) (positive : 0<length) :
    post source base u v length bits={source with
      locals:=(post source base u v length bits).locals,memory:=(post source base u v length bits).memory,
      clock:=source.clock-length} := by
  let vn:=divisorPost source base v bits
  let top:=topPost source base u v length bits
  let target:=post source base u v length bits
  have vnFrame:=NormalizeLoop.arrayPost_frame source (Workspace.pointer base .normalizedDivisor) v bits 2
  have unFrame:=NormalizeLoop.arrayPost_frame top (Workspace.pointer base .normalizedNumerator) u bits length
  have topStatic : top={source with locals:=top.locals,memory:=top.memory,clock:=top.clock}:=by
    have fields:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
      {state with locals:=top.locals,memory:=top.memory,clock:=top.clock}) vnFrame
    exact fields
  have unStatic : target={top with locals:=target.locals,memory:=target.memory,clock:=target.clock}:=by
    have fields:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
      {state with locals:=target.locals,memory:=target.memory,clock:=target.clock}) unFrame
    exact fields
  have topClock : top.clock=source.clock-1:=by
    have fields:=congrArg PanSemStateFiniteExact.clock vnFrame
    exact fields
  have unClock : target.clock=top.clock-(length-1):=by
    have fields:=congrArg PanSemStateFiniteExact.clock unFrame
    exact fields
  have clock : target.clock=source.clock-length:=by omega
  have fields:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    {state with locals:=target.locals,memory:=target.memory,clock:=target.clock}) topStatic
  have static : target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock}:=unStatic.trans fields
  rw [clock] at static
  exact static

/-- Every actually represented normalized numerator word is32-bit. -/
theorem Ready.u_number {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length bits : Nat}
    (ready : Ready source base u v length bits) :
    number (Normalized.extended u bits length) (length+1)=number u length*2^bits ∧
      ∀ index,index≤length→(Normalized.extended u bits length index).toNat<4294967296 :=
  ⟨Normalized.extended_number u bits length ready.bitsSmall ready.entry.uSmall,
    fun index inside=>Normalized.extended_small u bits length index ready.bitsSmall ready.entry.uSmall inside⟩

theorem Ready.v_number {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length bits : Nat}
    (ready : Ready source base u v length bits) :
    number (Normalized.digit v bits) 2=number v 2*2^bits :=
  Normalized.divisor_number v bits 2 ready.bitsSmall (by decide) ready.entry.vSmall ready.upper

theorem Ready.top_large {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length bits : Nat}
    (ready : Ready source base u v length bits) :
    2147483648≤(Normalized.digit v bits 1).toNat ∧ (Normalized.digit v bits 1).toNat<4294967296 :=
  Nlz32.normalized_digit (v 1) (v 0) bits ready.bitsSmall ready.lower ready.upper

end InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.post_ready
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.post_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.Ready.u_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.Ready.v_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.Ready.top_large

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def program : ProgHOL 64:=body .skip

theorem program_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat)
    (checked : Entry source base u v length) (bitsSmall : bits≤31)
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits)))) (enough : length≤source.clock) :
    evaluateHOLFiniteState source program=(none,post source base u v length bits) := by
  rw [program,body_continue source base u v length bits checked bitsSmall s enough .skip,evaluateHOLFiniteState_skip]

/-- The whole two-array normalization body has an all-outcome m-tick bound. -/
theorem program_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat)
    (checked : Entry source base u v length) (bitsSmall : bits≤31)
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits)))) :
    source.clock-(evaluateHOLFiniteState source program).2.clock≤length := by
  by_cases enough : length≤source.clock
  · rw [program_execute source base u v length bits checked bitsSmall s enough]
    have clock:=congrArg PanSemStateFiniteExact.clock (post_frame source base u v length bits (by have bound:=checked.large;omega))
    change (post source base u v length bits).clock=source.clock-length at clock
    change source.clock-(post source base u v length bits).clock≤length
    omega
  · omega

theorem program_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat)
    (checked : Entry source base u v length) (bitsSmall : bits≤31)
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))))
    (normal : evaluateHOLFiniteState source program=(none,target)) :
    length≤source.clock ∧ target=post source base u v length bits := by
  let baseSource:={source with clock:=length}
  let baseTarget:=post baseSource base u v length bits
  have baseRun:=program_execute baseSource base u v length bits (checked.withClock length) bitsSmall s (by rfl)
  have zero : baseTarget.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock (post_frame baseSource base u v length bits (by have bound:=checked.large;omega))
    change baseTarget.clock=length-length at clock
    omega
  have funded:=(ClockCost.normal_from_zero_clock source baseTarget target program length none none baseRun zero (by decide) normal (by decide)).1
  have expected:=program_execute source base u v length bits checked bitsSmall s funded
  exact ⟨funded,congrArg Prod.snd (normal.symm.trans expected)⟩

def arguments : List (ExpHOL 64):=[.load .one (NormalizeLoop.address "v" (.op .sub [localVar "n",.const 1#64]))]
def call (continuation : ProgHOL 64) : ProgHOL 64:=.decCall (ofString "s") .one (ofString "nlz32") arguments (body continuation)

private def findCall : ProgHOL 64→Option (ProgHOL 64)
  | .decCall name shape function args rest=>
    if function=ofString "nlz32" then some (.decCall name shape function args rest) else findCall rest
  | .dec _ _ _ rest=>findCall rest
  | .seq first rest=>(findCall first).orElse (fun _=>findCall rest)
  | .ite _ yes no=>(findCall yes).orElse (fun _=>findCall no)
  | .while _ contents=>findCall contents
  | _=>none

set_option maxRecDepth 100000 in
/-- The actual original s call and both normalization arrays, retaining its
real vtop/vsec/outer-loop continuation inside the original s scope. -/
theorem literal_call : ∃ continuation,findCall Single.body=some (call continuation) := by
  have different : ofString "div64by32"≠ofString "nlz32":=by decide
  simp [findCall,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    call,arguments,body,NormalizeLoop.loop,NormalizeLoop.body,NormalizeLoop.test,NormalizeLoop.expression,NormalizeLoop.address,
    NormalizeLoop.previous,NormalizeLoop.remaining,NormalizeLoop.firstStore,NormalizeLoop.firstExpression,NormalizeLoop.topStore,NormalizeLoop.topExpression,
    localVar,different]

private theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length : Nat)
    (checked : Entry source base u v length) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word (v 1))] := by
  have previous:=NormalizeLoop.counter_previous_read source "n" 2 (by decide) checked.n
  have address:=NormalizeLoop.indexed_address_read source "v" (Workspace.pointer base .divisor) _ 1 checked.vCell previous
  have loaded:=Witness.load_word_read source _ _ (v 1) address
    (Workspace.slot_mapped source base checked.context .divisor 1 (by decide)) (checked.vImage 1 (by decide))
  simp only [eval] at loaded
  simp only [arguments,evalListHOLFinite,evalListHOLExact]
  rw [loaded]

/-- The real nlz32 caller supplies s and its bounds to both original array
blocks. The actual ready state, clock and resumed s scope all come from
that same execution, without a supplied future callee/output oracle. -/
theorem prefix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length : Nat)
    (checked : Entry source base u v length) (installed : OriginalCode.Installed source.code)
    (enough : length+1≤source.clock) (continuation : ProgHOL 64) :
    ∃ bits,
      Ready (post (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits) base u v length bits ∧
      (post (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits).clock=source.clock-(length+1) ∧
      evaluateHOLFiniteState source (call continuation)=
        (let result:=evaluateHOLFiniteState (post (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits) continuation
         (result.1,restore source "s" result.2)) := by
  obtain ⟨bits,bitsSmall,lower,upper,actual⟩:=Nlz32.call_execute source (v 1) "s" arguments (body continuation) installed
    (checked.vSmall 1 (by decide)) checked.leadingPositive (arguments_read source base u v length checked) (by omega)
  let entered:=bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)
  have next : Entry entered base u v length:=(checked.withClock (source.clock-1)).bindS bits
  have s : entered.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits))):=bind_lookup_same _ _ _
  have normalized:=post_ready entered base u v length bits next bitsSmall s lower upper
  have clock : (post entered base u v length bits).clock=source.clock-(length+1):=by
    have projected:=congrArg PanSemStateFiniteExact.clock (post_frame entered base u v length bits (by have bound:=checked.large;omega))
    change (post entered base u v length bits).clock=source.clock-1-length at projected
    omega
  refine ⟨bits,normalized,clock,?_⟩
  rw [call,actual]
  change (let result:=evaluateHOLFiniteState entered (body continuation);(result.1,restore source "s" result.2))=_
  rw [body_continue entered base u v length bits next bitsSmall s (by change length≤source.clock-1;omega) continuation]

end InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.program_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.program_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.program_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.literal_call
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.prefix_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Both arrays change only the i binding; the top store changes no locals. -/
theorem post_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat)
    (name : String) (notI : ofString "i"≠ofString name) :
    (post source base u v length bits).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (NormalizeLoop.arrayPost_other (topPost source base u v length bits) (Workspace.pointer base .normalizedNumerator) u bits length name notI).trans
    (NormalizeLoop.arrayPost_other source (Workspace.pointer base .normalizedDivisor) v bits 2 name notI)

/-- No original normalization store reaches outside the real UN[0..m]
and VN[0..1] ranges, including the extra top-word write. -/
theorem post_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base query : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat)
    (positive : 0<length)
    (outsideU : ∀ index,index≤length→query≠slot (Workspace.pointer base .normalizedNumerator) index)
    (outsideV : ∀ index,index<2→query≠slot (Workspace.pointer base .normalizedDivisor) index) :
    (post source base u v length bits).memory query=source.memory query := by
  have un:=NormalizeLoop.arrayPost_away (topPost source base u v length bits) (Workspace.pointer base .normalizedNumerator) query u bits length positive
    (by intro index inside;exact outsideU index (by omega))
  have top : (topPost source base u v length bits).memory query=(divisorPost source base v bits).memory query:=by
    simp only [topPost,StoreWord.put,if_neg (outsideU length (by omega))]
  have vn:=NormalizeLoop.arrayPost_away source (Workspace.pointer base .normalizedDivisor) query v bits 2 (by decide) outsideV
  exact un.trans (top.trans vn)

/-- The actual scoped nlz32 call plus the complete two-array prefix costs
at most m+1source ticks, including all short-clock executions. -/
theorem prefix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length : Nat)
    (checked : Entry source base u v length) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (call .skip)).2.clock≤length+1 := by
  by_cases enough : length+1≤source.clock
  · obtain ⟨bits,ready,clock,actual⟩:=prefix_execute source base u v length checked installed enough .skip
    rw [actual]
    simp only [evaluateHOLFiniteState_skip]
    change source.clock-(post (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits).clock≤length+1
    rw [clock]
    omega
  · omega

end InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.post_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.post_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.prefix_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual restored k scope leaves every binding except i unchanged. -/
theorem initializedPost_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) (name : String)
    (notI : ofString name≠ofString "i") (notK : ofString name≠ofString "k") :
    (initializedPost source base position quotient low middle divisorLow divisorHigh).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  unfold initializedPost
  rw [restore_lookup_other source _ "k" name notK]
  exact (pairPost_other (subtractionEntry source) base position quotient low middle divisorLow divisorHigh name notI notK).trans
    (initialize_other source name notI notK)

theorem initializedPost_index (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (quotient low middle divisorLow divisorHigh : BitVec 64) :
    (initializedPost source base position quotient low middle divisorLow divisorHigh).locals.lookup (ofString "i")=some (.val (.word 2#64)) := by
  unfold initializedPost
  rw [restore_lookup_other source _ "k" "i" (by decide)]
  exact post_index _ base 1 position quotient _ middle divisorHigh

private theorem corrected_endpoint (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (q r low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (ready : QhatCorrection.Bindings source q r 1#64 divisorHigh divisorLow low) (small : q.toNat<4294967296)
    (estimate : q.toNat*divisorHigh.toNat+r.toNat=top.toNat*4294967296+middle.toNat)
    (upper : TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh≤q.toNat)
    (normal : evaluateHOLFiniteState source corrected=(none,target)) :
    ∃ correctionState quotient,evaluateHOLFiniteState source QhatCorrection.loop=(none,correctionState) ∧
      target=initializedPost correctionState base position quotient low middle divisorLow divisorHigh := by
  obtain ⟨correctionState,front,back⟩:=sequence_none source target QhatCorrection.loop initialized normal
  obtain ⟨quotient,nextModel,qhat,qSmall,exactQuotient⟩:=correction_result source correctionState base position q r low middle top divisorLow divisorHigh
    checked ready small estimate upper front
  obtain ⟨funded,endpoint⟩:=initialized_normal correctionState target base position quotient low middle top divisorLow divisorHigh nextModel qhat qSmall exactQuotient back
  exact ⟨correctionState,quotient,front,endpoint⟩

/-- An actual normal correction/subtraction run retains the outer loop's
counter/pointers and other bindings outside its real writable locals. -/
theorem corrected_other (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (q r low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (ready : QhatCorrection.Bindings source q r 1#64 divisorHigh divisorLow low) (small : q.toNat<4294967296)
    (estimate : q.toNat*divisorHigh.toNat+r.toNat=top.toNat*4294967296+middle.toNat)
    (upper : TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh≤q.toNat)
    (normal : evaluateHOLFiniteState source corrected=(none,target)) (name : String)
    (notI : ofString name≠ofString "i") (notK : ofString name≠ofString "k")
    (notQ : ofString name≠ofString "qhat") (notR : ofString name≠ofString "rhat") (notAgain : ofString name≠ofString "again") :
    target.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  obtain ⟨correctionState,quotient,front,rfl⟩:=corrected_endpoint source target base position q r low middle top divisorLow divisorHigh checked ready small estimate upper normal
  exact (initializedPost_other correctionState base position quotient low middle divisorLow divisorHigh name notI notK).trans
    (QhatCorrection.loop_other source correctionState name notQ notR notAgain front)

theorem corrected_index (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (q r low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (ready : QhatCorrection.Bindings source q r 1#64 divisorHigh divisorLow low) (small : q.toNat<4294967296)
    (estimate : q.toNat*divisorHigh.toNat+r.toNat=top.toNat*4294967296+middle.toNat)
    (upper : TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh≤q.toNat)
    (normal : evaluateHOLFiniteState source corrected=(none,target)) :
    target.locals.lookup (ofString "i")=some (.val (.word 2#64)) := by
  obtain ⟨correctionState,quotient,front,rfl⟩:=corrected_endpoint source target base position q r low middle top divisorLow divisorHigh checked ready small estimate upper normal
  exact initializedPost_index correctionState base position quotient low middle divisorLow divisorHigh

end InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.initializedPost_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.initializedPost_index
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.corrected_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Subtract.corrected_index

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The real whole per-digit phase retains outer j and every pointer/count
binding, obtained from its actual normal trace and restored again scope. -/
theorem phase_other (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Entry source base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source phase=(none,target)) (name : String)
    (notI : ofString name≠ofString "i") (notK : ofString name≠ofString "k")
    (notQ : ofString name≠ofString "qhat") (notR : ofString name≠ofString "rhat") (notAgain : ofString name≠ofString "again") :
    target.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  obtain ⟨middleState,front,back⟩:=sequence_none source target program continuation normal
  obtain ⟨q,r,paid,price,funded,endpoint,qSmall,balance,upper⟩:=program_normal source middleState base position low middle top divisorLow divisorHigh checked front
  subst middleState
  obtain ⟨window,ready⟩:=entry_after_estimate source base position low middle top divisorLow divisorHigh checked q r paid
  obtain ⟨inner,remaining,restored⟩:=ScalarScope.declare_trace (post source q r paid) target "again" (.const 1#64) 1#64 Subtract.corrected none rfl back
  have kept:=Subtract.corrected_other (afterEstimate source q r paid) inner base position q r low middle top divisorLow divisorHigh
    window ready qSmall balance upper remaining name notI notK notQ notR notAgain
  rw [restored,restore_lookup_other _ _ "again" name notAgain,kept]
  exact (bind_lookup_other _ "again" name _ (Ne.symm notAgain)).trans (post_other source q r paid name notQ notR)

/-- Every actual normal two-digit phase leaves its real inner counter at2,
so the next outer iteration receives a genuine scalar binding. -/
theorem phase_index (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Entry source base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source phase=(none,target)) :
    target.locals.lookup (ofString "i")=some (.val (.word 2#64)) := by
  obtain ⟨middleState,front,back⟩:=sequence_none source target program continuation normal
  obtain ⟨q,r,paid,price,funded,endpoint,qSmall,balance,upper⟩:=program_normal source middleState base position low middle top divisorLow divisorHigh checked front
  subst middleState
  obtain ⟨window,ready⟩:=entry_after_estimate source base position low middle top divisorLow divisorHigh checked q r paid
  obtain ⟨inner,remaining,restored⟩:=ScalarScope.declare_trace (post source q r paid) target "again" (.const 1#64) 1#64 Subtract.corrected none rfl back
  have index:=Subtract.corrected_index (afterEstimate source q r paid) inner base position q r low middle top divisorLow divisorHigh
    window ready qSmall balance upper remaining
  rw [restored,restore_lookup_other _ _ "again" "i" (by decide)]
  exact index

end InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.phase_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Estimate.phase_index

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def previous : ExpHOL 64:=.op .sub [localVar "j",.const 1#64]
def topIndex : ExpHOL 64:=.op .add [localVar "j",localVar "n"]
def middleIndex : ExpHOL 64:=.op .sub [topIndex,.const 1#64]
def lowIndex : ExpHOL 64:=.op .sub [topIndex,.const 2#64]
def loadAt (index : ExpHOL 64) : ExpHOL 64:=.load .one (NormalizeLoop.address "un" index)
def captures : ProgHOL 64:=.dec (ofString "ujn") .one (loadAt topIndex)
  (.dec (ofString "ujn1") .one (loadAt middleIndex)
    (.dec (ofString "ujn2") .one (loadAt lowIndex)
      (.dec (ofString "qhat") .one (.const 0#64) (.dec (ofString "rhat") .one (.const 0#64) Estimate.phase))))
def body : ProgHOL 64:=.seq (.assign .local (ofString "j") previous) captures
def test : ExpHOL 64:=.cmp .lower (.const 0#64) (localVar "j")
def loop : ProgHOL 64:=.while test body

private def findLoop : ProgHOL 64→Option (ProgHOL 64)
  | .while condition contents=>
    match condition,contents with
    | .cmp .lower (.const zero) (.var .local counter),.seq (.assign .local assigned _) (.dec captured _ _ _)=>
      if zero=0#64 ∧ counter=ofString "j" ∧ assigned=ofString "j" ∧ captured=ofString "ujn" then some (.while condition contents) else findLoop contents
    | _,_=>findLoop contents
  | .dec _ _ _ rest=>findLoop rest
  | .seq first rest=>(findLoop first).orElse (fun _=>findLoop rest)
  | .ite _ yes no=>(findLoop yes).orElse (fun _=>findLoop no)
  | .decCall _ _ _ _ rest=>findLoop rest
  | _=>none

set_option maxRecDepth 100000 in
/-- Literal current outer quotient loop, including all three actual loads,
fresh qhat/rhat scopes and the already checked per-digit phase. -/
theorem literal_loop : findLoop Single.body=some loop := by
  simp [findLoop,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    loop,test,body,previous,captures,loadAt,topIndex,middleIndex,lowIndex,
    Estimate.phase,Estimate.program,Estimate.test,Estimate.maximum,Estimate.remainderExpression,Estimate.scalar,Estimate.arguments,Estimate.updates,Estimate.continuation,
    Subtract.corrected,QhatCorrection.loop,QhatCorrection.test,QhatCorrection.body,QhatCorrection.branch,QhatCorrection.correct,
    QhatCorrection.roomTest,QhatCorrection.estimateTest,QhatCorrection.leftEstimate,QhatCorrection.rightEstimate,
    QhatCorrection.quotientExpression,QhatCorrection.remainderExpression,Subtract.initialized,Subtract.loop,Subtract.test,Subtract.step,Subtract.updates,
    Subtract.productExpression,Subtract.residualExpression,Subtract.lowExpression,Subtract.carryExpression,Subtract.increment,Subtract.inputAddress,Subtract.divisorAddress,
    Subtract.finish,Subtract.findFinish,Subtract.topAddress,Subtract.quotientAddress,Subtract.address,Subtract.difference,Subtract.negativeTest,Subtract.keep,
    NormalizeLoop.address,returnShape,localVar]

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.literal_loop

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The three original capture expressions read exactly the actual mapped
window at j,j+1,j+2. Their n=2 arithmetic is checked at64-bit word width. -/
theorem captures_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top : BitVec 64) (context : Workspace.Context source base) (inside : position+2<17)
    (un : source.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator))))
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position))))
    (n : source.locals.lookup (ofString "n")=some (.val (.word 2#64)))
    (lowCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) position)=.word low)
    (middleCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (position+1))=.word middle)
    (topCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (position+2))=.word top) :
    eval source (loadAt topIndex)=some (.val (.word top)) ∧
      eval source (loadAt middleIndex)=some (.val (.word middle)) ∧
      eval source (loadAt lowIndex)=some (.val (.word low)) := by
  have topRead : eval source topIndex=some (.val (.word (BitVec.ofNat 64 (position+2)))):=by
    simp [eval,topIndex,localVar,evalHOLExact,evalListHOLExact,toExact,j,n,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have middleNumber:=BitVec.ofNat_sub_ofNat_of_le (w:=64) (position+2) 1 (by decide) (by omega)
  have middleNatural : position+2-1=position+1:=by omega
  rw [middleNatural] at middleNumber
  have middleRead : eval source middleIndex=some (.val (.word (BitVec.ofNat 64 (position+1)))):=
    Subtract.binary_read source .sub topIndex (.const 1#64) (BitVec.ofNat 64 (position+2)) 1#64 (BitVec.ofNat 64 (position+1)) topRead rfl
      (by change some (BitVec.ofNat 64 (position+2)-1#64)=some (BitVec.ofNat 64 (position+1));rw [middleNumber])
  have lowNumber:=BitVec.ofNat_sub_ofNat_of_le (w:=64) (position+2) 2 (by decide) (by omega)
  simp only [Nat.add_sub_cancel] at lowNumber
  have lowRead : eval source lowIndex=some (.val (.word (BitVec.ofNat 64 position))):=
    Subtract.binary_read source .sub topIndex (.const 2#64) (BitVec.ofNat 64 (position+2)) 2#64 (BitVec.ofNat 64 position) topRead rfl
      (by change some (BitVec.ofNat 64 (position+2)-2#64)=some (BitVec.ofNat 64 position);rw [lowNumber])
  refine ⟨?_,?_,?_⟩
  · exact Witness.load_word_read source _ _ top
      (NormalizeLoop.indexed_address_read source "un" _ topIndex (position+2) un topRead)
      (Workspace.slot_mapped source base context .normalizedNumerator (position+2) inside) topCell
  · exact Witness.load_word_read source _ _ middle
      (NormalizeLoop.indexed_address_read source "un" _ middleIndex (position+1) un middleRead)
      (Workspace.slot_mapped source base context .normalizedNumerator (position+1) (by change position+1<17;omega)) middleCell
  · exact Witness.load_word_read source _ _ low
      (NormalizeLoop.indexed_address_read source "un" _ lowIndex position un lowRead)
      (Workspace.slot_mapped source base context .normalizedNumerator position (by change position<17;omega)) lowCell

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.captures_read

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current physical window before the original capture declarations. -/
structure Window (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  inside : position+2<17
  un : source.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator)))
  vn : source.locals.lookup (ofString "vn")=some (.val (.word (Workspace.pointer base .normalizedDivisor)))
  q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))
  j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))
  highCell : source.locals.lookup (ofString "vtop")=some (.val (.word divisorHigh))
  secondCell : source.locals.lookup (ofString "vsec")=some (.val (.word divisorLow))
  lowCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) position)=.word low
  middleCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (position+1))=.word middle
  topCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (position+2))=.word top
  divisorLowCell : source.memory (slot (Workspace.pointer base .normalizedDivisor) 0)=.word divisorLow
  divisorHighCell : source.memory (slot (Workspace.pointer base .normalizedDivisor) 1)=.word divisorHigh
  lowSmall : low.toNat<4294967296
  middleSmall : middle.toNat<4294967296
  divisorLowSmall : divisorLow.toNat<4294967296
  divisorHighSmall : divisorHigh.toNat<4294967296
  divisorHighLarge : 2147483648≤divisorHigh.toNat
  digitRange : TwoDigitSubtract.window low middle top<TwoDigitSubtract.divisorNumber divisorLow divisorHigh*4294967296

private theorem Window.bindTemporary {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {position : Nat}
    {low middle top divisorLow divisorHigh : BitVec 64} (checked : Window source base position low middle top divisorLow divisorHigh)
    (name : String) (word : BitVec 64) (allowed : name="ujn" ∨ name="ujn1" ∨ name="ujn2" ∨ name="qhat" ∨ name="rhat") :
    Window (bind source name word) base position low middle top divisorLow divisorHigh := by
  rcases allowed with rfl|rfl|rfl|rfl|rfl <;>
    refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,checked.inside,
      ?_,?_,?_,?_,?_,?_,?_,?_,checked.lowCell,checked.middleCell,checked.topCell,checked.divisorLowCell,checked.divisorHighCell,
      checked.lowSmall,checked.middleSmall,checked.divisorLowSmall,checked.divisorHighSmall,checked.divisorHighLarge,checked.digitRange⟩ <;>
    first
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.un
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.vn
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.q
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.j
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.n
    | obtain ⟨old,cell⟩:=checked.i
      exact ⟨old,(bind_lookup_other _ _ _ _ (by decide)).trans cell⟩
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.highCell
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.secondCell

private theorem Window.reads {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {position : Nat}
    {low middle top divisorLow divisorHigh : BitVec 64} (checked : Window source base position low middle top divisorLow divisorHigh) :
    eval source (loadAt topIndex)=some (.val (.word top)) ∧
      eval source (loadAt middleIndex)=some (.val (.word middle)) ∧ eval source (loadAt lowIndex)=some (.val (.word low)) :=
  captures_read source base position low middle top checked.context checked.inside checked.un checked.j checked.n checked.lowCell checked.middleCell checked.topCell

def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (low middle top : BitVec 64) :=
  bind (bind (bind (bind (bind source "ujn" top) "ujn1" middle) "ujn2" low) "qhat" 0#64) "rhat" 0#64

def restored (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (low middle top : BitVec 64) :=
  restore source "ujn" (restore (bind source "ujn" top) "ujn1"
    (restore (bind (bind source "ujn" top) "ujn1" middle) "ujn2"
      (restore (bind (bind (bind source "ujn" top) "ujn1" middle) "ujn2" low) "qhat"
        (restore (bind (bind (bind (bind source "ujn" top) "ujn1" middle) "ujn2" low) "qhat" 0#64) "rhat" target))))

/-- The genuine mapped loads and fresh zero declarations produce the
already checked phase entry, without assuming any future phase result. -/
theorem prepared_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh) :
    Estimate.Entry (prepared source low middle top) base position low middle top divisorLow divisorHigh := by
  have one:=checked.bindTemporary "ujn" top (Or.inl rfl)
  have two:=one.bindTemporary "ujn1" middle (Or.inr (Or.inl rfl))
  have three:=two.bindTemporary "ujn2" low (Or.inr (Or.inr (Or.inl rfl)))
  have four:=three.bindTemporary "qhat" 0#64 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have five:=four.bindTemporary "rhat" 0#64 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have ujn : (prepared source low middle top).locals.lookup (ofString "ujn")=some (.val (.word top)):=
    (bind_lookup_other _ "rhat" "ujn" _ (by decide)).trans ((bind_lookup_other _ "qhat" "ujn" _ (by decide)).trans
      ((bind_lookup_other _ "ujn2" "ujn" _ (by decide)).trans ((bind_lookup_other _ "ujn1" "ujn" _ (by decide)).trans (bind_lookup_same _ _ _))))
  refine ⟨⟨five.context,five.inside,five.un,five.vn,five.q,five.j,five.n,ujn,five.i,?_,?_,five.topCell,five.divisorLowCell,five.divisorHighCell,
    five.lowSmall,five.middleSmall,five.divisorLowSmall,five.divisorHighSmall,five.divisorHighLarge⟩,
    five.installed,?_,?_,five.highCell,five.secondCell,?_,bind_lookup_same _ _ _,five.digitRange⟩
  · change source.memory (slot (Workspace.pointer base .normalizedNumerator) (0+position))=.word low
    simpa only [Nat.zero_add] using checked.lowCell
  · change source.memory (slot (Workspace.pointer base .normalizedNumerator) (1+position))=.word middle
    simpa only [Nat.add_comm] using checked.middleCell
  · exact (bind_lookup_other _ "rhat" "ujn1" _ (by decide)).trans ((bind_lookup_other _ "qhat" "ujn1" _ (by decide)).trans
      ((bind_lookup_other _ "ujn2" "ujn1" _ (by decide)).trans (bind_lookup_same _ _ _)))
  · exact (bind_lookup_other _ "rhat" "ujn2" _ (by decide)).trans ((bind_lookup_other _ "qhat" "ujn2" _ (by decide)).trans (bind_lookup_same _ _ _))
  · exact (bind_lookup_other _ "rhat" "qhat" _ (by decide)).trans (bind_lookup_same _ _ _)

/-- Execute all five original declarations with their actual lexical
restorations, for every real phase outcome including a stopped outcome. -/
theorem captures_execute (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (result : Option (PanSemResultExact 64)) (phaseRun : evaluateHOLFiniteState (prepared source low middle top) Estimate.phase=(result,target)) :
    evaluateHOLFiniteState source captures=(result,restored source target low middle top) := by
  let first:=bind source "ujn" top
  let second:=bind first "ujn1" middle
  let third:=bind second "ujn2" low
  let fourth:=bind third "qhat" 0#64
  have one:=checked.bindTemporary "ujn" top (Or.inl rfl)
  have two:=one.bindTemporary "ujn1" middle (Or.inr (Or.inl rfl))
  have rhatRun:=ScalarScope.declare_execute fourth target "rhat" (.const 0#64) 0#64 Estimate.phase result rfl phaseRun
  have qhatRun:=ScalarScope.declare_execute third _ "qhat" (.const 0#64) 0#64 (.dec (ofString "rhat") .one (.const 0#64) Estimate.phase) result rfl rhatRun
  have lowRun:=ScalarScope.declare_execute second _ "ujn2" (loadAt lowIndex) low _ result two.reads.2.2 qhatRun
  have middleRun:=ScalarScope.declare_execute first _ "ujn1" (loadAt middleIndex) middle _ result one.reads.2.1 lowRun
  exact ScalarScope.declare_execute source _ "ujn" (loadAt topIndex) top _ result checked.reads.1 middleRun

/-- All source-clock work of the original captures is charged by the real
phase bound; declarations and loads introduce no call/loop ticks. -/
theorem captures_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh) :
    source.clock-(evaluateHOLFiniteState source captures).2.clock≤38 := by
  let output:=evaluateHOLFiniteState (prepared source low middle top) Estimate.phase
  have actual:=captures_execute source output.2 base position low middle top divisorLow divisorHigh checked output.1 rfl
  have price:=Estimate.phase_cost (prepared source low middle top) base position low middle top divisorLow divisorHigh (prepared_entry source base position low middle top divisorLow divisorHigh checked)
  rw [actual]
  exact price

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.prepared_entry
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.captures_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.captures_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem captures_trace (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source captures=(none,target)) :
    ∃ phaseTarget,evaluateHOLFiniteState (prepared source low middle top) Estimate.phase=(none,phaseTarget) ∧ target=restored source phaseTarget low middle top := by
  let output:=evaluateHOLFiniteState (prepared source low middle top) Estimate.phase
  have actual:=captures_execute source output.2 base position low middle top divisorLow divisorHigh checked output.1 rfl
  have result : output.1=none:=congrArg Prod.fst (actual.symm.trans normal)
  have endpoint : target=restored source output.2 low middle top:=congrArg Prod.snd (normal.symm.trans actual)
  exact ⟨output.2,Prod.ext result rfl,endpoint⟩

private theorem restored_other (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (low middle top : BitVec 64) (name : String)
    (notTop : ofString name≠ofString "ujn") (notMiddle : ofString name≠ofString "ujn1") (notLow : ofString name≠ofString "ujn2")
    (notQ : ofString name≠ofString "qhat") (notR : ofString name≠ofString "rhat") :
    (restored source target low middle top).locals.lookup (ofString name)=target.locals.lookup (ofString name) := by
  unfold restored
  rw [restore_lookup_other _ _ "ujn" name notTop,restore_lookup_other _ _ "ujn1" name notMiddle,
    restore_lookup_other _ _ "ujn2" name notLow,restore_lookup_other _ _ "qhat" name notQ,restore_lookup_other _ _ "rhat" name notR]

private theorem prepared_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (low middle top : BitVec 64) (name : String)
    (notTop : ofString name≠ofString "ujn") (notMiddle : ofString name≠ofString "ujn1") (notLow : ofString name≠ofString "ujn2")
    (notQ : ofString name≠ofString "qhat") (notR : ofString name≠ofString "rhat") :
    (prepared source low middle top).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "rhat" name _ (Ne.symm notR)).trans ((bind_lookup_other _ "qhat" name _ (Ne.symm notQ)).trans
    ((bind_lookup_other _ "ujn2" name _ (Ne.symm notLow)).trans ((bind_lookup_other _ "ujn1" name _ (Ne.symm notMiddle)).trans
      (bind_lookup_other _ "ujn" name _ (Ne.symm notTop)))))

/-- A genuine normal capture/declaration/phase run retains all external
counter and pointer bindings through the five original restored scopes. -/
theorem captures_other (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source captures=(none,target)) (name : String)
    (notTop : ofString name≠ofString "ujn") (notMiddle : ofString name≠ofString "ujn1") (notLow : ofString name≠ofString "ujn2")
    (notQ : ofString name≠ofString "qhat") (notR : ofString name≠ofString "rhat")
    (notI : ofString name≠ofString "i") (notK : ofString name≠ofString "k") (notAgain : ofString name≠ofString "again") :
    target.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  obtain ⟨phaseTarget,phaseRun,endpoint⟩:=captures_trace source target base position low middle top divisorLow divisorHigh checked normal
  have kept:=Estimate.phase_other (prepared source low middle top) phaseTarget base position low middle top divisorLow divisorHigh
    (prepared_entry source base position low middle top divisorLow divisorHigh checked) phaseRun name notI notK notQ notR notAgain
  rw [endpoint,restored_other source phaseTarget low middle top name notTop notMiddle notLow notQ notR,kept]
  exact prepared_other source low middle top name notTop notMiddle notLow notQ notR

/-- The same original captures and real division phase derive the exact
quotient/remainder cells, paid cost and typed successor i binding. -/
theorem captures_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64) (checked : Window source base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source captures=(none,target)) :
    ∃ quotient,quotient.toNat<4294967296 ∧
      quotient.toNat=TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
      (TwoDigitSubtract.firstLow low quotient divisorLow).toNat<4294967296 ∧
      (TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh).toNat<4294967296 ∧
      (TwoDigitSubtract.firstLow low quotient divisorLow).toNat+4294967296*(TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh).toNat=
        TwoDigitSubtract.window low middle top%TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
      target.memory=Subtract.digitMemory source.memory base position quotient low middle divisorLow divisorHigh ∧
      target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock} ∧
      target.locals.lookup (ofString "i")=some (.val (.word 2#64)) ∧ source.clock-target.clock≤38 := by
  obtain ⟨phaseTarget,phaseRun,endpoint⟩:=captures_trace source target base position low middle top divisorLow divisorHigh checked normal
  have phaseEntry:=prepared_entry source base position low middle top divisorLow divisorHigh checked
  obtain ⟨quotient,qSmall,qNumber,remainder,written,static,cost⟩:=Estimate.phase_normal (prepared source low middle top) phaseTarget base position low middle top divisorLow divisorHigh phaseEntry phaseRun
  have firstBounds:=TwoDigitSubtract.product_digit low 0#64 quotient divisorLow checked.lowSmall (by decide) qSmall checked.divisorLowSmall
  have secondBounds:=TwoDigitSubtract.product_digit middle (TwoDigitSubtract.firstCarry low quotient divisorLow) quotient divisorHigh checked.middleSmall firstBounds.2.1 qSmall checked.divisorHighSmall
  have targetMemory : target.memory=Subtract.digitMemory source.memory base position quotient low middle divisorLow divisorHigh:=by
    rw [endpoint]
    exact written
  have targetStatic : target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock}:=by
    rw [endpoint]
    have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
      {state with
        locals:=(restored source phaseTarget low middle top).locals,
        memory:=(restored source phaseTarget low middle top).memory,
        clock:=(restored source phaseTarget low middle top).clock}) static
    exact projected
  have index:=Estimate.phase_index (prepared source low middle top) phaseTarget base position low middle top divisorLow divisorHigh phaseEntry phaseRun
  have targetI : target.locals.lookup (ofString "i")=some (.val (.word 2#64)):=by
    rw [endpoint,restored_other source phaseTarget low middle top "i" (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact index
  have totalCost:=captures_cost source base position low middle top divisorLow divisorHigh checked
  rw [normal] at totalCost
  exact ⟨quotient,qSmall,qNumber,firstBounds.1,secondBounds.1,remainder,targetMemory,targetStatic,targetI,totalCost⟩

private theorem previous_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (position : Nat)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (position+1))))) :
    eval source previous=some (.val (.word (BitVec.ofNat 64 position))) := by
  have difference:=BitVec.ofNat_sub_ofNat_of_le (w:=64) (position+1) 1 (by decide) (by omega)
  simp [eval,previous,localVar,evalHOLExact,evalListHOLExact,toExact,j,valueIsWord,valueWord,wordOpHOL,wordOp,difference]

/-- The original j decrement enters the real capture block. The staged
entry is a pure description of that exact assignment's current data. -/
theorem body_enter (source : PanSemStateFiniteExact 64 Guest.HostMemory) (position : Nat)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (position+1))))) :
    evaluateHOLFiniteState source body=evaluateHOLFiniteState (bind source "j" (BitVec.ofNat 64 position)) captures := by
  have assigned:=StateSteps.assign_execute source "j" previous (BitVec.ofNat 64 (position+1)) (BitVec.ofNat 64 position) j (previous_read source position j)
  rw [body,evaluateHOLFiniteState_seq_line780,assigned]

/-- The real outer body consumes≤38source ticks at a valid current window;
the enclosing while iteration contributes its own separate tick. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (position+1)))))
    (checked : Window (bind source "j" (BitVec.ofNat 64 position)) base position low middle top divisorLow divisorHigh) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤38 := by
  rw [body_enter source position j]
  exact captures_cost _ base position low middle top divisorLow divisorHigh checked

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.captures_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.captures_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.body_enter
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.body_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem body_other (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (position+1)))))
    (checked : Window (bind source "j" (BitVec.ofNat 64 position)) base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source body=(none,target)) (name : String)
    (notTop : ofString name≠ofString "ujn") (notMiddle : ofString name≠ofString "ujn1") (notLow : ofString name≠ofString "ujn2")
    (notQ : ofString name≠ofString "qhat") (notR : ofString name≠ofString "rhat")
    (notI : ofString name≠ofString "i") (notK : ofString name≠ofString "k") (notAgain : ofString name≠ofString "again") (notJ : ofString name≠ofString "j") :
    target.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  rw [body_enter source position j] at normal
  have kept:=captures_other _ target base position low middle top divisorLow divisorHigh checked normal name notTop notMiddle notLow notQ notR notI notK notAgain
  exact kept.trans (bind_lookup_other _ "j" name _ (Ne.symm notJ))

/-- One actual outer iteration derives its decremented j, real quotient and
remainder stores and typed inner-counter exit from the original execution. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (position : Nat)
    (low middle top divisorLow divisorHigh : BitVec 64)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (position+1)))))
    (checked : Window (bind source "j" (BitVec.ofNat 64 position)) base position low middle top divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source body=(none,target)) :
    ∃ quotient,quotient.toNat<4294967296 ∧
      quotient.toNat=TwoDigitSubtract.window low middle top/TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
      (TwoDigitSubtract.firstLow low quotient divisorLow).toNat<4294967296 ∧
      (TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh).toNat<4294967296 ∧
      (TwoDigitSubtract.firstLow low quotient divisorLow).toNat+4294967296*(TwoDigitSubtract.secondLow low middle quotient divisorLow divisorHigh).toNat=
        TwoDigitSubtract.window low middle top%TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
      target.memory=Subtract.digitMemory source.memory base position quotient low middle divisorLow divisorHigh ∧
      target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock} ∧
      target.locals.lookup (ofString "i")=some (.val (.word 2#64)) ∧
      target.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position))) ∧ source.clock-target.clock≤38 := by
  have entered:=normal
  rw [body_enter source position j] at entered
  obtain ⟨quotient,qSmall,qNumber,lowSmall,middleSmall,remainder,memory,static,index,cost⟩:=captures_normal _ target base position low middle top divisorLow divisorHigh checked entered
  have nextJ : target.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 position))):=
    (captures_other _ target base position low middle top divisorLow divisorHigh checked entered "j"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans checked.j
  have targetStatic : target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock}:=by
    have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
      {state with locals:=target.locals,memory:=target.memory,clock:=target.clock}) static
    exact projected
  exact ⟨quotient,qSmall,qNumber,lowSmall,middleSmall,remainder,memory,targetStatic,index,nextJ,cost⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.body_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.body_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current physical state at the descending quotient-loop guard. The
untouched low prefix and two current carry words determine the next window. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (carryLow carryHigh divisorLow divisorHigh : BitVec 64) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  small : count≤15
  un : source.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator)))
  vn : source.locals.lookup (ofString "vn")=some (.val (.word (Workspace.pointer base .normalizedDivisor)))
  q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))
  j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 count)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))
  highCell : source.locals.lookup (ofString "vtop")=some (.val (.word divisorHigh))
  secondCell : source.locals.lookup (ofString "vsec")=some (.val (.word divisorLow))
  input : ∀ index,index<count→source.memory (slot (Workspace.pointer base .normalizedNumerator) index)=.word (contents index)
  inputSmall : ∀ index,index<count→(contents index).toNat<4294967296
  carryLowCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) count)=.word carryLow
  carryHighCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (count+1))=.word carryHigh
  divisorLowCell : source.memory (slot (Workspace.pointer base .normalizedDivisor) 0)=.word divisorLow
  divisorHighCell : source.memory (slot (Workspace.pointer base .normalizedDivisor) 1)=.word divisorHigh
  carryLowSmall : carryLow.toNat<4294967296
  carryHighSmall : carryHigh.toNat<4294967296
  divisorLowSmall : divisorLow.toNat<4294967296
  divisorHighSmall : divisorHigh.toNat<4294967296
  divisorHighLarge : 2147483648≤divisorHigh.toNat
  carryRange : carryLow.toNat+4294967296*carryHigh.toNat<TwoDigitSubtract.divisorNumber divisorLow divisorHigh

theorem Entry.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} {carryLow carryHigh divisorLow divisorHigh : BitVec 64}
    (checked : Entry source base contents count carryLow carryHigh divisorLow divisorHigh) (clock : Nat) :
    Entry {source with clock:=clock} base contents count carryLow carryHigh divisorLow divisorHigh :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    checked.installed,checked.small,checked.un,checked.vn,checked.q,checked.j,checked.n,checked.i,checked.highCell,checked.secondCell,
    checked.input,checked.inputSmall,checked.carryLowCell,checked.carryHighCell,checked.divisorLowCell,checked.divisorHighCell,
    checked.carryLowSmall,checked.carryHighSmall,checked.divisorLowSmall,checked.divisorHighSmall,checked.divisorHighLarge,checked.carryRange⟩

/-- The next real j assignment exposes a valid per-digit entry. Its range
is derived from the current remainder and the next untouched input digit. -/
theorem Entry.window {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} {carryLow carryHigh divisorLow divisorHigh : BitVec 64}
    (checked : Entry source base contents (count+1) carryLow carryHigh divisorLow divisorHigh) :
    Window (bind source "j" (BitVec.ofNat 64 count)) base count (contents count) carryLow carryHigh divisorLow divisorHigh := by
  refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    checked.installed,by have h:=checked.small;omega,?_,?_,?_,bind_lookup_same _ _ _,?_,?_,?_,?_,
    checked.input count (by omega),checked.carryLowCell,checked.carryHighCell,checked.divisorLowCell,checked.divisorHighCell,
    checked.inputSmall count (by omega),checked.carryLowSmall,checked.divisorLowSmall,checked.divisorHighSmall,checked.divisorHighLarge,?_⟩
  · exact (bind_lookup_other source "j" "un" _ (by decide)).trans checked.un
  · exact (bind_lookup_other source "j" "vn" _ (by decide)).trans checked.vn
  · exact (bind_lookup_other source "j" "q" _ (by decide)).trans checked.q
  · exact (bind_lookup_other source "j" "n" _ (by decide)).trans checked.n
  · obtain ⟨old,cell⟩:=checked.i
    exact ⟨old,(bind_lookup_other source "j" "i" _ (by decide)).trans cell⟩
  · exact (bind_lookup_other source "j" "vtop" _ (by decide)).trans checked.highCell
  · exact (bind_lookup_other source "j" "vsec" _ (by decide)).trans checked.secondCell
  · have range:=checked.carryRange
    have digit:=checked.inputSmall count (by omega)
    unfold TwoDigitSubtract.window
    nlinarith

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.Entry.withClock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.Entry.window

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real normal body produces the next complete physical loop entry.
The original untouched prefix survives, and its current two-word carry is
the derived remainder below the same actual divisor. -/
theorem Entry.successor {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} {carryLow carryHigh divisorLow divisorHigh : BitVec 64}
    (checked : Entry source base contents (count+1) carryLow carryHigh divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source body=(none,target)) :
    ∃ quotient,quotient.toNat<4294967296 ∧
      quotient.toNat=TwoDigitSubtract.window (contents count) carryLow carryHigh/TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
      Entry target base contents count (TwoDigitSubtract.firstLow (contents count) quotient divisorLow)
        (TwoDigitSubtract.secondLow (contents count) carryLow quotient divisorLow divisorHigh) divisorLow divisorHigh ∧
      target.memory=Subtract.digitMemory source.memory base count quotient (contents count) carryLow divisorLow divisorHigh ∧
      target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock} ∧ source.clock-target.clock≤38 := by
  obtain ⟨quotient,qSmall,qNumber,lowSmall,middleSmall,remainder,written,static,index,nextJ,cost⟩:=
    body_normal source target base count (contents count) carryLow carryHigh divisorLow divisorHigh checked.j checked.window normal
  have countSmall:=checked.small
  have cells:=Subtract.digitMemory_cells source base count quotient (contents count) carryLow divisorLow divisorHigh checked.context (by have h:=checked.small;omega)
  have keep:=body_other source target base count (contents count) carryLow carryHigh divisorLow divisorHigh checked.j checked.window normal
  have targetContext : Workspace.Context target base:=by
    have global:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "u256_ws")) static
    have domain:=congrArg PanSemStateFiniteExact.memaddrs static
    exact ⟨global.trans checked.context.global,domain.trans checked.context.domain,checked.context.arena,checked.context.aligned⟩
  have targetInstalled : OriginalCode.Installed target.code:=by
    have code:=congrArg PanSemStateFiniteExact.code static
    rw [code]
    exact checked.installed
  have prefixKept : ∀ position,position<count→target.memory (slot (Workspace.pointer base .normalizedNumerator) position)=.word (contents position):=by
    intro position inside
    rw [written,Subtract.digitMemory_away _ base count quotient (contents count) carryLow divisorLow divisorHigh _]
    · exact checked.input position (by omega)
    · exact Subtract.slots_different source base checked.context position (0+count) (by omega) (by have h:=checked.small;omega) (by omega)
    · exact Subtract.slots_different source base checked.context position (1+count) (by omega) (by have h:=checked.small;omega) (by omega)
    · exact Workspace.separate base .normalizedNumerator .quotient (by intro same;cases same) position count (by change position<17;have h:=checked.small;omega) (by change count<16;have h:=checked.small;omega)
    · exact Subtract.slots_different source base checked.context position (count+2) (by omega) (by have h:=checked.small;omega) (by omega)
  have divisorKept (position : Nat) (inside : position<2) :
      target.memory (slot (Workspace.pointer base .normalizedDivisor) position)=source.memory (slot (Workspace.pointer base .normalizedDivisor) position):=by
    rw [written]
    exact Subtract.digitMemory_away _ base count quotient (contents count) carryLow divisorLow divisorHigh _
      (Workspace.separate base .normalizedDivisor .normalizedNumerator (by intro same;cases same) position (0+count) (by change position<8;omega) (by change 0+count<17;have h:=checked.small;omega))
      (Workspace.separate base .normalizedDivisor .normalizedNumerator (by intro same;cases same) position (1+count) (by change position<8;omega) (by change 1+count<17;have h:=checked.small;omega))
      (Workspace.separate base .normalizedDivisor .quotient (by intro same;cases same) position count (by change position<8;omega) (by change count<16;have h:=checked.small;omega))
      (Workspace.separate base .normalizedDivisor .normalizedNumerator (by intro same;cases same) position (count+2) (by change position<8;omega) (by change count+2<17;have h:=checked.small;omega))
  refine ⟨quotient,qSmall,qNumber,⟨targetContext,targetInstalled,by have h:=checked.small;omega,?_,?_,?_,nextJ,?_,⟨2#64,index⟩,?_,?_,prefixKept,
    (by intro position inside;exact checked.inputSmall position (by omega)),?_,?_,?_,?_,lowSmall,middleSmall,
    checked.divisorLowSmall,checked.divisorHighSmall,checked.divisorHighLarge,?_⟩,written,static,cost⟩
  · exact (keep "un" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans checked.un
  · exact (keep "vn" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans checked.vn
  · exact (keep "q" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans checked.q
  · exact (keep "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans checked.n
  · exact (keep "vtop" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans checked.highCell
  · exact (keep "vsec" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans checked.secondCell
  · rw [written]
    simpa only [Nat.zero_add] using cells.1
  · rw [written]
    simpa only [Nat.add_comm] using cells.2.1
  · exact (divisorKept 0 (by decide)).trans checked.divisorLowCell
  · exact (divisorKept 1 (by decide)).trans checked.divisorHighCell
  · rw [remainder]
    apply Nat.mod_lt
    unfold TwoDigitSubtract.divisorNumber
    have h:=checked.divisorHighLarge
    omega

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.Entry.successor

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
private theorem finish_safe : LocalPrefix (ofString "u") Subtract.finish := by
  simp [Subtract.finish,Subtract.findFinish,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL]
  repeat' first
    | exact LocalPrefix.skip
    | apply LocalPrefix.seq
    | apply LocalPrefix.ite
    | apply LocalPrefix.loop
    | apply LocalPrefix.dec
    | apply LocalPrefix.decCall
    | apply LocalPrefix.assign
    | exact LocalPrefix.store _ _
    | decide

/-- The complete original iteration has no escaping return, break or
continue. Scoped callees retain their own original control behavior. -/
private theorem body_safe : LocalPrefix (ofString "u") body := by
  unfold body captures Estimate.phase Estimate.program Estimate.maximum Estimate.scalar Estimate.updates Estimate.continuation
    Subtract.corrected Subtract.initialized Subtract.loop Subtract.step Subtract.updates
    QhatCorrection.loop QhatCorrection.body QhatCorrection.branch QhatCorrection.correct
  repeat' first
    | exact finish_safe
    | exact LocalPrefix.skip
    | apply LocalPrefix.seq
    | apply LocalPrefix.ite
    | apply LocalPrefix.loop
    | apply LocalPrefix.dec
    | apply LocalPrefix.decCall
    | apply LocalPrefix.assign
    | exact LocalPrefix.store _ _
    | decide

/-- The full actual descending quotient loop costs at most39source ticks
per incoming digit, including every stopped and short-clock outcome. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (carryLow carryHigh divisorLow divisorHigh : BitVec 64)
    (checked : Entry source base contents count carryLow carryHigh divisorLow divisorHigh) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤39*count := by
  induction count generalizing source carryLow carryHigh with
  | zero=>
    have read:=Single.loop_test source 0 (by decide) checked.j
    have done:=Subtract.while_done source test body read
    rw [loop,done]
    simp
  | succ count ih=>
    have read:=Single.loop_test source (count+1) (by have h:=checked.small;omega) checked.j
    simp only [show 0<count+1 from by omega,↓reduceIte] at read
    change evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word 1#64)) at read
    rw [loop,evaluateHOLFiniteState_while_total,read]
    simp only [if_pos (show (1#64 : BitVec 64)≠0 by decide)]
    by_cases zero : source.clock=0
    · simp [zero]
    · rw [if_neg zero]
      have current:=checked.withClock (source.clock-1)
      have price:=body_cost (decClockHOLFinite source) base count (contents count) carryLow carryHigh divisorLow divisorHigh current.j current.window
      have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
      have safe:=body_safe.summary_full (decClockHOLFinite source)
      unfold LocalSummary at safe
      generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body=output at price forward safe ⊢
      obtain ⟨result,middle⟩:=output
      rw [StateSteps.fixed_clock (decClockHOLFinite source) middle result forward]
      change source.clock-1-middle.clock≤38 at price
      change middle.clock≤source.clock-1 at forward
      have stopped : source.clock-middle.clock≤39*(count+1):=by omega
      cases result with
      | none=>
        obtain ⟨quotient,qSmall,qNumber,next,written,static,paid⟩:=current.successor computed
        have tail:=ih middle _ _ next
        have tailClock:=evaluateHOLFiniteState_clock_le middle loop
        change source.clock-(evaluateHOLFiniteState middle loop).2.clock≤39*(count+1)
        omega
      | some result=>
        cases result <;> first
          | exact (safe.2.2.2 rfl).elim
          | exact stopped

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.loop_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem loop_normal_step (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat)
    (small : count+1≤15) (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (count+1)))))
    (normal : evaluateHOLFiniteState source loop=(none,target)) :
    ∃ middle,evaluateHOLFiniteState (decClockHOLFinite source) body=(none,middle) ∧ evaluateHOLFiniteState middle loop=(none,target) := by
  have read:=Single.loop_test source (count+1) (by omega) j
  simp only [show 0<count+1 from by omega,↓reduceIte] at read
  change evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word 1#64)) at read
  rw [loop,evaluateHOLFiniteState_while_total,read] at normal
  simp only [if_pos (show (1#64 : BitVec 64)≠0 by decide)] at normal
  by_cases zero : source.clock=0
  · rw [if_pos zero] at normal
    have impossible:=congrArg Prod.fst normal
    cases impossible
  · rw [if_neg zero] at normal
    have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
    have safe:=body_safe.summary_full (decClockHOLFinite source)
    unfold LocalSummary at safe
    generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body=output at forward safe normal ⊢
    obtain ⟨result,middle⟩:=output
    rw [StateSteps.fixed_clock (decClockHOLFinite source) middle result forward] at normal
    cases result with
    | none=>exact ⟨middle,rfl,normal⟩
    | some result=>
      cases result <;> first
        | exact (safe.2.2.1 rfl).elim
        | exact (safe.2.2.2 rfl).elim
        | cases (congrArg Prod.fst normal)

/-- Full physical output of the original descending loop. Every entry and
conservation fact follows from the same actual normal evaluation. -/
structure LoopResult (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (carryLow carryHigh divisorLow divisorHigh : BitVec 64)
    (quotient : Nat→ BitVec 64) (remainderLow remainderHigh : BitVec 64) : Prop where
  entry : Entry target base contents 0 remainderLow remainderHigh divisorLow divisorHigh
  state : target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock}
  image : Image target (Workspace.pointer base .quotient) quotient count
  digits : ∀ index,index<count→ (quotient index).toNat<4294967296
  value : TwoDigitSubtract.divisorNumber divisorLow divisorHigh*number quotient count+
    (remainderLow.toNat+4294967296*remainderHigh.toNat)=
    (carryLow.toNat+4294967296*carryHigh.toNat)*2^(32*count)+number contents count
  other : ∀ name : String,ofString name≠ofString "ujn"→ ofString name≠ofString "ujn1"→ ofString name≠ofString "ujn2"→
    ofString name≠ofString "qhat"→ ofString name≠ofString "rhat"→ ofString name≠ofString "i"→ ofString name≠ofString "k"→
    ofString name≠ofString "again"→ ofString name≠ofString "j"→ target.locals.lookup (ofString name)=source.locals.lookup (ofString name)
  away : ∀ query,(∀ index,index<count→ query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<count+2→ query≠slot (Workspace.pointer base .normalizedNumerator) index)→ target.memory query=source.memory query
  topZero : 0<count→ target.memory (slot (Workspace.pointer base .normalizedNumerator) 2)=.word 0#64
  cost : source.clock-target.clock≤39*count

/-- Induct over the actual descending loop. The quotient image, final
remainder, outer frames and D*Q+R identity are derived without assuming a
future successful body, helper return or incoming clock funding. -/
theorem loop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (contents : Nat→ BitVec 64) (count : Nat) (carryLow carryHigh divisorLow divisorHigh : BitVec 64)
    (checked : Entry source base contents count carryLow carryHigh divisorLow divisorHigh)
    (normal : evaluateHOLFiniteState source loop=(none,target)) :
    ∃ quotient remainderLow remainderHigh,LoopResult source target base contents count carryLow carryHigh divisorLow divisorHigh quotient remainderLow remainderHigh := by
  have price:=loop_cost source base contents count carryLow carryHigh divisorLow divisorHigh checked
  rw [normal] at price
  induction count generalizing source target carryLow carryHigh with
  | zero=>
    have read:=Single.loop_test source 0 (by decide) checked.j
    have done:=Subtract.while_done source test body read
    have same : target=source:=congrArg Prod.snd (normal.symm.trans done)
    subst target
    refine ⟨(fun _=>0#64),carryLow,carryHigh,⟨checked,?_,?_,?_,?_,?_,?_,?_,price⟩⟩
    · rfl
    · intro index inside
      omega
    · intro index inside
      omega
    · simp [number]
    · intros
      rfl
    · intros
      rfl
    · omega
  | succ count ih=>
    obtain ⟨middle,bodyRun,tailRun⟩:=loop_normal_step source target count checked.small checked.j normal
    have current:=checked.withClock (source.clock-1)
    obtain ⟨digit,digitSmall,digitNumber,next,written,static,paid⟩:=current.successor bodyRun
    obtain ⟨tailDigits,remainderLow,remainderHigh,tail⟩:=ih middle target _ _ next tailRun (by
      have p:=loop_cost middle base contents count _ _ divisorLow divisorHigh next
      rw [tailRun] at p
      exact p)
    let finalDigits : Nat→ BitVec 64:=fun index=>if index=count then digit else tailDigits index
    have lowNumber : number finalDigits count=number tailDigits count:=Single.number_congr finalDigits tailDigits count
      (by intro index inside;simp only [finalDigits,if_neg (show index≠count by omega)])
    have countSmall:=checked.small
    have cells:=Subtract.digitMemory_cells (decClockHOLFinite source) base count digit (contents count) carryLow divisorLow divisorHigh current.context (by omega)
    have outputLast : target.memory (slot (Workspace.pointer base .quotient) count)=.word digit:=by
      have kept:=tail.away (slot (Workspace.pointer base .quotient) count)
        (by
          intro index inside hit
          have same:=slot_injective (Workspace.pointer base .quotient) count index (by omega) (by omega) hit
          omega)
        (by
          intro index inside
          exact Workspace.separate base .quotient .normalizedNumerator (by intro same;cases same) count index
            (by change count<16;omega) (by change index<17;omega))
      rw [kept,written]
      exact cells.2.2.1
    refine ⟨finalDigits,remainderLow,remainderHigh,⟨tail.entry,?_,?_,?_,?_,?_,?_,?_,price⟩⟩
    · have combined:=tail.state
      rw [static] at combined
      exact combined
    · intro index inside
      by_cases last : index=count
      · subst index
        simpa only [finalDigits,if_pos rfl,ite_true] using outputLast
      · simpa only [finalDigits,if_neg last] using tail.image index (by omega)
    · intro index inside
      by_cases last : index=count
      · simpa only [finalDigits,if_pos last] using digitSmall
      · simpa only [finalDigits,if_neg last] using tail.digits index (by omega)
    · have positive : 0<TwoDigitSubtract.divisorNumber divisorLow divisorHigh:=by
        unfold TwoDigitSubtract.divisorNumber
        have h:=checked.divisorHighLarge
        omega
      have remainder:=(TwoDigitSubtract.pair_from_quotient (contents count) carryLow carryHigh digit divisorLow divisorHigh
        (checked.inputSmall count (by omega)) checked.carryLowSmall digitSmall checked.divisorLowSmall checked.divisorHighSmall positive digitNumber).2.2
      have step : TwoDigitSubtract.divisorNumber divisorLow divisorHigh*digit.toNat+
          ((TwoDigitSubtract.firstLow (contents count) digit divisorLow).toNat+
            4294967296*(TwoDigitSubtract.secondLow (contents count) carryLow digit divisorLow divisorHigh).toNat)=
          TwoDigitSubtract.window (contents count) carryLow carryHigh:=by
        rw [digitNumber,remainder]
        exact Nat.div_add_mod _ _
      have scaled:=congrArg (fun value:Nat=>value*2^(32*count)) step
      have power : 2^(32*(count+1))=4294967296*2^(32*count):=by
        rw [show 32*(count+1)=32+32*count by omega,Nat.pow_add]
      have tailValue:=tail.value
      rw [number,lowNumber]
      simp only [finalDigits,if_pos rfl,ite_true]
      rw [number,power]
      unfold TwoDigitSubtract.window at scaled
      nlinarith [scaled,tailValue]
    · intro name notTop notMiddle notLow notQ notR notI notK notAgain notJ
      exact (tail.other name notTop notMiddle notLow notQ notR notI notK notAgain notJ).trans
        (body_other (decClockHOLFinite source) middle base count (contents count) carryLow carryHigh divisorLow divisorHigh current.j current.window bodyRun name
          notTop notMiddle notLow notQ notR notI notK notAgain notJ)
    · intro query outsideQ outsideUN
      rw [tail.away query (by intro index inside;exact outsideQ index (by omega)) (by intro index inside;exact outsideUN index (by omega)),written]
      exact Subtract.digitMemory_away _ base count digit (contents count) carryLow divisorLow divisorHigh query
        (outsideUN (0+count) (by omega)) (outsideUN (1+count) (by omega)) (outsideQ count (by omega)) (outsideUN (count+2) (by omega))
    · intro positive
      by_cases zero : count=0
      · subst count
        have finalSame : target=middle:=by
          have read:=Single.loop_test middle 0 (by decide) next.j
          have done:=Subtract.while_done middle test body read
          exact congrArg Prod.snd (tailRun.symm.trans done)
        rw [finalSame,written]
        exact cells.2.2.2
      · exact tail.topZero (by omega)

/-- The derived physical quotient/remainder obey ordinary natural division. -/
theorem LoopResult.division {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {contents quotient : Nat→ BitVec 64} {count : Nat} {carryLow carryHigh divisorLow divisorHigh remainderLow remainderHigh : BitVec 64}
    (checked : LoopResult source target base contents count carryLow carryHigh divisorLow divisorHigh quotient remainderLow remainderHigh) :
    number quotient count=((carryLow.toNat+4294967296*carryHigh.toNat)*2^(32*count)+number contents count)/TwoDigitSubtract.divisorNumber divisorLow divisorHigh ∧
    remainderLow.toNat+4294967296*remainderHigh.toNat=((carryLow.toNat+4294967296*carryHigh.toNat)*2^(32*count)+number contents count)%TwoDigitSubtract.divisorNumber divisorLow divisorHigh := by
  have positive : 0<TwoDigitSubtract.divisorNumber divisorLow divisorHigh:=by
    have small:=checked.entry.carryRange
    omega
  constructor
  · rw [←checked.value,Nat.mul_add_div positive,Nat.div_eq_of_lt checked.entry.carryRange,Nat.add_zero]
  · rw [←checked.value,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt checked.entry.carryRange]

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.loop_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.LoopResult.division

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The two actual top normalized numerator words form a carry below the
normalized divisor. This comes from the original32-bit input and the same
normalization factor; no future quotient-loop range is assumed. -/
theorem Ready.initial_carry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v : Nat→BitVec 64} {length bits : Nat} (ready : Ready source base u v length bits) :
    (Normalized.extended u bits length (length-1)).toNat+
      4294967296*(Normalized.extended u bits length length).toNat<
      TwoDigitSubtract.divisorNumber (Normalized.digit v bits 0) (Normalized.digit v bits 1) := by
  have large:=ready.entry.large
  have lastInside : length-1<length:=by omega
  have balance:=Normalized.digit_balance u bits (length-1) ready.bitsSmall
    (by intro index inside;exact ready.entry.uSmall index (by omega))
  have incomingBound : (Normalized.incoming u bits (length-1)).toNat<2^bits:=by
    have nonzero : length-1≠0:=by omega
    obtain ⟨previous,previousEq⟩:=Nat.exists_eq_succ_of_ne_zero nonzero
    rw [previousEq,Normalized.incoming]
    exact Normalize.high_bound (u previous) bits ready.bitsSmall (ready.entry.uSmall previous (by omega))
  have lastSmall:=ready.entry.uSmall (length-1) lastInside
  have normalizedDivisor : TwoDigitSubtract.divisorNumber (Normalized.digit v bits 0) (Normalized.digit v bits 1)=number v 2*2^bits:=by
    simpa only [number,TwoDigitSubtract.divisorNumber,Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.zero_add,Nat.one_mul,show (2:Nat)^32=4294967296 by decide] using ready.v_number
  have divisorLarge : 4294967296≤number v 2:=by
    simp only [number,Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.zero_add,Nat.one_mul]
    have positive:=ready.entry.leadingPositive
    omega
  have scaled:=Nat.mul_le_mul_right (2^bits) divisorLarge
  have carryIndex : Normalized.incoming u bits length=Normalized.incoming u bits (length-1+1):=by rw [show length-1+1=length by omega]
  rw [Normalized.extended,if_pos lastInside,Normalized.extended,if_neg (by omega),carryIndex,balance.2,normalizedDivisor]
  nlinarith

end InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.Ready.initial_carry

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Pure description of the original two leading-divisor declarations
and original j initialization at the first outer guard. -/
def start (source : PanSemStateFiniteExact 64 Guest.HostMemory) (v : Nat→BitVec 64) (length bits : Nat) :=
  bind (bind (bind source "vtop" (Normalized.digit v bits 1)) "vsec" (Normalized.digit v bits 0)) "j" (BitVec.ofNat 64 (length-1))

private theorem start_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (v : Nat→BitVec 64) (length bits : Nat) (name : String)
    (notTop : ofString name≠ofString "vtop") (notSecond : ofString name≠ofString "vsec") (notJ : ofString name≠ofString "j") :
    (start source v length bits).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "j" name _ (Ne.symm notJ)).trans ((bind_lookup_other _ "vsec" name _ (Ne.symm notSecond)).trans
    (bind_lookup_other _ "vtop" name _ (Ne.symm notTop)))

/-- The already checked physical normalization supplies every initial
loop invariant, including its derived carry range and actual mapped words. -/
theorem normalization_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (ready : Normalization.Ready source base u v length bits)
    (installed : OriginalCode.Installed source.code)
    (q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))) :
    Entry (start source v length bits) base (Normalized.extended u bits length) (length-1)
      (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
      (Normalized.digit v bits 0) (Normalized.digit v bits 1) := by
  have large:=ready.entry.large
  have small:=ready.entry.small
  have uBounds:=ready.u_number.2
  refine ⟨⟨ready.entry.context.global,ready.entry.context.domain,ready.entry.context.arena,ready.entry.context.aligned⟩,
    installed,by omega,?_,?_,?_,bind_lookup_same _ _ _,?_,?_,?_,?_,?_,?_,?_,?_,ready.vImage 0 (by decide),ready.vImage 1 (by decide),
    uBounds (length-1) (by omega),uBounds length (by omega),?_,ready.top_large.2,ready.top_large.1,ready.initial_carry⟩
  · exact (start_other source v length bits "un" (by decide) (by decide) (by decide)).trans ready.entry.un
  · exact (start_other source v length bits "vn" (by decide) (by decide) (by decide)).trans ready.entry.vn
  · exact (start_other source v length bits "q" (by decide) (by decide) (by decide)).trans q
  · exact (start_other source v length bits "n" (by decide) (by decide) (by decide)).trans ready.entry.n
  · exact ⟨0#64,(start_other source v length bits "i" (by decide) (by decide) (by decide)).trans ready.i⟩
  · exact (bind_lookup_other _ "j" "vtop" _ (by decide)).trans ((bind_lookup_other _ "vsec" "vtop" _ (by decide)).trans (bind_lookup_same _ _ _))
  · exact (bind_lookup_other _ "j" "vsec" _ (by decide)).trans (bind_lookup_same _ _ _)
  · intro index inside
    exact ready.uImage index (by omega)
  · intro index inside
    exact uBounds index (by omega)
  · exact ready.uImage (length-1) (by omega)
  · change source.memory (slot (Workspace.pointer base .normalizedNumerator) (length-1+1))=.word (Normalized.extended u bits length length)
    simpa only [show length-1+1=length by omega] using ready.uImage length (by omega)
  · exact (Normalize.first_balance (v 0) bits ready.bitsSmall (ready.entry.vSmall 0 (by decide))).1

private theorem top_pair_number (contents : Nat→BitVec 64) (count : Nat) :
    ((contents count).toNat+4294967296*(contents (count+1)).toNat)*2^(32*count)+number contents count=number contents (count+2) := by
  have power : 2^(32*(count+1))=4294967296*2^(32*count):=by
    rw [show 32*(count+1)=32+32*count by omega,Nat.pow_add]
  rw [number,number,power]
  ring

/-- The loop's actual low prefix and top carry represent the whole
normalized numerator, hence the original numerator times the same factor. -/
theorem normalization_number (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (ready : Normalization.Ready source base u v length bits) :
    ((Normalized.extended u bits length (length-1)).toNat+4294967296*(Normalized.extended u bits length length).toNat)*2^(32*(length-1))+
      number (Normalized.extended u bits length) (length-1)=number u length*2^bits := by
  have large:=ready.entry.large
  have pair:=top_pair_number (Normalized.extended u bits length) (length-1)
  rw [show length-1+1=length by omega,show length-1+2=length+1 by omega] at pair
  exact pair.trans ready.u_number.1

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.normalization_entry
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.normalization_number

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def topLoad : ExpHOL 64:=.load .one (NormalizeLoop.address "vn" (.op .sub [localVar "n",.const 1#64]))
def secondLoad : ExpHOL 64:=.load .one (NormalizeLoop.address "vn" (.op .sub [localVar "n",.const 2#64]))
def countExpression : ExpHOL 64:=.op .add [.op .sub [localVar "m",localVar "n"],.const 1#64]
def leading (continuation : ProgHOL 64) : ProgHOL 64:=
  .dec (ofString "vtop") .one topLoad (.dec (ofString "vsec") .one secondLoad
    (.seq (.assign .local (ofString "j") countExpression) continuation))
def startRestored (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (v : Nat→BitVec 64) (bits : Nat) :=
  restore source "vtop" (restore (bind source "vtop" (Normalized.digit v bits 1)) "vsec" target)

private def findLeading : ProgHOL 64→Option (ProgHOL 64)
  | .dec name shape expression rest=>
    if name=ofString "vtop" then some (.dec name shape expression rest) else findLeading rest
  | .seq first rest=>(findLeading first).orElse (fun _=>findLeading rest)
  | .ite _ yes no=>(findLeading yes).orElse (fun _=>findLeading no)
  | .while _ contents=>findLeading contents
  | .decCall _ _ _ _ rest=>findLeading rest
  | _=>none

set_option maxRecDepth 100000 in
/-- Original leading VN loads, lexical declarations and m-n+1 assignment,
with its complete original quotient/remainder continuation retained. -/
theorem literal_leading : ∃ continuation,findLeading Single.body=some (leading continuation) := by
  have not_i : ofString "i"≠ofString "vtop":=by decide
  have not_j : ofString "j"≠ofString "vtop":=by decide
  have not_d : ofString "d"≠ofString "vtop":=by decide
  have not_k : ofString "k"≠ofString "vtop":=by decide
  have not_un : ofString "un"≠ofString "vtop":=by decide
  have not_vn : ofString "vn"≠ofString "vtop":=by decide
  simp [findLeading,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    leading,topLoad,secondLoad,countExpression,NormalizeLoop.address,localVar,not_i,not_j,not_d,not_k,not_un,not_vn]

private theorem leading_reads (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (ready : Normalization.Ready source base u v length bits) :
    eval source topLoad=some (.val (.word (Normalized.digit v bits 1))) ∧
    eval (bind source "vtop" (Normalized.digit v bits 1)) secondLoad=some (.val (.word (Normalized.digit v bits 0))) := by
  have previous:=NormalizeLoop.counter_previous_read source "n" 2 (by decide) ready.entry.n
  have highAddress:=NormalizeLoop.indexed_address_read source "vn" (Workspace.pointer base .normalizedDivisor) _ 1 ready.entry.vn previous
  have highRead:=Witness.load_word_read source _ _ (Normalized.digit v bits 1) highAddress
    (Workspace.slot_mapped source base ready.entry.context .normalizedDivisor 1 (by decide)) (ready.vImage 1 (by decide))
  let first:=bind source "vtop" (Normalized.digit v bits 1)
  have n : first.locals.lookup (ofString "n")=some (.val (.word 2#64)):=
    (bind_lookup_other source "vtop" "n" _ (by decide)).trans ready.entry.n
  have vn : first.locals.lookup (ofString "vn")=some (.val (.word (Workspace.pointer base .normalizedDivisor))):=
    (bind_lookup_other source "vtop" "vn" _ (by decide)).trans ready.entry.vn
  have lower : eval first (.op .sub [localVar "n",.const 2#64])=some (.val (.word 0#64)):=by
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,n,valueIsWord,valueWord,wordOpHOL,wordOp]
  have lowAddress:=NormalizeLoop.indexed_address_read first "vn" (Workspace.pointer base .normalizedDivisor) _ 0 vn lower
  have lowRead:=Witness.load_word_read first _ _ (Normalized.digit v bits 0) lowAddress
    (Workspace.slot_mapped source base ready.entry.context .normalizedDivisor 0 (by decide)) (ready.vImage 0 (by decide))
  exact ⟨highRead,lowRead⟩

private theorem count_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (large : 2≤length)
    (m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 length))))
    (n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))) :
    eval source countExpression=some (.val (.word (BitVec.ofNat 64 (length-1)))) := by
  have difference:=BitVec.ofNat_sub_ofNat_of_le (w:=64) length 2 (by decide) large
  have result : BitVec.ofNat 64 length-2#64+1#64=BitVec.ofNat 64 (length-1):=by
    rw [difference,←BitVec.ofNat_add]
    congr 1
    omega
  simp [eval,countExpression,localVar,evalHOLExact,evalListHOLExact,toExact,m,n,valueIsWord,valueWord,wordOpHOL,wordOp,result]

/-- Both actual mapped VN loads and the original typed j assignment resume
any original continuation at the proved first-guard state, at every clock. -/
theorem leading_execute (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (ready : Normalization.Ready source base u v length bits)
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old)))
    (continuation : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState (start source v length bits) continuation=(result,target)) :
    evaluateHOLFiniteState source (leading continuation)=(result,startRestored source target v bits) := by
  let first:=bind source "vtop" (Normalized.digit v bits 1)
  let second:=bind first "vsec" (Normalized.digit v bits 0)
  have m : second.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other _ "vsec" "m" _ (by decide)).trans ((bind_lookup_other _ "vtop" "m" _ (by decide)).trans ready.entry.m)
  have n : second.locals.lookup (ofString "n")=some (.val (.word 2#64)):=
    (bind_lookup_other _ "vsec" "n" _ (by decide)).trans ((bind_lookup_other _ "vtop" "n" _ (by decide)).trans ready.entry.n)
  obtain ⟨old,j⟩:=j
  have oldJ : second.locals.lookup (ofString "j")=some (.val (.word old)):=
    (bind_lookup_other _ "vsec" "j" _ (by decide)).trans ((bind_lookup_other _ "vtop" "j" _ (by decide)).trans j)
  have assigned:=StateSteps.assign_execute second "j" countExpression old (BitVec.ofNat 64 (length-1)) oldJ (count_read second length ready.entry.large m n)
  have resumed : evaluateHOLFiniteState second (.seq (.assign .local (ofString "j") countExpression) continuation)=(result,target):=by
    rw [StateSteps.next_sequence second (start source v length bits) _ _ assigned (by rfl)]
    exact run
  have reads:=leading_reads source base u v length bits ready
  have inner:=ScalarScope.declare_execute first target "vsec" secondLoad (Normalized.digit v bits 0) _ result reads.2 resumed
  exact ScalarScope.declare_execute source _ "vtop" topLoad (Normalized.digit v bits 1) _ result reads.1 inner

/-- Complete original leading prefix and outer loop, all outcomes. -/
theorem leading_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (ready : Normalization.Ready source base u v length bits)
    (installed : OriginalCode.Installed source.code)
    (q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))))
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old))) :
    source.clock-(evaluateHOLFiniteState source (leading loop)).2.clock≤39*(length-1) := by
  let output:=evaluateHOLFiniteState (start source v length bits) loop
  have actual:=leading_execute source output.2 base u v length bits ready j loop output.1 rfl
  have price:=loop_cost (start source v length bits) base (Normalized.extended u bits length) (length-1)
    (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
    (Normalized.digit v bits 0) (Normalized.digit v bits 1) (normalization_entry source base u v length bits ready installed q)
  rw [actual]
  exact price

/-- A normal execution of the actual leading prefix and complete outer
loop exposes its physical quotient/remainder result inside the true scopes. -/
theorem leading_loop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (ready : Normalization.Ready source base u v length bits)
    (installed : OriginalCode.Installed source.code)
    (q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))))
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old)))
    (normal : evaluateHOLFiniteState source (leading loop)=(none,target)) :
    ∃ inner quotient remainderLow remainderHigh,target=startRestored source inner v bits ∧
      LoopResult (start source v length bits) inner base (Normalized.extended u bits length) (length-1)
        (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
        (Normalized.digit v bits 0) (Normalized.digit v bits 1) quotient remainderLow remainderHigh := by
  let output:=evaluateHOLFiniteState (start source v length bits) loop
  have actual:=leading_execute source output.2 base u v length bits ready j loop output.1 rfl
  have observed : output.1=none:=congrArg Prod.fst (actual.symm.trans normal)
  have loopRun : evaluateHOLFiniteState (start source v length bits) loop=(none,output.2):=Prod.ext observed rfl
  obtain ⟨quotient,remainderLow,remainderHigh,checked⟩:=loop_normal (start source v length bits) output.2 base (Normalized.extended u bits length) (length-1)
    (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
    (Normalized.digit v bits 0) (Normalized.digit v bits 1) (normalization_entry source base u v length bits ready installed q) loopRun
  exact ⟨output.2,quotient,remainderLow,remainderHigh,congrArg Prod.snd (normal.symm.trans actual),checked⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.literal_leading
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.leading_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.leading_loop_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.leading_loop_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Outer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Cancel the actual common normalization factor in the quotient and
remainder derived by the physical original outer-loop execution. -/
theorem normalization_division (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v quotient : Nat→BitVec 64) (length bits : Nat) (remainderLow remainderHigh : BitVec 64)
    (ready : Normalization.Ready source base u v length bits)
    (checked : LoopResult (start source v length bits) target base (Normalized.extended u bits length) (length-1)
      (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
      (Normalized.digit v bits 0) (Normalized.digit v bits 1) quotient remainderLow remainderHigh) :
    number quotient (length-1)=number u length/number v 2 ∧
      remainderLow.toNat+4294967296*remainderHigh.toNat=(number u length%number v 2)*2^bits ∧
      (Denormalize.digit remainderLow remainderHigh bits).toNat+4294967296*(Denormalize.digit remainderHigh 0#64 bits).toNat=number u length%number v 2 := by
  have divisorNumber : TwoDigitSubtract.divisorNumber (Normalized.digit v bits 0) (Normalized.digit v bits 1)=number v 2*2^bits:=by
    simpa only [number,TwoDigitSubtract.divisorNumber,Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.zero_add,Nat.one_mul,show (2:Nat)^32=4294967296 by decide] using ready.v_number
  have division:=checked.division
  rw [normalization_number source base u v length bits ready,divisorNumber] at division
  have quotientEq : number quotient (length-1)=number u length/number v 2:=
    division.1.trans (Nat.mul_div_mul_right _ _ (Nat.two_pow_pos bits))
  have remainderEq : remainderLow.toNat+4294967296*remainderHigh.toNat=(number u length%number v 2)*2^bits:=
    division.2.trans (Nat.mul_mod_mul_right (2^bits) _ _)
  refine ⟨quotientEq,remainderEq,?_⟩
  rw [Denormalize.pair_number remainderLow remainderHigh bits ready.bitsSmall checked.entry.carryLowSmall checked.entry.carryHighSmall,
    remainderEq,Nat.mul_div_cancel _ (Nat.two_pow_pos bits)]

end InitECandidate.Solver.Input.UDivMod.WideDigits.Outer

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Outer.normalization_division

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def nextIndex : ExpHOL 64:=.op .add [localVar "i",.const 1#64]
def inputAddress : ExpHOL 64:=NormalizeLoop.address "un" (localVar "i")
def nextAddress : ExpHOL 64:=NormalizeLoop.address "un" nextIndex
def outputAddress : ExpHOL 64:=NormalizeLoop.address "r" (localVar "i")
def expression : ExpHOL 64:=.op .or [
  .shift .lsr (.load .one inputAddress) (localVar "s"),
  .op .and [.shift .lsl (.load .one nextAddress) NormalizeLoop.remaining,.const 4294967295#64]]
def step : ProgHOL 64:=.seq (.store outputAddress expression) (.assign .local (ofString "i") nextIndex)
def test : ExpHOL 64:=.cmp .lower (localVar "i") (localVar "n")
def loop : ProgHOL 64:=.while test step

def stepPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index : Nat) (low high : BitVec 64) (bits : Nat) :=
  bind {source with memory:=StoreWord.put source.memory (slot (Workspace.pointer base .remainder) index) (Denormalize.digit low high bits)} "i" (BitVec.ofNat 64 (index+1))

structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index : Nat) (low high : BitVec 64) (bits : Nat) : Prop where
  context : Workspace.Context source base
  inside : index<2
  bitsSmall : bits≤31
  un : source.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator)))
  r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits)))
  i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  lowCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) index)=.word low
  highCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) (index+1))=.word high

theorem Entry.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {index : Nat} {low high : BitVec 64} {bits : Nat}
    (checked : Entry source base index low high bits) (clock : Nat) : Entry {source with clock:=clock} base index low high bits :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    checked.inside,checked.bitsSmall,checked.un,checked.r,checked.n,checked.s,checked.i,checked.lowCell,checked.highCell⟩

private theorem next_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source nextIndex=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
  simp [eval,nextIndex,localVar,evalHOLExact,evalListHOLExact,toExact,i,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]

private theorem expression_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index : Nat) (low high : BitVec 64) (bits : Nat)
    (checked : Entry source base index low high bits) : eval source expression=some (.val (.word (Denormalize.digit low high bits))) := by
  have lowRead:=Witness.load_word_read source inputAddress _ low
    (NormalizeLoop.address_read source "un" (Workspace.pointer base .normalizedNumerator) index checked.un checked.i)
    (Workspace.slot_mapped source base checked.context .normalizedNumerator index (by have h:=checked.inside;change index<17;omega)) checked.lowCell
  have highAddress:=NormalizeLoop.indexed_address_read source "un" (Workspace.pointer base .normalizedNumerator) nextIndex (index+1) checked.un (next_read source index checked.i)
  have highRead:=Witness.load_word_read source nextAddress _ high highAddress
    (Workspace.slot_mapped source base checked.context .normalizedNumerator (index+1) (by have h:=checked.inside;change index+1<17;omega)) checked.highCell
  have bitsNumber : (BitVec.ofNat 64 bits).toNat=bits:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=checked.bitsSmall;omega)]
  have restNumber : (BitVec.ofNat 64 (32-bits)).toNat=32-bits:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have right:=NormalizeLoop.shift_read source .lsr (.load .one inputAddress) (localVar "s") low (BitVec.ofNat 64 bits) (low>>>bits)
    lowRead (Subtract.local_read source "s" _ checked.s) (by simp [wordShiftHOL,bitsNumber,show bits<64 from by have h:=checked.bitsSmall;omega])
  have left:=NormalizeLoop.shift_read source .lsl (.load .one nextAddress) NormalizeLoop.remaining high (BitVec.ofNat 64 (32-bits)) (high<<<(32-bits))
    highRead (NormalizeLoop.remaining_read source bits checked.bitsSmall checked.s) (by simp [wordShiftHOL,restNumber,show 32-bits<64 from by omega])
  have masked:=Subtract.binary_read source .and _ (.const 4294967295#64) _ 4294967295#64 ((high<<<(32-bits)) &&& 4294967295#64) left rfl rfl
  exact Subtract.binary_read source .or _ _ _ _ (Denormalize.digit low high bits) right masked (by simp [Denormalize.digit,wordOpHOL,wordOp,OrOp.or])

/-- The original two mapped UN loads and original shifts/mask/OR write
one actual R word and advance the real inner counter, at every clock. -/
theorem step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index : Nat) (low high : BitVec 64) (bits : Nat)
    (checked : Entry source base index low high bits) : evaluateHOLFiniteState source step=(none,stepPost source base index low high bits) := by
  have stored:=StoreWord.execute source outputAddress expression _ (Denormalize.digit low high bits)
    (NormalizeLoop.address_read source "r" (Workspace.pointer base .remainder) index checked.r checked.i)
    (expression_read source base index low high bits checked)
    (Workspace.slot_mapped source base checked.context .remainder index (by have h:=checked.inside;change index<8;omega))
  rw [step,evaluateHOLFiniteState_seq_line780,stored]
  exact StateSteps.assign_execute _ "i" nextIndex _ _ checked.i (next_read _ index checked.i)

/-- All work of this literal step is straight-line source work. -/
theorem step_cost (code) : ClockCost.Bound code step 0 :=
  ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.assign code _ _)

theorem stepPost_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index : Nat) (low high : BitVec 64) (bits : Nat)
    (name : String) (notI : ofString name≠ofString "i") :
    (stepPost source base index low high bits).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  bind_lookup_other _ "i" name _ (Ne.symm notI)

theorem stepPost_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (index : Nat) (low high : BitVec 64) (bits : Nat) (query : BitVec 64)
    (outside : query≠slot (Workspace.pointer base .remainder) index) :
    (stepPost source base index low high bits).memory query=source.memory query := by
  simp only [stepPost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,StoreWord.put,if_neg outside]

end InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.step_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.step_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.stepPost_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.stepPost_away

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat) : Prop where
  context : Workspace.Context source base
  bitsSmall : bits≤31
  un : source.locals.lookup (ofString "un")=some (.val (.word (Workspace.pointer base .normalizedNumerator)))
  r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 bits)))
  lowCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) 0)=.word low
  highCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) 1)=.word high
  zeroCell : source.memory (slot (Workspace.pointer base .normalizedNumerator) 2)=.word 0#64
  lowSmall : low.toNat<4294967296
  highSmall : high.toNat<4294967296

theorem Ready.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base low high : BitVec 64} {bits : Nat}
    (checked : Ready source base low high bits) (clock : Nat) : Ready {source with clock:=clock} base low high bits :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    checked.bitsSmall,checked.un,checked.r,checked.n,checked.s,checked.lowCell,checked.highCell,checked.zeroCell,checked.lowSmall,checked.highSmall⟩

theorem Ready.bindI {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base low high : BitVec 64} {bits : Nat}
    (checked : Ready source base low high bits) (word : BitVec 64) : Ready (bind source "i" word) base low high bits := by
  refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    checked.bitsSmall,?_,?_,?_,?_,checked.lowCell,checked.highCell,checked.zeroCell,checked.lowSmall,checked.highSmall⟩
  · exact (bind_lookup_other source "i" "un" word (by decide)).trans checked.un
  · exact (bind_lookup_other source "i" "r" word (by decide)).trans checked.r
  · exact (bind_lookup_other source "i" "n" word (by decide)).trans checked.n
  · exact (bind_lookup_other source "i" "s" word (by decide)).trans checked.s

private theorem Ready.first {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base low high : BitVec 64} {bits : Nat}
    (checked : Ready source base low high bits) (i : source.locals.lookup (ofString "i")=some (.val (.word 0#64))) : Entry source base 0 low high bits :=
  ⟨checked.context,by decide,checked.bitsSmall,checked.un,checked.r,checked.n,checked.s,i,checked.lowCell,checked.highCell⟩

private theorem Ready.second {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base low high : BitVec 64} {bits : Nat}
    (checked : Ready source base low high bits) : Entry (stepPost (decClockHOLFinite source) base 0 low high bits) base 1 high 0#64 bits := by
  refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,
    by decide,checked.bitsSmall,?_,?_,?_,?_,bind_lookup_same _ _ _,?_,?_⟩
  · exact (stepPost_other _ base 0 low high bits "un" (by decide)).trans checked.un
  · exact (stepPost_other _ base 0 low high bits "r" (by decide)).trans checked.r
  · exact (stepPost_other _ base 0 low high bits "n" (by decide)).trans checked.n
  · exact (stepPost_other _ base 0 low high bits "s" (by decide)).trans checked.s
  · exact (stepPost_away _ base 0 low high bits _ (Workspace.separate base .normalizedNumerator .remainder (by intro same;cases same) 1 0 (by decide) (by decide))).trans checked.highCell
  · exact (stepPost_away _ base 0 low high bits _ (Workspace.separate base .normalizedNumerator .remainder (by intro same;cases same) 2 0 (by decide) (by decide))).trans checked.zeroCell

def pairPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat) :=
  stepPost (decClockHOLFinite (stepPost (decClockHOLFinite source) base 0 low high bits)) base 1 high 0#64 bits

theorem pairPost_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat) :
    pairPost source base low high bits={source with
      locals:=(pairPost source base low high bits).locals,
      memory:=StoreWord.put (StoreWord.put source.memory (slot (Workspace.pointer base .remainder) 0) (Denormalize.digit low high bits))
        (slot (Workspace.pointer base .remainder) 1) (Denormalize.digit high 0#64 bits),clock:=source.clock-2} := by
  simp only [pairPost,stepPost,WitnessRadix.QueryBranch.bind,setVarHOLFinite,decClockHOLFinite]
  congr 1

theorem pairPost_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat) (name : String)
    (notI : ofString name≠ofString "i") : (pairPost source base low high bits).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (stepPost_other _ base 1 high 0#64 bits name notI).trans (stepPost_other _ base 0 low high bits name notI)

private theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (small : index≤2)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word (if index<2 then 1#64 else 0#64))) := by
  have indexNumber : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [finite_eval]
  simp [eval,test,localVar,evalHOLExact,toExact,i,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,indexNumber]

/-- Both actual remainder iterations and the original final false guard. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat)
    (checked : Ready source base low high bits) (i : source.locals.lookup (ofString "i")=some (.val (.word 0#64))) (enough : 2≤source.clock) :
    evaluateHOLFiniteState source loop=(none,pairPost source base low high bits) := by
  let first:=stepPost (decClockHOLFinite source) base 0 low high bits
  let second:=pairPost source base low high bits
  have firstRun:=step_execute (decClockHOLFinite source) base 0 low high bits ((checked.first i).withClock (source.clock-1))
  have secondEntry:=checked.second
  have secondRun:=step_execute (decClockHOLFinite first) base 1 high 0#64 bits (secondEntry.withClock (first.clock-1))
  have read0:=test_read source 0 (by decide) i checked.n
  have read1:=test_read first 1 (by decide) secondEntry.i secondEntry.n
  have read2:=test_read second 2 (by decide) (bind_lookup_same _ _ _) ((pairPost_other source base low high bits "n" (by decide)).trans checked.n)
  simp only [if_pos (by decide : 0<2)] at read0
  simp only [if_pos (by decide : 1<2)] at read1
  simp only [if_neg (by decide : ¬2<2)] at read2
  have done : evaluateHOLFiniteState second loop=(none,second):=Subtract.while_done second test step read2
  have firstClock : first.clock=source.clock-1:=rfl
  have tail : evaluateHOLFiniteState first loop=(none,second):=
    Subtract.while_next first second second test step read1 (by rw [firstClock];omega) secondRun done
  exact Subtract.while_next source first second test step read0 (by omega) firstRun tail

/-- Every actual stopped or short-clock remainder loop costs≤2ticks. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat)
    (checked : Ready source base low high bits) (i : source.locals.lookup (ofString "i")=some (.val (.word 0#64))) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤2 := by
  by_cases enough : 2≤source.clock
  · rw [loop_execute source base low high bits checked i enough]
    have clock:=congrArg PanSemStateFiniteExact.clock (pairPost_frame source base low high bits)
    change (pairPost source base low high bits).clock=source.clock-2 at clock
    change source.clock-(pairPost source base low high bits).clock≤2
    omega
  · omega

/-- A real normal loop derives its own two ticks and exact physical stores. -/
theorem loop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat)
    (checked : Ready source base low high bits) (i : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source loop=(none,target)) : 2≤source.clock ∧ target=pairPost source base low high bits := by
  let fundedSource:={source with clock:=2}
  let paid:=pairPost fundedSource base low high bits
  have baseRun:=loop_execute fundedSource base low high bits (checked.withClock 2) i (by rfl)
  have zero : paid.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock (pairPost_frame fundedSource base low high bits)
    change paid.clock=2-2 at clock
    exact clock
  have funded:=(ClockCost.normal_from_zero_clock source paid target loop 2 none none baseRun zero (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)).1
  have actual:=loop_execute source base low high bits checked i funded
  exact ⟨funded,congrArg Prod.snd (normal.symm.trans actual)⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.pairPost_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.pairPost_other
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.loop_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.loop_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.loop_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Both final original R stores are retained in their actual physical cells. -/
theorem pairPost_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat) :
    (pairPost source base low high bits).memory (slot (Workspace.pointer base .remainder) 0)=.word (Denormalize.digit low high bits) ∧
    (pairPost source base low high bits).memory (slot (Workspace.pointer base .remainder) 1)=.word (Denormalize.digit high 0#64 bits) := by
  have different : slot (Workspace.pointer base .remainder) 0≠slot (Workspace.pointer base .remainder) 1:=by
    intro hit
    have same:=slot_injective (Workspace.pointer base .remainder) 0 1 (by decide) (by decide) hit
    omega
  have memory:=congrArg PanSemStateFiniteExact.memory (pairPost_frame source base low high bits)
  rw [memory]
  simp only [StoreWord.put,if_neg different,if_pos rfl,ite_true,and_self]

theorem pairPost_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat) (query : BitVec 64)
    (outsideLow : query≠slot (Workspace.pointer base .remainder) 0) (outsideHigh : query≠slot (Workspace.pointer base .remainder) 1) :
    (pairPost source base low high bits).memory query=source.memory query := by
  have memory:=congrArg PanSemStateFiniteExact.memory (pairPost_frame source base low high bits)
  rw [memory]
  simp only [StoreWord.put,if_neg outsideLow,if_neg outsideHigh]

def complete : ProgHOL 64:=.seq (.assign .local (ofString "i") (.const 0#64)) (.seq loop (.return (.const 0#64)))

private def findComplete : ProgHOL 64→Option (ProgHOL 64)
  | .seq (.assign .local name expression) (.seq (.while condition contents) (.return result))=>
    if name=ofString "i" then some (.seq (.assign .local name expression) (.seq (.while condition contents) (.return result))) else findComplete contents
  | .dec _ _ _ rest=>findComplete rest
  | .seq first rest=>(findComplete first).orElse (fun _=>findComplete rest)
  | .ite _ yes no=>(findComplete yes).orElse (fun _=>findComplete no)
  | .while _ contents=>findComplete contents
  | .decCall _ _ _ _ rest=>findComplete rest
  | _=>none

set_option maxRecDepth 100000 in
/-- The literal original i initialization, final remainder loop and return0. -/
theorem literal_complete : findComplete Single.body=some complete := by
  simp [findComplete,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    complete,loop,test,step,expression,inputAddress,nextAddress,outputAddress,nextIndex,NormalizeLoop.remaining,NormalizeLoop.address,localVar]

/-- The original initialized final loop physically writes both actual
remainder words and returns0, paying exactly its two real loop ticks. -/
theorem complete_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat)
    (checked : Ready source base low high bits) (i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))) (enough : 2≤source.clock) :
    evaluateHOLFiniteState source complete=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (pairPost (bind source "i" 0#64) base low high bits)) := by
  let entered:=bind source "i" 0#64
  let target:=pairPost entered base low high bits
  obtain ⟨old,i⟩:=i
  have assigned:=StateSteps.assign_execute source "i" (.const 0#64) old 0#64 i rfl
  have loopRun:=loop_execute entered base low high bits (checked.bindI 0#64) (bind_lookup_same _ _ _) enough
  have forward:=evaluateHOLFiniteState_clock_le entered loop
  rw [loopRun] at forward
  have returned : evaluateHOLFiniteState target (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite target):=by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rw [complete,StateSteps.next_sequence source entered _ _ assigned (by rfl),StateSteps.next_sequence entered target _ _ loopRun forward]
  exact returned

/-- All outcomes of the complete original final block cost≤2source ticks. -/
theorem complete_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat)
    (checked : Ready source base low high bits) (i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))) :
    source.clock-(evaluateHOLFiniteState source complete).2.clock≤2 := by
  by_cases enough : 2≤source.clock
  · rw [complete_execute source base low high bits checked i enough]
    have clock:=congrArg PanSemStateFiniteExact.clock (pairPost_frame (bind source "i" 0#64) base low high bits)
    change (pairPost (bind source "i" 0#64) base low high bits).clock=source.clock-2 at clock
    change source.clock-(pairPost (bind source "i" 0#64) base low high bits).clock≤2
    omega
  · omega

/-- A genuine returned final block derives its own funding, returned0 and
exact actual stores, without assuming incoming successful execution. -/
theorem complete_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (bits : Nat)
    (checked : Ready source base low high bits) (i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source complete=(some (.returned value),target)) :
    2≤source.clock ∧ value=.val (.word 0#64) ∧ target=emptyLocalsHOLFinite (pairPost (bind source "i" 0#64) base low high bits) := by
  let fundedSource:={source with clock:=2}
  let paid:=emptyLocalsHOLFinite (pairPost (bind fundedSource "i" 0#64) base low high bits)
  have baseRun:=complete_execute fundedSource base low high bits (checked.withClock 2) i (by rfl)
  have zero : paid.clock=0:=by
    have clock:=congrArg PanSemStateFiniteExact.clock (pairPost_frame (bind fundedSource "i" 0#64) base low high bits)
    change paid.clock=2-2 at clock
    exact clock
  have funded:=(ClockCost.normal_from_zero_clock source paid target complete 2 (some (.returned (.val (.word 0#64)))) (some (.returned value)) baseRun zero (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)).1
  have actual:=complete_execute source base low high bits checked i funded
  have observed:=congrArg Prod.fst (normal.symm.trans actual)
  have valueEq : value=.val (.word 0#64):=by simpa only [Prod.fst,Option.some.injEq,PanSemResultExact.returned.injEq] using observed
  exact ⟨funded,valueEq,congrArg Prod.snd (normal.symm.trans actual)⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.pairPost_cells
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.pairPost_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.literal_complete
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.complete_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.complete_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.complete_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The same actual normalized outer-loop result supplies all mapped
remainder-loop inputs, including its derived zero third UN cell. -/
theorem of_outer_loop (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v quotient : Nat→BitVec 64) (length bits : Nat) (low high : BitVec 64)
    (normalized : Normalization.Ready source base u v length bits)
    (checked : Outer.LoopResult (Outer.start source v length bits) target base (Normalized.extended u bits length) (length-1)
      (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
      (Normalized.digit v bits 0) (Normalized.digit v bits 1) quotient low high)
    (r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder)))) : Ready target base low high bits := by
  have rKept:=checked.other "r" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have sKept:=checked.other "s" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have sourceR:=(Outer.start_other source v length bits "r" (by decide) (by decide) (by decide)).trans r
  have sourceS:=(Outer.start_other source v length bits "s" (by decide) (by decide) (by decide)).trans normalized.s
  exact ⟨checked.entry.context,normalized.bitsSmall,checked.entry.un,rKept.trans sourceR,checked.entry.n,sKept.trans sourceS,
    checked.entry.carryLowCell,checked.entry.carryHighCell,checked.topZero (by have h:=normalized.entry.large;omega),checked.entry.carryLowSmall,checked.entry.carryHighSmall⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Remainder.of_outer_loop

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def address : ExpHOL 64:=NormalizeLoop.address "q" (localVar "j")
def increment : ExpHOL 64:=.op .add [localVar "j",.const 1#64]
def body : ProgHOL 64:=.seq (.store address (.const 0#64)) (.assign .local (ofString "j") increment)
def test : ExpHOL 64:=.cmp .lower (localVar "j") (localVar "m")
def loop : ProgHOL 64:=.while test body

def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat) :=
  bind {source with memory:=StoreWord.put source.memory (slot (Workspace.pointer base .quotient) (length-1)) 0#64,clock:=source.clock-1} "j" (BitVec.ofNat 64 length)

structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat) : Prop where
  context : Workspace.Context source base
  large : 2≤length
  small : length≤16
  q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))
  m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 length)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))

theorem Ready.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {length : Nat}
    (checked : Ready source base length) (clock : Nat) : Ready {source with clock:=clock} base length :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.large,checked.small,checked.q,checked.m,checked.n⟩

theorem Ready.bindJ {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {length : Nat}
    (checked : Ready source base length) (word : BitVec 64) : Ready (bind source "j" word) base length :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.large,checked.small,
    (bind_lookup_other source "j" "q" word (by decide)).trans checked.q,
    (bind_lookup_other source "j" "m" word (by decide)).trans checked.m,
    (bind_lookup_other source "j" "n" word (by decide)).trans checked.n⟩

theorem post_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat) (name : String)
    (notJ : ofString name≠ofString "j") : (post source base length).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  bind_lookup_other _ "j" name _ (Ne.symm notJ)

theorem post_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat) (query : BitVec 64)
    (outside : query≠slot (Workspace.pointer base .quotient) (length-1)) : (post source base length).memory query=source.memory query := by
  simp only [post,WitnessRadix.QueryBranch.bind,setVarHOLFinite,StoreWord.put,if_neg outside]

private theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length index : Nat) (small : length≤16) (inside : index≤16)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))))
    (m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 length)))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word (if index<length then 1#64 else 0#64))) := by
  have indexNumber : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have lengthNumber : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [finite_eval]
  simp [eval,test,localVar,evalHOLExact,toExact,j,m,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,indexNumber,lengthNumber]

private theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat)
    (checked : Ready source base length) (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (length-1))))) :
    evaluateHOLFiniteState source body=(none,post {source with clock:=source.clock+1} base length) := by
  have addressRead : eval source address=some (.val (.word (slot (Workspace.pointer base .quotient) (length-1)))):=by
    simp [eval,address,NormalizeLoop.address,localVar,evalHOLExact,evalListHOLExact,toExact,checked.q,j,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,slot,BitVec.ofNat_mul,Nat.mul_comm]
  have next : eval source increment=some (.val (.word (BitVec.ofNat 64 length))):=by
    have same : BitVec.ofNat 64 (length-1)+1#64=BitVec.ofNat 64 length:=by
      rw [←BitVec.ofNat_add,show length-1+1=length by have h:=checked.large;omega]
    simp [eval,increment,localVar,evalHOLExact,evalListHOLExact,toExact,j,valueIsWord,valueWord,wordOpHOL,wordOp,same]
  have stored:=StoreWord.execute source address (.const 0#64) _ 0#64 addressRead rfl
    (Workspace.slot_mapped source base checked.context .quotient (length-1) (by change length-1<16;have large:=checked.large;have small:=checked.small;omega))
  rw [body,evaluateHOLFiniteState_seq_line780,stored]
  exact StateSteps.assign_execute _ "j" increment _ _ j next

/-- At n=2 the original trailing quotient-clear loop makes exactly one
real mapped zero store, increments j to m and observes its false guard. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat)
    (checked : Ready source base length) (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (length-1))))) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source loop=(none,post source base length) := by
  let target:=post source base length
  have bodyRun:=body_execute (decClockHOLFinite source) base length (checked.withClock (source.clock-1)) j
  have reset : {decClockHOLFinite source with clock:=(decClockHOLFinite source).clock+1}=source:=by
    simp only [decClockHOLFinite]
    have clock : source.clock-1+1=source.clock:=by omega
    simp only [clock]
  rw [reset] at bodyRun
  have read:=test_read source length (length-1) checked.small (by have large:=checked.large;have small:=checked.small;omega) j checked.m
  simp only [if_pos (show length-1<length by have h:=checked.large;omega)] at read
  have finalRead:=test_read target length length checked.small checked.small (bind_lookup_same _ _ _) ((post_other source base length "m" (by decide)).trans checked.m)
  simp only [if_neg (by omega : ¬length<length)] at finalRead
  have done : evaluateHOLFiniteState target loop=(none,target):=Subtract.while_done target test body finalRead
  exact Subtract.while_next source target target test body read (by omega) bodyRun done

theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat)
    (checked : Ready source base length) (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (length-1))))) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤1 := by
  by_cases enough : 1≤source.clock
  · rw [loop_execute source base length checked j enough]
    change source.clock-(source.clock-1)≤1
    omega
  · omega

theorem loop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat)
    (checked : Ready source base length) (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (length-1)))))
    (normal : evaluateHOLFiniteState source loop=(none,target)) : 1≤source.clock ∧ target=post source base length := by
  let fundedSource:={source with clock:=1}
  have baseRun:=loop_execute fundedSource base length (checked.withClock 1) j (by rfl)
  have funded:=(ClockCost.normal_from_zero_clock source (post fundedSource base length) target loop 1 none none baseRun rfl (by decide) normal (by decide)).1
  have actual:=loop_execute source base length checked j funded
  exact ⟨funded,congrArg Prod.snd (normal.symm.trans actual)⟩

def block (continuation : ProgHOL 64) : ProgHOL 64:=
  .seq (.assign .local (ofString "j") Outer.countExpression) (.seq loop continuation)

/-- The exact original right-associated counter/clear prefix resumes any
original continuation from its real one-store post-state. -/
theorem block_continue (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat)
    (checked : Ready source base length) (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old))) (enough : 1≤source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (block continuation)=evaluateHOLFiniteState (post (bind source "j" (BitVec.ofNat 64 (length-1))) base length) continuation := by
  let entered:=bind source "j" (BitVec.ofNat 64 (length-1))
  let target:=post entered base length
  obtain ⟨old,j⟩:=j
  have assigned:=StateSteps.assign_execute source "j" Outer.countExpression old (BitVec.ofNat 64 (length-1)) j (Outer.count_read source length checked.large checked.m checked.n)
  have loopRun:=loop_execute entered base length (checked.bindJ _) (bind_lookup_same _ _ _) enough
  have forward:=evaluateHOLFiniteState_clock_le entered loop
  rw [loopRun] at forward
  rw [block,StateSteps.next_sequence source entered _ _ assigned (by rfl),StateSteps.next_sequence entered target _ _ loopRun forward]

end InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.loop_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.loop_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.loop_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.block_continue

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual preceding outer loop retains the real quotient pointer,
original m and n=2 needed by the trailing-clear guard and assignment. -/
theorem of_outer_loop (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v quotient : Nat→BitVec 64) (length bits : Nat) (low high : BitVec 64)
    (normalized : Normalization.Ready source base u v length bits)
    (checked : Outer.LoopResult (Outer.start source v length bits) target base (Normalized.extended u bits length) (length-1)
      (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
      (Normalized.digit v bits 0) (Normalized.digit v bits 1) quotient low high) : Ready target base length := by
  have mKept:=checked.other "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have sourceM:=(Outer.start_other source v length bits "m" (by decide) (by decide) (by decide)).trans normalized.entry.m
  exact ⟨checked.entry.context,normalized.entry.large,normalized.entry.small,checked.entry.q,mKept.trans sourceM,checked.entry.n⟩

def cleared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat) :=
  post (bind source "j" (BitVec.ofNat 64 (length-1))) base length

private theorem cleared_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (length : Nat) (name : String)
    (notJ : ofString name≠ofString "j") : (cleared source base length).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (post_other _ base length name notJ).trans (bind_lookup_other source "j" name _ (Ne.symm notJ))

/-- The genuine quotient zero store leaves the complete physical remainder
entry intact, using actual Q/UN workspace separation. -/
theorem remainder_after (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (length bits : Nat)
    (checked : Ready source base length) (ready : Remainder.Ready source base low high bits) :
    Remainder.Ready (cleared source base length) base low high bits := by
  have large:=checked.large
  have small:=checked.small
  have cells (index : Nat) (inside : index<17) :
      (cleared source base length).memory (slot (Workspace.pointer base .normalizedNumerator) index)=source.memory (slot (Workspace.pointer base .normalizedNumerator) index):=
    post_away _ base length _ (Workspace.separate base .normalizedNumerator .quotient (by intro same;cases same) index (length-1) inside (by change length-1<16;omega))
  exact ⟨⟨ready.context.global,ready.context.domain,ready.context.arena,ready.context.aligned⟩,ready.bitsSmall,
    (cleared_other source base length "un" (by decide)).trans ready.un,
    (cleared_other source base length "r" (by decide)).trans ready.r,
    (cleared_other source base length "n" (by decide)).trans ready.n,
    (cleared_other source base length "s" (by decide)).trans ready.s,
    (cells 0 (by decide)).trans ready.lowCell,(cells 1 (by decide)).trans ready.highCell,(cells 2 (by decide)).trans ready.zeroCell,ready.lowSmall,ready.highSmall⟩

def finish : ProgHOL 64:=block Remainder.complete
def finishPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (length bits : Nat) :=
  emptyLocalsHOLFinite (Remainder.pairPost (bind (cleared source base length) "i" 0#64) base low high bits)

theorem finishPost_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (length bits : Nat) :
    (finishPost source base low high length bits).clock=source.clock-3 := by
  change source.clock-1-1-1=source.clock-3
  omega

private def findFinish : ProgHOL 64→Option (ProgHOL 64)
  | .seq (.assign .local name expression) (.seq (.while (.cmp .lower (.var .local counter) (.var .local bound)) contents) rest)=>
    if name=ofString "j" ∧ counter=ofString "j" ∧ bound=ofString "m" then
      some (.seq (.assign .local name expression) (.seq (.while (.cmp .lower (.var .local counter) (.var .local bound)) contents) rest))
    else (findFinish contents).orElse (fun _=>findFinish rest)
  | .dec _ _ _ rest=>findFinish rest
  | .seq first rest=>(findFinish first).orElse (fun _=>findFinish rest)
  | .ite _ yes no=>(findFinish yes).orElse (fun _=>findFinish no)
  | .while _ contents=>findFinish contents
  | .decCall _ _ _ _ rest=>findFinish rest
  | _=>none

set_option maxRecDepth 100000 in
/-- The complete original final quotient-clear and remainder-return suffix. -/
theorem literal_finish : findFinish Single.body=some finish := by
  have notI : ofString "i"≠ofString "j":=by decide
  simp [findFinish,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    finish,block,loop,test,body,address,increment,Outer.countExpression,
    Remainder.complete,Remainder.loop,Remainder.test,Remainder.step,Remainder.expression,Remainder.inputAddress,Remainder.nextAddress,Remainder.outputAddress,Remainder.nextIndex,
    NormalizeLoop.remaining,NormalizeLoop.address,localVar,notI]

/-- All three actual final loop ticks execute through the original zero
store, both remainder stores and return0, with its genuine local clearing. -/
theorem finish_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (length bits : Nat)
    (checked : Ready source base length) (ready : Remainder.Ready source base low high bits)
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old)))
    (i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))) (enough : 3≤source.clock) :
    evaluateHOLFiniteState source finish=(some (.returned (.val (.word 0#64))),finishPost source base low high length bits) := by
  have nextReady:=remainder_after source base low high length bits checked ready
  have nextI : ∃ old,(cleared source base length).locals.lookup (ofString "i")=some (.val (.word old)):=by
    obtain ⟨old,i⟩:=i
    exact ⟨old,(cleared_other source base length "i" (by decide)).trans i⟩
  have nextFunded : 2≤(cleared source base length).clock:=by change 2≤source.clock-1;omega
  rw [finish,block_continue source base length checked j (by omega) Remainder.complete]
  exact Remainder.complete_execute _ base low high bits nextReady nextI nextFunded

/-- The original final clear/remainder suffix costs≤3ticks on every outcome. -/
theorem finish_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (length bits : Nat)
    (checked : Ready source base length) (ready : Remainder.Ready source base low high bits)
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old)))
    (i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))) :
    source.clock-(evaluateHOLFiniteState source finish).2.clock≤3 := by
  by_cases enough : 3≤source.clock
  · rw [finish_execute source base low high length bits checked ready j i enough]
    change source.clock-(finishPost source base low high length bits).clock≤3
    rw [finishPost_clock]
    omega
  · omega

/-- Actual returned suffixes derive their own funding, result and memory
post-state, rather than assuming a future successful final block. -/
theorem finish_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base low high : BitVec 64) (length bits : Nat)
    (checked : Ready source base length) (ready : Remainder.Ready source base low high bits)
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old)))
    (i : ∃ old,source.locals.lookup (ofString "i")=some (.val (.word old))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source finish=(some (.returned value),target)) :
    3≤source.clock ∧ value=.val (.word 0#64) ∧ target=finishPost source base low high length bits := by
  let fundedSource:={source with clock:=3}
  let paid:=finishPost fundedSource base low high length bits
  have baseRun:=finish_execute fundedSource base low high length bits (checked.withClock 3) (ready.withClock 3) j i (by rfl)
  have zero : paid.clock=0:=by rw [finishPost_clock];rfl
  have funded:=(ClockCost.normal_from_zero_clock source paid target finish 3 (some (.returned (.val (.word 0#64)))) (some (.returned value)) baseRun zero
    (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)).1
  have actual:=finish_execute source base low high length bits checked ready j i funded
  have observed:=congrArg Prod.fst (normal.symm.trans actual)
  have valueEq : value=.val (.word 0#64):=by simpa only [Prod.fst,Option.some.injEq,PanSemResultExact.returned.injEq] using observed
  exact ⟨funded,valueEq,congrArg Prod.snd (normal.symm.trans actual)⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.of_outer_loop
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.remainder_after
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.literal_finish
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.finish_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.finish_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Trailing.finish_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def continuation : ProgHOL 64:=.seq Outer.loop Trailing.finish
def postNormalization : ProgHOL 64:=Outer.leading continuation

set_option maxRecDepth 100000 in
/-- The complete literal original continuation after normalization. -/
theorem literal_postNormalization : Outer.findLeading Single.body=some postNormalization := by
  have not_i : ofString "i"≠ofString "vtop":=by decide
  have not_j : ofString "j"≠ofString "vtop":=by decide
  have not_d : ofString "d"≠ofString "vtop":=by decide
  have not_k : ofString "k"≠ofString "vtop":=by decide
  have not_un : ofString "un"≠ofString "vtop":=by decide
  have not_vn : ofString "vn"≠ofString "vtop":=by decide
  simp [Outer.findLeading,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    postNormalization,continuation,Outer.leading,Outer.topLoad,Outer.secondLoad,Outer.countExpression,
    Outer.loop,Outer.test,Outer.body,Outer.previous,Outer.captures,Outer.loadAt,Outer.topIndex,Outer.middleIndex,Outer.lowIndex,
    Estimate.phase,Estimate.program,Estimate.test,Estimate.maximum,Estimate.remainderExpression,Estimate.scalar,Estimate.arguments,Estimate.updates,Estimate.continuation,
    Subtract.corrected,QhatCorrection.loop,QhatCorrection.test,QhatCorrection.body,QhatCorrection.branch,QhatCorrection.correct,
    QhatCorrection.roomTest,QhatCorrection.estimateTest,QhatCorrection.leftEstimate,QhatCorrection.rightEstimate,
    QhatCorrection.quotientExpression,QhatCorrection.remainderExpression,Subtract.initialized,Subtract.loop,Subtract.test,Subtract.step,Subtract.updates,
    Subtract.productExpression,Subtract.residualExpression,Subtract.lowExpression,Subtract.carryExpression,Subtract.increment,Subtract.inputAddress,Subtract.divisorAddress,
    Subtract.finish,Subtract.findFinish,Subtract.topAddress,Subtract.quotientAddress,Subtract.address,Subtract.difference,Subtract.negativeTest,Subtract.keep,
    Trailing.finish,Trailing.block,Trailing.loop,Trailing.test,Trailing.body,Trailing.address,Trailing.increment,
    Remainder.complete,Remainder.loop,Remainder.test,Remainder.step,Remainder.expression,Remainder.inputAddress,Remainder.nextAddress,Remainder.outputAddress,Remainder.nextIndex,
    NormalizeLoop.remaining,NormalizeLoop.address,returnShape,localVar,not_i,not_j,not_d,not_k,not_un,not_vn]

/-- The whole original continuation from physical normalized arrays, on
all actual outcomes and at every clock, including all final stores. -/
theorem postNormalization_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (ready : Normalization.Ready source base u v length bits)
    (installed : OriginalCode.Installed source.code)
    (q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))))
    (r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))))
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old))) :
    source.clock-(evaluateHOLFiniteState source postNormalization).2.clock≤39*(length-1)+3 := by
  let entered:=Outer.start source v length bits
  have checked:=Outer.normalization_entry source base u v length bits ready installed q
  let output:=evaluateHOLFiniteState entered continuation
  have actual:=Outer.leading_execute source output.2 base u v length bits ready j continuation output.1 rfl
  have price : source.clock-output.2.clock≤39*(length-1)+3:=by
    have front:=Outer.loop_cost entered base (Normalized.extended u bits length) (length-1)
      (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
      (Normalized.digit v bits 0) (Normalized.digit v bits 1) checked
    have forward:=evaluateHOLFiniteState_clock_le entered Outer.loop
    change source.clock-(evaluateHOLFiniteState entered continuation).2.clock≤39*(length-1)+3
    rw [continuation,evaluateHOLFiniteState_seq_line780]
    generalize computed : evaluateHOLFiniteState entered Outer.loop=loopOutput at front forward ⊢
    obtain ⟨result,middle⟩:=loopOutput
    cases result with
    | none=>
      obtain ⟨quotient,low,high,loopResult⟩:=Outer.loop_normal entered middle base (Normalized.extended u bits length) (length-1)
        (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
        (Normalized.digit v bits 0) (Normalized.digit v bits 1) checked computed
      have trailingReady:=Trailing.of_outer_loop source middle base u v quotient length bits low high ready loopResult
      have remainderReady:=Remainder.of_outer_loop source middle base u v quotient length bits low high ready loopResult r
      have back:=Trailing.finish_cost middle base low high length bits trailingReady remainderReady ⟨0#64,loopResult.entry.j⟩ loopResult.entry.i
      have lastForward:=evaluateHOLFiniteState_clock_le middle Trailing.finish
      change source.clock-middle.clock≤39*(length-1) at front
      change middle.clock≤source.clock at forward
      change source.clock-(evaluateHOLFiniteState middle Trailing.finish).2.clock≤39*(length-1)+3
      omega
    | some result=>
      change source.clock-middle.clock≤39*(length-1)+3
      change source.clock-middle.clock≤39*(length-1) at front
      omega
  change source.clock-(evaluateHOLFiniteState source (Outer.leading continuation)).2.clock≤39*(length-1)+3
  rw [actual]
  exact price

/-- A genuine returned complete post-normalization continuation exposes
its actual quotient-loop result and exact three-store final suffix. -/
theorem postNormalization_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (ready : Normalization.Ready source base u v length bits)
    (installed : OriginalCode.Installed source.code)
    (q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))))
    (r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))))
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source postNormalization=(some (.returned value),target)) :
    ∃ middle quotient low high,
      Outer.LoopResult (Outer.start source v length bits) middle base (Normalized.extended u bits length) (length-1)
        (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
        (Normalized.digit v bits 0) (Normalized.digit v bits 1) quotient low high ∧
      value=.val (.word 0#64) ∧ target=Outer.startRestored source (Trailing.finishPost middle base low high length bits) v bits ∧
      source.clock-target.clock≤39*(length-1)+3 := by
  let entered:=Outer.start source v length bits
  let output:=evaluateHOLFiniteState entered continuation
  have actual:=Outer.leading_execute source output.2 base u v length bits ready j continuation output.1 rfl
  have observed : output.1=some (.returned value):=congrArg Prod.fst (actual.symm.trans normal)
  have innerRun : evaluateHOLFiniteState entered continuation=(some (.returned value),output.2):=Prod.ext observed rfl
  have safe : LocalPrefix (ofString "u") Outer.loop:=.loop Outer.test Outer.body_safe
  obtain ⟨middle,loopRun,finishRun,kept⟩:=safe.normal_continue entered output.2 Trailing.finish value innerRun
  obtain ⟨quotient,low,high,loopResult⟩:=Outer.loop_normal entered middle base (Normalized.extended u bits length) (length-1)
    (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
    (Normalized.digit v bits 0) (Normalized.digit v bits 1) (Outer.normalization_entry source base u v length bits ready installed q) loopRun
  have trailingReady:=Trailing.of_outer_loop source middle base u v quotient length bits low high ready loopResult
  have remainderReady:=Remainder.of_outer_loop source middle base u v quotient length bits low high ready loopResult r
  obtain ⟨funded,valueEq,endpoint⟩:=Trailing.finish_normal middle output.2 base low high length bits trailingReady remainderReady ⟨0#64,loopResult.entry.j⟩ loopResult.entry.i value finishRun
  have targetEq : target=Outer.startRestored source (Trailing.finishPost middle base low high length bits) v bits:=by
    have frame:=congrArg Prod.snd (normal.symm.trans actual)
    rw [endpoint] at frame
    exact frame
  have price:=postNormalization_cost source base u v length bits ready installed q r j
  rw [normal] at price
  exact ⟨middle,quotient,low,high,loopResult,valueEq,targetEq,price⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.literal_postNormalization
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.postNormalization_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.postNormalization_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real non-timeout enclosing execution derives the normalization
prefix's own funding. Clock padding exposes the actual fixed prefix before
any continuation, without assuming a future successful normalization result. -/
theorem prefix_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length : Nat) (checked : Entry source base u v length)
    (installed : OriginalCode.Installed source.code) (continuation : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (normal : evaluateHOLFiniteState source (call continuation)=(result,target)) (notTimeout : result≠some .timeOut) :
    ∃ bits inner,length+1≤source.clock ∧
      Ready (post (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits) base u v length bits ∧
      (post (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits).clock=source.clock-(length+1) ∧
      evaluateHOLFiniteState (post (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits) continuation=(result,inner) ∧
      target=restore source "s" inner := by
  let paddedSource:={source with clock:=source.clock+(length+1)}
  have padded:=panPropsEvaluateAddClockEq (call continuation) source result target (length+1) ⟨normal,notTimeout⟩
  obtain ⟨paddedBits,paddedReady,paddedClock,prefixRun⟩:=prefix_execute paddedSource base u v length (checked.withClock (source.clock+(length+1))) installed
    (by change length+1≤source.clock+(length+1);omega) continuation
  let boundary:=post (bind {paddedSource with clock:=paddedSource.clock-1} "s" (BitVec.ofNat 64 paddedBits)) base u v length paddedBits
  have compared:=congrArg (fun output : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>output.2.clock) (prefixRun.symm.trans padded)
  change (evaluateHOLFiniteState boundary continuation).2.clock=target.clock+(length+1) at compared
  have forward:=evaluateHOLFiniteState_clock_le boundary continuation
  change boundary.clock=(source.clock+(length+1))-(length+1) at paddedClock
  have funded : length+1≤source.clock:=by omega
  obtain ⟨bits,ready,clock,actual⟩:=prefix_execute source base u v length checked installed funded continuation
  let entered:=post (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits
  let output:=evaluateHOLFiniteState entered continuation
  have observed : output.1=result:=congrArg Prod.fst (actual.symm.trans normal)
  have endpoint : target=restore source "s" output.2:=congrArg Prod.snd (normal.symm.trans actual)
  exact ⟨bits,output.2,funded,ready,clock,Prod.ext observed rfl,endpoint⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Normalization.prefix_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def normalizedProgram : ProgHOL 64:=Normalization.call postNormalization
def boundary (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length bits : Nat) :=
  Normalization.post (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits

set_option maxRecDepth 100000 in
/-- The original wide branch introduces its actual UN/VN scopes around the
complete checked nlz32/normalization/quotient/remainder/return program. -/
theorem otherBranch_shape : Single.otherBranch=
    .dec (ofString "un") .one (.op .add [.var .global (ofString "u256_ws"),.const 0#64])
      (.dec (ofString "vn") .one (.op .add [.var .global (ofString "u256_ws"),.const 144#64]) normalizedProgram) := by
  simp [Single.otherBranch,normalizedProgram,Normalization.call,Normalization.arguments,Normalization.body,
    NormalizeLoop.loop,NormalizeLoop.body,NormalizeLoop.test,NormalizeLoop.expression,NormalizeLoop.previous,NormalizeLoop.firstStore,NormalizeLoop.firstExpression,NormalizeLoop.topStore,NormalizeLoop.topExpression,Single.body,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    postNormalization,continuation,Outer.leading,Outer.topLoad,Outer.secondLoad,Outer.countExpression,
    Outer.loop,Outer.test,Outer.body,Outer.previous,Outer.captures,Outer.loadAt,Outer.topIndex,Outer.middleIndex,Outer.lowIndex,
    Estimate.phase,Estimate.program,Estimate.test,Estimate.maximum,Estimate.remainderExpression,Estimate.scalar,Estimate.arguments,Estimate.updates,Estimate.continuation,
    Subtract.corrected,QhatCorrection.loop,QhatCorrection.test,QhatCorrection.body,QhatCorrection.branch,QhatCorrection.correct,
    QhatCorrection.roomTest,QhatCorrection.estimateTest,QhatCorrection.leftEstimate,QhatCorrection.rightEstimate,
    QhatCorrection.quotientExpression,QhatCorrection.remainderExpression,Subtract.initialized,Subtract.loop,Subtract.test,Subtract.step,Subtract.updates,
    Subtract.productExpression,Subtract.residualExpression,Subtract.lowExpression,Subtract.carryExpression,Subtract.increment,Subtract.inputAddress,Subtract.divisorAddress,
    Subtract.finish,Subtract.findFinish,Subtract.topAddress,Subtract.quotientAddress,Subtract.address,Subtract.difference,Subtract.negativeTest,Subtract.keep,
    Trailing.finish,Trailing.block,Trailing.loop,Trailing.test,Trailing.body,Trailing.address,Trailing.increment,
    Remainder.complete,Remainder.loop,Remainder.test,Remainder.step,Remainder.expression,Remainder.inputAddress,Remainder.nextAddress,Remainder.outputAddress,Remainder.nextIndex,
    NormalizeLoop.remaining,NormalizeLoop.address,returnShape,localVar]

private theorem boundary_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (name : String)
    (notI : ofString name≠ofString "i") (notS : ofString name≠ofString "s") :
    (boundary source base u v length bits).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (Normalization.post_other _ base u v length bits name (Ne.symm notI)).trans (bind_lookup_other _ "s" name _ (Ne.symm notS))

private theorem boundary_installed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (positive : 0<length) (installed : OriginalCode.Installed source.code) :
    OriginalCode.Installed (boundary source base u v length bits).code := by
  have frame:=Normalization.post_frame (bind {source with clock:=source.clock-1} "s" (BitVec.ofNat 64 bits)) base u v length bits positive
  have code:=congrArg PanSemStateFiniteExact.code frame
  change (boundary source base u v length bits).code=source.code at code
  rw [code]
  exact installed

/-- Complete original normalization call through the actual final return,
including every short-clock/stopped outcome, at n=2 and2≤m≤16. -/
theorem normalized_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length : Nat) (checked : Normalization.Entry source base u v length)
    (installed : OriginalCode.Installed source.code)
    (q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))))
    (r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))))
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old))) :
    source.clock-(evaluateHOLFiniteState source normalizedProgram).2.clock≤40*length-35 := by
  have large:=checked.large
  by_cases enough : length+1≤source.clock
  · obtain ⟨bits,ready,clock,actual⟩:=Normalization.prefix_execute source base u v length checked installed enough postNormalization
    have qNext:=(boundary_other source base u v length bits "q" (by decide) (by decide)).trans q
    have rNext:=(boundary_other source base u v length bits "r" (by decide) (by decide)).trans r
    have jNext : ∃ old,(boundary source base u v length bits).locals.lookup (ofString "j")=some (.val (.word old)):=by
      obtain ⟨old,j⟩:=j
      exact ⟨old,(boundary_other source base u v length bits "j" (by decide) (by decide)).trans j⟩
    have back:=postNormalization_cost (boundary source base u v length bits) base u v length bits ready
      (boundary_installed source base u v length bits (by omega) installed) qNext rNext jNext
    have forward:=evaluateHOLFiniteState_clock_le (boundary source base u v length bits) postNormalization
    rw [normalizedProgram,actual]
    change source.clock-(evaluateHOLFiniteState (boundary source base u v length bits) postNormalization).2.clock≤40*length-35
    change (boundary source base u v length bits).clock=source.clock-(length+1) at clock
    omega
  · omega

/-- A genuine returned complete normalization program exposes the same
real shift, normalized arrays, quotient-loop result and exact final stores. -/
theorem normalized_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length : Nat) (checked : Normalization.Entry source base u v length)
    (installed : OriginalCode.Installed source.code)
    (q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))))
    (r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))))
    (j : ∃ old,source.locals.lookup (ofString "j")=some (.val (.word old))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source normalizedProgram=(some (.returned value),target)) :
    ∃ bits middle quotient low high,
      Normalization.Ready (boundary source base u v length bits) base u v length bits ∧
      Outer.LoopResult (Outer.start (boundary source base u v length bits) v length bits) middle base (Normalized.extended u bits length) (length-1)
        (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
        (Normalized.digit v bits 0) (Normalized.digit v bits 1) quotient low high ∧
      value=.val (.word 0#64) ∧
      target=restore source "s" (Outer.startRestored (boundary source base u v length bits) (Trailing.finishPost middle base low high length bits) v bits) ∧
      source.clock-target.clock≤40*length-35 := by
  obtain ⟨bits,inner,funded,ready,clock,continuationRun,restored⟩:=Normalization.prefix_normal source target base u v length checked installed postNormalization
    (some (.returned value)) normal (by intro impossible;cases impossible)
  have qNext:=(boundary_other source base u v length bits "q" (by decide) (by decide)).trans q
  have rNext:=(boundary_other source base u v length bits "r" (by decide) (by decide)).trans r
  have jNext : ∃ old,(boundary source base u v length bits).locals.lookup (ofString "j")=some (.val (.word old)):=by
    obtain ⟨old,j⟩:=j
    exact ⟨old,(boundary_other source base u v length bits "j" (by decide) (by decide)).trans j⟩
  obtain ⟨middle,quotient,low,high,loopResult,valueEq,endpoint,paid⟩:=postNormalization_normal (boundary source base u v length bits) inner base u v length bits ready
    (boundary_installed source base u v length bits (by have h:=checked.large;omega) installed) qNext rNext jNext value continuationRun
  have price:=normalized_cost source base u v length checked installed q r j
  rw [normal] at price
  rw [endpoint] at restored
  exact ⟨bits,middle,quotient,low,high,ready,loopResult,valueEq,restored,price⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.otherBranch_shape
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.normalized_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.normalized_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual function formals and physical original inputs before any local
or normalized workspace declaration; no future helper result is assumed. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length : Nat) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  large : 2≤length
  small : length≤16
  q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))
  r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder)))
  uCell : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator)))
  vCell : source.locals.lookup (ofString "v")=some (.val (.word (Workspace.pointer base .divisor)))
  m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 length)))
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  uImage : Image source (Workspace.pointer base .numerator) u length
  vImage : Image source (Workspace.pointer base .divisor) v 2
  uSmall : ∀ index,index<length→(u index).toNat<4294967296
  vSmall : ∀ index,index<2→(v index).toNat<4294967296
  leadingPositive : 0<(v 1).toNat

def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :=
  bind (bind (bind (bind source "i" 0#64) "j" 0#64) "un" (Workspace.pointer base .normalizedNumerator)) "vn" (Workspace.pointer base .normalizedDivisor)

def restored (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :=
  restore source "i" (restore (bind source "i" 0#64) "j" (restore (bind (bind source "i" 0#64) "j" 0#64) "un"
    (restore (bind (bind (bind source "i" 0#64) "j" 0#64) "un" (Workspace.pointer base .normalizedNumerator)) "vn" target)))

private theorem prepared_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (name : String)
    (notI : ofString name≠ofString "i") (notJ : ofString name≠ofString "j")
    (notUn : ofString name≠ofString "un") (notVn : ofString name≠ofString "vn") :
    (prepared source base).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "vn" name _ (Ne.symm notVn)).trans ((bind_lookup_other _ "un" name _ (Ne.symm notUn)).trans
    ((bind_lookup_other _ "j" name _ (Ne.symm notJ)).trans (bind_lookup_other _ "i" name _ (Ne.symm notI))))

private theorem prepared_j (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    (prepared source base).locals.lookup (ofString "j")=some (.val (.word 0#64)) :=
  (bind_lookup_other _ "vn" "j" _ (by decide)).trans ((bind_lookup_other _ "un" "j" _ (by decide)).trans (bind_lookup_same _ _ _))

/-- The genuine original declarations supply the actual normalization entry. -/
theorem Entry.normalization {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {u v : Nat→BitVec 64} {length : Nat}
    (checked : Entry source base u v length) : Normalization.Entry (prepared source base) base u v length := by
  refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.large,checked.small,
    ?_,bind_lookup_same _ _ _,?_,?_,?_,?_,?_,checked.uImage,checked.vImage,checked.uSmall,checked.vSmall,checked.leadingPositive⟩
  · exact (bind_lookup_other _ "vn" "un" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact (prepared_other source base "u" (by decide) (by decide) (by decide) (by decide)).trans checked.uCell
  · exact (prepared_other source base "v" (by decide) (by decide) (by decide) (by decide)).trans checked.vCell
  · exact (prepared_other source base "m" (by decide) (by decide) (by decide) (by decide)).trans checked.m
  · exact (prepared_other source base "n" (by decide) (by decide) (by decide) (by decide)).trans checked.n
  · exact ⟨0#64,(bind_lookup_other _ "vn" "i" _ (by decide)).trans ((bind_lookup_other _ "un" "i" _ (by decide)).trans
      ((bind_lookup_other _ "j" "i" _ (by decide)).trans (bind_lookup_same _ _ _)))⟩

def workspaceExpression (offset : Nat) : ExpHOL 64:=.op .add [.var .global (ofString "u256_ws"),.const (BitVec.ofNat 64 offset)]

private theorem workspace_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (buffer : Workspace.Buffer)
    (global : source.globals.lookup (ofString "u256_ws")=some (.val (.word base))) :
    eval source (workspaceExpression (Workspace.offset buffer))=some (.val (.word (Workspace.pointer base buffer))) := by
  simp [eval,workspaceExpression,evalHOLExact,evalListHOLExact,toExact,global,valueIsWord,valueWord,wordOpHOL,wordOp,Workspace.pointer]

/-- Actual i/j declarations, false n=1 guard and UN/VN declarations resume
the unchanged normalized program with their true lexical restorations. -/
theorem preamble_execute (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length : Nat) (checked : Entry source base u v length) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState (prepared source base) normalizedProgram=(result,target)) :
    evaluateHOLFiniteState source Single.body=(result,restored source target base) := by
  let first:=bind source "i" 0#64
  let second:=bind first "j" 0#64
  let third:=bind second "un" (Workspace.pointer base .normalizedNumerator)
  have n : second.locals.lookup (ofString "n")=some (.val (.word 2#64)):=
    (bind_lookup_other _ "j" "n" _ (by decide)).trans ((bind_lookup_other _ "i" "n" _ (by decide)).trans checked.n)
  have falseTest : eval second Single.oneTest=some (.val (.word 0#64)):=by
    simp [eval,Single.oneTest,localVar,evalHOLExact,toExact,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have skipped : evaluateHOLFiniteState second (.ite Single.oneTest Single.oneBranch .skip)=(none,second):=by
    simp only [eval] at falseTest
    rw [evaluateHOLFiniteState_ite,falseTest]
    simp [evaluateHOLFiniteState_skip]
  have unRead:=workspace_read second base .normalizedNumerator checked.context.global
  have vnRead:=workspace_read third base .normalizedDivisor checked.context.global
  have declaredVn:=ScalarScope.declare_execute third target "vn" (workspaceExpression 144) (Workspace.pointer base .normalizedDivisor) normalizedProgram result vnRead run
  have declaredUn:=ScalarScope.declare_execute second _ "un" (workspaceExpression 0) (Workspace.pointer base .normalizedNumerator)
    (.dec (ofString "vn") .one (workspaceExpression 144) normalizedProgram) result unRead declaredVn
  have guarded : evaluateHOLFiniteState second (.seq (.ite Single.oneTest Single.oneBranch .skip) Single.otherBranch)=
      (result,restore second "un" (restore third "vn" target)):=by
    rw [StateSteps.next_sequence second second _ _ skipped (by rfl),otherBranch_shape]
    exact declaredUn
  have declaredJ:=ScalarScope.declare_execute first _ "j" (.const 0#64) 0#64 (.seq (.ite Single.oneTest Single.oneBranch .skip) Single.otherBranch) result rfl guarded
  rw [Single.body_shape]
  exact ScalarScope.declare_execute source _ "i" (.const 0#64) 0#64
    (.dec (ofString "j") .one (.const 0#64) (.seq (.ite Single.oneTest Single.oneBranch .skip) Single.otherBranch)) result rfl declaredJ

/-- Uniform all-outcome source allowance for the unchanged full divmnu
function at the actual two-digit divisor entry. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length : Nat) (checked : Entry source base u v length) :
    source.clock-(evaluateHOLFiniteState source Single.body).2.clock≤40*length-35 := by
  let output:=evaluateHOLFiniteState (prepared source base) normalizedProgram
  have actual:=preamble_execute source output.2 base u v length checked output.1 rfl
  have price:=normalized_cost (prepared source base) base u v length checked.normalization checked.installed
    ((prepared_other source base "q" (by decide) (by decide) (by decide) (by decide)).trans checked.q)
    ((prepared_other source base "r" (by decide) (by decide) (by decide) (by decide)).trans checked.r) ⟨0#64,prepared_j source base⟩
  rw [actual]
  exact price

end InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Entry.normalization
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.preamble_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.body_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Physical result of the unchanged whole two-digit divmnu function,
with its true lexical restorations and natural quotient/remainder values. -/
structure Result (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length bits : Nat) (middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (quotient : Nat→BitVec 64) (low high : BitVec 64) : Prop where
  ready : Normalization.Ready (boundary (prepared source base) base u v length bits) base u v length bits
  loop : Outer.LoopResult (Outer.start (boundary (prepared source base) base u v length bits) v length bits) middle base (Normalized.extended u bits length) (length-1)
    (Normalized.extended u bits length (length-1)) (Normalized.extended u bits length length)
    (Normalized.digit v bits 0) (Normalized.digit v bits 1) quotient low high
  state : target=restored source (restore (prepared source base) "s"
    (Outer.startRestored (boundary (prepared source base) base u v length bits) (Trailing.finishPost middle base low high length bits) v bits)) base
  quotientEq : number quotient (length-1)=number u length/number v 2
  remainderEq : (Denormalize.digit low high bits).toNat+4294967296*(Denormalize.digit high 0#64 bits).toNat=number u length%number v 2
  cost : source.clock-target.clock≤40*length-35

/-- The genuine returned unchanged function derives its exact physical
result and ordinary quotient/remainder; no future callee result is assumed. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length : Nat) (checked : Entry source base u v length) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Single.body=(some (.returned value),target)) :
    ∃ bits middle quotient low high,value=.val (.word 0#64) ∧ Result source target base u v length bits middle quotient low high := by
  let output:=evaluateHOLFiniteState (prepared source base) normalizedProgram
  have actual:=preamble_execute source output.2 base u v length checked output.1 rfl
  have observed : output.1=some (.returned value):=congrArg Prod.fst (actual.symm.trans normal)
  have run : evaluateHOLFiniteState (prepared source base) normalizedProgram=(some (.returned value),output.2):=Prod.ext observed rfl
  obtain ⟨bits,middle,quotient,low,high,ready,loopResult,valueEq,endpoint,paid⟩:=normalized_normal (prepared source base) output.2 base u v length checked.normalization checked.installed
    ((prepared_other source base "q" (by decide) (by decide) (by decide) (by decide)).trans checked.q)
    ((prepared_other source base "r" (by decide) (by decide) (by decide) (by decide)).trans checked.r) ⟨0#64,prepared_j source base⟩ value run
  have state : target=restored source (restore (prepared source base) "s"
      (Outer.startRestored (boundary (prepared source base) base u v length bits) (Trailing.finishPost middle base low high length bits) v bits)) base:=by
    have frame:=congrArg Prod.snd (normal.symm.trans actual)
    rw [endpoint] at frame
    exact frame
  have division:=Outer.normalization_division (boundary (prepared source base) base u v length bits) middle base u v quotient length bits low high ready loopResult
  have price:=body_cost source base u v length checked
  rw [normal] at price
  exact ⟨bits,middle,quotient,low,high,valueEq,⟨ready,loopResult,state,division.1,division.2.2,price⟩⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.body_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The whole actual normal function preserves every source field except
locals, clock and the explicitly described workspace memory. -/
theorem Result.frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high) :
    target={source with locals:=target.locals,memory:=target.memory,clock:=target.clock} := by
  let adjust:=fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals,memory:=target.memory,clock:=target.clock}
  have last : target=adjust middle:=by
    dsimp only [adjust]
    rw [checked.state]
    rfl
  have loopFrame:=congrArg adjust checked.loop.state
  have normalizeFrame:=congrArg adjust (Normalization.post_frame (bind {prepared source base with clock:=(prepared source base).clock-1} "s" (BitVec.ofNat 64 bits))
    base u v length bits (by have h:=checked.ready.entry.large;omega))
  exact last.trans (loopFrame.trans normalizeFrame)

/-- Every actual word outside the four concrete workspace write ranges is
retained through normalization, the complete quotient loop and final stores. -/
theorem Result.memory_away {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high) (query : BitVec 64)
    (outsideU : ∀ index,index≤length→ query≠slot (Workspace.pointer base .normalizedNumerator) index)
    (outsideV : ∀ index,index<2→ query≠slot (Workspace.pointer base .normalizedDivisor) index)
    (outsideQ : ∀ index,index<length→ query≠slot (Workspace.pointer base .quotient) index)
    (outsideR : ∀ index,index<2→ query≠slot (Workspace.pointer base .remainder) index) : target.memory query=source.memory query := by
  have large:=checked.ready.entry.large
  have final : target.memory query=middle.memory query:=by
    rw [checked.state]
    change (Remainder.pairPost (bind (Trailing.cleared middle base length) "i" 0#64) base low high bits).memory query=middle.memory query
    rw [Remainder.pairPost_away _ base low high bits query (outsideR 0 (by decide)) (outsideR 1 (by decide))]
    exact Trailing.post_away (bind middle "j" (BitVec.ofNat 64 (length-1))) base length query (outsideQ (length-1) (by omega))
  have loopFrame:=checked.loop.away query (by intro index inside;exact outsideQ index (by omega))
    (by intro index inside;exact outsideU index (by omega))
  have normalizeFrame:=Normalization.post_away (bind {prepared source base with clock:=(prepared source base).clock-1} "s" (BitVec.ofNat 64 bits)) base query u v length bits
    (by omega) outsideU outsideV
  exact final.trans (loopFrame.trans normalizeFrame)

/-- The actual returned memory contains both genuine denormalized words. -/
theorem Result.remainder_cells {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high) :
    target.memory (slot (Workspace.pointer base .remainder) 0)=.word (Denormalize.digit low high bits) ∧
    target.memory (slot (Workspace.pointer base .remainder) 1)=.word (Denormalize.digit high 0#64 bits) := by
  rw [checked.state]
  exact Remainder.pairPost_cells (bind (Trailing.cleared middle base length) "i" 0#64) base low high bits

/-- Neither the trailing quotient zero nor either real remainder store
changes any quotient digit produced by the actual descending loop. -/
theorem Result.quotient_prefix {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high) : Image target (Workspace.pointer base .quotient) quotient (length-1) := by
  have large:=checked.ready.entry.large
  have small:=checked.ready.entry.small
  intro index inside
  have different : slot (Workspace.pointer base .quotient) index≠slot (Workspace.pointer base .quotient) (length-1):=by
    intro hit
    have same:=slot_injective (Workspace.pointer base .quotient) index (length-1) (by omega) (by omega) hit
    omega
  rw [checked.state]
  change (Remainder.pairPost (bind (Trailing.cleared middle base length) "i" 0#64) base low high bits).memory (slot (Workspace.pointer base .quotient) index)=.word (quotient index)
  rw [Remainder.pairPost_away _ base low high bits _
    (Workspace.separate base .quotient .remainder (by intro same;cases same) index 0 (by change index<16;omega) (by decide))
    (Workspace.separate base .quotient .remainder (by intro same;cases same) index 1 (by change index<16;omega) (by decide))]
  exact (Trailing.post_away (bind middle "j" (BitVec.ofNat 64 (length-1))) base length _ different).trans (checked.loop.image index inside)

/-- The original final quotient-clear loop supplies its actual extra zero. -/
theorem Result.quotient_top_zero {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high) :
    target.memory (slot (Workspace.pointer base .quotient) (length-1))=.word 0#64 := by
  have large:=checked.ready.entry.large
  have small:=checked.ready.entry.small
  rw [checked.state]
  change (Remainder.pairPost (bind (Trailing.cleared middle base length) "i" 0#64) base low high bits).memory (slot (Workspace.pointer base .quotient) (length-1))=.word 0#64
  rw [Remainder.pairPost_away _ base low high bits _
    (Workspace.separate base .quotient .remainder (by intro same;cases same) (length-1) 0 (by change length-1<16;omega) (by decide))
    (Workspace.separate base .quotient .remainder (by intro same;cases same) (length-1) 1 (by change length-1<16;omega) (by decide))]
  simp [Trailing.cleared,Trailing.post,WitnessRadix.QueryBranch.bind,setVarHOLFinite,StoreWord.put]

end InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.memory_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.remainder_cells
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.quotient_prefix
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.quotient_top_zero

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current physical caller inputs, independently of its local names. -/
structure Buffers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length : Nat) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  large : 2≤length
  small : length≤16
  uImage : Image source (Workspace.pointer base .numerator) u length
  vImage : Image source (Workspace.pointer base .divisor) v 2
  uSmall : ∀ index,index<length→(u index).toNat<4294967296
  vSmall : ∀ index,index<2→(v index).toNat<4294967296
  leadingPositive : 0<(v 1).toNat

def values (base : BitVec 64) (length : Nat) : List (ValueHOL 64):=
  [.val (.word (Workspace.pointer base .quotient)),.val (.word (Workspace.pointer base .remainder)),
    .val (.word (Workspace.pointer base .numerator)),.val (.word (BitVec.ofNat 64 length)),
    .val (.word (Workspace.pointer base .divisor)),.val (.word 2#64)]

private def rawLocals (base : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "n" then some (.val (.word 2#64)) else
  if name=ofString "v" then some (.val (.word (Workspace.pointer base .divisor))) else
  if name=ofString "m" then some (.val (.word (BitVec.ofNat 64 length))) else
  if name=ofString "u" then some (.val (.word (Workspace.pointer base .numerator))) else
  if name=ofString "r" then some (.val (.word (Workspace.pointer base .remainder))) else
  if name=ofString "q" then some (.val (.word (Workspace.pointer base .quotient))) else none

/-- The genuine six-scalar signature installs each actual two-digit
argument, independently of the names of the caller's expressions. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (base : BitVec 64) (length : Nat)
    (code : codeFn (ofString "divmnu")=some (Single.formals,Single.body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "divmnu") (values base length)=some (Single.body,callee,.one) ∧
      callee.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))) ∧
      callee.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))) ∧
      callee.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))) ∧
      callee.lookup (ofString "v")=some (.val (.word (Workspace.pointer base .divisor))) ∧
      callee.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 length))) ∧
      callee.lookup (ofString "n")=some (.val (.word 2#64)) := by
  have valid : (Single.formals.map Prod.fst).Nodup ∧ Single.formals.length=(values base length).length ∧
      ((Single.formals.zip (values base length)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=by
    exact ⟨by decide,rfl,by simp [Single.formals,values,shapeOfHOLExact,shapeEqHOL_eq_true]⟩
  have raw : lookupCodeHOLExact codeFn (ofString "divmnu") (values base length)=some (Single.body,rawLocals base length,.one):=by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [locals];simp [rawLocals,ofString]

private theorem callee_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (u v : Nat→BitVec 64) (length : Nat)
    (checked : Buffers source base u v length) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (q : callee.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))))
    (r : callee.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))))
    (uCell : callee.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))))
    (vCell : callee.lookup (ofString "v")=some (.val (.word (Workspace.pointer base .divisor))))
    (m : callee.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 length))))
    (n : callee.lookup (ofString "n")=some (.val (.word 2#64))) :
    Entry (callEntryStateHOLFinite source callee) base u v length :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,checked.large,checked.small,
    q,r,uCell,vCell,m,n,checked.uImage,checked.vImage,checked.uSmall,checked.vSmall,checked.leadingPositive⟩

/-- The actual ignored-result call to the unchanged two-digit divmnu costs
≤40*m-34source ticks, including its real caller tick and stopped outcomes. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length : Nat) (checked : Buffers source base u v length) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values base length)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "divmnu") arguments)).2.clock≤40*length-34 := by
  obtain ⟨callee,called,q,r,uCell,vCell,m,n⟩:=environment source.code.lookup base length (Single.original_code source.code checked.installed)
  have actual:=callee_entry source base u v length checked callee q r uCell vCell m n
  have price:=ClockCost.call_current source (some none) (ofString "divmnu") arguments _ Single.body callee .one (40*length-35) args called
    (body_cost (callEntryStateHOLFinite source callee) base u v length actual)
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "divmnu") arguments)).2.clock≤(40*length-35)+1 at price
  have large:=checked.large
  omega

end InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.environment
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.call_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def remainderDigits (low high : BitVec 64) (bits index : Nat) : BitVec 64:=
  if index=0 then Denormalize.digit low high bits else if index=1 then Denormalize.digit high 0#64 bits else 0#64

/-- Earlier actual quotient zeros beyond m survive, while the real loop
and final store supply every newly produced or cleared lower digit. -/
theorem Result.quotient_image {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high)
    (zeros : ∀ index,length≤index→index<16→source.memory (slot (Workspace.pointer base .quotient) index)=.word 0#64) :
    Image target (Workspace.pointer base .quotient) (Single.padded quotient (length-1)) 16 := by
  have large:=checked.ready.entry.large
  have small:=checked.ready.entry.small
  intro index inside
  by_cases lower : index<length-1
  · simpa only [Single.padded,if_pos lower] using checked.quotient_prefix index lower
  · by_cases last : index=length-1
    · subst index
      simpa only [Single.padded,if_neg (show ¬length-1<length-1 by omega)] using checked.quotient_top_zero
    · have retained:=checked.memory_away (slot (Workspace.pointer base .quotient) index)
        (by intro current bound;exact Workspace.separate base .quotient .normalizedNumerator (by intro same;cases same) index current inside (by change current<17;omega))
        (by intro current bound;exact Workspace.separate base .quotient .normalizedDivisor (by intro same;cases same) index current inside (by change current<8;omega))
        (by
          intro current bound hit
          have same:=slot_injective (Workspace.pointer base .quotient) index current inside (by omega) hit
          omega)
        (by intro current bound;exact Workspace.separate base .quotient .remainder (by intro same;cases same) index current inside (by change current<8;omega))
      rw [retained,zeros index (by omega) inside]
      simp only [Single.padded,if_neg lower]

theorem Result.quotient_digits {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high) :
    ∀ index,index<16→(Single.padded quotient (length-1) index).toNat<4294967296 := by
  intro index inside
  by_cases lower : index<length-1
  · simpa only [Single.padded,if_pos lower] using checked.loop.digits index lower
  · simp only [Single.padded,if_neg lower,BitVec.toNat_zero]
    decide

/-- Earlier actual R[2..7] zeros survive both real remainder stores. -/
theorem Result.remainder_image {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high)
    (zeros : ∀ index,2≤index→index<8→source.memory (slot (Workspace.pointer base .remainder) index)=.word 0#64) :
    Image target (Workspace.pointer base .remainder) (remainderDigits low high bits) 8 := by
  have large:=checked.ready.entry.large
  have small:=checked.ready.entry.small
  intro index inside
  by_cases zero : index=0
  · subst index
    simpa only [remainderDigits,if_pos rfl,ite_true] using checked.remainder_cells.1
  · by_cases one : index=1
    · subst index
      simpa only [remainderDigits,if_neg (by decide : ¬(1:Nat)=0),if_pos rfl,ite_true] using checked.remainder_cells.2
    · have retained:=checked.memory_away (slot (Workspace.pointer base .remainder) index)
        (by intro current bound;exact Workspace.separate base .remainder .normalizedNumerator (by intro same;cases same) index current inside (by change current<17;omega))
        (by intro current bound;exact Workspace.separate base .remainder .normalizedDivisor (by intro same;cases same) index current inside (by change current<8;omega))
        (by intro current bound;exact Workspace.separate base .remainder .quotient (by intro same;cases same) index current inside (by change current<16;omega))
        (by
          intro current bound hit
          have same:=slot_injective (Workspace.pointer base .remainder) index current (by omega) (by omega) hit
          omega)
      rw [retained,zeros index (by omega) inside]
      simp only [remainderDigits,if_neg zero,if_neg one]

theorem Result.remainder_digits {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high) :
    ∀ index,index<8→(remainderDigits low high bits index).toNat<4294967296 := by
  intro index inside
  by_cases zero : index=0
  · simpa only [remainderDigits,if_pos zero] using Denormalize.digit_bound low high bits checked.ready.bitsSmall checked.loop.entry.carryLowSmall checked.loop.entry.carryHighSmall
  · by_cases one : index=1
    · simpa only [remainderDigits,if_neg zero,if_pos one] using Denormalize.digit_bound high 0#64 bits checked.ready.bitsSmall checked.loop.entry.carryHighSmall (by decide)
    · simp only [remainderDigits,if_neg zero,if_neg one,BitVec.toNat_zero]
      decide

theorem Result.remainder_number {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {u v quotient : Nat→BitVec 64} {length bits : Nat} {middle : PanSemStateFiniteExact 64 Guest.HostMemory} {low high : BitVec 64}
    (checked : Result source target base u v length bits middle quotient low high) :
    number (remainderDigits low high bits) 8=number u length%number v 2 := by
  simpa [number,remainderDigits,show (2:Nat)^32=4294967296 by decide] using checked.remainderEq

end InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.quotient_image
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.quotient_digits
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.remainder_image
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.remainder_digits
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.Result.remainder_number

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Real caller output, including the complete padded physical arrays and
all metadata retained by the original ignored-result call. -/
structure CallerResult (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v quotient remainder : Nat→BitVec 64) (length : Nat) : Prop where
  state : post={source with memory:=post.memory,clock:=post.clock}
  qImage : Image post (Workspace.pointer base .quotient) quotient 16
  qDigits : ∀ index,index<16→(quotient index).toNat<4294967296
  rImage : Image post (Workspace.pointer base .remainder) remainder 8
  rDigits : ∀ index,index<8→(remainder index).toNat<4294967296
  quotientEq : number quotient 16=number u length/number v 2
  remainderEq : number remainder 8=number u length%number v 2
  remainderSmall : number remainder 8<number v 2
  away : ∀ query,(∀ index,index≤length→query≠slot (Workspace.pointer base .normalizedNumerator) index)→
    (∀ index,index<2→query≠slot (Workspace.pointer base .normalizedDivisor) index)→
    (∀ index,index<length→query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<2→query≠slot (Workspace.pointer base .remainder) index)→post.memory query=source.memory query
  cost : source.clock-post.clock≤40*length-34

/-- The same real normal ignored-result call derives its callee execution,
ordinary quotient/remainder arrays and canonical retained caller state. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (u v : Nat→BitVec 64) (length : Nat) (checked : Buffers source base u v length) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values base length))
    (qZeros : ∀ index,length≤index→index<16→source.memory (slot (Workspace.pointer base .quotient) index)=.word 0#64)
    (rZeros : ∀ index,2≤index→index<8→source.memory (slot (Workspace.pointer base .remainder) index)=.word 0#64)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "divmnu") arguments)=(none,post)) :
    ∃ quotient remainder,CallerResult source post base u v quotient remainder length := by
  obtain ⟨callee,called,q,r,uCell,vCell,m,n⟩:=environment source.code.lookup base length (Single.original_code source.code checked.installed)
  obtain ⟨funded,target,returned,bodyRun⟩:=CallNormal.ignored_callee_return source post (ofString "divmnu") arguments _ Single.body callee .one args called normal
  have actual:=callee_entry source base u v length checked callee q r uCell vCell m n
  obtain ⟨bits,middle,quotient,low,high,returnedEq,result⟩:=body_normal (callEntryStateHOLFinite source callee) target base u v length actual returned bodyRun
  rw [returnedEq] at bodyRun
  let expected:={target with locals:=source.locals}
  have expectedRun:=evaluateHOLFiniteState_call_return_caller_locals source none (ofString "divmnu") arguments _ Single.body callee .one
    (.val (.word 0#64)) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have same : post=expected:=congrArg Prod.snd (normal.symm.trans expectedRun)
  have frame : expected={source with memory:=expected.memory,clock:=expected.clock}:=by
    have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) result.frame
    exact projected
  have quotientEq : number (Single.padded quotient (length-1)) 16=number u length/number v 2:=by
    rw [Single.padded_number quotient (length-1) 16 (by have h:=checked.small;omega)]
    exact result.quotientEq
  have remainderSmall : number (remainderDigits low high bits) 8<number v 2:=by
    rw [result.remainder_number]
    apply Nat.mod_lt
    simp only [number,Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.zero_add,Nat.one_mul]
    have positive:=checked.leadingPositive
    omega
  have price:=call_cost source base u v length checked arguments args
  rw [normal] at price
  refine ⟨Single.padded quotient (length-1),remainderDigits low high bits,?_⟩
  rw [same]
  exact ⟨frame,result.quotient_image qZeros,result.quotient_digits,result.remainder_image rZeros,result.remainder_digits,
    quotientEq,result.remainder_number,remainderSmall,result.memory_away,(by simpa only [same] using price)⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.TwoDigit.call_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The exact original eight-digit image produced from a64-bit divisor. -/
def divisorDigits (divisor : BitVec 64) : Nat→BitVec 64:=digit (Single.remainderWords divisor)

theorem divisor_number (divisor : BitVec 64) : number (divisorDigits divisor) 2=divisor.toNat := by
  simpa [number,divisorDigits,digit,Single.remainderWords] using half_number divisor

theorem divisor_small (divisor : BitVec 64) (index : Nat) (inside : index<8) : (divisorDigits divisor index).toNat<2^32 :=
  digit_small (Single.remainderWords divisor) index inside

theorem divisor_high_positive (divisor : BitVec 64) (large : 4294967296≤divisor.toNat) : 0<(divisorDigits divisor 1).toNat := by
  have lower:=divisor_small divisor 0 (by decide)
  have total:=half_number divisor
  change (divisor &&& 4294967295#64).toNat<2^32 at lower
  change 0<(divisor>>>(32:Nat)).toNat
  omega

private theorem divisor_high_nonzero (divisor : BitVec 64) (large : 4294967296≤divisor.toNat) : divisor>>>(32:Nat)≠0#64 := by
  intro zero
  have positive:=divisor_high_positive divisor large
  change 0<(divisor>>>(32:Nat)).toNat at positive
  rw [zero] at positive
  simp only [BitVec.toNat_zero] at positive
  omega

/-- The actual converted high half is nonzero and every higher digit is
zero, so the original scan returns exactly2after seven real scan ticks. -/
theorem divisor_length (divisor : BitVec 64) (large : 4294967296≤divisor.toNat) :
    Length.result (divisorDigits divisor) 8=2 ∧ Length.scans (divisorDigits divisor) 8=7 := by
  have nonzero:=divisor_high_nonzero divisor large
  simp [Length.result,Length.scans,divisorDigits,digit,Single.remainderWords,nonzero]

/-- Actual digits_divmod arguments after its q/r/v declarations, before
conversion or either scan. The divisor is a genuine64-bit word with2digits. -/
structure Prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  eight : 8≤count
  small : count≤16
  q : source.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient)))
  r : source.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder)))
  u : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator)))
  v : source.locals.lookup (ofString "v")=some (.val (.word (Workspace.pointer base .divisor)))
  m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count)))
  d : source.locals.lookup (ofString "d")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor))
  image : Image source (Workspace.pointer base .numerator) contents count
  divisorLarge : 4294967296≤divisor.toNat
  digitsSmall : ∀ index,index<count→(contents index).toNat<2^32

theorem Prepared.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Prepared source base divisor contents count) (clock : Nat) :
    Prepared {source with clock:=clock} base divisor contents count :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
    checked.eight,checked.small,checked.q,checked.r,checked.u,checked.v,checked.m,checked.d,checked.image,checked.divisorLarge,checked.digitsSmall⟩

theorem Prepared.bindTemporary {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Prepared source base divisor contents count) (name : String) (word : BitVec 64)
    (allowed : name="n" ∨ name="mm" ∨ name="i") : Prepared (bind source name word) base divisor contents count := by
  rcases allowed with rfl|rfl|rfl <;>
    refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
      checked.eight,checked.small,?_,?_,?_,?_,?_,?_,checked.image,checked.divisorLarge,checked.digitsSmall⟩ <;>
    first
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.q
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.r
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.u
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.v
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.m
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.d

/-- The actual converter fills V[0..7] and preserves the entire real
numerator image through derived U/V workspace separation. -/
theorem Prepared.convert {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Prepared source base divisor contents count) :
    Prepared (ToDigits.callerPost source (Workspace.pointer base .divisor) (Single.remainderWords divisor)) base divisor contents count ∧
      Image (ToDigits.callerPost source (Workspace.pointer base .divisor) (Single.remainderWords divisor))
        (Workspace.pointer base .divisor) (divisorDigits divisor) 8 := by
  constructor
  · refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
      checked.eight,checked.small,checked.q,checked.r,checked.u,checked.v,checked.m,checked.d,?_,checked.divisorLarge,checked.digitsSmall⟩
    intro index inside
    rw [ToDigits.caller_away source (Workspace.pointer base .divisor) (slot (Workspace.pointer base .numerator) index) (Single.remainderWords divisor) (by
      intro other bound
      exact Workspace.separate base .numerator .divisor (by intro same;cases same) index other (by change index<16;have h:=checked.small;omega) bound)]
    exact checked.image index inside
  · exact ToDigits.caller_image source (Workspace.pointer base .divisor) (Single.remainderWords divisor)

structure Scanned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) : Prop extends Prepared source base divisor contents count where
  divisorImage : Image source (Workspace.pointer base .divisor) (divisorDigits divisor) 8
  n : source.locals.lookup (ofString "n")=some (.val (.word 2#64))
  mm : source.locals.lookup (ofString "mm")=some (.val (.word (BitVec.ofNat 64 (Length.result contents count))))

theorem Scanned.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Scanned source base divisor contents count) (clock : Nat) :
    Scanned {source with clock:=clock} base divisor contents count :=
  ⟨checked.toPrepared.withClock clock,checked.divisorImage,checked.n,checked.mm⟩

/-- Once the actual mm≥n guard is passed, the retained converted images
and actual scan value establish the real divmnu physical input buffers. -/
theorem Scanned.buffers {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Scanned source base divisor contents count)
    (large : 2≤Length.result contents count) : TwoDigit.Buffers source base contents (divisorDigits divisor) (Length.result contents count) := by
  have bound:=Length.result_bound contents count
  have small:=checked.small
  refine ⟨checked.context,checked.installed,large,by omega,?_,?_,?_,?_,divisor_high_positive divisor checked.divisorLarge⟩
  · intro index inside
    exact checked.image index (by omega)
  · intro index inside
    exact checked.divisorImage index (by omega)
  · intro index inside
    exact checked.digitsSmall index (by omega)
  · intro index inside
    exact divisor_small divisor index (by omega)

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.divisor_number
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.divisor_small
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.divisor_high_positive
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.divisor_length
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.Prepared.convert
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.Scanned.buffers

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def afterDivisorLength (continuation : ProgHOL 64) : ProgHOL 64:=
  .decCall (ofString "mm") .one (ofString "digits_len") DivMod.numeratorLengthArguments continuation
def afterConversion (continuation : ProgHOL 64) : ProgHOL 64:=
  .decCall (ofString "n") .one (ofString "digits_len") DivMod.divisorLengthArguments (afterDivisorLength continuation)
def setup (continuation : ProgHOL 64) : ProgHOL 64:=
  .seq (.call (some (none,none)) (ofString "u256_to_digits") DivMod.convertArguments) (afterConversion continuation)

theorem literal_setup : DivMod.setupDivisor=setup DivMod.afterCounts := by rfl

def converted (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) :=
  ToDigits.callerPost source (Workspace.pointer base .divisor) (Single.remainderWords divisor)
def nEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) :=
  bind {converted source base divisor with clock:=(converted source base divisor).clock-1-7} "n" 2#64
def scannedSource (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (contents : Nat→BitVec 64) (count : Nat) :=
  bind {nEntry source base divisor with clock:=(nEntry source base divisor).clock-1-Length.scans contents count} "mm" (BitVec.ofNat 64 (Length.result contents count))
def prefixRestored (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) :=
  restore (converted source base divisor) "n" (restore (nEntry source base divisor) "mm" target)
def prefixPrice (contents : Nat→BitVec 64) (count : Nat) : Nat:=10+Length.scans contents count

theorem scannedSource_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (contents : Nat→BitVec 64) (count : Nat) :
    (scannedSource source base divisor contents count).clock=source.clock-prefixPrice contents count := by
  change source.clock-1-1-7-1-Length.scans contents count=source.clock-(10+Length.scans contents count)
  omega

/-- The original divisor conversion and both actual scoped length calls
resume any real continuation with the derived n=2/mm and physical images. -/
theorem prefix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Prepared source base divisor contents count)
    (enough : prefixPrice contents count≤source.clock) (continuation : ProgHOL 64) :
    Scanned (scannedSource source base divisor contents count) base divisor contents count ∧
      evaluateHOLFiniteState source (setup continuation)=
        (let output:=evaluateHOLFiniteState (scannedSource source base divisor contents count) continuation
         (output.1,prefixRestored source output.2 base divisor)) := by
  obtain ⟨convertedModel,divisorImage⟩:=checked.convert
  have nModel : Prepared (nEntry source base divisor) base divisor contents count:=
    (convertedModel.withClock ((converted source base divisor).clock-1-7)).bindTemporary "n" 2#64 (Or.inl rfl)
  have mmModel : Prepared (scannedSource source base divisor contents count) base divisor contents count:=
    (nModel.withClock ((nEntry source base divisor).clock-1-Length.scans contents count)).bindTemporary "mm" _ (Or.inr (Or.inl rfl))
  have scansReady : Scanned (scannedSource source base divisor contents count) base divisor contents count:=
    ⟨mmModel,divisorImage,(bind_lookup_other _ "mm" "n" _ (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _⟩
  have convertArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) DivMod.convertArguments=
      some [.val (.word (Workspace.pointer base .divisor)),RlpWrite.U256Value.tuple (Single.remainderWords divisor)]:=by
    have vLocal:=checked.v
    have dLocal:=checked.d
    simp [DivMod.convertArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,vLocal,dLocal]
  have convertRun:=ToDigits.call_execute source (Workspace.pointer base .divisor) (Single.remainderWords divisor) DivMod.convertArguments checked.installed convertArgs
    (by intro index inside;exact Workspace.slot_mapped source base checked.context .divisor index inside) (by unfold prefixPrice at enough;omega)
  have nArgs : evalListHOLFinite (converted source base divisor) (h:=fun query=>Classical.propDecidable ((converted source base divisor).memaddrs query)) DivMod.divisorLengthArguments=
      some [.val (.word (Workspace.pointer base .divisor)),.val (.word (BitVec.ofNat 64 8))]:=by
    have vLocal : (converted source base divisor).locals.lookup (ofString "v")=some (.val (.word (Workspace.pointer base .divisor))):=convertedModel.v
    simp [DivMod.divisorLengthArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,vLocal]
  have mmArgs : evalListHOLFinite (nEntry source base divisor) (h:=fun query=>Classical.propDecidable ((nEntry source base divisor).memaddrs query)) DivMod.numeratorLengthArguments=
      some [.val (.word (Workspace.pointer base .numerator)),.val (.word (BitVec.ofNat 64 count))]:=by
    have uLocal:=nModel.u
    have mLocal:=nModel.m
    simp [DivMod.numeratorLengthArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,uLocal,mLocal]
  have nClock : (nEntry source base divisor).clock=source.clock-9:=by change source.clock-1-1-7=source.clock-9;omega
  have mmFunded : Length.scans contents count+1≤(nEntry source base divisor).clock:=by
    rw [nClock]
    unfold prefixPrice at enough
    omega
  have mmRun:=Length.call_execute (nEntry source base divisor) (Workspace.pointer base .numerator) contents count checked.small "mm" DivMod.numeratorLengthArguments continuation nModel.installed mmArgs nModel.image
    (by intro index inside;exact Workspace.slot_mapped _ base nModel.context .numerator index (by have h:=checked.small;change index<16;omega)) mmFunded
  have divisorFacts:=divisor_length divisor checked.divisorLarge
  have nFunded : Length.scans (divisorDigits divisor) 8+1≤(converted source base divisor).clock:=by
    rw [divisorFacts.2]
    change 8≤source.clock-1
    unfold prefixPrice at enough
    omega
  have nRun:=Length.call_execute (converted source base divisor) (Workspace.pointer base .divisor) (divisorDigits divisor) 8 (by decide) "n" DivMod.divisorLengthArguments (afterDivisorLength continuation)
    convertedModel.installed nArgs divisorImage (by intro index inside;exact Workspace.slot_mapped _ base convertedModel.context .divisor index inside) nFunded
  rw [divisorFacts.1,divisorFacts.2] at nRun
  change evaluateHOLFiniteState (converted source base divisor) (afterConversion continuation)=
    (let output:=evaluateHOLFiniteState (nEntry source base divisor) (afterDivisorLength continuation)
     (output.1,restore (converted source base divisor) "n" output.2)) at nRun
  rw [afterDivisorLength,mmRun] at nRun
  refine ⟨scansReady,?_⟩
  rw [setup,StateSteps.next_sequence source (converted source base divisor) _ _ convertRun (by change source.clock-1≤source.clock;omega)]
  exact nRun

/-- Both scans are charged by their actual observed input digits. -/
theorem prefix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Prepared source base divisor contents count) :
    source.clock-(evaluateHOLFiniteState source (setup .skip)).2.clock≤prefixPrice contents count := by
  by_cases enough : prefixPrice contents count≤source.clock
  · have actual:=(prefix_execute source base divisor contents count checked enough .skip).2
    rw [actual]
    simp only [evaluateHOLFiniteState_skip]
    change source.clock-(scannedSource source base divisor contents count).clock≤prefixPrice contents count
    rw [scannedSource_clock]
    omega
  · omega

/-- Actual non-timeout enclosing executions derive the prefix's funding
and exact real scan continuation; no future successful scan is supplied. -/
theorem prefix_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Prepared source base divisor contents count) (continuation : ProgHOL 64)
    (result : Option (PanSemResultExact 64)) (normal : evaluateHOLFiniteState source (setup continuation)=(result,target)) (notTimeout : result≠some .timeOut) :
    ∃ inner,prefixPrice contents count≤source.clock ∧ Scanned (scannedSource source base divisor contents count) base divisor contents count ∧
      evaluateHOLFiniteState (scannedSource source base divisor contents count) continuation=(result,inner) ∧ target=prefixRestored source inner base divisor := by
  let paddedSource:={source with clock:=source.clock+prefixPrice contents count}
  have padded:=panPropsEvaluateAddClockEq (setup continuation) source result target (prefixPrice contents count) ⟨normal,notTimeout⟩
  have paddedRun:=(prefix_execute paddedSource base divisor contents count (checked.withClock (source.clock+prefixPrice contents count)) (by change prefixPrice contents count≤source.clock+prefixPrice contents count;omega) continuation).2
  have compared:=congrArg (fun output : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>output.2.clock) (paddedRun.symm.trans padded)
  change (evaluateHOLFiniteState (scannedSource paddedSource base divisor contents count) continuation).2.clock=target.clock+prefixPrice contents count at compared
  have forward:=evaluateHOLFiniteState_clock_le (scannedSource paddedSource base divisor contents count) continuation
  have clock:=scannedSource_clock paddedSource base divisor contents count
  change (scannedSource paddedSource base divisor contents count).clock=(source.clock+prefixPrice contents count)-prefixPrice contents count at clock
  have funded : prefixPrice contents count≤source.clock:=by omega
  obtain ⟨ready,actual⟩:=prefix_execute source base divisor contents count checked funded continuation
  let output:=evaluateHOLFiniteState (scannedSource source base divisor contents count) continuation
  have observed : output.1=result:=congrArg Prod.fst (actual.symm.trans normal)
  exact ⟨output.2,funded,ready,Prod.ext observed rfl,congrArg Prod.snd (normal.symm.trans actual)⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.literal_setup
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.scannedSource_clock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.prefix_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.prefix_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.prefix_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem Scanned.bindIndex {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Scanned source base divisor contents count) (word : BitVec 64) :
    Scanned (bind source "i" word) base divisor contents count :=
  ⟨checked.toPrepared.bindTemporary "i" word (Or.inr (Or.inr rfl)),checked.divisorImage,
    (bind_lookup_other source "i" "n" word (by decide)).trans checked.n,(bind_lookup_other source "i" "mm" word (by decide)).trans checked.mm⟩

/-- The actual zero-store state preserves both current input images and
all scan/formal bindings when the cleared array is distinct from U and V. -/
theorem Scanned.afterClear {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Scanned source base divisor contents count)
    (cleared : Workspace.Buffer) (notU : .numerator≠cleared) (notV : .divisor≠cleared) :
    Scanned (Clear.after source (Workspace.pointer base cleared) 0 (Workspace.count cleared)) base divisor contents count := by
  let pointer:=Workspace.pointer base cleared
  let target:=Clear.after source pointer 0 (Workspace.count cleared)
  have fields:=Clear.after_state source pointer 0 (Workspace.count cleared)
  have code:=congrArg PanSemStateFiniteExact.code fields
  change target.code=source.code at code
  have installed : OriginalCode.Installed target.code:=by rw [code];exact checked.installed
  have numeratorImage : Image target (Workspace.pointer base .numerator) contents count:=by
    intro index inside
    have retained:=Clear.after_away source pointer (slot (Workspace.pointer base .numerator) index) (Workspace.count cleared) (by
      intro other bound
      exact Workspace.separate base .numerator cleared notU index other (by change index<16;have h:=checked.small;omega) bound)
    exact retained.trans (checked.image index inside)
  have divisorImage : Image target (Workspace.pointer base .divisor) (divisorDigits divisor) 8:=by
    intro index inside
    have retained:=Clear.after_away source pointer (slot (Workspace.pointer base .divisor) index) (Workspace.count cleared) (by
      intro other bound
      exact Workspace.separate base .divisor cleared notV index other inside bound)
    exact retained.trans (checked.divisorImage index inside)
  refine ⟨⟨Clear.after_context source base pointer (Workspace.count cleared) checked.context,installed,checked.eight,checked.small,
    ?_,?_,?_,?_,?_,?_,numeratorImage,checked.divisorLarge,checked.digitsSmall⟩,divisorImage,?_,?_⟩
  · exact (Clear.after_other source pointer 0 _ "q" (by decide)).trans checked.q
  · exact (Clear.after_other source pointer 0 _ "r" (by decide)).trans checked.r
  · exact (Clear.after_other source pointer 0 _ "u" (by decide)).trans checked.u
  · exact (Clear.after_other source pointer 0 _ "v" (by decide)).trans checked.v
  · exact (Clear.after_other source pointer 0 _ "m" (by decide)).trans checked.m
  · exact (Clear.after_other source pointer 0 _ "d" (by decide)).trans checked.d
  · exact (Clear.after_other source pointer 0 _ "n" (by decide)).trans checked.n
  · exact (Clear.after_other source pointer 0 _ "mm" (by decide)).trans checked.mm

def qCleared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :=
  Clear.after (bind source "i" 0#64) (Workspace.pointer base .quotient) 0 16
def clearedSource (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :=
  Clear.after (bind (qCleared source base) "i" 0#64) (Workspace.pointer base .remainder) 0 8

theorem Scanned.cleared {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Scanned source base divisor contents count) :
    Scanned (clearedSource source base) base divisor contents count :=
  ((((checked.bindIndex 0#64).afterClear .quotient (by intro same;cases same) (by intro same;cases same)).bindIndex 0#64).afterClear .remainder (by intro same;cases same) (by intro same;cases same))

theorem cleared_qzeros (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    Image (clearedSource source base) (Workspace.pointer base .quotient) (fun _=>0#64) 16 := by
  intro index inside
  have retained:=Clear.after_away (bind (qCleared source base) "i" 0#64) (Workspace.pointer base .remainder) (slot (Workspace.pointer base .quotient) index) 8 (by
    intro other bound
    exact Workspace.separate base .quotient .remainder (by intro same;cases same) index other inside bound)
  exact retained.trans (Clear.after_image (bind source "i" 0#64) (Workspace.pointer base .quotient) 16 index inside)

theorem cleared_rzeros (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    Image (clearedSource source base) (Workspace.pointer base .remainder) (fun _=>0#64) 8 :=
  Clear.after_image (bind (qCleared source base) "i" 0#64) (Workspace.pointer base .remainder) 8

theorem Scanned.wide_args {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Scanned source base divisor contents count) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Single.wideArguments=
      some (TwoDigit.values base (Length.result contents count)) := by
  have q:=checked.q
  have r:=checked.r
  have u:=checked.u
  have v:=checked.v
  have mm:=checked.mm
  have n:=checked.n
  simp [Single.wideArguments,TwoDigit.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,q,r,u,v,mm,n]

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.Scanned.afterClear
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.Scanned.cleared
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.cleared_qzeros
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.cleared_rzeros
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.Scanned.wide_args

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem guard_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count) :
    eval source DivMod.lessTest=some (.val (.word (if Length.result contents count<2 then 1#64 else 0#64))) := by
  have bound:=Length.result_bound contents count
  have small:=checked.small
  have encoded : (BitVec.ofNat 64 (Length.result contents count)).toNat=Length.result contents count:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have mm:=checked.mm
  have n:=checked.n
  simp [eval,DivMod.lessTest,localVar,evalHOLExact,toExact,mm,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,encoded]

def afterCounts (continuation : ProgHOL 64) : ProgHOL 64:=
  .dec (ofString "i") .one (.const 0#64) (.seq (Clear.loop "q" 16)
    (.seq DivMod.guard (.seq DivMod.resetIndex (.seq (Clear.loop "r" 8) continuation))))

theorem literal_afterCounts : DivMod.afterCounts=afterCounts (Single.afterClearing Single.wideArguments) := by rfl

theorem qCleared_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    (qCleared source base).clock=source.clock-16 := by
  have clock:=congrArg PanSemStateFiniteExact.clock (Clear.after_state (bind source "i" 0#64) (Workspace.pointer base .quotient) 0 16)
  exact clock

private theorem bind_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64) :
    (bind source name word).clock=source.clock := rfl

private theorem clear_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    (Clear.after source pointer index rounds).clock=source.clock-rounds :=
  congrArg PanSemStateFiniteExact.clock (Clear.after_state source pointer index rounds)

theorem clearedSource_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    (clearedSource source base).clock=source.clock-24 := by
  have qClock:=qCleared_clock source base
  have rClock:=clear_clock (bind (qCleared source base) "i" 0#64) (Workspace.pointer base .remainder) 0 8
  simp only [bind_clock] at rClock
  change (clearedSource source base).clock=(qCleared source base).clock-8 at rClock
  omega

set_option maxHeartbeats 800000 in
/-- The actual Q clear, false mm<n guard, i reset and R clear resume any
original continuation after24real loop ticks on the reached large branch. -/
theorem clears_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (large : 2≤Length.result contents count) (enough : 24≤source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (afterCounts continuation)=
      (let output:=evaluateHOLFiniteState (clearedSource source base) continuation
       (output.1,restore source "i" output.2)) := by
  let indexed:=bind source "i" 0#64
  let reset:=bind (qCleared source base) "i" 0#64
  have indexedModel:=checked.bindIndex 0#64
  have qModel : Scanned (qCleared source base) base divisor contents count:=
    indexedModel.afterClear .quotient (by intro same;cases same) (by intro same;cases same)
  have resetModel:=qModel.bindIndex 0#64
  have qRun:=Clear.loop_execute indexed "q" (Workspace.pointer base .quotient) 16 0 16 (by decide) rfl indexedModel.q (bind_lookup_same _ _ _) (by decide)
    (by intro index inside;exact Workspace.slot_mapped indexed base indexedModel.context .quotient index inside) (by change 16≤source.clock;omega)
  have qForward:=evaluateHOLFiniteState_clock_le indexed (Clear.loop "q" 16)
  rw [qRun] at qForward
  have qI : (qCleared source base).locals.lookup (ofString "i")=some (.val (.word 16#64)):=
    Clear.after_index indexed (Workspace.pointer base .quotient) 0 16 (bind_lookup_same _ _ _)
  have guardFalse:=guard_read (qCleared source base) base divisor contents count qModel
  rw [if_neg (by omega : ¬Length.result contents count<2)] at guardFalse
  have guardRun : evaluateHOLFiniteState (qCleared source base) DivMod.guard=(none,qCleared source base):=by
    simp only [eval] at guardFalse
    rw [DivMod.guard,evaluateHOLFiniteState_ite,guardFalse]
    simp [evaluateHOLFiniteState_skip]
  have resetRun:=StateSteps.assign_execute (qCleared source base) "i" (.const 0#64) 16#64 0#64 qI rfl
  have rFunded : 8≤reset.clock:=by
    dsimp only [reset]
    rw [bind_clock,qCleared_clock]
    omega
  have rRun:=Clear.loop_execute reset "r" (Workspace.pointer base .remainder) 8 0 8 (by decide) rfl resetModel.r (bind_lookup_same _ _ _) (by decide)
    (by intro index inside;exact Workspace.slot_mapped reset base resetModel.context .remainder index inside) rFunded
  have rForward:=evaluateHOLFiniteState_clock_le reset (Clear.loop "r" 8)
  rw [rRun] at rForward
  have run : evaluateHOLFiniteState indexed (.seq (Clear.loop "q" 16)
      (.seq DivMod.guard (.seq DivMod.resetIndex (.seq (Clear.loop "r" 8) continuation))))=
      evaluateHOLFiniteState (clearedSource source base) continuation := by
    rw [DivMod.resetIndex,StateSteps.next_sequence indexed (qCleared source base) _ _ qRun qForward,
      StateSteps.next_sequence (qCleared source base) (qCleared source base) _ _ guardRun (by rfl),
      StateSteps.next_sequence (qCleared source base) reset _ _ resetRun (Nat.le_of_eq (bind_clock _ _ _)),
      StateSteps.next_sequence reset (clearedSource source base) _ _ rRun rForward]
  let output:=evaluateHOLFiniteState (clearedSource source base) continuation
  have declared:=ScalarScope.declare_execute source output.2 "i" (.const 0#64) 0#64
    (.seq (Clear.loop "q" 16) (.seq DivMod.guard (.seq DivMod.resetIndex (.seq (Clear.loop "r" 8) continuation)))) output.1 rfl (by rw [run])
  exact declared

/-- A real non-timeout large-branch continuation derives the two clears'
funding and exact continuation state from the same execution. -/
theorem clears_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (large : 2≤Length.result contents count) (continuation : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (normal : evaluateHOLFiniteState source (afterCounts continuation)=(result,target)) (notTimeout : result≠some .timeOut) :
    ∃ inner,24≤source.clock ∧ evaluateHOLFiniteState (clearedSource source base) continuation=(result,inner) ∧ target=restore source "i" inner := by
  let paddedSource:={source with clock:=source.clock+24}
  have padded:=panPropsEvaluateAddClockEq (afterCounts continuation) source result target 24 ⟨normal,notTimeout⟩
  have paddedRun:=clears_execute paddedSource base divisor contents count (checked.withClock (source.clock+24)) large (by change 24≤source.clock+24;omega) continuation
  have compared:=congrArg (fun output : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>output.2.clock) (paddedRun.symm.trans padded)
  change (evaluateHOLFiniteState (clearedSource paddedSource base) continuation).2.clock=target.clock+24 at compared
  have forward:=evaluateHOLFiniteState_clock_le (clearedSource paddedSource base) continuation
  have clock:=clearedSource_clock paddedSource base
  change (clearedSource paddedSource base).clock=(source.clock+24)-24 at clock
  have funded : 24≤source.clock:=by omega
  have actual:=clears_execute source base divisor contents count checked large funded continuation
  let output:=evaluateHOLFiniteState (clearedSource source base) continuation
  have observed : output.1=result:=congrArg Prod.fst (actual.symm.trans normal)
  exact ⟨output.2,funded,Prod.ext observed rfl,congrArg Prod.snd (normal.symm.trans actual)⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.literal_afterCounts
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.qCleared_clock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.clearedSource_clock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.clears_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.clears_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- All outcomes of the actual reached divmnu/reconstruction tail. -/
theorem after_clearing_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (large : 2≤Length.result contents count) :
    source.clock-(evaluateHOLFiniteState source (Single.afterClearing Single.wideArguments)).2.clock≤40*Length.result contents count-33 := by
  have price:=ClockCost.sequence_current source
    (.call (some (none,none)) (ofString "divmnu") Single.wideArguments) (.call none (ofString "digits_to_u256") Single.returnArguments)
    (40*Length.result contents count-34) 1
    (TwoDigit.call_cost source base contents (divisorDigits divisor) (Length.result contents count) (checked.buffers large) Single.wideArguments checked.wide_args)
    (ToWords.tail_cost source.code checked.installed Single.returnArguments)
  change source.clock-(evaluateHOLFiniteState source (Single.afterClearing Single.wideArguments)).2.clock≤(40*Length.result contents count-34)+1 at price
  omega

structure TailResult (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents quotient : Nat→BitVec 64) (count : Nat) (remainder : Quad) : Prop where
  state : post={source with locals:=post.locals,memory:=post.memory,clock:=post.clock}
  quotientImage : Image post (Workspace.pointer base .quotient) quotient 16
  quotientDigits : ∀ index,index<16→(quotient index).toNat<4294967296
  quotientEq : number quotient 16=number contents count/divisor.toNat
  remainderEq : quadNumber remainder=number contents count%divisor.toNat
  small : quadNumber remainder<divisor.toNat
  away : ∀ query,(∀ index,index≤Length.result contents count→ query≠slot (Workspace.pointer base .normalizedNumerator) index)→
    (∀ index,index<2→ query≠slot (Workspace.pointer base .normalizedDivisor) index)→
    (∀ index,index<Length.result contents count→ query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<2→ query≠slot (Workspace.pointer base .remainder) index)→post.memory query=source.memory query
  cost : source.clock-post.clock≤40*Length.result contents count-33

/-- The real normal tail exposes its actual ignored-result division and
physical remainder reconstruction, with no assumed future child success. -/
theorem after_clearing_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (large : 2≤Length.result contents count)
    (qZero : Image source (Workspace.pointer base .quotient) (fun _=>0#64) 16)
    (rZero : Image source (Workspace.pointer base .remainder) (fun _=>0#64) 8)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (Single.afterClearing Single.wideArguments)=(some (.returned returned),post)) :
    ∃ quotient remainder,returned=RlpWrite.U256Value.tuple remainder ∧ TailResult source post base divisor contents quotient count remainder := by
  have safe : LocalPrefix (ofString "unused") (.call (some (none,none)) (ofString "divmnu") Single.wideArguments):=
    .call none (ofString "divmnu") Single.wideArguments (by intro name impossible;cases impossible)
  rw [Single.afterClearing] at normal
  obtain ⟨middle,divisionRun,returnRun⟩:=sequence_returned source post
    (.call (some (none,none)) (ofString "divmnu") Single.wideArguments) (.call none (ofString "digits_to_u256") Single.returnArguments)
    returned (safe.summary_full source).2.1 normal
  obtain ⟨quotient,remainder,division⟩:=TwoDigit.call_normal source middle base contents (divisorDigits divisor) (Length.result contents count)
    (checked.buffers large) Single.wideArguments checked.wide_args (by intro index after inside;exact qZero index inside)
    (by intro index after inside;exact rZero index inside) divisionRun
  have nextContext : Workspace.Context middle base:=by
    refine ⟨?_,?_,checked.context.arena,checked.context.aligned⟩
    · rw [division.state]
      exact checked.context.global
    · rw [division.state]
      exact checked.context.domain
  have nextCode : OriginalCode.Installed middle.code:=by rw [division.state];exact checked.installed
  have nextR : middle.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))):=by
    rw [division.state]
    exact checked.r
  have returnArgs : evalListHOLFinite middle (h:=fun query=>Classical.propDecidable (middle.memaddrs query)) Single.returnArguments=some [.val (.word (Workspace.pointer base .remainder))]:=by
    simp [Single.returnArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,nextR]
  obtain ⟨returnFunded,returnedEq,postEq⟩:=ToWords.tail_normal middle post (Workspace.pointer base .remainder) remainder Single.returnArguments nextCode returnArgs division.rImage
    (by intro index inside;exact Workspace.slot_mapped middle base nextContext .remainder index inside) returned returnRun
  have quotientEq:=division.quotientEq
  rw [Length.trimmed_number,divisor_number] at quotientEq
  have remainderEq : quadNumber (ToWords.words remainder)=number contents count%divisor.toNat:=by
    have value:=(ToWords.words_number remainder division.rDigits).trans division.remainderEq
    rw [Length.trimmed_number,divisor_number] at value
    exact value
  have small : quadNumber (ToWords.words remainder)<divisor.toNat:=by
    rw [remainderEq]
    apply Nat.mod_lt
    have h:=checked.divisorLarge
    omega
  have price:=after_clearing_cost source base divisor contents count checked large
  have original : evaluateHOLFiniteState source (Single.afterClearing Single.wideArguments)=(some (.returned returned),post):=normal
  rw [original] at price
  refine ⟨quotient,ToWords.words remainder,returnedEq,⟨?_,?_,division.qDigits,quotientEq,remainderEq,small,?_,price⟩⟩
  · rw [postEq,division.state]
    rfl
  · rw [postEq]
    exact division.qImage
  · intro query outsideU outsideV outsideQ outsideR
    rw [postEq]
    exact division.away query outsideU outsideV outsideQ outsideR

/-- The complete actually reached large branch, including both genuine
clears, is bounded by40*mm-9source ticks on every stopped outcome too. -/
theorem large_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (large : 2≤Length.result contents count) :
    source.clock-(evaluateHOLFiniteState source DivMod.afterCounts).2.clock≤40*Length.result contents count-9 := by
  by_cases enough : 24≤source.clock
  · have actual:=clears_execute source base divisor contents count checked large enough (Single.afterClearing Single.wideArguments)
    have price:=after_clearing_cost (clearedSource source base) base divisor contents count checked.cleared large
    have forward:=evaluateHOLFiniteState_clock_le (clearedSource source base) (Single.afterClearing Single.wideArguments)
    rw [literal_afterCounts,actual]
    change source.clock-(evaluateHOLFiniteState (clearedSource source base) (Single.afterClearing Single.wideArguments)).2.clock≤40*Length.result contents count-9
    have clock:=clearedSource_clock source base
    omega
  · omega

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.after_clearing_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.after_clearing_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.large_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual complete reached post-scan branch derives its own clear
funding and genuine division/reconstruction result, including scope exit. -/
theorem large_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (large : 2≤Length.result contents count) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source DivMod.afterCounts=(some (.returned returned),post)) :
    ∃ inner quotient remainder,24≤source.clock ∧ returned=RlpWrite.U256Value.tuple remainder ∧
      TailResult (clearedSource source base) inner base divisor contents quotient count remainder ∧
      post=restore source "i" inner ∧ source.clock-post.clock≤40*Length.result contents count-9 := by
  have actual : evaluateHOLFiniteState source (afterCounts (Single.afterClearing Single.wideArguments))=(some (.returned returned),post):=by
    rw [←literal_afterCounts]
    exact normal
  obtain ⟨inner,funded,tailRun,restored⟩:=clears_normal source post base divisor contents count checked large (Single.afterClearing Single.wideArguments)
    (some (.returned returned)) actual (by intro impossible;cases impossible)
  obtain ⟨quotient,remainder,returnedEq,result⟩:=after_clearing_normal (clearedSource source base) inner base divisor contents count checked.cleared large
    (cleared_qzeros source base) (cleared_rzeros source base) returned tailRun
  have price:=large_cost source base divisor contents count checked large
  rw [normal] at price
  exact ⟨inner,quotient,remainder,funded,returnedEq,result,restored,price⟩

/-- Actual quotient cells above the original numerator width remain zero.
This connects the16-word caller image to the later8-word reconstruction. -/
theorem TailResult.quotient_padding {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents quotient : Nat→BitVec 64} {count : Nat} {remainder : Quad}
    (checked : Scanned source base divisor contents count) (result : TailResult source post base divisor contents quotient count remainder)
    (qZero : Image source (Workspace.pointer base .quotient) (fun _=>0#64) 16) :
    ∀ index,count≤index→index<16→quotient index=0#64 := by
  have bound:=Length.result_bound contents count
  have small:=checked.small
  intro index after inside
  have retained:=result.away (slot (Workspace.pointer base .quotient) index)
    (by intro current currentInside;exact Workspace.separate base .quotient .normalizedNumerator (by intro same;cases same) index current inside (by change current<17;omega))
    (by intro current currentInside;exact Workspace.separate base .quotient .normalizedDivisor (by intro same;cases same) index current inside (by change current<8;omega))
    (by
      intro current currentInside hit
      have same:=slot_injective (Workspace.pointer base .quotient) index current inside (by omega) hit
      omega)
    (by intro current currentInside;exact Workspace.separate base .quotient .remainder (by intro same;cases same) index current inside (by change current<8;omega))
  have cell : HolWordLab.word (quotient index)=HolWordLab.word (0#64 : BitVec 64):=
    (result.quotientImage index inside).symm.trans (retained.trans (qZero index inside))
  exact HolWordLab.word.inj cell

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.large_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.TailResult.quotient_padding

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Clearing the real quotient array resumes any continuation with the
actual zero-store state and restores the original lexical index on exit. -/
theorem quotient_clear_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (enough : 16≤source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (.dec (ofString "i") .one (.const 0#64) (.seq (Clear.loop "q" 16) continuation))=
      (let output:=evaluateHOLFiniteState (qCleared source base) continuation
       (output.1,restore source "i" output.2)) := by
  let indexed:=bind source "i" 0#64
  have indexedModel:=checked.bindIndex 0#64
  have qRun:=Clear.loop_execute indexed "q" (Workspace.pointer base .quotient) 16 0 16 (by decide) rfl indexedModel.q (bind_lookup_same _ _ _) (by decide)
    (by intro index inside;exact Workspace.slot_mapped indexed base indexedModel.context .quotient index inside) enough
  let output:=evaluateHOLFiniteState (qCleared source base) continuation
  have run : evaluateHOLFiniteState indexed (.seq (Clear.loop "q" 16) continuation)=(output.1,output.2):=by
    rw [evaluateHOLFiniteState_seq_line780,qRun]
    rfl
  exact ScalarScope.declare_execute source output.2 "i" (.const 0#64) 0#64 (.seq (Clear.loop "q" 16) continuation) output.1 rfl run

def earlyPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :=
  restore source "i" (emptyLocalsHOLFinite {(qCleared source base) with clock:=(qCleared source base).clock-1})

/-- If the real scan found fewer than two digits, the actual guard returns
U immediately after Q clearing; neither R clearing nor divmnu is executed. -/
theorem early_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (short : Length.result contents count<2) (enough : 17≤source.clock) :
    evaluateHOLFiniteState source DivMod.afterCounts=
      (some (.returned (RlpWrite.U256Value.tuple (ToWords.words contents))),earlyPost source base) := by
  have qModel : Scanned (qCleared source base) base divisor contents count:=
    (checked.bindIndex 0#64).afterClear .quotient (by intro same;cases same) (by intro same;cases same)
  have args : evalListHOLFinite (qCleared source base) (h:=fun query=>Classical.propDecidable ((qCleared source base).memaddrs query)) DivMod.underflowArguments=
      some [.val (.word (Workspace.pointer base .numerator))]:=by
    have u:=qModel.u
    simp [DivMod.underflowArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,u]
  have clock:=qCleared_clock source base
  have returned:=ToWords.tail_execute (qCleared source base) (Workspace.pointer base .numerator) contents DivMod.underflowArguments qModel.installed args
    (by intro index inside;exact qModel.image index (by have eight:=checked.eight;omega))
    (by intro index inside;exact Workspace.slot_mapped _ base qModel.context .numerator index (by change index<16;omega)) (by omega)
  have tested:=guard_read (qCleared source base) base divisor contents count qModel
  simp only [eval,if_pos short] at tested
  have guardRun : evaluateHOLFiniteState (qCleared source base) DivMod.guard=
      (some (.returned (RlpWrite.U256Value.tuple (ToWords.words contents))),
        emptyLocalsHOLFinite {(qCleared source base) with clock:=(qCleared source base).clock-1}):=by
    rw [DivMod.guard,evaluateHOLFiniteState_ite,tested]
    simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)]
    exact returned
  have cleared:=quotient_clear_execute source base divisor contents count checked (by omega)
    (.seq DivMod.guard (.seq DivMod.resetIndex (.seq (Clear.loop "r" 8) (Single.afterClearing Single.wideArguments))))
  change evaluateHOLFiniteState source DivMod.afterCounts=_ at cleared
  rw [cleared]
  simp only [evaluateHOLFiniteState_seq_line780,guardRun]
  rfl

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.quotient_clear_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.early_execute

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem restored_empty_clock (saved target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) :
    (restore saved name (emptyLocalsHOLFinite {target with clock:=target.clock-1})).clock=target.clock-1 := rfl

theorem earlyPost_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    (earlyPost source base).clock=source.clock-17 := by
  have clock:=restored_empty_clock source (qCleared source base) "i"
  rw [qCleared_clock] at clock
  exact clock.trans (by omega)

/-- All actual early-guard outcomes spend at most sixteen clear ticks and
one reconstruction call, including a clock exhausted inside either phase. -/
theorem early_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (short : Length.result contents count<2) :
    source.clock-(evaluateHOLFiniteState source DivMod.afterCounts).2.clock≤17 := by
  by_cases enough : 17≤source.clock
  · rw [early_execute source base divisor contents count checked short enough]
    change source.clock-(earlyPost source base).clock≤17
    rw [earlyPost_clock]
    omega
  · omega

/-- A genuine early return derives its own funding and returned quad from
the unchanged guard; the short numerator is reconstructed from physical U. -/
theorem early_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (short : Length.result contents count<2) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source DivMod.afterCounts=(some (.returned returned),post)) :
    17≤source.clock ∧ returned=RlpWrite.U256Value.tuple (ToWords.words contents) ∧ post=earlyPost source base := by
  let model:={source with clock:=17}
  have baseRun:=early_execute model base divisor contents count (checked.withClock 17) short (by rfl)
  have baseClock : (earlyPost model base).clock=0:=by
    rw [earlyPost_clock]
    rfl
  obtain ⟨funded,_,_⟩:=ClockCost.normal_from_zero_clock source (earlyPost model base) post DivMod.afterCounts 17 _ _ baseRun baseClock
    (by intro impossible;cases impossible) normal (by intro impossible;cases impossible)
  have run:=early_execute source base divisor contents count checked short funded
  have same:=normal.symm.trans run
  have returnedEq:=congrArg Prod.fst same
  have valueEq : returned=RlpWrite.U256Value.tuple (ToWords.words contents):=by
    cases returnedEq
    rfl
  exact ⟨funded,valueEq,congrArg Prod.snd same⟩

/-- A current trim of zero or one makes U strictly smaller than the
actual two-digit divisor. Its genuine quotient is zero and remainder is U. -/
theorem short_number (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (short : Length.result contents count<2) :
    number contents count<divisor.toNat ∧ quadNumber (ToWords.words contents)=number contents count := by
  have eight:=checked.eight
  have divisorLarge:=checked.divisorLarge
  have trimmed:=Length.trimmed_number contents count
  have below : number contents count<4294967296:=by
    have alternatives : Length.result contents count=0 ∨ Length.result contents count=1:=by omega
    rcases alternatives with zero|one
    · rw [zero] at trimmed
      change 0=number contents count at trimmed
      omega
    · rw [one] at trimmed
      have digit:=checked.digitsSmall 0 (by omega)
      simp only [number,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add] at trimmed
      omega
  have same : number contents count=number (Single.padded contents 8) count:=by
    apply Single.number_congr
    intro index inside
    by_cases first : index<8
    · simp only [Single.padded,if_pos first]
    · rw [Single.padded,if_neg first]
      exact Length.result_suffix contents count index (by omega) inside
  have reconstructed:=ToWords.words_number contents (by intro index inside;exact checked.digitsSmall index (by omega))
  have width : number contents count=number contents 8:=same.trans (Single.padded_number contents 8 count eight)
  exact ⟨by omega,reconstructed.trans width.symm⟩

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.earlyPost_clock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.early_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.early_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.short_number

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem static_trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first : middle={source with
      locals:=middle.locals,memory:=middle.memory,clock:=middle.clock})
    (second : target={middle with
      locals:=target.locals,memory:=target.memory,clock:=target.clock}) :
    target={source with
      locals:=target.locals,memory:=target.memory,clock:=target.clock} :=
  second.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    {state with
      locals:=target.locals,memory:=target.memory,clock:=target.clock}) first)

private theorem bind_static (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64) :
    bind source name word={source with
      locals:=(bind source name word).locals,memory:=(bind source name word).memory,clock:=(bind source name word).clock} := rfl

private theorem restore_static (saved target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) :
    restore saved name target={target with
      locals:=(restore saved name target).locals,memory:=(restore saved name target).memory,clock:=(restore saved name target).clock} := rfl

private theorem clear_static (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (rounds : Nat) :
    Clear.after source pointer 0 rounds={source with
      locals:=(Clear.after source pointer 0 rounds).locals,
      memory:=(Clear.after source pointer 0 rounds).memory,clock:=(Clear.after source pointer 0 rounds).clock} := by
  have frame:=Clear.after_frame source pointer 0 rounds
  have clock:=clear_clock source pointer 0 rounds
  rw [←clock] at frame
  exact frame

private theorem bind_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word query : BitVec 64) :
    (bind source name word).memory query=source.memory query := rfl

theorem qCleared_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    qCleared source base={source with
      locals:=(qCleared source base).locals,memory:=(qCleared source base).memory,clock:=(qCleared source base).clock} :=
  static_trans source (bind source "i" 0#64) (qCleared source base) (bind_static source "i" 0#64)
    (clear_static (bind source "i" 0#64) (Workspace.pointer base .quotient) 16)

theorem clearedSource_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    clearedSource source base={source with
      locals:=(clearedSource source base).locals,memory:=(clearedSource source base).memory,clock:=(clearedSource source base).clock} :=
  static_trans source (qCleared source base) (clearedSource source base) (qCleared_frame source base)
    (static_trans (qCleared source base) (bind (qCleared source base) "i" 0#64) (clearedSource source base)
      (bind_static (qCleared source base) "i" 0#64)
      (clear_static (bind (qCleared source base) "i" 0#64) (Workspace.pointer base .remainder) 8))

theorem qCleared_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base query : BitVec 64)
    (outside : ∀ index,index<16→query≠slot (Workspace.pointer base .quotient) index) :
    (qCleared source base).memory query=source.memory query := by
  have retained:=Clear.after_away (bind source "i" 0#64) (Workspace.pointer base .quotient) query 16 outside
  simp only [bind_memory] at retained
  exact retained

theorem clearedSource_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base query : BitVec 64)
    (outsideQ : ∀ index,index<16→query≠slot (Workspace.pointer base .quotient) index)
    (outsideR : ∀ index,index<8→query≠slot (Workspace.pointer base .remainder) index) :
    (clearedSource source base).memory query=source.memory query := by
  have retained:=Clear.after_away (bind (qCleared source base) "i" 0#64) (Workspace.pointer base .remainder) query 8 outsideR
  simp only [bind_memory] at retained
  exact retained.trans (qCleared_away source base query outsideQ)

/-- Actual branch-dependent post-scan allowance, before conversion/scans
are combined with the numerator's observed trim. -/
def afterCountsPrice (contents : Nat→BitVec 64) (count : Nat) : Nat :=
  if Length.result contents count<2 then 17 else 40*Length.result contents count-9

theorem after_counts_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count) :
    source.clock-(evaluateHOLFiniteState source DivMod.afterCounts).2.clock≤afterCountsPrice contents count := by
  by_cases short : Length.result contents count<2
  · simpa only [afterCountsPrice,if_pos short] using early_cost source base divisor contents count checked short
  · simpa only [afterCountsPrice,if_neg short] using large_cost source base divisor contents count checked (by omega)

/-- Both real branches retain a complete physical quotient, their actual
returned remainder, all natural arithmetic and the caller's unchanged fields. -/
structure AfterResult (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents quotient : Nat→BitVec 64) (count : Nat) (remainder : Quad) : Prop where
  state : post={source with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}
  quotientImage : Image post (Workspace.pointer base .quotient) quotient 16
  quotientDigits : ∀ index,index<16→(quotient index).toNat<4294967296
  quotientEq : number quotient 16=number contents count/divisor.toNat
  remainderEq : quadNumber remainder=number contents count%divisor.toNat
  small : quadNumber remainder<divisor.toNat
  quotientPadding : ∀ index,count≤index→index<16→quotient index=0#64
  away : ∀ query,(∀ index,index<17→query≠slot (Workspace.pointer base .normalizedNumerator) index)→
    (∀ index,index<8→query≠slot (Workspace.pointer base .normalizedDivisor) index)→
    (∀ index,index<16→query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<8→query≠slot (Workspace.pointer base .remainder) index)→post.memory query=source.memory query
  cost : source.clock-post.clock≤afterCountsPrice contents count

private theorem early_static (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    earlyPost source base={qCleared source base with
      locals:=(earlyPost source base).locals,
      memory:=(earlyPost source base).memory,clock:=(earlyPost source base).clock} := rfl

/-- One actual post-scan return supplies either the real early U result or
the complete cleared/divided/reconstructed result from the same execution. -/
theorem after_counts_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Scanned source base divisor contents count)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source DivMod.afterCounts=(some (.returned returned),post)) :
    ∃ quotient remainder,returned=RlpWrite.U256Value.tuple remainder ∧ AfterResult source post base divisor contents quotient count remainder := by
  have price:=after_counts_cost source base divisor contents count checked
  rw [normal] at price
  by_cases short : Length.result contents count<2
  · obtain ⟨funded,returnedEq,postEq⟩:=early_normal source post base divisor contents count checked short returned normal
    obtain ⟨smaller,reconstructed⟩:=short_number source base divisor contents count checked short
    refine ⟨(fun _=>0#64),ToWords.words contents,returnedEq,⟨?_,?_,?_,?_,?_,?_,?_,?_,price⟩⟩
    · rw [postEq]
      exact static_trans source (qCleared source base) (earlyPost source base) (qCleared_frame source base) (early_static source base)
    · rw [postEq]
      exact Clear.after_image (bind source "i" 0#64) (Workspace.pointer base .quotient) 16
    · intro index inside
      decide
    · rw [Nat.div_eq_of_lt smaller]
      simp [number]
    · rw [reconstructed,Nat.mod_eq_of_lt smaller]
    · rw [reconstructed]
      exact smaller
    · intro index lower upper
      rfl
    · intro query outsideU outsideV outsideQ outsideR
      rw [postEq]
      exact qCleared_away source base query outsideQ
  · obtain ⟨inner,quotient,remainder,funded,returnedEq,result,restored,paid⟩:=large_normal source post base divisor contents count checked (by omega) returned normal
    refine ⟨quotient,remainder,returnedEq,⟨?_,?_,result.quotientDigits,result.quotientEq,result.remainderEq,result.small,?_,?_,price⟩⟩
    · exact static_trans source (clearedSource source base) post (clearedSource_frame source base)
        (static_trans (clearedSource source base) inner post result.state (by rw [restored];exact restore_static source inner "i"))
    · rw [restored]
      exact result.quotientImage
    · exact result.quotient_padding checked.cleared (cleared_qzeros source base)
    · intro query outsideU outsideV outsideQ outsideR
      rw [restored]
      have bound:=Length.result_bound contents count
      have small:=checked.small
      have retained:=result.away query
        (by intro index inside;exact outsideU index (by omega))
        (by intro index inside;exact outsideV index (by omega))
        (by intro index inside;exact outsideQ index (by omega))
        (by intro index inside;exact outsideR index (by omega))
      exact retained.trans (clearedSource_away source base query outsideQ outsideR)

/-- The actual scan counts and actual trimmed width share one numerator,
so their coupled bound avoids charging both worst cases independently. -/
def wholePrice (contents : Nat→BitVec 64) (count : Nat) : Nat :=
  prefixPrice contents count+afterCountsPrice contents count

theorem wholePrice_upper (contents : Nat→BitVec 64) (count : Nat) (positive : 0<count) :
    wholePrice contents count≤40*count+2 := by
  have coupled:=Length.scans_result_bound contents count
  have bounded:=Length.result_bound contents count
  by_cases short : Length.result contents count<2
  · simp only [wholePrice,prefixPrice,afterCountsPrice,if_pos short]
    omega
  · simp only [wholePrice,prefixPrice,afterCountsPrice,if_neg short]
    omega

/-- Original conversion, both real scans and either actual post-scan branch
are bounded together on every outcome, including all insufficient clocks. -/
theorem setup_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Prepared source base divisor contents count) :
    source.clock-(evaluateHOLFiniteState source DivMod.setupDivisor).2.clock≤wholePrice contents count := by
  by_cases enough : prefixPrice contents count≤source.clock
  · obtain ⟨ready,actual⟩:=prefix_execute source base divisor contents count checked enough DivMod.afterCounts
    rw [literal_setup,actual]
    change source.clock-(evaluateHOLFiniteState (scannedSource source base divisor contents count) DivMod.afterCounts).2.clock≤wholePrice contents count
    have price:=after_counts_cost (scannedSource source base divisor contents count) base divisor contents count ready
    have forward:=evaluateHOLFiniteState_clock_le (scannedSource source base divisor contents count) DivMod.afterCounts
    have clock:=scannedSource_clock source base divisor contents count
    unfold wholePrice
    omega
  · unfold wholePrice
    omega

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.qCleared_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.clearedSource_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.qCleared_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.clearedSource_away
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.after_counts_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.after_counts_normal
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.wholePrice_upper
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.setup_cost

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem scannedSource_static (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) :
    scannedSource source base divisor contents count={source with
      locals:=(scannedSource source base divisor contents count).locals,
      memory:=(scannedSource source base divisor contents count).memory,clock:=(scannedSource source base divisor contents count).clock} := rfl

private theorem prefixRestored_static (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) :
    prefixRestored source target base divisor={target with
      locals:=(prefixRestored source target base divisor).locals,
      memory:=(prefixRestored source target base divisor).memory,clock:=(prefixRestored source target base divisor).clock} := rfl

/-- Physical result of the complete unchanged digits_divmod setup/body:
all arrays are real output cells and the returned quad is the true U%D. -/
structure Result (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents quotient : Nat→BitVec 64) (count : Nat) (remainder : Quad) : Prop where
  state : post={source with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}
  quotientImage : Image post (Workspace.pointer base .quotient) quotient 16
  quotientDigits : ∀ index,index<16→(quotient index).toNat<4294967296
  quotientEq : number quotient 16=number contents count/divisor.toNat
  remainderEq : quadNumber remainder=number contents count%divisor.toNat
  small : quadNumber remainder<divisor.toNat
  quotientPadding : ∀ index,count≤index→index<16→quotient index=0#64
  away : ∀ query,(∀ index,index<17→query≠slot (Workspace.pointer base .normalizedNumerator) index)→
    (∀ index,index<8→query≠slot (Workspace.pointer base .normalizedDivisor) index)→
    (∀ index,index<16→query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<8→query≠slot (Workspace.pointer base .remainder) index)→
    (∀ index,index<8→query≠slot (Workspace.pointer base .divisor) index)→post.memory query=source.memory query
  cost : source.clock-post.clock≤wholePrice contents count

/-- The same actual returned setup derives both scan results, takes the
real branch and restores its actual n/mm declarations around the result. -/
theorem setup_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Prepared source base divisor contents count)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source DivMod.setupDivisor=(some (.returned returned),post)) :
    ∃ quotient remainder,returned=RlpWrite.U256Value.tuple remainder ∧ Result source post base divisor contents quotient count remainder := by
  have modeled : evaluateHOLFiniteState source (setup DivMod.afterCounts)=(some (.returned returned),post):=by
    rw [←literal_setup]
    exact normal
  obtain ⟨inner,funded,ready,tailRun,restored⟩:=prefix_normal source post base divisor contents count checked DivMod.afterCounts (some (.returned returned)) modeled
    (by intro impossible;cases impossible)
  obtain ⟨quotient,remainder,returnedEq,result⟩:=after_counts_normal (scannedSource source base divisor contents count) inner base divisor contents count ready returned tailRun
  have price:=setup_cost source base divisor contents count checked
  rw [normal] at price
  refine ⟨quotient,remainder,returnedEq,⟨?_,?_,result.quotientDigits,result.quotientEq,result.remainderEq,result.small,result.quotientPadding,?_,price⟩⟩
  · exact static_trans source (scannedSource source base divisor contents count) post (scannedSource_static source base divisor contents count)
      (static_trans (scannedSource source base divisor contents count) inner post result.state
        (by rw [restored];exact prefixRestored_static source inner base divisor))
  · rw [restored]
    exact result.quotientImage
  · intro query outsideU outsideV outsideQ outsideR outsideD
    rw [restored]
    have retained:=result.away query outsideU outsideV outsideQ outsideR
    exact retained.trans (ToDigits.caller_away source (Workspace.pointer base .divisor) query (Single.remainderWords divisor) outsideD)

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.setup_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual function entry before the original q/r/v declarations. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  eight : 8≤count
  small : count≤16
  u : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator)))
  m : source.locals.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count)))
  d : source.locals.lookup (ofString "d")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor))
  image : Image source (Workspace.pointer base .numerator) contents count
  divisorLarge : 4294967296≤divisor.toNat
  digitsSmall : ∀ index,index<count→(contents index).toNat<2^32

theorem Entry.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Entry source base divisor contents count) (clock : Nat) :
    Entry {source with clock:=clock} base divisor contents count :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
    checked.eight,checked.small,checked.u,checked.m,checked.d,checked.image,checked.divisorLarge,checked.digitsSmall⟩

theorem Entry.bindPointer {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Entry source base divisor contents count)
    (name : String) (word : BitVec 64) (allowed : name="q" ∨ name="r" ∨ name="v") :
    Entry (bind source name word) base divisor contents count := by
  rcases allowed with rfl|rfl|rfl <;>
    refine ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
      checked.eight,checked.small,?_,?_,?_,checked.image,checked.divisorLarge,checked.digitsSmall⟩ <;>
    first
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.u
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.m
    | exact (bind_lookup_other _ _ _ _ (by decide)).trans checked.d

def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :=
  bind (bind (bind source "q" (Workspace.pointer base .quotient)) "r" (Workspace.pointer base .remainder)) "v" (Workspace.pointer base .divisor)

def restored (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :=
  restore source "q" (restore (bind source "q" (Workspace.pointer base .quotient)) "r"
    (restore (bind (bind source "q" (Workspace.pointer base .quotient)) "r" (Workspace.pointer base .remainder)) "v" target))

theorem Entry.prepared {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents : Nat→BitVec 64} {count : Nat} (checked : Entry source base divisor contents count) :
    Prepared (prepared source base) base divisor contents count := by
  let qEntry:=bind source "q" (Workspace.pointer base .quotient)
  have qModel : Entry qEntry base divisor contents count:=checked.bindPointer "q" _ (Or.inl rfl)
  let rEntry:=bind qEntry "r" (Workspace.pointer base .remainder)
  have rModel : Entry rEntry base divisor contents count:=qModel.bindPointer "r" _ (Or.inr (Or.inl rfl))
  let vEntry:=bind rEntry "v" (Workspace.pointer base .divisor)
  have vModel : Entry vEntry base divisor contents count:=rModel.bindPointer "v" _ (Or.inr (Or.inr rfl))
  have qCell : vEntry.locals.lookup (ofString "q")=some (.val (.word (Workspace.pointer base .quotient))):=
    (bind_lookup_other _ "v" "q" _ (by decide)).trans
      ((bind_lookup_other _ "r" "q" _ (by decide)).trans (bind_lookup_same _ _ _))
  have rCell : vEntry.locals.lookup (ofString "r")=some (.val (.word (Workspace.pointer base .remainder))):=
    (bind_lookup_other _ "v" "r" _ (by decide)).trans (bind_lookup_same _ _ _)
  exact ⟨vModel.context,vModel.installed,vModel.eight,vModel.small,qCell,rCell,vModel.u,bind_lookup_same _ _ _,
    vModel.m,vModel.d,vModel.image,vModel.divisorLarge,vModel.digitsSmall⟩

/-- Original pointer declarations resume the actual setup on every outcome,
including failures and exhaustion, with their true lexical restorations. -/
theorem preamble_execute (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Entry source base divisor contents count)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (prepared source base) DivMod.setupDivisor=(result,target)) :
    evaluateHOLFiniteState source DivMod.body=(result,restored source target base) := by
  let qEntry:=bind source "q" (Workspace.pointer base .quotient)
  have qModel : Entry qEntry base divisor contents count:=checked.bindPointer "q" _ (Or.inl rfl)
  let rEntry:=bind qEntry "r" (Workspace.pointer base .remainder)
  have rModel : Entry rEntry base divisor contents count:=qModel.bindPointer "r" _ (Or.inr (Or.inl rfl))
  have vRun:=ScalarScope.declare_execute rEntry target "v" (DivMod.workspaceAddress .divisor) (Workspace.pointer base .divisor)
    DivMod.setupDivisor result (DivMod.workspace_read rEntry base rModel.context .divisor) run
  have rRun:=ScalarScope.declare_execute qEntry (restore rEntry "v" target) "r" (DivMod.workspaceAddress .remainder) (Workspace.pointer base .remainder)
    (.dec (ofString "v") .one (DivMod.workspaceAddress .divisor) DivMod.setupDivisor) result (DivMod.workspace_read qEntry base qModel.context .remainder) vRun
  have qRun:=ScalarScope.declare_execute source (restore qEntry "r" (restore rEntry "v" target)) "q" (DivMod.workspaceAddress .quotient) (Workspace.pointer base .quotient)
    (.dec (ofString "r") .one (DivMod.workspaceAddress .remainder) (.dec (ofString "v") .one (DivMod.workspaceAddress .divisor) DivMod.setupDivisor)) result
    (DivMod.workspace_read source base checked.context .quotient) rRun
  rw [DivMod.body_shape]
  exact qRun

/-- The complete unchanged digits_divmod body at genuine two-digit divisor
entries costs at most40*count+2source ticks (322at8,642at16). -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Entry source base divisor contents count) :
    source.clock-(evaluateHOLFiniteState source DivMod.body).2.clock≤wholePrice contents count := by
  let output:=evaluateHOLFiniteState (prepared source base) DivMod.setupDivisor
  have actual:=preamble_execute source output.2 base divisor contents count checked output.1 rfl
  have price:=setup_cost (prepared source base) base divisor contents count checked.prepared
  rw [actual]
  exact price

private theorem prepared_static (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    prepared source base={source with
      locals:=(prepared source base).locals,memory:=(prepared source base).memory,clock:=(prepared source base).clock} := rfl

private theorem restored_static (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    restored source target base={target with
      locals:=(restored source target base).locals,
      memory:=(restored source target base).memory,clock:=(restored source target base).clock} := rfl

/-- A genuine body return exposes its actual physical quotient/remainder
and the fully restored original function state; no future call is supplied. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Entry source base divisor contents count)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source DivMod.body=(some (.returned returned),post)) :
    ∃ quotient remainder,returned=RlpWrite.U256Value.tuple remainder ∧ Result source post base divisor contents quotient count remainder := by
  let output:=evaluateHOLFiniteState (prepared source base) DivMod.setupDivisor
  have actual:=preamble_execute source output.2 base divisor contents count checked output.1 rfl
  have observed : output.1=some (.returned returned):=congrArg Prod.fst (actual.symm.trans normal)
  have run : evaluateHOLFiniteState (prepared source base) DivMod.setupDivisor=(some (.returned returned),output.2):=Prod.ext observed rfl
  obtain ⟨quotient,remainder,returnedEq,result⟩:=setup_normal (prepared source base) output.2 base divisor contents count checked.prepared returned run
  have endpoint : post=restored source output.2 base:=congrArg Prod.snd (normal.symm.trans actual)
  have price:=body_cost source base divisor contents count checked
  rw [normal] at price
  refine ⟨quotient,remainder,returnedEq,⟨?_,?_,result.quotientDigits,result.quotientEq,result.remainderEq,result.small,result.quotientPadding,?_,price⟩⟩
  · exact static_trans source (prepared source base) post (prepared_static source base)
      (static_trans (prepared source base) output.2 post result.state (by rw [endpoint];exact restored_static source output.2 base))
  · rw [endpoint]
    exact result.quotientImage
  · intro query outsideU outsideV outsideQ outsideR outsideD
    rw [endpoint]
    exact result.away query outsideU outsideV outsideQ outsideR outsideD

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.Entry.withClock
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.Entry.bindPointer
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.Entry.prepared
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.preamble_execute
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.body_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.body_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Caller-side physical input requirements, independent of callee locals
and without a future successful child execution or funding requirement. -/
structure Buffers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) : Prop where
  context : Workspace.Context source base
  installed : OriginalCode.Installed source.code
  eight : 8≤count
  small : count≤16
  image : Image source (Workspace.pointer base .numerator) contents count
  divisorLarge : 4294967296≤divisor.toNat
  digitsSmall : ∀ index,index<count→(contents index).toNat<2^32

private theorem callee_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Buffers source base divisor contents count)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (u : callee.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))))
    (m : callee.lookup (ofString "m")=some (.val (.word (BitVec.ofNat 64 count))))
    (d : callee.lookup (ofString "d")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor))) :
    Entry (callEntryStateHOLFinite source callee) base divisor contents count :=
  ⟨⟨checked.context.global,checked.context.domain,checked.context.arena,checked.context.aligned⟩,checked.installed,
    checked.eight,checked.small,u,m,d,checked.image,checked.divisorLarge,checked.digitsSmall⟩

/-- The genuine mixed scalar/quad ABI connects every ordinary call form to
the full unchanged body. The uniform price is at most40*count+3. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Buffers source base divisor contents count)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (DivMod.values (Workspace.pointer base .numerator) count divisor)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "digits_divmod") arguments)).2.clock≤wholePrice contents count+1 := by
  obtain ⟨callee,called,u,m,d⟩:=DivMod.environment source.code.lookup (Workspace.pointer base .numerator) count divisor
    (DivMod.original_code source.code checked.installed)
  have actual:=callee_entry source base divisor contents count checked callee u m d
  exact ClockCost.call_current source destination (ofString "digits_divmod") arguments _ DivMod.body callee RlpWrite.U256Value.tupleShape
    (wholePrice contents count) args called (body_cost (callEntryStateHOLFinite source callee) base divisor contents count actual)

/-- A real returned scoped child derives its physical result and the exact
caller continuation entry at its actual remaining clock, which can vary. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (checked : Buffers source base divisor contents count) (name : String)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "digits_divmod") (DivMod.values (Workspace.pointer base .numerator) count divisor)=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    ∃ quotient remainder,returned=RlpWrite.U256Value.tuple remainder ∧
      Result (callEntryStateHOLFinite source callee) target base divisor contents quotient count remainder ∧
      CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple remainder) {source with memory:=target.memory,clock:=target.clock} := by
  obtain ⟨expected,lookup,u,m,d⟩:=DivMod.environment source.code.lookup (Workspace.pointer base .numerator) count divisor
    (DivMod.original_code source.code checked.installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=DivMod.body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at u m d
  rw [bodyEq] at run
  have entry:=callee_entry source base divisor contents count checked callee u m d
  obtain ⟨quotient,remainder,returnedEq,result⟩:=body_normal (callEntryStateHOLFinite source callee) target base divisor contents count entry returned run
  refine ⟨quotient,remainder,returnedEq,result,?_⟩
  have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
      locals:=source.locals}) result.state
  change {target with
      locals:=source.locals}={source with memory:=target.memory,clock:=target.clock} at frame
  rw [CallNormal.continuationEntry,returnedEq,frame]

/-- Reading the actual eight-digit quotient output gives the full natural
quotient when the original numerator width is eight; higher cells are zero. -/
theorem Result.quotient_number {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base divisor : BitVec 64}
    {contents quotient : Nat→BitVec 64} {count : Nat} {remainder : Quad}
    (result : Result source post base divisor contents quotient count remainder) (small : count≤8) :
    quadNumber (ToWords.words quotient)=number contents count/divisor.toNat := by
  have same : number quotient 16=number (Single.padded quotient 8) 16:=by
    apply Single.number_congr
    intro index inside
    by_cases before : index<8
    · simp only [Single.padded,if_pos before]
    · rw [Single.padded,if_neg before]
      exact result.quotientPadding index (by omega) inside
  have width : number quotient 16=number quotient 8:=same.trans (Single.padded_number quotient 8 16 (by decide))
  exact (ToWords.words_number quotient (by intro index inside;exact result.quotientDigits index (by omega))).trans (width.symm.trans result.quotientEq)

end InitECandidate.Solver.Input.UDivMod.WideDigits.Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.call_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.resume
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.Double.Result.quotient_number

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Invert an actual returned scoped call, deriving its own call funding,
real child return, shape checks and genuine continued caller execution. -/
theorem scoped_returned {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)=(some (.returned value),post)) :
    1≤source.clock ∧ ∃ target returned inner,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target) ∧
      (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true ∧
      evaluateHOLFiniteState (continuationEntry source target name returned) continuation=(some (.returned value),inner) ∧
      post=restore source name inner := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at normal
  simp only [args,called] at normal
  by_cases zero : source.clock=0
  · rw [if_pos zero] at normal
    cases normal
  · rw [if_neg zero] at normal
    generalize bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at normal
    obtain ⟨result,target⟩:=output
    cases result with
    | none=>cases normal
    | some result=>
      cases result with
      | returned returned=>
        simp only at normal
        split at normal
        · rename_i valid
          have resultEq:=congrArg Prod.fst normal
          have postEq:=congrArg Prod.snd normal
          exact ⟨by omega,target,returned,(evaluateHOLFiniteState (continuationEntry source target name returned) continuation).2,
            rfl,valid,Prod.ext resultEq rfl,postEq.symm⟩
        · cases normal
      | error=>cases normal
      | timeOut=>cases normal
      | «break»=>cases normal
      | «continue»=>cases normal
      | exception identifier payload=>cases normal
      | finalFfi event=>cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.scoped_returned

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_division_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code U256.afterDivision 1 :=
  ToWords.call_cost code installed "q" U256.quotientArguments U256.finish 0 (ClockCost.returned code _)

/-- The original numerator conversion, genuine two-digit scoped division
and quotient reconstruction together cost at most325source ticks. -/
theorem slow_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (uLocal : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))))
    (divisorLarge : 4294967296≤divisor.toNat) :
    source.clock-(evaluateHOLFiniteState source U256.slowTail).2.clock≤Double.wholePrice (digit a) 8+3 := by
  by_cases funded : 1≤source.clock
  · let converted:=ToDigits.callerPost source (Workspace.pointer base .numerator) a
    have convertArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) U256.numeratorArguments=
        some [.val (.word (Workspace.pointer base .numerator)),RlpWrite.U256Value.tuple a]:=by
      simp [U256.numeratorArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,uLocal,aLocal]
    have convertedRun:=ToDigits.call_execute source (Workspace.pointer base .numerator) a U256.numeratorArguments installed convertArgs
      (by intro index inside;exact Workspace.slot_mapped source base context .numerator index (by change index<16;omega)) funded
    have convertedContext : Workspace.Context converted base:=⟨context.global,context.domain,context.arena,context.aligned⟩
    have checked : Double.Buffers converted base divisor (digit a) 8:=
      ⟨convertedContext,installed,by decide,by decide,ToDigits.caller_image source _ a,divisorLarge,digit_small a⟩
    have divisionArgs : evalListHOLFinite converted (h:=fun query=>Classical.propDecidable (converted.memaddrs query)) U256.divisionArguments=
        some (DivMod.values (Workspace.pointer base .numerator) 8 divisor):=by
      have u : converted.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))):=uLocal
      have b : converted.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)):=bLocal
      simp [U256.divisionArguments,DivMod.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,u,b]
    obtain ⟨callee,called,u,m,d⟩:=DivMod.environment converted.code.lookup (Workspace.pointer base .numerator) 8 divisor
      (DivMod.original_code converted.code installed)
    have entry:=Double.callee_entry converted base divisor (digit a) 8 checked callee u m d
    have tailPrice:=ClockCost.scoped_current converted (ofString "r") RlpWrite.U256Value.tupleShape (ofString "digits_divmod") U256.divisionArguments _
      DivMod.body U256.afterDivision callee RlpWrite.U256Value.tupleShape (Double.wholePrice (digit a) 8) 1 divisionArgs called
      (Double.body_cost (callEntryStateHOLFinite converted callee) base divisor (digit a) 8 entry) (after_division_cost converted.code installed)
    have forward:=evaluateHOLFiniteState_clock_le converted (.decCall (ofString "r") RlpWrite.U256Value.tupleShape (ofString "digits_divmod") U256.divisionArguments U256.afterDivision)
    have clock : converted.clock=source.clock-1:=rfl
    rw [U256.slowTail,evaluateHOLFiniteState_seq_line780,convertedRun]
    change source.clock-(evaluateHOLFiniteState converted (.decCall (ofString "r") RlpWrite.U256Value.tupleShape (ofString "digits_divmod") U256.divisionArguments U256.afterDivision)).2.clock≤Double.wholePrice (digit a) 8+3
    omega
  · omega

structure Result (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (a : Quad)
    (divisor : BitVec 64) (quotient remainder : Quad) (price : Nat:=Double.wholePrice (digit a) 8+3) : Prop where
  state : post={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}
  quotientEq : quadNumber quotient=quadNumber a/divisor.toNat
  remainderEq : quadNumber remainder=quadNumber a%divisor.toNat
  small : quadNumber remainder<divisor.toNat
  away : ∀ query,(∀ index,index<17→query≠slot (Workspace.pointer base .normalizedNumerator) index)→
    (∀ index,index<8→query≠slot (Workspace.pointer base .normalizedDivisor) index)→
    (∀ index,index<16→query≠slot (Workspace.pointer base .quotient) index)→
    (∀ index,index<8→query≠slot (Workspace.pointer base .remainder) index)→
    (∀ index,index<8→query≠slot (Workspace.pointer base .divisor) index)→
    (∀ index,index<8→query≠slot (Workspace.pointer base .numerator) index)→post.memory query=source.memory query
  cost : source.clock-post.clock≤price

/-- The real returned wide tail derives its conversion, actual division,
physical quotient read and eight-word return through both scoped calls. -/
theorem slow_tail_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (uLocal : source.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))))
    (divisorLarge : 4294967296≤divisor.toNat) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source U256.slowTail=(some (.returned returned),post)) :
    ∃ quotient remainder,returned=U256.pairValue quotient remainder ∧ Result source post base a divisor quotient remainder := by
  have convertArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) U256.numeratorArguments=
      some [.val (.word (Workspace.pointer base .numerator)),RlpWrite.U256Value.tuple a]:=by
    simp [U256.numeratorArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,uLocal,aLocal]
  have safe : LocalPrefix (ofString "unused") (.call (some (none,none)) (ofString "u256_to_digits") U256.numeratorArguments):=
    .call none (ofString "u256_to_digits") U256.numeratorArguments (by intro name impossible;cases impossible)
  have modeled : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "u256_to_digits") U256.numeratorArguments)
      (.decCall (ofString "r") RlpWrite.U256Value.tupleShape (ofString "digits_divmod") U256.divisionArguments U256.afterDivision))=(some (.returned returned),post):=normal
  obtain ⟨middle,convertRun,divisionRun⟩:=sequence_returned source post _ _ returned (safe.summary_full source).2.1 modeled
  obtain ⟨convertFunded,middleEq⟩:=ToDigits.call_normal source middle (Workspace.pointer base .numerator) a U256.numeratorArguments installed convertArgs
    (by intro index inside;exact Workspace.slot_mapped source base context .numerator index (by change index<16;omega)) convertRun
  subst middle
  let converted:=ToDigits.callerPost source (Workspace.pointer base .numerator) a
  have convertedContext : Workspace.Context converted base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  have checked : Double.Buffers converted base divisor (digit a) 8:=
    ⟨convertedContext,installed,by decide,by decide,ToDigits.caller_image source _ a,divisorLarge,digit_small a⟩
  have divisionArgs : evalListHOLFinite converted (h:=fun query=>Classical.propDecidable (converted.memaddrs query)) U256.divisionArguments=
      some (DivMod.values (Workspace.pointer base .numerator) 8 divisor):=by
    have u : converted.locals.lookup (ofString "u")=some (.val (.word (Workspace.pointer base .numerator))):=uLocal
    have b : converted.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)):=bLocal
    simp [U256.divisionArguments,DivMod.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,u,b]
  obtain ⟨callee,called,u,m,d⟩:=DivMod.environment converted.code.lookup (Workspace.pointer base .numerator) 8 divisor
    (DivMod.original_code converted.code installed)
  obtain ⟨divisionFunded,child,childValue,divisionInner,childRun,valid,quotientRun,postEq⟩:=CallNormal.scoped_returned converted post "r"
    RlpWrite.U256Value.tupleShape (ofString "digits_divmod") U256.divisionArguments _ DivMod.body U256.afterDivision callee RlpWrite.U256Value.tupleShape
    divisionArgs called returned divisionRun
  obtain ⟨quotient,remainder,childValueEq,division,entryEq⟩:=Double.resume converted child base divisor (digit a) 8 checked "r" DivMod.body callee
    RlpWrite.U256Value.tupleShape called childValue childRun
  let rEntry:=CallNormal.continuationEntry converted child "r" childValue
  have rEntryEq : rEntry=setVarHOLFinite (ofString "r") (RlpWrite.U256Value.tuple remainder) {converted with memory:=child.memory,clock:=child.clock}:=entryEq
  have rContext : Workspace.Context rEntry base:=by
    refine ⟨?_,?_,context.arena,context.aligned⟩
    · rw [rEntryEq]
      exact context.global
    · rw [rEntryEq]
      exact context.domain
  have rCode : OriginalCode.Installed rEntry.code:=by rw [rEntryEq];exact installed
  have rCell : rEntry.locals.lookup (ofString "r")=some (RlpWrite.U256Value.tuple remainder):=by
    rw [rEntryEq]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have quotientArgs : evalListHOLFinite rEntry (h:=fun query=>Classical.propDecidable (rEntry.memaddrs query)) U256.quotientArguments=
      some [.val (.word (Workspace.pointer base .quotient))]:=by
    have address:=DivMod.workspace_read rEntry base rContext .quotient
    simp only [eval] at address
    simpa only [U256.quotientArguments,evalListHOLFinite,evalListHOLExact,address] using
      (show some [.val (.word (Workspace.pointer base .quotient))]=some [.val (.word (Workspace.pointer base .quotient))] from rfl)
  obtain ⟨qCallee,qCalled,p⟩:=ToWords.environment rEntry.code.lookup (Workspace.pointer base .quotient) (ToWords.original_code rEntry.code rCode)
  obtain ⟨qFunded,qChild,qValue,finishInner,qRun,qValid,finishRun,divisionEq⟩:=CallNormal.scoped_returned rEntry divisionInner "q"
    RlpWrite.U256Value.tupleShape (ofString "digits_to_u256") U256.quotientArguments _ ToWords.body U256.finish qCallee RlpWrite.U256Value.tupleShape
    quotientArgs qCalled returned quotientRun
  have qImage : Image rEntry (Workspace.pointer base .quotient) quotient 8:=by
    intro index inside
    rw [rEntryEq]
    exact division.quotientImage index (by omega)
  have qExpected:=ToWords.execute (callEntryStateHOLFinite rEntry qCallee) (Workspace.pointer base .quotient) quotient p qImage
    (by intro index inside;exact Workspace.slot_mapped rEntry base rContext .quotient index (by change index<16;omega))
  have qChildEq : qChild=emptyLocalsHOLFinite (callEntryStateHOLFinite rEntry qCallee):=congrArg Prod.snd (qRun.symm.trans qExpected)
  have qValueEq : qValue=RlpWrite.U256Value.tuple (ToWords.words quotient):=by
    have value:=congrArg Prod.fst (qRun.symm.trans qExpected)
    cases value
    rfl
  let qWords:=ToWords.words quotient
  let qReady:=setVarHOLFinite (ofString "q") (RlpWrite.U256Value.tuple qWords) {rEntry with clock:=rEntry.clock-1}
  have qEntryEq : CallNormal.continuationEntry rEntry qChild "q" qValue=qReady:=by
    rw [qChildEq,qValueEq]
    rfl
  rw [qEntryEq] at finishRun
  have qCell : qReady.locals.lookup (ofString "q")=some (RlpWrite.U256Value.tuple qWords):=by
    simp [qReady,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have retainedR : qReady.locals.lookup (ofString "r")=some (RlpWrite.U256Value.tuple remainder):=by
    simp [qReady,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,show ofString "q"≠ofString "r" by decide,
      show ofString "r"≠ofString "q" by decide,rCell]
  have finished:=U256.finish_execute qReady qWords remainder qCell retainedR
  have returnedEq : returned=U256.pairValue qWords remainder:=by
    have value:=congrArg Prod.fst (finishRun.symm.trans finished)
    cases value
    rfl
  have finishEq : finishInner=emptyLocalsHOLFinite qReady:=congrArg Prod.snd (finishRun.symm.trans finished)
  have rFrame : rEntry={converted with
      locals:=rEntry.locals,memory:=rEntry.memory,clock:=rEntry.clock}:=by rw [rEntryEq];rfl
  have postFrame : post={rEntry with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by
    rw [postEq,divisionEq,finishEq]
    rfl
  have convertedFrame : converted={source with
      locals:=converted.locals,memory:=converted.memory,clock:=converted.clock}:=rfl
  have postMemory : post.memory=child.memory:=by
    rw [postEq,divisionEq,finishEq]
    change rEntry.memory=child.memory
    rw [rEntryEq]
    rfl
  have quotientEq:=division.quotient_number (by decide : 8≤8)
  rw [digits_number] at quotientEq
  have remainderEq:=division.remainderEq
  rw [digits_number] at remainderEq
  have price:=slow_tail_cost source base divisor a context installed aLocal bLocal uLocal divisorLarge
  rw [normal] at price
  refine ⟨qWords,remainder,returnedEq,⟨Double.static_trans source converted post convertedFrame
    (Double.static_trans converted rEntry post rFrame postFrame),quotientEq,remainderEq,division.small,?_,price⟩⟩
  intro query outsideUN outsideVN outsideQ outsideR outsideV outsideU
  rw [postMemory]
  exact (division.away query outsideUN outsideVN outsideQ outsideR outsideV).trans
    (ToDigits.caller_away source (Workspace.pointer base .numerator) query a outsideU)

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256Double.after_division_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256Double.slow_tail_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256Double.slow_tail_normal

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256Double
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Include the genuine numerator-pointer declaration of the unchanged
wide u256 division branch, covering every stopped or short-clock outcome. -/
theorem slow_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorLarge : 4294967296≤divisor.toNat) :
    source.clock-(evaluateHOLFiniteState source U256.slowBranch).2.clock≤Double.wholePrice (digit a) 8+3 := by
  let ready:=bind source "u" (Workspace.pointer base .numerator)
  have readyContext : Workspace.Context ready base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  exact ClockCost.declared_current source "u" (DivMod.workspaceAddress .numerator) (Workspace.pointer base .numerator) U256.slowTail _
    (DivMod.workspace_read source base context .numerator)
    (slow_tail_cost ready base divisor a readyContext installed
      ((bind_lookup_other source "u" "a" _ (by decide)).trans aLocal)
      ((bind_lookup_other source "u" "b" _ (by decide)).trans bLocal) (bind_lookup_same _ _ _) divisorLarge)

/-- Its actual normal return restores the original u binding and retains
both natural arithmetic results and the full protected-memory contract. -/
theorem slow_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorLarge : 4294967296≤divisor.toNat) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source U256.slowBranch=(some (.returned returned),post)) :
    ∃ quotient remainder,returned=U256.pairValue quotient remainder ∧ Result source post base a divisor quotient remainder := by
  let ready:=bind source "u" (Workspace.pointer base .numerator)
  have readyContext : Workspace.Context ready base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  obtain ⟨inner,run,endpoint⟩:=ScalarScope.declare_trace source post "u" (DivMod.workspaceAddress .numerator) (Workspace.pointer base .numerator)
    U256.slowTail (some (.returned returned)) (DivMod.workspace_read source base context .numerator) normal
  obtain ⟨quotient,remainder,returnedEq,result⟩:=slow_tail_normal ready inner base divisor a readyContext installed
    ((bind_lookup_other source "u" "a" _ (by decide)).trans aLocal)
    ((bind_lookup_other source "u" "b" _ (by decide)).trans bLocal) (bind_lookup_same _ _ _) divisorLarge returned run
  have price:=slow_cost source base divisor a context installed aLocal bLocal divisorLarge
  rw [normal] at price
  refine ⟨quotient,remainder,returnedEq,⟨?_,result.quotientEq,result.remainderEq,result.small,?_,price⟩⟩
  · exact Double.static_trans source ready post (Double.bind_static source "u" (Workspace.pointer base .numerator))
      (Double.static_trans ready inner post result.state (by rw [endpoint];exact Double.restore_static source inner "u"))
  · intro query outsideUN outsideVN outsideQ outsideR outsideV outsideU
    rw [endpoint]
    exact result.away query outsideUN outsideVN outsideQ outsideR outsideV outsideU

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256Double

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256Double.slow_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256Double.slow_normal
