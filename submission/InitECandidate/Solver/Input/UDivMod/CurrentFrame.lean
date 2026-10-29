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

theorem scalar_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (divisorSmall : divisor.toNat<2^32) (positive : 0<divisor.toNat) (upper : upperZero a)
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

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256

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
