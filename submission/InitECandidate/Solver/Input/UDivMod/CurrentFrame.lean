import Flapjack.Pancake.Semantics.PanSem.ClockTimeout
import InitECandidate.Solver.WitnessRadix.RestoreLookup
import InitECandidate.Solver.Input.LoadWord
import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.Input.WordTupleFour
import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.WitnessRadix.AllocatedArena
import InitECandidate.Solver.Input.UDivMod.CurrentCost
import InitECandidate.Solver.Input.LocalEffectsCurrentScoped

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

def number (contents : Nat→BitVec 64) : Nat→Nat
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

theorem number_zero (contents : Nat→BitVec 64) (count : Nat) (zero : ∀ index,index<count→contents index=0#64) :
    number contents count=0 := by
  induction count with
  | zero=>rfl
  | succ count ih=>
    rw [number,ih (by intro index inside;exact zero index (by omega)),zero count (by omega)]
    simp

def slot (pointer : BitVec 64) (index : Nat) : BitVec 64:=pointer+BitVec.ofNat 64 (8*index)
def Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (count : Nat) : Prop:=
  ∀ index,index<count→source.memory (slot pointer index)=.word (contents index)

theorem slot_injective (pointer : BitVec 64) (left right : Nat) (leftSmall : left<16) (rightSmall : right<16)
    (same : slot pointer left=slot pointer right) : left=right := by
  have equal : (BitVec.ofNat 64 (8*left))=(BitVec.ofNat 64 (8*right)):=
    (BitVec.add_right_inj pointer).mp same
  have native:=congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at native
  omega

def writeMemory (memory : BitVec 64→HolWordLab 64) (pointer : BitVec 64) (contents : Nat→BitVec 64) : Nat→BitVec 64→HolWordLab 64
  | 0=>memory
  | count+1=>StoreWord.put (writeMemory memory pointer contents count) (slot pointer count) (contents count)
def written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (count : Nat) :=
  {source with memory:=writeMemory source.memory pointer contents count}

theorem written_image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64)
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

theorem written_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (contents : Nat→BitVec 64)
    (count : Nat) (away : ∀ index,index<count→query≠slot pointer index) :
    (written source pointer contents count).memory query=source.memory query := by
  change writeMemory source.memory pointer contents count query=source.memory query
  induction count with
  | zero=>rfl
  | succ count ih=>
    simp only [writeMemory,StoreWord.put,if_neg (away count (by omega))]
    exact ih (by intro index inside;exact away index (by omega))

theorem mapped_arena (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 64)
    (aligned : pointer.toNat%8=0) : ∀ index,index<8→source.memaddrs (slot pointer index) := by
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
def stores (index : Nat) : Nat→ProgHOL 64
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
    (mapped : ∀ index,index<8→source.memaddrs (slot pointer index)) :
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
    (mapped : ∀ index,index<8→source.memaddrs (slot pointer index)) :
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

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer : BitVec 64) (words : Quad)
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
    (mapped : ∀ index,index<8→source.memaddrs (slot pointer index)) (enough : 1≤source.clock) :
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
    (mapped : ∀ index,index<8→source.memaddrs (slot pointer index))
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
    (away : ∀ index,index<8→query≠slot pointer index) : (callerPost source pointer words).memory query=source.memory query :=
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

def result (contents : Nat→BitVec 64) : Nat→Nat
  | 0=>0
  | count+1=>if contents count=0#64 then result contents count else count+1
def scans (contents : Nat→BitVec 64) : Nat→Nat
  | 0=>0
  | count+1=>if contents count=0#64 then scans contents count+1 else 1

theorem result_bound (contents : Nat→BitVec 64) (count : Nat) : result contents count≤count := by
  induction count with
  | zero=>rfl
  | succ count ih=>simp only [result];split_ifs <;> omega

theorem scans_bound (contents : Nat→BitVec 64) (count : Nat) : scans contents count≤count := by
  induction count with
  | zero=>rfl
  | succ count ih=>simp only [scans];split_ifs <;> omega

theorem result_zero (contents : Nat→BitVec 64) (count : Nat) : result contents count=0 ↔ ∀ index,index<count→contents index=0#64 := by
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

theorem result_leading (contents : Nat→BitVec 64) (count : Nat) (positive : 0<result contents count) :
    contents (result contents count-1)≠0#64 := by
  induction count with
  | zero=>simp [result] at positive
  | succ count ih=>
    by_cases zero : contents count=0#64
    · rw [result,if_pos zero] at positive ⊢
      exact ih positive
    · simpa only [result,if_neg zero,Nat.add_sub_cancel] using zero

theorem result_suffix (contents : Nat→BitVec 64) (count index : Nat)
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

private theorem loop_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (small : count≤8)
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
theorem body_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64) (count : Nat)
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
    (contents : Nat→BitVec 64) (count : Nat) (small : count≤8)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→source.memaddrs (slot pointer index)) :
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
        have nextMapped : ∀ index,index<count→next.memaddrs (slot pointer index):=by
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
    (contents : Nat→BitVec 64) (count : Nat) (small : count≤8)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→source.memaddrs (slot pointer index)) :
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
    (contents : Nat→BitVec 64) (count : Nat) (small : count≤8)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→source.memaddrs (slot pointer index)) (returned : ValueHOL 64)
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
theorem trimmed_number (contents : Nat→BitVec 64) (count : Nat) :
    number contents (result contents count)=number contents count := by
  induction count with
  | zero=>rfl
  | succ count ih=>
    by_cases zero : contents count=0#64
    · simpa [result,zero,number] using ih
    · simp only [result,if_neg zero]

theorem positive_length (contents : Nat→BitVec 64) (count : Nat) (positive : 0<number contents count) :
    0<result contents count := by
  by_contra zero
  have all:=(result_zero contents count).1 (by omega)
  have vanished:=number_zero contents count all
  omega

/-- Real scalar ABI and current physical image price the scoped caller. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (small : count≤8)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 count))])
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→source.memaddrs (slot pointer index))
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
    (contents : Nat→BitVec 64) (count : Nat) (small : count≤8)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 count))])
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→source.memaddrs (slot pointer index))
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
    (contents : Nat→BitVec 64) (count : Nat) (small : count≤8)
    (installed : OriginalCode.Installed source.code)
    (image : Image source pointer contents count)
    (mapped : ∀ index,index<count→source.memaddrs (slot pointer index))
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

def words (contents : Nat→BitVec 64) : Quad:=fun index=>
  contents (2*index.val) ||| (contents (2*index.val+1)<<<(32:Nat))

theorem pair_number (low high : BitVec 64) (lowSmall : low.toNat<2^32) (highSmall : high.toNat<2^32) :
    (low ||| (high<<<(32:Nat))).toNat=low.toNat+2^32*high.toNat := by
  have shifted : (high<<<(32:Nat)).toNat=2^32*high.toNat:=by
    rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mod_eq_of_lt (by nlinarith)]
    omega
  rw [BitVec.toNat_or,shifted,Nat.or_comm]
  exact (Nat.two_pow_add_eq_or_of_lt (i:=32) lowSmall high.toNat).symm.trans (by omega)

theorem words_number (contents : Nat→BitVec 64) (small : ∀ index,index<8→(contents index).toNat<2^32) :
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

private theorem limb_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64)
    (index : Fin 4) (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→source.memaddrs (slot pointer index)) :
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
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→source.memaddrs (slot pointer index)) :
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
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer : BitVec 64)
    (code : codeFn (ofString "digits_to_u256")=some (formals,body,RlpWrite.U256Value.tupleShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "digits_to_u256") [.val (.word pointer)]=some (body,callee,RlpWrite.U256Value.tupleShape) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) := by
  let rawLocals : MlS→Option (ValueHOL 64):=fun name=>if name=ofString "p" then some (.val (.word pointer)) else none
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

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (contents : Nat→BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word pointer)])
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→source.memaddrs (slot pointer index))
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
    (contents : Nat→BitVec 64) (installed : OriginalCode.Installed source.code)
    (image : Image source pointer contents 8) (mapped : ∀ index,index<8→source.memaddrs (slot pointer index))
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

private theorem loop_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (small : count≤8)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 count)))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) loopTest=
      some (.val (.word (if 0<count then 1#64 else 0#64))) := by
  have encoded : (BitVec.ofNat 64 count).toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [finite_eval]
  simp [eval,loopTest,localVar,evalHOLExact,toExact,j,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,encoded]

private theorem number_congr (left right : Nat→BitVec 64) (count : Nat)
    (agree : ∀ index,index<count→left index=right index) : number left count=number right count := by
  induction count with
  | zero=>rfl
  | succ count ih=>rw [number,number,agree count (by omega),ih (by intro index inside;exact agree index (by omega))]

structure LoopResult (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer : BitVec 64)
    (contents : Nat→BitVec 64) (divisor high : BitVec 64) (count : Nat) (quotient : Nat→BitVec 64) (remainder : BitVec 64) : Prop where
  run : evaluateHOLFiniteState source loop=(none,target)
  state : target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-34*count}
  image : Image target qPointer quotient count
  digits : ∀ index,index<count→(quotient index).toNat<2^32
  small : remainder.toNat<divisor.toNat
  value : divisor.toNat*number quotient count+remainder.toNat=high.toNat*2^(32*count)+number contents count
  index : target.locals.lookup (ofString "j")=some (.val (.word 0#64))
  carry : target.locals.lookup (ofString "k")=some (.val (.word remainder))
  other : ∀ name : String,ofString name≠ofString "j"→ ofString name≠ofString "k"→ ofString name≠ofString "qr"→
    target.locals.lookup (ofString name)=source.locals.lookup (ofString name)
  away : ∀ query,(∀ index,index<count→query≠slot qPointer index)→target.memory query=source.memory query

/-- Full physical one-digit division loop: actual quotient stores, exact
natural division identity, carried remainder and protected-memory frame. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (qPointer uPointer high divisor : BitVec 64)
    (contents : Nat→BitVec 64) (count : Nat) (small : count≤8)
    (installed : OriginalCode.Installed source.code)
    (qCell : source.locals.lookup (ofString "q")=some (.val (.word qPointer)))
    (uCell : source.locals.lookup (ofString "u")=some (.val (.word uPointer)))
    (jCell : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 count))))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word high)))
    (dCell : source.locals.lookup (ofString "d")=some (.val (.word divisor)))
    (image : Image source uPointer contents count)
    (inputMapped : ∀ index,index<count→source.memaddrs (slot uPointer index))
    (outputMapped : ∀ index,index<count→source.memaddrs (slot qPointer index))
    (separate : ∀ inputIndex,inputIndex<count→∀ outputIndex,outputIndex<count→slot uPointer inputIndex≠slot qPointer outputIndex)
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat)
    (digitsSmall : ∀ index,index<count→(contents index).toNat<2^32)
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
    have midInput : ∀ index,index<count→middle.memaddrs (slot uPointer index):=by
      intro index inside
      exact inputMapped index (by omega)
    have midOutput : ∀ index,index<count→middle.memaddrs (slot qPointer index):=by
      intro index inside
      exact outputMapped index (by omega)
    obtain ⟨target,tailDigits,finalR,tailRun⟩:=ih middle carry (by omega) (by rw [middleCode];exact installed)
      midQ midU (next_index entry qPointer count digit carry) (next_remainder entry qPointer count digit carry) midD
      middleImage midInput midOutput (by intro i hi j hj;exact separate i (by omega) j (by omega)) carrySmall
      (by intro index inside;exact digitsSmall index (by omega)) (by rw [middleClock];omega)
    let finalDigits : Nat→BitVec 64:=fun index=>if index=count then digit else tailDigits index
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
    (contents : Nat→BitVec 64) (count : Nat) (small : count≤8)
    (installed : OriginalCode.Installed source.code)
    (qCell : source.locals.lookup (ofString "q")=some (.val (.word qPointer)))
    (uCell : source.locals.lookup (ofString "u")=some (.val (.word uPointer)))
    (jCell : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 count))))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word high)))
    (dCell : source.locals.lookup (ofString "d")=some (.val (.word divisor)))
    (image : Image source uPointer contents count)
    (inputMapped : ∀ index,index<count→source.memaddrs (slot uPointer index))
    (outputMapped : ∀ index,index<count→source.memaddrs (slot qPointer index))
    (separate : ∀ inputIndex,inputIndex<count→∀ outputIndex,outputIndex<count→slot uPointer inputIndex≠slot qPointer outputIndex)
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat)
    (digitsSmall : ∀ index,index<count→(contents index).toNat<2^32)
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
    (contents : Nat→BitVec 64) (count : Nat) (small : count≤8)
    (installed : OriginalCode.Installed source.code)
    (qCell : source.locals.lookup (ofString "q")=some (.val (.word qPointer)))
    (uCell : source.locals.lookup (ofString "u")=some (.val (.word uPointer)))
    (jCell : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 count))))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word high)))
    (dCell : source.locals.lookup (ofString "d")=some (.val (.word divisor)))
    (image : Image source uPointer contents count)
    (inputMapped : ∀ index,index<count→source.memaddrs (slot uPointer index))
    (outputMapped : ∀ index,index<count→source.memaddrs (slot qPointer index))
    (separate : ∀ inputIndex,inputIndex<count→∀ outputIndex,outputIndex<count→slot uPointer inputIndex≠slot qPointer outputIndex)
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat)
    (digitsSmall : ∀ index,index<count→(contents index).toNat<2^32)
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
    {contents quotient : Nat→BitVec 64} {divisor high remainder : BitVec 64} {count : Nat}
    (checked : LoopResult source target qPointer contents divisor high count quotient remainder) :
    number quotient count=(high.toNat*2^(32*count)+number contents count)/divisor.toNat ∧
      remainder.toNat=(high.toNat*2^(32*count)+number contents count)%divisor.toNat := by
  have positive : 0<divisor.toNat:=by have small:=checked.small;omega
  constructor
  · rw [←checked.value,Nat.mul_add_div positive,Nat.div_eq_of_lt checked.small,Nat.add_zero]
  · rw [←checked.value,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt checked.small]

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
