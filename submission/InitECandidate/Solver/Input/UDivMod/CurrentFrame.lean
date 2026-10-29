import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.Input.WordTupleFour
import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.WitnessRadix.AllocatedArena
import InitECandidate.Solver.Input.UDivMod.CurrentCost
import InitECandidate.Solver.Input.LocalEffectsCurrentScoped

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
