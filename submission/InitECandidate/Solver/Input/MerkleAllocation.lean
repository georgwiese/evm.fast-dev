import InitECandidate.Solver.Input.MerkleZero
import InitECandidate.Solver.Input.InitializerAllocations
import InitECandidate.Solver.Input.InitializerControl
import InitECandidate.Solver.Input.HeapMarkTrace
import InitECandidate.Solver.Input.HeapScopeCost
import InitECandidate.Solver.Input.TerminatingProgramPrefix

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch ProgramPrefix

def afterMark : ProgHOL 64 := match afterZero with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterBuffer : ProgHOL 64 := match afterMark with
  | .dec _ _ _ rest=>(match rest with | .decCall _ _ _ _ tail=>tail | _=>.skip)
  | _=>.skip
def sizeExpression : ExpHOL 64 := .shift .lsl (.const 1#64) (localVar "dn")
def amountExpression : ExpHOL 64 := .panop .mul [localVar "size",.const 32#64]
def allocationActions : List Action := [.declare "size" sizeExpression,.allocate "buf" amountExpression]
def sized (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dn : Nat) := bind source "size" (BitVec.ofNat 64 (2^dn))
def bufferEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (dn : Nat) :=
  bind (PersistentAlloc.post {sized source dn with clock:=source.clock-1} cursor (BitVec.ofNat 64 (32*2^dn))) "buf" cursor

set_option maxRecDepth 100000 in
theorem allocation_shape : afterZero=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark ∧
    afterMark=ProgramPrefix.program allocationActions afterBuffer := by
  simp only [afterZero,afterDepth,afterCount,afterLimit,body,afterMark,afterBuffer,Guest.guestFn_merkleize,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,allocationActions,ProgramPrefix.program,sizeExpression,amountExpression,localVar]
  exact ⟨True.intro,True.intro⟩

theorem size_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dn : Nat) (small : dn<64)
    (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn)))) :
    eval source sizeExpression=some (.val (.word (BitVec.ofNat 64 (2^dn)))) := by
  have number : (BitVec.ofNat 64 dn).toNat=dn := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have shift : ((1#64 : BitVec 64)<<<dn)=BitVec.ofNat 64 (2^dn) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  have valid : ¬(dn≠0 ∧ 64≤dn) := by omega
  simp [eval,sizeExpression,localVar,evalHOLExact,toExact,depth,wordShiftHOL,number,valid,shift]

private theorem amount_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dn : Nat) :
    eval (sized source dn) amountExpression=some (.val (.word (BitVec.ofNat 64 (32*2^dn)))) := by
  have size : (sized source dn).locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 (2^dn)))) := bind_lookup_same source _ _
  simp [eval,amountExpression,localVar,evalHOLExact,evalListHOLExact,toExact,size,valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

private theorem setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (dn : Nat)
    (small : dn<64) (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))))
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (32*2^dn)) (enough : 1≤source.clock) :
    Executes source allocationActions (bufferEntry source cursor dn) (fun target=>restore source "size" (restore (sized source dn) "buf" target)) := by
  have amountNumber : (BitVec.ofNat 64 (32*2^dn)).toNat=32*2^dn := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have upper := arena.upper; omega)]
  apply Executes.declare (restoreRest:=restore (sized source dn) "buf") (BitVec.ofNat 64 (2^dn)) (size_read source dn small depth)
  exact Executes.allocate (restoreRest:=id) cursor (BitVec.ofNat 64 (32*2^dn)) (amount_read source dn)
    (PersistentAlloc.original_code source.code installed) heap (by rw [amountNumber]; exact arena.upper) enough (Executes.done _)

/-- Real nonempty Merkle size declaration/allocation at its current arena.
Funding follows from the same observed execution, with exact scope/data and
no assumption that the later copies or hashing loops succeed. -/
theorem allocation_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (dn : Nat)
    (small : dn<64) (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))))
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (32*2^dn))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    1≤source.clock ∧ ∃ final,evaluateHOLFiniteState (bufferEntry source cursor dn) afterBuffer=(result,final) ∧
      post=restore source "size" (restore (sized source dn) "buf" final) := by
  have padded := setup {source with clock:=source.clock+1} cursor dn small depth installed heap arena (by change 1≤source.clock+1; omega)
  rw [allocation_shape.2] at run
  have paid := terminating_program_prefix source post (bufferEntry {source with clock:=source.clock+1} cursor dn) allocationActions afterBuffer
    (fun target=>restore {source with clock:=source.clock+1} "size" (restore (sized {source with clock:=source.clock+1} dn) "buf" target)) 1 padded result run notTimeout
  have funded : 1≤source.clock := by change 1≤source.clock+1-1 at paid; omega
  have actual := setup source cursor dn small depth installed heap arena funded
  rw [ProgramPrefix.execute actual afterBuffer] at run
  let final := (evaluateHOLFiniteState (bufferEntry source cursor dn) afterBuffer).2
  have observed := congrArg Prod.fst run
  have endpoint := congrArg Prod.snd run
  exact ⟨funded,final,Prod.ext observed rfl,endpoint.symm⟩

theorem buffer_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (dn : Nat) :
    (bufferEntry source cursor dn).locals.lookup (ofString "buf")=some (.val (.word cursor)) ∧
    (bufferEntry source cursor dn).locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 (2^dn)))) ∧
    (bufferEntry source cursor dn).memory=source.memory ∧
    InitializerAllocations.context (bufferEntry source cursor dn)=InitializerAllocations.context source ∧
    (bufferEntry source cursor dn).clock=source.clock-1 := by
  refine ⟨bind_lookup_same _ _ _,?_,rfl,rfl,rfl⟩
  exact (bind_lookup_other _ "buf" "size" _ (by decide)).trans (bind_lookup_same source "size" _)

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.allocation_shape
#print axioms InitECandidate.Solver.Input.Merkle.size_read
#print axioms InitECandidate.Solver.Input.Merkle.allocation_prefix
#print axioms InitECandidate.Solver.Input.Merkle.buffer_fields
