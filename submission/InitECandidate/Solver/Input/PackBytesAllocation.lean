import InitECandidate.Solver.Input.PackBytesProgram
import InitECandidate.Solver.Input.TerminatingProgramPrefix

namespace InitECandidate.Solver.Input.PackBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch ProgramPrefix

def allocationActions : List Action := [.declare "count" countExpression,.allocate "buf" amountExpression]
def sized (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat) := bind source "count" (BitVec.ofNat 64 (chunks n))
def buffered (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat) :=
  bind (PersistentAlloc.post {sized source n with clock:=source.clock-1} cursor (BitVec.ofNat 64 (padded n))) "buf" cursor

private theorem amount_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat) :
    eval (sized source n) amountExpression=some (.val (.word (BitVec.ofNat 64 (padded n)))) := by
  have count : (sized source n).locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))) := bind_lookup_same _ _ _
  simp [eval,amountExpression,localVar,evalHOLExact,evalListHOLExact,toExact,count,valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,padded,BitVec.mul_comm]

private theorem allocation_program : body=ProgramPrefix.program allocationActions afterBuffer := by
  rw [body_shape.1,body_shape.2.1]
  rfl

private theorem setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat)
    (small : n≤134217728) (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (installed : OriginalCode.Installed source.code) (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (padded n)) (enough : 1≤source.clock) :
    Executes source allocationActions (buffered source cursor n) (fun target=>restore source "count" (restore (sized source n) "buf" target)) := by
  have number : (BitVec.ofNat 64 (padded n)).toNat=padded n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=arena.upper; omega)]
  apply Executes.declare (restoreRest:=restore (sized source n) "buf") (BitVec.ofNat 64 (chunks n)) (count_read source n small count)
  exact Executes.allocate (source:=sized source n) (restoreRest:=id) cursor (BitVec.ofNat 64 (padded n)) (amount_read source n)
    (PersistentAlloc.original_code source.code installed) heap (by rw [number]; exact arena.upper) enough (Executes.done _)

/-- The actual original pack count/allocation prefix, including exact scope
restoration and funding derived from its own non-timeout continuation. -/
theorem allocation_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat)
    (small : n≤134217728) (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (installed : OriginalCode.Installed source.code) (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (padded n))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    1≤source.clock ∧ ∃ final,evaluateHOLFiniteState (buffered source cursor n) afterBuffer=(result,final) ∧
      post=restore source "count" (restore (sized source n) "buf" final) := by
  have paddedSetup := setup {source with clock:=source.clock+1} cursor n small count installed heap arena (by change 1≤source.clock+1; omega)
  rw [allocation_program] at run
  have paid := terminating_program_prefix source post (buffered {source with clock:=source.clock+1} cursor n) allocationActions afterBuffer
    (fun target=>restore {source with clock:=source.clock+1} "count" (restore (sized {source with clock:=source.clock+1} n) "buf" target)) 1 paddedSetup result run notTimeout
  have funded : 1≤source.clock := by change 1≤source.clock+1-1 at paid; omega
  have actual := setup source cursor n small count installed heap arena funded
  rw [ProgramPrefix.execute actual afterBuffer] at run
  let final := (evaluateHOLFiniteState (buffered source cursor n) afterBuffer).2
  have observed := congrArg Prod.fst run
  have endpoint := congrArg Prod.snd run
  exact ⟨funded,final,Prod.ext observed rfl,endpoint.symm⟩

theorem buffered_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat) :
    (buffered source cursor n).locals.lookup (ofString "buf")=some (.val (.word cursor)) ∧
    (buffered source cursor n).locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))) ∧
    (buffered source cursor n).clock=source.clock-1 ∧ (buffered source cursor n).memory=source.memory :=
  ⟨bind_lookup_same _ _ _,(bind_lookup_other _ "buf" "count" cursor (by decide)).trans (bind_lookup_same _ _ _),rfl,rfl⟩

theorem buffered_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat) (name : String)
    (notBuf : ofString "buf"≠ofString name) (notCount : ofString "count"≠ofString name) :
    (buffered source cursor n).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  change (bind (PersistentAlloc.post {sized source n with clock:=source.clock-1} cursor (BitVec.ofNat 64 (padded n))) "buf" cursor).locals.lookup _=_
  rw [bind_lookup_other _ "buf" name cursor notBuf]
  exact bind_lookup_other source "count" name (BitVec.ofNat 64 (chunks n)) notCount

theorem buffered_global_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat) (key : MlS) (other : key≠ofString "heap_ptr") :
    (buffered source cursor n).globals.lookup key=source.globals.lookup key := by
  change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n)))))).lookup key=_
  simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm other]

end InitECandidate.Solver.Input.PackBytes

#print axioms InitECandidate.Solver.Input.PackBytes.allocation_prefix
#print axioms InitECandidate.Solver.Input.PackBytes.buffered_fields
#print axioms InitECandidate.Solver.Input.PackBytes.buffered_other
#print axioms InitECandidate.Solver.Input.PackBytes.buffered_global_other
