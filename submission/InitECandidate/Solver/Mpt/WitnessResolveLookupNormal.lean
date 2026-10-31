import InitECandidate.Solver.Mpt.WitnessResolveHashNormal
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.SequenceChoice

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem hash_never : Input.NoFallthrough hashCall :=
  Input.NoFallthrough.scoped _ _ _ _ _ (Input.NoFallthrough.returned _)

theorem lookup_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (answer : Option (BitVec 64×BitVec 64))
    (rCell : source.locals.lookup (ofString "r")=some (lookupValue answer)) :
    evaluateHOLFiniteState source afterLookup=
      if answer=none then evaluateHOLFiniteState source hashCall else evaluateHOLFiniteState source hitReturn := by
  have selected : evaluateHOLFiniteState source (.ite (.cmp .equal (field "r" 0) (.const 0#64)) hashCall .skip)=
      if answer=none then evaluateHOLFiniteState source hashCall else (none,source):=by
    cases answer <;> simp [evaluateHOLFiniteState_ite,field,evalHOLExact,localVar,toExact,rCell,
      lookupValue,Input.CurrentTable.NodeLookup.absentValue,Input.CurrentTable.NodeLookup.presentValue,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  exact Input.sequence_choice source _ hashCall hitReturn (answer=none) selected hash_never

/-- The resolver's genuine lookup continuation either constructs a fresh
hashed node on absence, or returns the actual table slice with its original
hash pointer. A returned hash constructor cannot fall through to hitReturn. -/
theorem after_lookup_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag heap : BitVec 64) (answer : Option (BitVec 64×BitVec 64))
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (rCell : source.locals.lookup (ofString "r")=some (lookupValue answer))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLookup=(some (.returned value),post)) :
    match answer with
    | none=>value=.rStruct [.val (.word 0#64),.val (.word heap),.val (.word 0#64),.val (.word 0#64)] ∧
        heap.toNat+32≤2952790016 ∧ AllocatedBytes.Arena heap 32 ∧ 2≤source.clock ∧
        emptyLocalsHOLFinite post=emptyLocalsHOLFinite (hashAllocated source heap (pointer+header))
    | some slice=>value=.rStruct [.val (.word 1#64),.val (.word slice.1),.val (.word slice.2),.val (.word (pointer+header))] ∧
        post=emptyLocalsHOLFinite source := by
  rw [lookup_choice source answer rCell] at normal
  cases answer with
  | none=>
    rw [if_pos rfl] at normal
    exact hash_call_normal source post pointer header payload flag heap itemCell heapCell domain arena aligned installed value normal
  | some slice=>
    rw [if_neg (by simp)] at normal
    obtain ⟨read,postEq⟩:=Input.return_normal source post _ value normal
    have expected : eval source (.rstruct [.const 1#64,field "r" 1,field "r" 2,field "it" 1])=
        some (.rStruct [.val (.word 1#64),.val (.word slice.1),.val (.word slice.2),.val (.word (pointer+header))]):=by
      simp [eval,evalHOLExact,evalListHOLExact,field,localVar,toExact,itemCell,rCell,Rlp.Item.result,lookupValue,Input.CurrentTable.NodeLookup.absentValue,Input.CurrentTable.NodeLookup.presentValue]
    exact ⟨Option.some.inj (read.symm.trans expected),postEq⟩

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_never
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.lookup_choice
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.after_lookup_normal
