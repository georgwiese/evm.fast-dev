import InitECandidate.Solver.Mpt.IndexedProgram
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def keyArguments : List (ExpHOL 64):=[.var .global (ofString "mpt_key_scratch"),localVar "i"]
def setArguments : List (ExpHOL 64):=[localVar "m",.var .global (ofString "mpt_key_scratch"),localVar "klen",
  .load .one (.op .add [localVar "slice_arr",.panop .mul [localVar "i",.const 16#64]]),
  .load .one (.op .add [localVar "slice_arr",.panop .mul [localVar "i",.const 16#64],.const 8#64])]
def advance : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def setCall : ProgHOL 64:=.call (some (none,none)) (ofString "mpt_set") setArguments

theorem loop_body_shape : loopBody=.decCall (ofString "klen") .one (ofString "rlp_encode_word") keyArguments (.seq setCall advance) := by
  simp only [loopBody,loop,loopAndAfter,afterNew,afterMark,body,Guest.guestFn_build_mpt_indexed,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,keyArguments,setCall,setArguments,advance,localVar] <;>rfl

theorem loop_body_limit : Input.LocalPrefix (ofString "n") loopBody := by
  rw [loop_body_shape]
  apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
  exact Input.LocalPrefix.seq (.call none _ _ (by simp)) (.assign _ _ (by decide))

theorem loop_body_advance : Input.CounterFlow.Advances (ofString "i") 1 loopBody := by
  rw [loop_body_shape]
  apply Input.CounterFlow.scoped_call (ofString "i") "klen" .one _ _ _ 1 (by decide)
  exact Input.CounterFlow.sequence _ _ _ 0 1
    (Input.CounterFlow.preserved _ setCall (.call none _ _ (by simp))) (Input.CounterFlow.increment _)

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : BitVec 64) (count : Nat) (small : count<2^64)
    (i : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    eval source test=some (.val (.word (if index.toNat<count then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 count).toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  simp [eval,test,localVar,evalHOLExact,toExact,i,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,number]

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.loop_body_shape
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_body_limit
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_body_advance
#print axioms InitECandidate.Solver.Mpt.Indexed.test_read
