import InitECandidate.Solver.Input.RequestPrefixProgram
import InitECandidate.Solver.Input.WorkspaceWord

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem first_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (globalArray : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (mapped : source.memaddrs array) (cell : source.memory array=.word 16#64) :
    eval source (.load .one Header.offsets)=some (.val (.word 16#64)) := by
  classical
  simp [eval,Header.offsets,evalHOLExact,toExact,globalArray,isWfShapeExactHOL,memLoadHOLExact,mapped,cell]


theorem second_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (witness : Nat)
    (globalArray : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (mapped : source.memaddrs (array+8#64)) (cell : source.memory (array+8#64)=.word (BitVec.ofNat 64 witness)) :
    eval (WitnessRadix.QueryBranch.bind source "o_npr" 16#64) (.load .one (Scalar.plus Header.offsets 8))=
      some (.val (.word (BitVec.ofNat 64 witness))) :=
  word_read (WitnessRadix.QueryBranch.bind source "o_npr" 16#64) array (BitVec.ofNat 64 witness) 8 globalArray mapped cell

theorem loaded_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (witness : Nat)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64)))) :
    (loaded source witness).locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))) ∧
    (loaded source witness).locals.lookup (ofString "o_npr")=some (.val (.word 16#64)) ∧
    (loaded source witness).locals.lookup (ofString "o_wit")=some (.val (.word (BitVec.ofNat 64 witness))) := by
  refine ⟨?_,?_,bind_lookup_same _ _ _⟩
  · rw [loaded,bind_lookup_other _ "o_wit" "p" _ (by decide),bind_lookup_other _ "o_npr" "p" _ (by decide)]
    exact pointerLocal
  · rw [loaded,bind_lookup_other _ "o_wit" "o_npr" _ (by decide)]
    exact bind_lookup_same _ _ _

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.first_read
#print axioms InitECandidate.Solver.Input.Request.second_read
#print axioms InitECandidate.Solver.Input.Request.loaded_locals

#print axioms InitECandidate.Solver.Input.Request.word_read
