import InitECandidate.Solver.Mpt.KeyToNibblesProgram
import InitECandidate.Solver.Input.ByteStoreLocal
import InitECandidate.Solver.Input.CounterDeclaration
import InitECandidate.Solver.Input.LocalSummaryDeclaration

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem pair_advances (name : String) (offset amount : Nat) (rest : ProgHOL 64)
    (advance : Input.CounterFlow.Advances (ofString "i") amount rest) :
    Input.CounterFlow.Advances (ofString "i") amount (pair name offset rest) := by
  have back:=Input.CounterFlow.sequence (ofString "i")
    (.storeByte (outputAddress (2*offset+1)) (.op .and [QueryBranch.localVar name,.const 15#64])) rest 0 amount
    (Input.CounterFlow.byte_store _ _ _) advance
  have front:=Input.CounterFlow.sequence (ofString "i")
    (.storeByte (outputAddress (2*offset)) (.shift .lsr (QueryBranch.localVar name) (.const 4#64))) _ 0 (0+amount)
    (Input.CounterFlow.byte_store _ _ _) back
  simpa only [Nat.zero_add,pair] using front

theorem pair_summary (key : MlS) (name : String) (offset : Nat) (rest : ProgHOL 64)
    (summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,Input.LocalSummary key rest source) :
    ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,Input.LocalSummary key (pair name offset rest) source := by
  intro source
  exact Input.local_summary_sequence key _ _ (Input.byte_store_local key _ _)
    (Input.local_summary_sequence key _ _ (Input.byte_store_local key _ _) summary) source

/-- Arbitrary reads and byte-store failures do not supply a successful
future block. Genuine fallthrough advances exactly the original4/1 counter. -/
theorem bodies_advance : Input.CounterFlow.Advances (ofString "i") 4 blockBody ∧
    Input.CounterFlow.Advances (ofString "i") 1 tailBody := by
  rw [block_body_shape,tail_body_shape]
  constructor
  all_goals repeat first
    | apply Input.CounterFlow.declared <;> (try decide)
    | apply pair_advances
    | exact Input.CounterFlow.increment_by (ofString "i") _

/-- Both original block bodies preserve their actual n binding and cannot
escape as return/break/continue, regardless of byte contents and mapping. -/
theorem bodies_length_summary :
    (∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,Input.LocalSummary (ofString "n") blockBody source) ∧
    (∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,Input.LocalSummary (ofString "n") tailBody source) := by
  rw [block_body_shape,tail_body_shape]
  constructor
  all_goals repeat first
    | apply Input.local_summary_declaration <;> (try decide)
    | apply pair_summary
    | exact (Input.LocalPrefix.assign (key:=ofString "n") (ofString "i") _ (by decide)).summary_full

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_advances
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_summary
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.bodies_advance
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.bodies_length_summary
