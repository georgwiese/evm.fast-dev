import InitECandidate.Solver.Input.MainBlakePrefix
import InitECandidate.Solver.Input.MainHeaderInitialization

namespace InitECandidate.Solver.Input.Main.BlakeInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (other : ∀ name ∈ symbols,key ≠ ofString name) :
    (template source cursor).globals.lookup key = source.globals.lookup key := by
  change (InitializerAllocationAliases.template source cursor blocks).globals.lookup key = _
  apply InitializerAllocationAliases.template_other source cursor blocks key heap ?_ ?_
  · intro block member
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals exact other _ (by simp [symbols,sigmaBlock,ivBlock,roundBlock,InitializerAllocations.constant])
  · intro block member action present
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [sigmaBlock] at present
    · simp [ivBlock] at present
    · simp only [roundBlock,List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl | rfl
      all_goals exact other _ (by simp [symbols,InitializerAliases.offset])

end InitECandidate.Solver.Input.Main.BlakeInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def touchedBlake : List String := touchedRipemd ++ BlakeInitialization.symbols

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem hdr_zero8_fresh : touchedBlake.all (fun name => decide (ofString "hdr_zero8" ≠ ofString name)) = true := by decide_cbv

theorem blake_initial_zero (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (key : MlS) (member : key ∈ OriginalScalarGlobals.names) (other : ∀ name ∈ touchedBlake,key ≠ ofString name) :
    (blakeState middle).globals.lookup key = some (.val (.word 0#64)) := by
  have prior (name : String) (present : name ∈ touchedRipemd) : key ≠ ofString name := other name (List.mem_append_left _ present)
  have heap := prior "heap_ptr" (by simp [touchedRipemd,touchedBls,touchedBeforeBls,initializedNames])
  change (BlakeInitialization.template (ripemdState middle) 2713730208).globals.lookup key = _
  rw [BlakeInitialization.template_other (ripemdState middle) 2713730208 key heap (by intro name present; exact other name (List.mem_append_right _ present))]
  exact ripemd_initial_zero input source mptMiddle middle entry mpt reached key member prior

theorem hdr_zero8_before (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) :
    (blakeState middle).globals.lookup (ofString "hdr_zero8") = some (.val (.word 0#64)) := by
  apply blake_initial_zero input source mptMiddle middle entry mpt reached _ HeaderInitialization.symbol_member
  intro name member
  exact of_decide_eq_true (List.all_eq_true.mp hdr_zero8_fresh name member)

theorem blake_domain (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) :
    (blakeState middle).memaddrs = InitE.ordinaryDomain :=
  (InitializerAllocations.domain_of_context middle (blakeState middle) (blake_context middle)).trans (bn_domain input source mptMiddle middle entry mpt reached)

theorem blake_code (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) : (blakeState middle).code = source.code :=
  (InitializerAllocations.code_of_context middle (blakeState middle) (blake_context middle)).trans (reached.code source mptMiddle middle mpt)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.template_other
#print axioms InitECandidate.Solver.Input.Main.hdr_zero8_fresh
#print axioms InitECandidate.Solver.Input.Main.blake_initial_zero
#print axioms InitECandidate.Solver.Input.Main.hdr_zero8_before
#print axioms InitECandidate.Solver.Input.Main.blake_domain
#print axioms InitECandidate.Solver.Input.Main.blake_code
