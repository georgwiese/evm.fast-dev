import InitECandidate.Solver.Input.MainRipemdPrefix
import InitECandidate.Solver.Input.MainBlakeProgram

namespace InitECandidate.Solver.Input.Main.RipemdInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (other : ∀ name ∈ symbols,key ≠ ofString name) :
    (template source cursor).globals.lookup key = source.globals.lookup key := by
  change (InitializerAllocations.template source cursor actions).globals.lookup key = _
  apply InitializerAllocations.template_other source cursor actions key heap
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exact other _ (by simp [symbols,InitializerAllocations.constant])

end InitECandidate.Solver.Input.Main.RipemdInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def touchedRipemd : List String := touchedBls ++ RipemdInitialization.symbols

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem b2_sigma_fresh : touchedRipemd.all (fun name => decide (ofString "b2_sigma" ≠ ofString name)) = true := by decide_cbv

theorem ripemd_initial_zero (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (key : MlS) (member : key ∈ OriginalScalarGlobals.names) (other : ∀ name ∈ touchedRipemd,key ≠ ofString name) :
    (ripemdState middle).globals.lookup key = some (.val (.word 0#64)) := by
  have prior (name : String) (present : name ∈ touchedBls) : key ≠ ofString name := other name (List.mem_append_left _ present)
  have heap := prior "heap_ptr" (by simp [touchedBls,touchedBeforeBls,initializedNames])
  change (RipemdInitialization.template (blsState middle) 2713729752).globals.lookup key = _
  rw [RipemdInitialization.template_other (blsState middle) 2713729752 key heap (by intro name present; exact other name (List.mem_append_right _ present))]
  exact bls_initial_zero input source mptMiddle middle entry mpt reached key member prior

theorem b2_sigma_before (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) :
    (ripemdState middle).globals.lookup (ofString "b2_sigma") = some (.val (.word 0#64)) := by
  apply ripemd_initial_zero input source mptMiddle middle entry mpt reached _ (BlakeInitialization.symbol_member "b2_sigma" (by simp [BlakeInitialization.symbols]))
  intro name member
  exact of_decide_eq_true (List.all_eq_true.mp b2_sigma_fresh name member)

theorem ripemd_domain (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) :
    (ripemdState middle).memaddrs = InitE.ordinaryDomain :=
  (InitializerAllocations.domain_of_context middle (ripemdState middle) (ripemd_context middle)).trans (bn_domain input source mptMiddle middle entry mpt reached)

theorem ripemd_code (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) : (ripemdState middle).code = source.code :=
  (InitializerAllocations.code_of_context middle (ripemdState middle) (ripemd_context middle)).trans (reached.code source mptMiddle middle mpt)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.template_other
#print axioms InitECandidate.Solver.Input.Main.b2_sigma_fresh
#print axioms InitECandidate.Solver.Input.Main.ripemd_initial_zero
#print axioms InitECandidate.Solver.Input.Main.b2_sigma_before
#print axioms InitECandidate.Solver.Input.Main.ripemd_domain
#print axioms InitECandidate.Solver.Input.Main.ripemd_code
