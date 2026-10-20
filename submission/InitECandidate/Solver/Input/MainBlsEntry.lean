import InitECandidate.Solver.Input.MainBnFields
import InitECandidate.Solver.Input.MainBlsProgram

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def blsEntryNames : List String := ["bls_discount","bls_c","fp_accel_params","fp2_accel_params","bls_g1_accel_params"]
def touchedBeforeBls : List String := initializedNames ++ ["bn_gamma","bn_b2","bn_expw"] ++ BnAccelInitialization.symbols

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem bls_entry_names_checked : (blsEntryNames.map ofString).all (fun key => OriginalScalarGlobals.names.contains key) = true := by decide_cbv

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem bls_entry_names_fresh : blsEntryNames.all (fun name => touchedBeforeBls.all (fun changed => decide (ofString name ≠ ofString changed))) = true := by decide_cbv

private theorem bls_entry_member (name : String) (member : name ∈ blsEntryNames) : ofString name ∈ OriginalScalarGlobals.names :=
  List.contains_iff_mem.mp (List.all_eq_true.mp bls_entry_names_checked (ofString name) (List.mem_map.mpr ⟨name,member,rfl⟩))

private theorem bls_entry_different (name : String) (member : name ∈ blsEntryNames) (changed : String) (touched : changed ∈ touchedBeforeBls) :
    ofString name ≠ ofString changed := by
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp bls_entry_names_fresh name member) changed touched)

private theorem globals_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.globals = source.globals := congrArg (fun state => state.globals) same

private theorem domain_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.memaddrs = source.memaddrs := congrArg (fun state => state.memaddrs) same

/-- All five original BLS guards are zero at the actual reached main state;
their values are traced through every preceding real initializer. -/
theorem bls_entry_zero (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (name : String) (member : name ∈ blsEntryNames) : middle.globals.lookup (ofString name) = some (.val (.word 0#64)) := by
  rw [globals_of_hash _ middle reached.control]
  have heap := bls_entry_different name member "heap_ptr" (by simp [touchedBeforeBls,initializedNames])
  have bn := BnInitialization.template_other (secpState mptMiddle) 2713718728 (ofString name) heap
    (bls_entry_different name member "bn_gamma" (by simp [touchedBeforeBls]))
    (bls_entry_different name member "bn_b2" (by simp [touchedBeforeBls]))
    (bls_entry_different name member "bn_expw" (by simp [touchedBeforeBls]))
    (by intro changed touched; exact bls_entry_different name member changed (List.mem_append_right _ touched))
  have before := secp_initial_zero input source mptMiddle entry mpt (ofString name) (bls_entry_member name member)
    (by
      intro changed touched
      apply bls_entry_different name member changed
      exact List.mem_append_left _ (List.mem_append_left _ touched))
  exact bn.trans before

theorem bn_domain (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) : middle.memaddrs = InitE.ordinaryDomain :=
  (domain_of_hash _ middle reached.control).trans
    ((InitializerAllocations.domain_of_context (secpState mptMiddle) (BnInitialization.template (secpState mptMiddle) 2713718728)
      (BnInitialization.template_context (secpState mptMiddle) 2713718728)).trans (secp_domain input source mptMiddle entry mpt))

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.bls_entry_names_checked
#print axioms InitECandidate.Solver.Input.Main.bls_entry_names_fresh
#print axioms InitECandidate.Solver.Input.Main.bls_entry_zero
#print axioms InitECandidate.Solver.Input.Main.bn_domain
