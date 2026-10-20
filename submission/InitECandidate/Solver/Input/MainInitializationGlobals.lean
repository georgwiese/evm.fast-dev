import InitECandidate.Solver.Input.MainBlsPrefix

namespace InitECandidate.Solver.Input.Main.BlsInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (discount : key ≠ ofString "bls_discount") (constants : key ≠ ofString "bls_c")
    (fp : ∀ name ∈ BlsFpInitialization.symbols,key ≠ ofString name) (pairs : ∀ name ∈ BlsPairInitialization.symbols,key ≠ ofString name) :
    (template source cursor).globals.lookup key = source.globals.lookup key :=
  (WordTableInitialization.template_other (libTemplate source cursor) (cursor + 7760) discountAction discountWords key heap discount).trans
    (lib_other source cursor key heap constants fp pairs)

end InitECandidate.Solver.Input.Main.BlsInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def touchedBls : List String := touchedBeforeBls ++ ["bls_c","bls_discount"] ++ BlsFpInitialization.symbols ++ BlsPairInitialization.symbols

private theorem globals_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.globals = source.globals := congrArg (fun state => state.globals) same

/-- Any declaration-zero scalar outside the actual preceding writes remains
zero at the reached BN state. This does not assume anything about later calls. -/
theorem bn_initial_zero (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (key : MlS) (member : key ∈ OriginalScalarGlobals.names) (other : ∀ name ∈ touchedBeforeBls,key ≠ ofString name) :
    middle.globals.lookup key = some (.val (.word 0#64)) := by
  rw [globals_of_hash _ middle reached.control]
  have heap := other "heap_ptr" (by simp [touchedBeforeBls,initializedNames])
  have bn := BnInitialization.template_other (secpState mptMiddle) 2713718728 key heap
    (other "bn_gamma" (by simp [touchedBeforeBls])) (other "bn_b2" (by simp [touchedBeforeBls])) (other "bn_expw" (by simp [touchedBeforeBls]))
    (by intro name present; exact other name (List.mem_append_right _ present))
  have before := secp_initial_zero input source mptMiddle entry mpt key member
    (by intro name present; exact other name (List.mem_append_left _ (List.mem_append_left _ present)))
  exact bn.trans before

theorem bls_initial_zero (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (key : MlS) (member : key ∈ OriginalScalarGlobals.names) (other : ∀ name ∈ touchedBls,key ≠ ofString name) :
    (blsState middle).globals.lookup key = some (.val (.word 0#64)) := by
  have prior (name : String) (present : name ∈ touchedBeforeBls) : key ≠ ofString name := by
    apply other name
    simp only [touchedBls,List.mem_append]
    exact Or.inl (Or.inl (Or.inl present))
  have heap := prior "heap_ptr" (by simp [touchedBeforeBls,initializedNames])
  have fp (name : String) (present : name ∈ BlsFpInitialization.symbols) : key ≠ ofString name := by
    apply other name
    simp only [touchedBls,List.mem_append]
    exact Or.inl (Or.inr present)
  have pairs (name : String) (present : name ∈ BlsPairInitialization.symbols) : key ≠ ofString name := by
    apply other name
    exact List.mem_append_right _ present
  have constants : key ≠ ofString "bls_c" := other "bls_c" (by simp [touchedBls])
  have discount : key ≠ ofString "bls_discount" := other "bls_discount" (by simp [touchedBls])
  change (BlsInitialization.template middle 2713719944).globals.lookup key = _
  rw [BlsInitialization.template_other middle 2713719944 key heap discount constants fp pairs]
  exact bn_initial_zero input source mptMiddle middle entry mpt reached key member prior

theorem bls_domain (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) :
    (blsState middle).memaddrs = InitE.ordinaryDomain :=
  (InitializerAllocations.domain_of_context middle (blsState middle) (bls_context middle)).trans (bn_domain input source mptMiddle middle entry mpt reached)

theorem bls_code (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) : (blsState middle).code = source.code :=
  (InitializerAllocations.code_of_context middle (blsState middle) (bls_context middle)).trans (reached.code source mptMiddle middle mpt)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.template_other
#print axioms InitECandidate.Solver.Input.Main.bn_initial_zero
#print axioms InitECandidate.Solver.Input.Main.bls_initial_zero
#print axioms InitECandidate.Solver.Input.Main.bls_domain
#print axioms InitECandidate.Solver.Input.Main.bls_code
