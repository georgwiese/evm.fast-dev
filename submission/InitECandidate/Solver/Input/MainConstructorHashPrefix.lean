import InitECandidate.Solver.Input.MainRequestRootHashTrace
import InitECandidate.Solver.Input.MainRootHashEntry
import InitECandidate.Solver.Input.ClockCostSpendChain

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def constructorHashPrefixBase (input : Guest.InputBlob) := inputPrice input+(input.length%2^64)/4+DecoderCall.witnessLength input/2+1410
def constructorHashPrefixPrice (input : Guest.InputBlob) := constructorHashPrefixBase input+RequestHash.sourcePrice input

/-- Extend the existing actual main terminal-run prefix through the entire
original request-root hash to its constructor continuation. Real stopped
prefixes are charged; normal hashing retains startup/decoded provenance. -/
theorem constructor_hash_prefix_of_main (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (bounded : input.length%2^64≤Guest.maxInputBytes) (gas : Guest.GasLimit.declaredGasLimit input≤200000000)
    (result : Option (PanSemResultExact 64)) (terminal : (∃ value,result=some (.returned value)) ∨ ∃ event,result=some (.finalFfi event))
    (run : evaluateHOLFiniteState source body=(result,target)) :
    source.clock-target.clock≤constructorHashPrefixPrice input ∨
      ∃ before copied decoded root hashed final counts,
        InputCopied input before copied ∧ DecoderCall.DecoderReady input (DecoderSetup.entered copied input) decoded ∧
        RequestRootHashData.Prepared input decoded root counts ∧ RequestHash.Returned input decoded hashed root ∧
        hashed.clock≤source.clock ∧ source.clock-hashed.clock≤constructorHashPrefixPrice input ∧
        evaluateHOLFiniteState hashed RequestHash.continuation=(result,final) ∧
        target=QueryBranch.restore before "inp" (DecoderSetup.restoration copied input (QueryBranch.restore decoded "root" final)) := by
  have notTimeout : result≠some .timeOut := by rcases terminal with ⟨value,same⟩|⟨event,same⟩ <;> rw [same] <;> simp
  rcases root_hash_prefix_of_main input source target entry bounded gas result terminal run with stopped|reached
  · exact Or.inl (stopped.trans (Nat.le_add_right _ _))
  · obtain ⟨before,copied,decoded,root,final,bytes,data,heap,aligned,arena,forward,price,remaining,endpoint⟩ := reached
    obtain ⟨counts,prepared⟩ := RequestRootHashData.prepared input before copied decoded root bytes data bounded heap
    have frontCost : source.clock-(RequestHash.entered decoded root).clock≤constructorHashPrefixBase input :=
      price.trans (Nat.add_le_add_left (by decide : 1360≤1410) _)
    rcases RequestHash.after_root_trace input decoded final root counts prepared result remaining notTimeout with stopped|hashed
    · have back := evaluateHOLFiniteState_clock_le (RequestHash.entered decoded root) RequestHash.afterRoot
      rw [remaining] at back
      have combined := ClockCost.spend_chain source.clock (RequestHash.entered decoded root).clock final.clock (constructorHashPrefixBase input) (RequestHash.sourcePrice input) forward back frontCost stopped
      have finalClock : target.clock=final.clock := by rw [endpoint]; rfl
      rw [finalClock]
      exact Or.inl combined
    · obtain ⟨hashed,returned,continued⟩ := hashed
      have combined := ClockCost.spend_chain source.clock (RequestHash.entered decoded root).clock hashed.clock (constructorHashPrefixBase input) (RequestHash.sourcePrice input) forward returned.forward frontCost returned.cost
      exact Or.inr ⟨before,copied,decoded,root,hashed,final,counts,bytes,data,prepared,returned,Nat.le_trans returned.forward forward,combined,continued,endpoint⟩

end InitECandidate.Solver.Input.Main
#print axioms InitECandidate.Solver.Input.Main.constructor_hash_prefix_of_main
