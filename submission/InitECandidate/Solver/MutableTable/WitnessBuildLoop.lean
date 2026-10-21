import InitECandidate.Solver.MutableTable.WitnessBuildContext
import InitECandidate.Solver.MutableTable.WitnessBuildHistory

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The complete actual original witness-construction while loop records
every observed digest in input order and establishes the represented table
history, including arbitrary duplicate keys. No per-iteration run is assumed. -/
theorem record_loop (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (scratch stp pad : BitVec 64) (slices : Nat→Graph.Slice) (maximum index remaining count : Nat)
    (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (sizeEq : index+remaining=plan.count) (processed : input.length=index)
    (built : Layout32.Built bits source plan scratch count input logical) (history : History plan input)
    (locals : Locals source plan index) (records : Records source plan slices)
    (context : Context source plan slices stp pad scratch maximum)
    (enough : (recordPrice maximum plan.count+1)*remaining≤source.clock) :
    ∃ nextCount finalInput finalLogical target,
      evaluateHOLFiniteState source recordLoop=(none,target) ∧
      Layout32.Built bits target plan scratch nextCount finalInput finalLogical ∧ History plan finalInput ∧ finalInput.length=plan.count ∧
      Locals target plan plan.count ∧ Records target plan slices ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source ∧ target.clock≤source.clock ∧
      source.clock-(recordPrice maximum plan.count+1)*remaining≤target.clock ∧
      ∀ name : MlS,ofString "i"≠name→target.locals.lookup name=source.locals.lookup name := by
  have countSmall : plan.count<2^64:=by have:=ready.recordsBefore;have:=ready.fits;omega
  induction remaining generalizing source index count input logical with
  | zero=>
    have same : index=plan.count:=by omega
    have test:=Zero.tail_condition source index plan.count countSmall (by omega) locals.index locals.count
    change @evalHOLFinite 64 Guest.HostMemory _ source (fun address=>Classical.propDecidable (source.memaddrs address)) Constructor.condition=
      some (.val (.word (if index<plan.count then 1#64 else 0#64))) at test
    rw [if_neg (by omega)] at test
    refine ⟨count,input,logical,source,?_,built,history,by omega,by simpa only [same] using locals,records,rfl,Nat.le_refl _,by simp,?_⟩
    · rw [recordLoop,evaluateHOLFiniteState_while_total,test];simp
    · intros;rfl
  | succ remaining ih=>
    simp only [Nat.mul_succ] at enough
    have inside : index<plan.count:=by omega
    let entry:=decClockHOLFinite source
    have entryBuilt:=Layout32.built_fields source entry plan bits scratch count input logical rfl rfl rfl built
    have entryRecords:=Records.of_earlier source entry plan ready slices (by intros;rfl) records
    have entryLocals : Locals entry plan index:=⟨locals.table,locals.records,locals.count,locals.index⟩
    have entryContext:=Context.of_control source entry plan slices stp pad scratch maximum rfl context
    have currentBound:=recordPrice_mono (slices index).2.toNat maximum index plan.count (context.lengthBound index inside) (Nat.le_of_lt inside)
    obtain ⟨key,slot,nextCount,next,slotInside,countLower,countUpper,bodyRun,bodyBuilt,bodyLocals,bodyRecords,bodyControl,bodyUpper,bodyLower,bodyOther,bodyMemory⟩:=
      record_step entry plan ready context.environment.domain scratch count index input logical bits small power entryBuilt processed inside entryLocals slices entryRecords stp pad
        entryContext.global entryContext.keccakCode entryContext.environment (context.buffers index inside) context.before context.aligned context.little
        entryContext.hashCode entryContext.copyCode entryContext.insertCode entryContext.memeqCode entryContext.findCode entryContext.setCode
        (by change recordPrice (slices index).2.toNat index≤source.clock-1;omega)
    have nextHistory : History plan (input++[(key,recordAddress plan index)]) := by
      simpa only [processed] using History.snoc input history key (by omega)
    have nextContext:=Context.of_control entry next plan slices stp pad scratch maximum bodyControl entryContext
    have bodyBudget : source.clock-1-recordPrice (slices index).2.toNat index≤next.clock:=bodyLower
    obtain ⟨finalCount,finalInput,finalLogical,target,tailRun,tailBuilt,tailHistory,tailLength,tailLocals,tailRecords,tailControl,tailUpper,tailLower,tailOther⟩:=
      ih next (index+1) nextCount (input++[(key,recordAddress plan index)]) (Placement.put logical slot key (recordAddress plan index)) (by omega)
        (by simp only [List.length_append,List.length_singleton,processed]) bodyBuilt nextHistory bodyLocals bodyRecords nextContext (by omega)
    refine ⟨finalCount,finalInput,finalLogical,target,?_,tailBuilt,tailHistory,tailLength,tailLocals,tailRecords,tailControl.trans bodyControl,?_,?_,?_⟩
    · have test:=Zero.tail_condition source index plan.count countSmall (by omega) locals.index locals.count
      change @evalHOLFinite 64 Guest.HostMemory _ source (fun address=>Classical.propDecidable (source.memaddrs address)) Constructor.condition=
        some (.val (.word (if index<plan.count then 1#64 else 0#64))) at test
      rw [if_pos inside] at test
      have unfolded:=evaluateHOLFiniteState_while_total source Constructor.condition recordBody
      rw [test] at unfolded
      simp only at unfolded
      rw [if_pos (show (1#64)≠(0:BitVec 64) by decide),if_neg (show source.clock≠0 by omega),bodyRun,
        StateSteps.fixed_clock entry next none bodyUpper] at unfolded
      exact unfolded.trans tailRun
    · change next.clock≤source.clock-1 at bodyUpper
      omega
    · simp only [Nat.mul_succ]
      omega
    · intro name different
      exact (tailOther name different).trans (bodyOther name different)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.record_loop
