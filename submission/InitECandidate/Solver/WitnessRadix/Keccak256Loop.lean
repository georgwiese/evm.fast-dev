import InitECandidate.Solver.WitnessRadix.Keccak256Context

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The entire literal full-block loop, from mapped input/state and actual
code/oracle/ABI facts. It spends exactly twenty source clocks per block. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer : BitVec 64) (index length rounds : Nat)
    (args : Args source stp pointer length) (code : Code source) (mapped : Mapped source stp pointer length)
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (small : length+136<2^64) (lower : index+136*rounds≤length) (upper : length<index+136*(rounds+1))
    (aligned : stp.toNat%8=0) (fits : stp.toNat+200<2^64) (enough : 20*rounds≤source.clock) :
    ∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source blocks=(none,output) ∧ output.clock=source.clock-20*rounds ∧
      KeccakAbsorb.hashControl output=KeccakAbsorb.hashControl source ∧
      output.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+136*rounds)))) ∧
      (∀ name : MlS, ofString "i"≠name → output.locals.lookup name=source.locals.lookup name) ∧
      ∀ query : BitVec 64, KeccakAbsorb.Away stp query → output.memory query=source.memory query := by
  classical
  induction rounds generalizing source index with
  | zero =>
    have testRun := condition_read source index length small (by omega) indexLocal args.lengthLocal
    have inactive : ¬index+136≤length := by omega
    simp only [if_neg inactive] at testRun
    refine ⟨source,?_,by simp,rfl,?_,?_,?_⟩
    · rw [blocks,evaluateHOLFiniteState_while_total,testRun]; simp
    · simpa using indexLocal
    · intro name different; rfl
    · intro query away; rfl
  | succ rounds ih =>
    have active : index+136≤length := by omega
    have positive : source.clock≠0 := by omega
    let entry := decClockHOLFinite source
    have entryControl : KeccakAbsorb.hashControl entry=KeccakAbsorb.hashControl source :=
      KeccakAbsorb.hashControl_clock source (source.clock-1)
    have entryArgs : Args entry stp pointer length := ⟨args.stateLocal,args.pointerLocal,args.lengthLocal⟩
    have entryCode := Code.of_control source entry entryControl code
    have entryMapped := mapped_of_control source entry stp pointer length entryControl mapped
    obtain ⟨next,bodyRun,bodyClock,bodyControl,bodyLocals,bodyMemory⟩ := block_execute entry stp pointer index length
      entryArgs entryCode entryMapped indexLocal active aligned fits (by change 19≤source.clock-1; omega)
    have nextArgs := Args.of_index entry next stp pointer length (BitVec.ofNat 64 (index+136)) bodyLocals entryArgs
    have nextCode := Code.of_control entry next bodyControl entryCode
    have nextMapped := mapped_of_control entry next stp pointer length bodyControl entryMapped
    have nextIndex : next.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+136)))) := by
      rw [bodyLocals,bind_lookup_same]
    have nextClock : next.clock=source.clock-20 := by
      rw [bodyClock]
      change source.clock-1-19=source.clock-20
      omega
    obtain ⟨output,tailRun,tailClock,tailControl,tailIndex,tailOther,tailMemory⟩ := ih next (index+136) nextArgs nextCode nextMapped nextIndex
      (by omega) (by omega) (by rw [nextClock]; omega)
    refine ⟨output,?_,?_,tailControl.trans (bodyControl.trans entryControl),?_,?_,?_⟩
    · have testRun := condition_read source index length small (by omega) indexLocal args.lengthLocal
      simp only [if_pos active] at testRun
      rw [blocks,evaluateHOLFiniteState_while_total,testRun]
      simp only [show (1#64 : BitVec 64)≠(0 : BitVec 64) from by decide,↓reduceIte,if_neg positive]
      rw [bodyRun,StateSteps.fixed_clock entry next none (by rw [bodyClock]; omega)]
      exact tailRun
    · rw [tailClock,nextClock]
      omega
    · have total : index+136+136*rounds=index+136*(rounds+1) := by omega
      simpa only [total] using tailIndex
    · intro name different
      rw [tailOther name different,bodyLocals]
      simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,entry,decClockHOLFinite]
    · intro query away
      exact (tailMemory query away).trans (bodyMemory query away)

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.loop_execute
