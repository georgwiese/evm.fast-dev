import InitECandidate.Solver.GuestWork.ChargeGasEntry

namespace InitECandidate.Solver.GuestWork.ChargeGasEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact source Work budget for the affordable path; the out-of-gas branch is
excluded by its actual evaluated comparison, not by replacing that branch. -/
theorem work {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (metadata offset heap globals frame gas amount : BitVec 64)
    (hmetadata : source.regs.lookup 25 = some (.word metadata))
    (hheap : source.regs.lookup 26 = some (.word heap))
    (hamount : source.regs.lookup 10 = some (.word amount))
    (metadataDomain : source.mdomain (metadata + 18446744073709551592#64) = true)
    (metadataValue : source.memory (metadata + 18446744073709551592#64) = .word offset)
    (globalsEq : (offset <<< (1 : Nat)) + heap = globals)
    (globalDomain : source.mdomain (globals + 18446744073709551360#64) = true)
    (globalValue : source.memory (globals + 18446744073709551360#64) = .word frame)
    (gasDomain : source.mdomain (frame + 64#64) = true)
    (gasValue : source.memory (frame + 64#64) = .word gas)
    (affordable : amount ≤ gas) : Work Named472.2 source 49 := by
  have available : amount.toNat ≤ gas.toNat := affordable
  have noUnderflow : ¬ gas < amount := by
    change ¬ gas.toNat < amount.toNat
    omega
  refine Work.seq (firstCredit := 1) (secondCredit := 48) (Work.basic (by decide)) ?_
  intro state0 run0
  simp [NamedBody472_0, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, wordShiftHOL, memLoad, setVar,
    hmetadata, hheap, hamount, metadataDomain, metadataValue, globalsEq,
    globalDomain, globalValue, gasDomain, gasValue,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run0
  subst state0
  refine Work.seq (firstCredit := 1) (secondCredit := 47) (Work.basic (by decide)) ?_
  intro state1 run1
  simp [NamedBody472_1, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, wordShiftHOL, memLoad, setVar,
    hmetadata, hheap, hamount, metadataDomain, metadataValue, globalsEq,
    globalDomain, globalValue, gasDomain, gasValue,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run1
  subst state1
  refine Work.seq (firstCredit := 1) (secondCredit := 46) (Work.basic (by decide)) ?_
  intro state2 run2
  simp [NamedBody472_2, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, wordShiftHOL, memLoad, setVar,
    hmetadata, hheap, hamount, metadataDomain, metadataValue, globalsEq,
    globalDomain, globalValue, gasDomain, gasValue,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run2
  subst state2
  refine Work.seq (firstCredit := 1) (secondCredit := 45) (Work.basic (by decide)) ?_
  intro state3 run3
  simp [NamedBody472_3, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, wordShiftHOL, memLoad, setVar,
    hmetadata, hheap, hamount, metadataDomain, metadataValue, globalsEq,
    globalDomain, globalValue, gasDomain, gasValue,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run3
  subst state3
  refine Work.seq (firstCredit := 1) (secondCredit := 44) (Work.basic (by decide)) ?_
  intro state4 run4
  simp [NamedBody472_4, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, wordShiftHOL, memLoad, setVar,
    hmetadata, hheap, hamount, metadataDomain, metadataValue, globalsEq,
    globalDomain, globalValue, gasDomain, gasValue,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run4
  subst state4
  refine Work.seq (firstCredit := 1) (secondCredit := 43) (Work.basic (by decide)) ?_
  intro state5 run5
  simp [NamedBody472_5, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, wordShiftHOL, memLoad, setVar,
    hmetadata, hheap, hamount, metadataDomain, metadataValue, globalsEq,
    globalDomain, globalValue, gasDomain, gasValue,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run5
  subst state5
  refine Work.seq (firstCredit := 1) (secondCredit := 42) (Work.basic (by decide)) ?_
  intro state6 run6
  simp [NamedBody472_6, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, wordShiftHOL, memLoad, setVar,
    hmetadata, hheap, hamount, metadataDomain, metadataValue, globalsEq,
    globalDomain, globalValue, gasDomain, gasValue,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run6
  subst state6
  refine Work.seq (firstCredit := 1) (secondCredit := 41) (Work.basic (by decide)) ?_
  intro state7 run7
  simp [NamedBody472_7, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, wordShiftHOL, memLoad, setVar,
    hmetadata, hheap, hamount, metadataDomain, metadataValue, globalsEq,
    globalDomain, globalValue, gasDomain, gasValue,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run7
  subst state7
  refine Work.seq (firstCredit := 2) (secondCredit := 39) ?_ ?_
  · apply Work.ite (credits := 1)
    · intro chosen
      simp [branchChoice, StackSemStateOps.getVar, StackSemStateOps.getVarImm,
        Flapjack.Compiler.Encoders.Asm.HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL,
        hamount, noUnderflow, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at chosen
    · intro _
      exact Work.basic (by decide)
  · intro next _
    exact ChargeGasTail.body_work next

end InitECandidate.Solver.GuestWork.ChargeGasEntry
#print axioms InitECandidate.Solver.GuestWork.ChargeGasEntry.work
