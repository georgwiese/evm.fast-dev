import InitECandidate.Solver.CrepToLoopBound.Common
import InitECandidate.Solver.CrepToLoopBound.ExpressionSimulation
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Dec

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem simulateDec {width : Nat} [NeZero width] {σ : Type} (limit : Nat) :
    ∀ (name : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width)
      (v1 : CrepSemHOLState width σ),
      CodeSafe limit v1.code → ceiling (.dec name e body) ≤ limit →
      (∀ value, evalCrepSemHOLExp v1 e = some value →
        Simulation limit body
          { v1 with locals := v1.locals.updateEq (name, value) }) →
    ∀ (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.dec name e body) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        ck ≤ (2 * limit + 3) * (v1.clock - s1.clock) + cost (.dec name e body) ∧
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.dec name e body))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = resultToLoop res ∧
        localsResultRel ctxt l res s1 t1 := by
  intro name e body v1 safe bounded ih res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  rw [evalCrepSemHOLProgExact_dec_holShape] at he
  cases hev : evalCrepSemHOLExp v1 e with
  | none =>
      simp only [hev, Prod.mk.injEq] at he
      exact absurd he.1.symm hne
  | some value =>
      simp only [hev] at he
      let sourceBody : CrepSemHOLState width σ :=
        { v1 with locals := v1.locals.updateEq (name, value) }
      cases hBody : evalCrepSemHOLProgExact sourceBody body with
      | mk bodyResult bodyState =>
        rw [hBody] at he
        simp only [Prod.mk.injEq] at he
        rcases he with ⟨hResult, hFinal⟩
        have hBodyEval : evalCrepSemHOLProgExact sourceBody body = (bodyResult, bodyState) := hBody
        rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with
          ⟨codePrefix, compiledValue, temporary, nextLive⟩
        obtain ⟨prefixClock, prefixState, prefixBudget, hPrefix, hValue, hPrefixState,
          hPrefixMem, hPrefixGlobals, hPrefixCode, hPrefixLocals⟩ :=
          expressionSimulation v1 e value t ctxt (ctxt.vmax + 1) l
            codePrefix compiledValue temporary nextLive
            ⟨hev, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
        obtain ⟨hNoContext, hTempBound, hNextLive⟩ :=
          compile_exp_out_rel ctxt (ctxt.vmax + 1) l e codePrefix compiledValue temporary nextLive hC
        have hLiveNext : ∀ k, sptMem k l → sptMem k nextLive := by
          intro k hk
          rw [hNextLive]
          exact cut_sets_union_domain_subset _ l hNoContext k hk
        have hLocalsBefore : crepToLoopLocalsRelExact ctxt l v1.locals prefixState.locals := by
          refine ⟨hPrefixLocals.1, hPrefixLocals.2.1, ?_, ?_⟩
          intro k hk
          exact hPrefixLocals.2.2.1 k (hLiveNext k hk)
          intro key val hval
          obtain ⟨n, hmap, hmem, _⟩ := hl.2.2.2 key val hval
          obtain ⟨n', hmap', _, hslot⟩ := hPrefixLocals.2.2.2 key val hval
          have hn : n' = n := Option.some.inj (hmap'.symm.trans hmap)
          subst n'
          exact ⟨n, hmap', hmem, hslot⟩
        have hFresh : ctxt.vmax < temporary := by omega
        let bodyCtxt : CrepToLoopContextExact :=
          { ctxt with vars := ctxt.vars.updateEq (name, temporary), vmax := temporary }
        let bodyLive : NumSet := sptInsert temporary () l
        let targetBody : LoopSemStateFiniteExact width σ :=
          LoopSemStateFiniteExact.setVar temporary (wlabWlocExact value) prefixState
        have hBodyLocals : crepToLoopLocalsRelExact bodyCtxt bodyLive
            sourceBody.locals targetBody.locals := by
          have hw : (wlabWlocExact : HolWordLab width → WordLocW width) = wlabWlocHOL := by
            funext v
            cases v
            rfl
          have hEntered := crepToLoopNcompileDecLocalsEnter ctxt l v1.locals prefixState.locals
            name temporary value hLocalsBefore hFresh
          rw [← hw] at hEntered
          simpa [sourceBody, targetBody, bodyLive, bodyCtxt, CrepSemHOLState.setVar,
            LoopSemStateFiniteExact.setVar] using hEntered
        have hBodyState : crepToLoopStateRelExact sourceBody targetBody := by
          simpa [sourceBody, targetBody, crepToLoopStateRelExact,
            LoopSemStateFiniteExact.setVar] using hPrefixState
        have hBodyMem : crepToLoopMemRelHOLExact sourceBody.memory targetBody.memory
            sourceBody.memaddrs := by
          simpa [sourceBody, targetBody, LoopSemStateFiniteExact.setVar] using hPrefixMem
        have hBodyGlobals : crepToLoopGlobalsRelHOLExact sourceBody.globals targetBody.globals := by
          simpa [sourceBody, targetBody, LoopSemStateFiniteExact.setVar] using hPrefixGlobals
        have hBodyCode : crepToLoopCodeRelExact bodyCtxt sourceBody.code targetBody.code := by
          simpa [sourceBody, targetBody, bodyCtxt, crepToLoopCodeRelExact,
            LoopSemStateFiniteExact.setVar] using hPrefixCode
        have hBodyNotError : bodyResult ≠ some .error := by
          intro herr
          apply hne
          rw [← hResult]
          exact herr
        let bodyIH := ih value hev
        obtain ⟨bodyClock, targetResult, targetFinal, bodyBudget, hTargetBodyEval,
          hFinalStateBody, hFinalMemBody, hFinalGlobalsBody, hFinalCodeBody,
          hResultBody, hLocalsBody⟩ :=
          bodyIH safe (decCeiling name e body limit bounded) bodyResult bodyState targetBody bodyCtxt bodyLive
            hBodyEval hBodyNotError hBodyState hBodyMem hBodyGlobals
              hBodyCode hBodyLocals
        have hCompile : compileHOLExact ctxt l (.dec name e body) =
            .seq (loopNestedSeqHOL codePrefix)
              (.seq (.assign temporary compiledValue)
                (compileHOLExact bodyCtxt bodyLive body)) := by
          rw [compileHOLExact, hC]
        have hPrefixLift : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL codePrefix)
            { t with clock := t.clock + (prefixClock + bodyClock) } =
              (none, { prefixState with clock := prefixState.clock + bodyClock }) := by
          have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
            (loopNestedSeqHOL codePrefix) { t with clock := t.clock + prefixClock }
            none prefixState bodyClock hPrefix (by simp)
          simpa [Nat.add_assoc] using hLift
        have hAssignEval : LoopSemStateFiniteExact.evaluate (.assign temporary compiledValue)
            { prefixState with clock := prefixState.clock + bodyClock } =
              (none, { targetBody with clock := targetBody.clock + bodyClock }) := by
          rw [LoopSemStateFiniteExact.evaluate.eq_3]
          simp [LoopSemStateFiniteExact.eval_upd_clock_eq, hValue, targetBody,
            LoopSemStateFiniteExact.setVar]
        have hRun : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.dec name e body))
            { t with clock := t.clock + (prefixClock + bodyClock) } = (targetResult, targetFinal) := by
          rw [hCompile]
          simp only [LoopSemStateFiniteExact.evaluate_seq, hPrefixLift]
          rw [hAssignEval]
          exact hTargetBodyEval
        have hResultFinal : targetResult = resultToLoop res := by
          calc
            targetResult = resultToLoop bodyResult := hResultBody
            _ = resultToLoop res := by rw [← hResult]
        have hSourceFinalLocals : s1.locals =
            bodyState.locals.resVarEq (name, v1.locals.lookup name) := by
          have hLocalsEq := congrArg (fun state : CrepSemHOLState width σ => state.locals) hFinal
          simpa [sourceBody] using hLocalsEq.symm
        have hMakePreserve : UnassignedGoodRes targetResult → ∀ n old,
            ctxt.vars.lookup name = some n → v1.locals.lookup name = some old →
              sptLookup n targetFinal.locals = sptLookup n prefixState.locals := by
          intro hGood n old hname hOld
          have hmax := hLocalsBefore.2.1 name n hname
          have hneTmp : n ≠ temporary := by omega
          obtain ⟨mapped, hmap, hmem, hslot⟩ :=
            hLocalsBefore.2.2.2 name old hOld
          have hmapped : mapped = n := Option.some.inj (hmap.symm.trans hname)
          subst mapped
          have hslotTarget : sptLookup n targetBody.locals = some (wlabWlocHOL old) := by
            simpa [targetBody, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert,
              hneTmp, wlabWlocExact, wlabWlocHOL] using hslot
          have hNotAssigned : n ∉ holLoopAssignedVars
              (compileHOLExact bodyCtxt bodyLive body) := by
            apply not_mem_context_assigned_mem_gt bodyCtxt bodyLive body n
            refine ⟨hBodyLocals.2.1, ?_, ?_⟩
            · intro var mapped hlookup
              by_cases hvar : var = name
              · subst var
                have hmapped : temporary = mapped := by
                  simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hlookup
                omega
              · have hlookupOld : ctxt.vars.lookup var = some mapped := by
                  simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hvar] using hlookup
                intro heq
                have hsame := hLocalsBefore.1 name var n mapped hname hlookupOld heq
                exact hvar hsame.symm
            · have hnle : n ≤ ctxt.vmax := hmax
              have hnleBody : n ≤ bodyCtxt.vmax := by
                simpa [bodyCtxt] using (Nat.le_trans hnle (Nat.le_of_lt hFresh))
              exact hnleBody
          have hLive : (sptLookup n bodyLive).isSome = true := by
            exact (sptMem_sptInsert n temporary () l).mpr (Or.inr hmem)
          have hSurvives : survivesHOLExact n
              (compileHOLExact bodyCtxt bodyLive body) = true :=
            member_cutset_survives_comp_prog bodyCtxt bodyLive body n hLive
          have hRunPreserved := unassigned_vars_evaluate_same
            (compileHOLExact bodyCtxt bodyLive body)
            { targetBody with clock := targetBody.clock + bodyClock }
            targetResult targetFinal n (wlabWlocHOL old)
            ⟨hTargetBodyEval, hGood, by
              simpa [targetBody, LoopSemStateFiniteExact.setVar] using hslotTarget,
              hNotAssigned, hSurvives⟩
          have hslotInitial : sptLookup n prefixState.locals = some (wlabWlocHOL old) := hslot
          calc
            sptLookup n targetFinal.locals = sptLookup n targetBody.locals := hRunPreserved
            _ = sptLookup n prefixState.locals := hslotTarget.trans hslotInitial.symm
        have hFinalLocals : localsResultRel ctxt l res s1 targetFinal := by
          cases res with
          | none =>
              have hGood : UnassignedGoodRes targetResult := by
                simp [hResultFinal, resultToLoop, UnassignedGoodRes]
              have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                  bodyState.locals targetFinal.locals := by
                  simpa [localsResultRel, hResultBody, hResult] using hLocalsBody
              exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                (hMakePreserve hGood)
          | some result =>
              cases result with
              | «break» n =>
                  have hGood : UnassignedGoodRes targetResult := by
                    simp [hResultFinal, resultToLoop, UnassignedGoodRes]
                  have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                      bodyState.locals targetFinal.locals := by
                    simpa [localsResultRel, hResultBody, hResult] using hLocalsBody
                  exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                    v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                    hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                    (hMakePreserve hGood)
              | «continue» n =>
                  have hGood : UnassignedGoodRes targetResult := by
                    simp [hResultFinal, resultToLoop, UnassignedGoodRes]
                  have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                      bodyState.locals targetFinal.locals := by
                    simpa [localsResultRel, hResultBody, hResult] using hLocalsBody
                  exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                    v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                    hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                    (hMakePreserve hGood)
              | «return» _ => trivial
              | exception _ => trivial
              | timeOut => trivial
              | finalFfi _ => trivial
              | error =>
                  exfalso
                  apply hne
                  rw [← hResult]
        have finalClock : bodyState.clock = s1.clock := by
          rw [← hFinal]
        have totalBudget : prefixClock + bodyClock ≤
            (2 * limit + 3) * (v1.clock - s1.clock) + cost (.dec name e body) := by
          change bodyClock ≤ (2 * limit + 3) * (v1.clock - bodyState.clock) + cost body at bodyBudget
          rw [finalClock] at bodyBudget
          simp only [cost]
          omega
        refine ⟨prefixClock + bodyClock, targetResult, targetFinal, totalBudget, hRun, ?_, ?_, ?_, ?_, hResultFinal,
          hFinalLocals⟩
        · rw [← hFinal]
          simpa [crepToLoopStateRelExact] using hFinalStateBody
        · rw [← hFinal]
          simpa using hFinalMemBody
        · rw [← hFinal]
          simpa using hFinalGlobalsBody
        · rw [← hFinal]
          simpa [crepToLoopCodeRelExact, bodyCtxt] using hFinalCodeBody

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.simulateDec
