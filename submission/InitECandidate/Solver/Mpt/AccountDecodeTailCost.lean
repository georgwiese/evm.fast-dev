import InitECandidate.Solver.Mpt.AccountDecodeBalanceCost
import InitECandidate.Solver.Input.StoreWordsNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def nonceSetup : ProgHOL 64 := .dec (ofString "nonce") .one (.const 0#64)
  (.dec (ofString "i") .one (.const 0#64) (.seq nonceLoop afterNonce))

theorem after_nonce_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer header payload flag : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (cell : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag))
    (output : Output out) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterNonce).2.clock≤36 := by
  rw [after_nonce_shape]
  have priced := Input.ClockCost.sequence_reached_current source
    (.store (.op .add [localVar "acct_out",.const 0#64]) (localVar "nonce"))
    (.seq (.ite (.cmp .lower (.const 32#64) (field "f1" 2)) (fail 22#64) .skip) balancePhase) 0 36
    (Input.ClockCost.store source.code _ _ source rfl) ?_
  · simpa only [Nat.zero_add] using priced
  · intro middle normal
    have addressRead : eval source (.op .add [localVar "acct_out",.const 0#64])=some (.val (.word out)) := by
      simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,outputCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    obtain ⟨value,memory,valueRead,stores,same⟩ := Input.store_at_normal source middle _ _ out addressRead normal
    have currentCell : middle.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag) := by rw [same]; exact cell
    have currentOutput : middle.locals.lookup (ofString "acct_out")=some (.val (.word out)) := by rw [same]; exact outputCell
    have currentDomain : middle.memaddrs=InitE.ordinaryDomain := by rw [same]; exact domain
    have currentInstalled : Input.OriginalCode.Installed middle.code := by rw [same]; exact installed
    have guardCost := Fail.guard_reached_cost middle (.cmp .lower (.const 32#64) (field "f1" 2)) 22#64 balancePhase 36 currentInstalled ?_
    · exact guardCost
    · intro passed
      have bounded := Fail.lower_guard_bound middle middle (.const 32#64) (field "f1" 2) 32#64 payload [.const 22#64]
        rfl (payload_read middle "f1" pointer header payload flag currentCell) currentInstalled passed
      have tailCost := balance_phase_cost middle out pointer header payload flag currentOutput currentCell output currentDomain currentInstalled
      change payload.toNat≤32 at bounded
      omega

theorem nonce_setup_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer0 header0 payload0 flag0 pointer1 header1 payload1 flag1 : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (cell0 : source.locals.lookup (ofString "f0")=some (Rlp.Item.result pointer0 header0 payload0 flag0))
    (cell1 : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1))
    (small : payload0.toNat≤8) (output : Output out) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code) : source.clock-(evaluateHOLFiniteState source nonceSetup).2.clock≤44 := by
  let entered := bind (bind source "nonce" 0#64) "i" 0#64
  have current0 : entered.locals.lookup (ofString "f0")=some (Rlp.Item.result pointer0 header0 payload0 flag0) :=
    (bind_lookup_other _ "i" "f0" _ (by decide)).trans ((bind_lookup_other _ "nonce" "f0" _ (by decide)).trans cell0)
  have current1 : entered.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1) :=
    (bind_lookup_other _ "i" "f1" _ (by decide)).trans ((bind_lookup_other _ "nonce" "f1" _ (by decide)).trans cell1)
  have currentOutput : entered.locals.lookup (ofString "acct_out")=some (.val (.word out)) :=
    (bind_lookup_other _ "i" "acct_out" _ (by decide)).trans ((bind_lookup_other _ "nonce" "acct_out" _ (by decide)).trans outputCell)
  have loopCost := nonce_loop_cost entered pointer0 header0 payload0 flag0 0#64 current0 (bind_lookup_same _ _ _) (by simp)
  have suffix := Input.ClockCost.sequence_reached_current entered nonceLoop afterNonce 8 36 (by simpa using loopCost.trans (by simpa using small)) ?_
  · rw [nonceSetup]
    apply Input.ClockCost.declared_current source "nonce" (.const 0#64) 0#64 _ 44 rfl
    apply Input.ClockCost.declared_current (bind source "nonce" 0#64) "i" (.const 0#64) 0#64 _ 44 rfl
    exact suffix
  · intro middle normal
    have safe1 : Input.LocalPrefix (ofString "f1") nonceLoop := by
      rw [nonce_loop_shape,nonce_body_shape]
      exact .loop _ (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide)))
    have safeOutput : Input.LocalPrefix (ofString "acct_out") nonceLoop := by
      rw [nonce_loop_shape,nonce_body_shape]
      exact .loop _ (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide)))
    have preserved1 := safe1.summary_full entered
    have preservedOutput := safeOutput.summary_full entered
    unfold Input.LocalSummary at preserved1 preservedOutput
    rw [normal] at preserved1 preservedOutput
    have next1 := (preserved1.1 rfl).trans current1
    have nextOutput := (preservedOutput.1 rfl).trans currentOutput
    have fields := Input.evaluation_fields entered middle nonceLoop none normal
    have nextDomain : middle.memaddrs=InitE.ordinaryDomain := fields.1.trans domain
    have nextInstalled : Input.OriginalCode.Installed middle.code := by rw [fields.2.2.2]; exact installed
    exact after_nonce_cost middle out pointer1 header1 payload1 flag1 nextOutput next1 output nextDomain nextInstalled

/-- Original post-field decoding, including either MPT failure guard, both
bounded byte loops, real balance clearing and both root/hash alternatives.
All outcomes are priced from current decoded words/output geometry. -/
theorem after_fields_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer0 header0 payload0 flag0 pointer1 header1 payload1 flag1 : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (cell0 : source.locals.lookup (ofString "f0")=some (Rlp.Item.result pointer0 header0 payload0 flag0))
    (cell1 : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1))
    (output : Output out) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterFields).2.clock≤44 := by
  have nonceCost := Fail.guard_reached_cost source (.cmp .lower (.const 8#64) (field "f0" 2)) 21#64 nonceSetup 44 installed ?_
  · rw [after_fields_shape]
    have allCost := Fail.guard_reached_cost source
      (.cmp .notEqual (.op .or [field "f0" 0,field "f1" 0,field "f2" 0,field "f3" 0]) (.const 0#64)) 20#64
      (.seq (.ite (.cmp .lower (.const 8#64) (field "f0" 2)) (fail 21#64) .skip) nonceSetup) 44 installed (by intro passed; exact nonceCost)
    exact allCost
  · intro passed
    have bounded := Fail.lower_guard_bound source source (.const 8#64) (field "f0" 2) 8#64 payload0 [.const 21#64]
      rfl (payload_read source "f0" pointer0 header0 payload0 flag0 cell0) installed passed
    exact nonce_setup_cost source out pointer0 header0 payload0 flag0 pointer1 header1 payload1 flag1 outputCell cell0 cell1 bounded output domain installed

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_nonce_cost
#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_setup_cost
#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_fields_cost
