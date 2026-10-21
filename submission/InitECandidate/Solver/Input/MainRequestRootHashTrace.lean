import InitECandidate.Solver.Input.EvaluationOracle
import InitECandidate.Solver.Input.MainRequestRootHashContract
import InitECandidate.Solver.Input.RequestRootHashBudgetBound

namespace InitECandidate.Solver.Input.Main.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def sourcePrice (input : Guest.InputBlob) := 6129*(input.length%2^64-622)+271426

/-- Uniform actual main hashing caller allowance, charging one common input
budget across all payload, request and blob hashing data. -/
theorem call_cost_uniform (input : Guest.InputBlob) (current post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (actual : RequestRootHashData.Prepared input current root counts)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (entered current root) call=(result,post)) (notTimeout : result≠some .timeOut) :
    (entered current root).clock-post.clock≤sourcePrice input := by
  have priced := call_cost input current post root counts actual result run notTimeout
  have budget := RequestRootHashData.budget_price_bound (RequestRootHashData.description input counts) (input.length%2^64) (DecoderCall.witnessLength input) actual.budget
  exact priced.trans (Nat.add_le_add_right budget 1)

/-- Actual normal hashing facts at main's constructor continuation. The
preserved data refers to the same decoded origin, before root allocation. -/
structure Returned (input : Guest.InputBlob) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) : Prop where
  forward : current.clock≤(entered origin root).clock
  cost : (entered origin root).clock-current.clock≤sourcePrice input
  heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded root 32#64)))
  input : HashInput.Frame origin current inputPointer.toNat root.toNat
  locals : ∀ key,current.locals.lookup key=(entered origin root).locals.lookup key
  code : current.code=origin.code
  domain : current.memaddrs=origin.memaddrs
  exceptions : current.eshapes=origin.eshapes
  endian : current.be=origin.be
  globals : ∀ key,key≠ofString "heap_ptr" → current.globals.lookup key=origin.globals.lookup key
  workspace : SszHash.Workspace current 2713714688#64 2713714880#64 2713715312#64 2713715408#64
  oracle : current.ffi.oracle=origin.ffi.oracle

/-- The literal main hash sequence either stops within its hash allowance,
or reaches the original constructor continuation with actual heap, data,
locals, code and nonheap globals. Neither outcome assumes future success. -/
theorem after_root_trace (input : Guest.InputBlob) (origin post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (actual : RequestRootHashData.Prepared input origin root counts)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (entered origin root) afterRoot=(result,post)) (notTimeout : result≠some .timeOut) :
    (entered origin root).clock-post.clock≤sourcePrice input ∨
      ∃ current,Returned input origin current root ∧ evaluateHOLFiniteState current continuation=(result,post) := by
  rw [original_shape.2] at run
  have firstNotTimeout : (evaluateHOLFiniteState (entered origin root) call).1≠some .timeOut := by
    intro timed
    have whole := sequence_timeout (entered origin root) call continuation timed
    rw [run] at whole
    exact notTimeout whole
  have price := call_cost_uniform input origin (evaluateHOLFiniteState (entered origin root) call).2 root counts actual
    (evaluateHOLFiniteState (entered origin root) call).1 rfl firstNotTimeout
  have forward := evaluateHOLFiniteState_clock_le (entered origin root) call
  rw [evaluateHOLFiniteState_seq_line780] at run
  generalize observed : evaluateHOLFiniteState (entered origin root) call=output at price forward run
  obtain ⟨called,current⟩ := output
  cases called with
  | some stopped=>
    have endpoint : current=post := congrArg Prod.snd run
    subst post
    exact Or.inl price
  | none=>
    have fields := evaluation_fields (entered origin root) current call none observed
    have restored := call_normal input origin current root counts actual observed
    have globals (key : MlS) (different : key≠ofString "heap_ptr") : current.globals.lookup key=origin.globals.lookup key := by
      have pure := call_globals key (entered origin root).code actual.workspace.sha.installed different (entered origin root) rfl
      rw [observed] at pure
      have caller : (entered origin root).globals.lookup key=origin.globals.lookup key := by
        change (origin.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded root 32#64)))).lookup key=_
        simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      exact (congrArg Prod.snd pure).trans caller
    have workspace := actual.workspace.after (entered origin root) current 2713714688#64 2713714880#64 2713715312#64 2713715408#64 call none observed
      (fun key different=>call_globals key (entered origin root).code actual.workspace.sha.installed different)
    exact Or.inr ⟨current,⟨forward,price,restored.1,restored.2,
      fun key=>CallNormal.ignored_lookup (entered origin root) current key (ofString "htr_new_payload_request") arguments observed,
      fields.2.2.2,fields.1,fields.2.2.1,fields.2.1,globals,workspace,evaluation_oracle (entered origin root) current call none observed⟩,run⟩

end InitECandidate.Solver.Input.Main.RequestHash
#print axioms InitECandidate.Solver.Input.Main.RequestHash.call_cost_uniform
#print axioms InitECandidate.Solver.Input.Main.RequestHash.after_root_trace
