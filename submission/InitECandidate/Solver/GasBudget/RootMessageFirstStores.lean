import InitECandidate.Solver.GasBudget.RootMessageInitialProgram

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- All four actual message stores preceding MSG_GAS. Scalar-load width
follows from its real expression; other widths follow from saved scalar
bindings. Earlier input/transaction records and all nonmemory fields survive. -/
theorem first_stores_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) (start : Nat)
    (blockEnv txEnv sender : HolWordLab 64) (region : MemoryRegion.Valid ⟨start, 176⟩)
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))))
    (blockLocal : source.globals.lookup (ofString "be") = some (.val blockEnv))
    (txLocal : source.locals.lookup (ofString "te") = some (.val txEnv))
    (senderLocal : source.locals.lookup (ofString "sender") = some (.val sender))
    (normal : evaluateHOLFiniteState source beforeGas = (some (.returned value), post)) :
    ∃ ready : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState ready RootCaller.msgGasSite = (some (.returned value), post) ∧ ready = {source with memory := ready.memory} ∧
      ∀ query : BitVec 64, query.toNat < start ∨ start + 176 ≤ query.toNat → ready.memory query = source.memory query := by
  rw [beforeGas] at normal
  have safe0 : Input.LocalPrefix (ofString "m") (MessageField.store 0 (.var .global (ofString "be"))) := .store _ _
  obtain ⟨first, firstRun, firstRest, _⟩ := safe0.normal_continue source post _ value normal
  obtain ⟨firstFrame, firstOutside, _⟩ := MessageField.normal_frame source first start 0 1 (.var .global (ofString "be")) region (by decide) messageLocal
    (fun actual read => Nat.le_of_eq (Input.global_one_length source "be" blockEnv actual blockLocal read)) firstRun
  have firstMessage : first.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) := by rw [firstFrame]; exact messageLocal
  have firstTx : first.locals.lookup (ofString "te") = some (.val txEnv) := by rw [firstFrame]; exact txLocal
  have safe8 : Input.LocalPrefix (ofString "m") (MessageField.store 8 (localVar "te")) := .store _ _
  obtain ⟨second, secondRun, secondRest, _⟩ := safe8.normal_continue first post _ value firstRest
  obtain ⟨secondFrame, secondOutside, _⟩ := MessageField.normal_frame first second start 8 1 (localVar "te") region (by decide) firstMessage
    (fun actual read => Nat.le_of_eq (Input.local_one_length first "te" txEnv actual firstTx read)) secondRun
  have secondMessage : second.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) := by rw [secondFrame, firstFrame]; exact messageLocal
  have secondSender : second.locals.lookup (ofString "sender") = some (.val sender) := by rw [secondFrame, firstFrame]; exact senderLocal
  have safe16 : Input.LocalPrefix (ofString "m") (MessageField.store 16 (localVar "sender")) := .store _ _
  obtain ⟨third, thirdRun, thirdRest, _⟩ := safe16.normal_continue second post _ value secondRest
  obtain ⟨thirdFrame, thirdOutside, _⟩ := MessageField.normal_frame second third start 16 1 (localVar "sender") region (by decide) secondMessage
    (fun actual read => Nat.le_of_eq (Input.local_one_length second "sender" sender actual secondSender read)) thirdRun
  have thirdMessage : third.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) := by rw [thirdFrame, secondFrame, firstFrame]; exact messageLocal
  have safe24 : Input.LocalPrefix (ofString "m") (MessageField.store 24 recipientExpression) := .store _ _
  obtain ⟨ready, fourthRun, fourthRest, _⟩ := safe24.normal_continue third post _ value thirdRest
  obtain ⟨fourthFrame, fourthOutside, _⟩ := MessageField.normal_frame third ready start 24 1 recipientExpression region (by decide) thirdMessage
    (fun actual read => Nat.le_of_eq (Input.load1_length third _ actual read)) fourthRun
  have frame12 := secondFrame.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := second.memory}) firstFrame)
  have frame123 := thirdFrame.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := third.memory}) frame12)
  have frame := fourthFrame.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := ready.memory}) frame123)
  refine ⟨ready, fourthRest, frame, ?_⟩
  intro query outside
  exact (fourthOutside query outside).trans ((thirdOutside query outside).trans ((secondOutside query outside).trans (firstOutside query outside)))

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.first_stores_normal
