import InitECandidate.Solver.MutableTable.DeleteHeader

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

/-- The whole actual present-deletion suffix: seven header declarations,
real inverse-position read, deleted_pos/j setup, scan, final mutation and
all nine declaration restorations. -/
theorem present_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots) (deleted : Fin slots.length)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (slots.get deleted)))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : scanPrice kind * (slots.length - 1) + 1 ≤ source.clock) :
    ∃ paid memory target next, paid ≤ scanPrice kind * (slots.length - 1) + 1 ∧
      evaluateHOLFiniteState source (program headerActions afterHeaders) = (some (.returned (.val (.word 1#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      next.length = slots.length - 1 ∧ MemoryModel.Header memory kind plan (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind plan next := by
  let hs := headerState source kind plan
  let ds := bind hs "deleted_pos" (BitVec.ofNat 64 deleted.val)
  let js := bind ds "j" (BitVec.ofNat 64 (slots.get deleted))
  have hI : hs.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (slots.get deleted)))) :=
    (header_other source kind plan "i" (by intro saved member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans indexLocal
  have hT : hs.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) :=
    (header_other source kind plan "t" (by intro saved member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans tableLocal
  have hCap : hs.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))) :=
    (header_other source kind plan "cap" (by intro saved member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans capLocal
  have getHeader (name : String) (word : BitVec 64) (member : (name, word) ∈ headerValues kind plan) :
      js.locals.lookup (ofString name) = some (.val (.word word)) := by
    have away : ofString "j" ≠ ofString name ∧ ofString "deleted_pos" ≠ ofString name := by
      simp only [headerValues, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> constructor <;> decide
    exact (bind_lookup_other _ "j" name _ away.1).trans ((bind_lookup_other _ "deleted_pos" name _ away.2).trans (header_lookup source kind plan name word member))
  have scanLocals : ScanLocals js kind plan (slots.get deleted) (slots.get deleted) :=
    ⟨⟨getHeader "keys" _ (by simp [headerValues]), getHeader "vals" _ (by simp [headerValues]),
      getHeader "order" _ (by simp [headerValues]), getHeader "order_pos" _ (by simp [headerValues]),
      getHeader "klen" _ (by simp [headerValues]), getHeader "stride" _ (by simp [headerValues]),
      (bind_lookup_other _ "j" "i" _ (by decide)).trans ((bind_lookup_other _ "deleted_pos" "i" _ (by decide)).trans hI),
      bind_lookup_same _ _ _⟩,
      (bind_lookup_other _ "j" "cap" _ (by decide)).trans ((bind_lookup_other _ "deleted_pos" "cap" _ (by decide)).trans hCap),
      getHeader "used" _ (by simp [headerValues])⟩
  have jsT : js.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) :=
    (bind_lookup_other _ "j" "t" _ (by decide)).trans ((bind_lookup_other _ "deleted_pos" "t" _ (by decide)).trans hT)
  have jsDeleted : js.locals.lookup (ofString "deleted_pos") = some (.val (.word (BitVec.ofNat 64 deleted.val))) :=
    (bind_lookup_other _ "j" "deleted_pos" _ (by decide)).trans (bind_lookup_same _ _ _)
  have entryModel := MemoryModel.Occupied.of_fields source js kind plan slots occupied rfl rfl rfl
  obtain ⟨paid, memory, target, next, bounded, actual, frame, length, nextHeader, nextModel⟩ :=
    scan_finish js kind plan valid domain little slots room entryModel deleted bits small power scanLocals header jsT jsDeleted hashCode copyCode enough
  have slotInside := occupied.inside _ (List.get_mem slots deleted)
  have positionMapped : hs.memaddrs (cell plan .position 0 + BitVec.ofNat 64 (slots.get deleted) * 8#64) := by
    rw [Move.natural_word_address kind plan valid .position _ slotInside]
    change source.memaddrs _
    rw [domain]
    exact mapped kind plan valid .position _ (by change 8 * slots.get deleted < 8 * plan.capacity; omega) (by omega)
  have positionCell : hs.memory (cell plan .position 0 + BitVec.ofNat 64 (slots.get deleted) * 8#64) = .word (BitVec.ofNat 64 deleted.val) := by
    rw [Move.natural_word_address kind plan valid .position _ slotInside]
    exact occupied.position deleted
  have positionRead := Move.word_read hs "order_pos" "i" _ _ (BitVec.ofNat 64 deleted.val)
    (header_lookup source kind plan "order_pos" _ (by simp [headerValues])) hI positionMapped positionCell
  have dI : ds.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (slots.get deleted)))) := (bind_lookup_other _ "deleted_pos" "i" _ (by decide)).trans hI
  have jRead : eval ds (localVar "i") = some (.val (.word (BitVec.ofNat 64 (slots.get deleted)))) := by
    simp only [eval, localVar, evalHOLExact, toExact, dI]
  have jRun := Input.ScalarScope.declare_execute ds target "j" (localVar "i") (BitVec.ofNat 64 (slots.get deleted)) (.seq loop afterLoop) _ jRead actual
  have dRun := Input.ScalarScope.declare_execute hs _ "deleted_pos" (Delete.positionRead "i") (BitVec.ofNat 64 deleted.val)
    (.dec (ofString "j") .one (localVar "i") (.seq loop afterLoop)) _ positionRead jRun
  obtain ⟨restoreStack, setup⟩ := header_executes source kind plan valid domain _ header tableLocal
  have prefixRun := ProgramPrefix.execute setup afterHeaders
  change evaluateHOLFiniteState hs afterHeaders = (some (.returned (.val (.word 1#64))), restore hs "deleted_pos" (restore ds "j" target)) at dRun
  rw [dRun] at prefixRun
  let output := restoreStack (restore hs "deleted_pos" (restore ds "j" target))
  refine ⟨paid, memory, output, next, bounded, prefixRun, ?_, length, nextHeader, ?_⟩
  · rw [ProgramPrefix.restoration_frame setup]
    exact frame
  · have restoredFrame := ProgramPrefix.restoration_frame setup (restore hs "deleted_pos" (restore ds "j" target))
    have memoryEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) restoredFrame
    have domainEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) restoredFrame
    have endianEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) restoredFrame
    exact MemoryModel.Occupied.of_fields target output kind plan next nextModel memoryEq.symm domainEq.symm endianEq.symm

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.present_execute
