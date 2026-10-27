import InitECandidate.Solver.Input.SharedRead

namespace InitECandidate.Solver.Input.SharedRead
open Flapjack

/-- A successful actual read supplies presence of every requested byte. -/
theorem mapM_present (host : Guest.HostMemory) (address : BitVec 64) (offsets : List Nat)
    (values : List UInt8)
    (read : offsets.mapM (fun offset => host (address + BitVec.ofNat 64 offset)) = some values) :
    ∀ offset ∈ offsets, (host (address + BitVec.ofNat 64 offset)).isSome = true := by
  induction offsets generalizing values with
  | nil => simp
  | cons first rest ih =>
    cases headRead : host (address + BitVec.ofNat 64 first) with
    | none => simp [List.mapM_cons, headRead] at read
    | some byte =>
      cases tailRead : rest.mapM (fun offset => host (address + BitVec.ofNat 64 offset)) with
      | none => simp [List.mapM_cons, headRead, tailRead] at read
      | some tail =>
        intro offset member
        rcases List.mem_cons.mp member with same | member
        · subst offset
          simp [headRead]
        · exact ih tail tailRead offset member

/-- The current oracle cannot return normally from a word read with an absent
byte. This derives presence from the observed reply, including malformed input. -/
theorem oracle_return_present (host next : Guest.HostMemory) (address : BitVec 64)
    (answer : List (BitVec 8))
    (reply : InitE.sourceOracle (.sharedMem .mappedRead) host [0#8]
      (panWordToBytesHOL address false) = .ret next answer) :
    ∀ offset < 8, (host (address + BitVec.ofNat 64 offset)).isSome = true := by
  have configZero : (bitsToByte (0#8)).toNat = 0 := rfl
  cases read : (List.range 8).mapM (fun offset => host (address + BitVec.ofNat 64 offset)) with
  | none =>
    simp [InitE.sourceOracle, Guest.guestOracle, Guest.sharedWidth,
      WordCodec.oracle_address, configZero, read] at reply
  | some values =>
    intro offset inside
    exact mapM_present host address (List.range 8) values read offset (List.mem_range.mpr inside)

/-- A real normal word-read reply retains the current host and returns exactly
the eight bytes that were present at that address. -/
theorem oracle_return_data (host next : Guest.HostMemory) (address : BitVec 64)
    (answer : List (BitVec 8))
    (reply : InitE.sourceOracle (.sharedMem .mappedRead) host [0#8]
      (panWordToBytesHOL address false) = .ret next answer) :
    next = host ∧ answer = (bytes host address).map byteToBits := by
  have present := oracle_return_present host next address answer reply
  have same := HolOracleResult.ret.inj ((oracle host address present).symm.trans reply)
  exact ⟨same.1.symm, same.2.symm⟩

/-- Invert the real FFI wrapper, including its returned-length check. -/
theorem ffi_return_oracle (source next : HolFfiState Guest.HostMemory) (address : BitVec 64)
    (answer : List (BitVec 8))
    (read : callFFIHOL source (.sharedMem .mappedRead) [0#8]
      (panWordToBytesHOL address false) = .ret next answer) :
    ∃ host, source.oracle (.sharedMem .mappedRead) source.ffiState [0#8]
      (panWordToBytesHOL address false) = .ret host answer ∧ next.ffiState = host := by
  cases reply : source.oracle (.sharedMem .mappedRead) source.ffiState [0#8]
      (panWordToBytesHOL address false) with
  | final outcome => simp [callFFIHOL, reply] at read
  | ret host values =>
    by_cases fits : values.length = (panWordToBytesHOL address false).length
    · have same := read
      simp only [callFFIHOL, reduceCtorEq, ↓reduceIte, reply, fits] at same
      have equal := HolFfiResult.ret.inj same
      refine ⟨host, ?_, ?_⟩
      · simpa only [equal.2] using reply
      · exact (congrArg HolFfiState.ffiState equal.1).symm
    · simp [callFFIHOL, reply, fits] at read

end InitECandidate.Solver.Input.SharedRead

#print axioms InitECandidate.Solver.Input.SharedRead.mapM_present
#print axioms InitECandidate.Solver.Input.SharedRead.oracle_return_present
#print axioms InitECandidate.Solver.Input.SharedRead.oracle_return_data
#print axioms InitECandidate.Solver.Input.SharedRead.ffi_return_oracle
