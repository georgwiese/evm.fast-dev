import InitECandidate.Solver.Input.CurrentHash.MerkleAllocationCost
import InitECandidate.Solver.Input.MerkleDepthPrefix
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input.CurrentHash.MerkleBodyCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def zeroTest : ExpHOL 64 := .cmp .equal (localVar "n") (.const 0#64)
def zeroArguments : List (ExpHOL 64) := [localVar "out", .op .add [.var .global (ofString "zero_hashes"),
  .panop .mul [localVar "target", .const 32#64]], .const 32#64]
def zeroBody : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "memcpy") zeroArguments) (.return (.const 0#64))
def zeroGuard : ProgHOL 64 := .ite zeroTest zeroBody .skip

set_option maxRecDepth 100000 in
theorem source_shape : Code.body .merkleize = Merkle.body ∧
    Merkle.afterDepth = .seq zeroGuard MerkleBufferCost.afterZero := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Merkle.body, Merkle.afterDepth, Merkle.afterCount, Merkle.afterLimit, MerkleBufferCost.afterZero,
    Guest.Software.guestFn_merkleize, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, zeroGuard, zeroTest, zeroBody, zeroArguments, localVar]
  exact ⟨True.intro, True.intro⟩

theorem zero_guard (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : BitVec 64)
    (count : source.locals.lookup (ofString "n") = some (.val (.word n))) :
    evaluateHOLFiniteState source zeroGuard = if n = 0#64 then evaluateHOLFiniteState source zeroBody else (none, source) := by
  have read : eval source zeroTest = some (.val (.word (if n = 0#64 then 1#64 else 0#64))) := by
    simp [eval, zeroTest, localVar, evalHOLExact, toExact, count, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at read
  rw [zeroGuard, evaluateHOLFiniteState_ite, read]
  by_cases empty : n = 0#64
  · simp only [if_pos empty]; rfl
  · simp only [if_neg empty]; exact evaluateHOLFiniteState_skip source

theorem empty_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code)
    (count : source.locals.lookup (ofString "n") = some (.val (.word 0#64))) :
    source.clock - (evaluateHOLFiniteState source Merkle.afterDepth).2.clock ≤ 42 := by
  have price : ClockCost.Bound source.code zeroBody 42 :=
    ClockCost.sequence source.code _ _ 42 0 (FixedMemoryCost.copy source.code installed (some none) _ _ 32 (by decide)) (ClockCost.returned source.code _)
  have paid := price source rfl
  have stopped : NoFallthrough zeroBody := .sequence _ _ (.returned _)
  have stops := stopped source
  rw [source_shape.2, evaluateHOLFiniteState_seq_line780, zero_guard source 0#64 count, if_pos rfl]
  generalize actual : evaluateHOLFiniteState source zeroBody = output at paid stops ⊢
  obtain ⟨result, post⟩ := output
  cases result with
  | none => exact False.elim (stops rfl)
  | some result => exact paid

/-- Every actual outcome after the depth prefix, including allocation traps,
failed memory operations and clock exhaustion. Empty trees stop before allocation. -/
theorem after_depth_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n depth target budget : Nat)
    (data : MerkleAllocationCost.Params source p n depth target) (installed : OriginalCode.Installed source.code)
    (depthSmall : depth ≤ budget) (budgetSmall : budget < 58) (targetBound : target ≤ budget) (depths : depth ≤ target)
    (ceiling : n ≤ 2^depth) (minimal : 2^depth ≤ max 1 (2*n)) :
    source.clock - (evaluateHOLFiniteState source Merkle.afterDepth).2.clock ≤ 88*n + 2*budget + 45 := by
  by_cases empty : n = 0
  · have count : source.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by simpa [empty] using data.count
    have price := empty_cost source installed count
    omega
  · have power : 2^depth ≤ 2^57 := Nat.pow_le_pow_right (by decide) (by omega)
    have sizeSmall : 32*2^depth + 32 < 2^64 := by omega
    have nSmall : n < 2^64 := by omega
    have nNumber : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nSmall]
    have nonzero : BitVec.ofNat 64 n ≠ 0#64 := by intro same; have equal := congrArg BitVec.toNat same; simp only [nNumber, BitVec.toNat_ofNat] at equal; omega
    have original : evaluateHOLFiniteState source Merkle.afterDepth = evaluateHOLFiniteState source MerkleBufferCost.afterZero := by
      rw [source_shape.2, StateSteps.next_sequence source source _ _
        (by rw [zero_guard source (BitVec.ofNat 64 n) data.count, if_neg nonzero]) (Nat.le_refl _)]
    have priced := MerkleAllocationCost.cost source p n depth target data installed (by omega) ceiling sizeSmall (by omega) depths
    rw [original]
    have sizeBound : 2^depth ≤ 2*n := by rw [Nat.max_eq_right (by omega)] at minimal; exact minimal
    omega

/-- Complete current software Merkle source cost for every non-timeout actual
outcome. The surrounding source observation supplies non-timeout; helper inputs
are current locals. No mapped arena, heap room, workspace or successful hash is
assumed. This does not yet count expanded straight-line target instructions. -/
theorem cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p n limit : BitVec 64) (budget : Nat)
    (small : budget < 58) (countBound : n.toNat ≤ 2^budget) (limitBound : limit.toNat ≤ 2^budget)
    (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "p") = some (.val (.word p)))
    (count : source.locals.lookup (ofString "n") = some (.val (.word n)))
    (maximum : source.locals.lookup (ofString "limit") = some (.val (.word limit)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source (Code.body .merkleize) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ 88*n.toNat + 4*budget + 48 := by
  rw [source_shape.1] at actual
  obtain ⟨current, final, dl, dn, restoration, dlBound, dnBound, limitPower, countPower, dlPrevious, dnPrevious, sizeBound,
    locals, paid, clock, prefixCost, frame, remaining, endpoint, restored⟩ :=
    Merkle.depth_prefix source post n limit budget (by omega) countBound limitBound installed count maximum result actual notTimeout
  have kept (name : String) (notDl : ofString "dl" ≠ ofString name) (notDn : ofString "dn" ≠ ofString name)
      (notTarget : ofString "target" ≠ ofString name) : current.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, notDl, notDn, notTarget]
  have currentCount : current.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n.toNat))) := by
    simpa using (kept "n" (by decide) (by decide) (by decide)).trans count
  have currentDepth : current.locals.lookup (ofString "dn") = some (.val (.word (BitVec.ofNat 64 dn))) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "target" ≠ ofString "dn" from by decide]
  have currentTarget : current.locals.lookup (ofString "target") = some (.val (.word (BitVec.ofNat 64 (max dl dn)))) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have currentCode : OriginalCode.Installed current.code := by
    have same := congrArg PanSemStateFiniteExact.code frame
    change current.code = source.code at same
    rw [same]
    exact installed
  have data : MerkleAllocationCost.Params current p n.toNat dn (max dl dn) :=
    ⟨(kept "p" (by decide) (by decide) (by decide)).trans pointer, currentCount, currentDepth, currentTarget⟩
  have tailCost := after_depth_cost current p n.toNat dn (max dl dn) budget data currentCode dnBound small
    (Nat.max_le.mpr ⟨dlBound, dnBound⟩) (Nat.le_max_right _ _) countPower sizeBound
  have tailClock := evaluateHOLFiniteState_clock_le current Merkle.afterDepth
  rw [remaining] at tailCost tailClock
  change current.clock - final.clock ≤ 88*n.toNat + 2*budget + 45 at tailCost
  change final.clock ≤ current.clock at tailClock
  have endpointClock : post.clock = final.clock := by
    have same := congrArg PanSemStateFiniteExact.clock (restored final)
    rw [endpoint]
    exact same
  rw [endpointClock]
  omega

end InitECandidate.Solver.Input.CurrentHash.MerkleBodyCost

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBodyCost.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBodyCost.zero_guard
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBodyCost.empty_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBodyCost.after_depth_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBodyCost.cost
