import InitECandidate.Solver.Input.PayloadHashTransactions

namespace InitECandidate.Solver.Input.PayloadHash.Transactions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The observed original transaction hash preserves every future row's
literal/backing word, using only current physical array/workspace separation. -/
theorem call_metadata (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index offset : Nat)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity) (active : index<n) (inside : offset<16*n)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") transactionArguments)=(none,post)) :
    post.memory (array+BitVec.ofNat 64 offset)=source.memory (array+BitVec.ofNat 64 offset) := by
  have positive : 0<n := by omega
  have arena := geometry.arrayArena positive
  let query := array+BitVec.ofNat 64 offset
  have number : query.toNat=array.toNat+offset := byteAddress_toNat array offset (by have h:=arena.upper; omega)
  have before : query.toNat<roots.toNat := by rw [number]; have h:=geometry.arrayBefore positive; omega
  have below : query.toNat<cursor.toNat := by have h:=geometry.rootsBefore; omega
  have protection : SszHash.Protected source stp accel chunk zeros query :=
    ⟨actual.workspace,
      CopyGeneral.Away.before stp query 64 array.toNat (geometry.stateBefore positive) array.isLt (by rw [number]; omega),
      CopyGeneral.Away.before accel query 96 array.toNat (geometry.accelBefore positive) array.isLt (by rw [number]; omega),
      CopyGeneral.Away.before chunk query 32 array.toNat (geometry.chunkBefore positive) array.isLt (by rw [number]; omega)⟩
  obtain ⟨outArena,temporary⟩ := call_geometry array roots cursor stp accel chunk pointers lengths n capacity index geometry active
  have rootsAway := CopyGeneral.Away.after roots query (32*n) geometry.rootsAligned (by have h:=geometry.rootsArena.upper; omega) before
  exact PBytes.call_memory source post (pointers index) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros query (lengths index)
    (by have a:=geometry.lengthsBound index active; have b:=geometry.capacityBound; omega) protection actual.heap (geometry.inputs index active) temporary geometry.aligned outArena below
    (CopyGeneral.Away.subrange roots query (32*n) (32*index) 32 rootsAway (by omega)) transactionArguments
    (arguments_read source array roots cursor stp accel chunk zeros pointers lengths n capacity index actual geometry active) run

/-- A genuine normal transaction hash retains all decoded row cells,
initialized workspace, caller locals and its actual temporary heap cursor. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity) (active : index<n)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") transactionArguments)=(none,post)) :
    RoundState post array roots cursor stp accel chunk zeros pointers lengths n index := by
  obtain ⟨outArena,temporary⟩ := call_geometry array roots cursor stp accel chunk pointers lengths n capacity index geometry active
  have args := arguments_read source array roots cursor stp accel chunk zeros pointers lengths n capacity index actual geometry active
  have heap := PBytes.ignored_return_heap source post (pointers index) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros (lengths index)
    (by have a:=geometry.lengthsBound index active; have b:=geometry.capacityBound; omega) actual.workspace actual.heap temporary geometry.aligned outArena transactionArguments args run
  have workspace := SszHash.Workspace.after source post stp accel chunk zeros actual.workspace _ none run
    (fun key different=>GlobalEffects.call_body key source.code (some none) (ofString "htr_pbytes") transactionArguments PBytes.formals PBytes.body .one
      (PBytes.original_code source.code actual.workspace.sha.installed) (PBytes.globals key source.code actual.workspace.sha.installed different))
  have other (name : String) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source post (ofString name) (ofString "htr_pbytes") transactionArguments run
  have image : Image post array pointers lengths n := by
    constructor
    intro selected bounded
    have pFrame := call_metadata source post array roots cursor stp accel chunk zeros pointers lengths n capacity index (16*selected) actual geometry active (by omega) run
    have nFrame := call_metadata source post array roots cursor stp accel chunk zeros pointers lengths n capacity index (16*selected+8) actual geometry active (by omega) run
    exact ⟨pFrame.trans (actual.image.fields selected bounded).1,nFrame.trans (actual.image.fields selected bounded).2⟩
  exact ⟨workspace,(other "txs").trans actual.arrayLocal,(other "ntx").trans actual.count,(other "roots").trans actual.rootsLocal,(other "i").trans actual.position,image,heap⟩

/-- Original hash plus counter update advances the actual decoded row index
and preserves every other current record/heap/workspace fact. -/
theorem step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity) (active : index<n)
    (run : evaluateHOLFiniteState source transactionStep=(none,post)) : RoundState post array roots cursor stp accel chunk zeros pointers lengths n (index+1) := by
  rw [loop_shapes.2.1] at run
  obtain ⟨middle,called,advanced⟩ := sequence_none source post _ increment run
  have current := call_normal source middle array roots cursor stp accel chunk zeros pointers lengths n capacity index actual geometry active called
  have read : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,current.position,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have endpoint := assign_none middle post "i" (.op .add [localVar "i",.const 1#64]) (BitVec.ofNat 64 (index+1)) read advanced
  rw [endpoint]
  exact ⟨SszHash.Workspace.of_fields middle _ stp accel chunk zeros current.workspace rfl rfl (by intro key different; rfl),
    (bind_lookup_other middle "i" "txs" _ (by decide)).trans current.arrayLocal,
    (bind_lookup_other middle "i" "ntx" _ (by decide)).trans current.count,
    (bind_lookup_other middle "i" "roots" _ (by decide)).trans current.rootsLocal,bind_lookup_same _ _ _,⟨current.image.fields⟩,current.heap⟩

end InitECandidate.Solver.Input.PayloadHash.Transactions

#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.call_metadata
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.call_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.step_normal
