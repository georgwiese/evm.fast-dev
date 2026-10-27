# Rebase onto current official main, 2026-10-27

The user explicitly authorized the rebase and a fresh estimate. The objective
now concerns the unchanged software guest on official main
`f892870c8682517186860842a3ff5f0dea1aa3eb`, rather than the old accelerated
program at `7d656e5b6878aa420de793d9d6f689fa26ec0842`. A finite bound has no
additional numerical target. Do not optimize or replace the current guest.

## Git and recovery

All 560 local commits replayed without conflicts. The rebased proof checkpoint
is `5676eca3c760b003b9177263e6acb2e1d3da9738`. The previous head
`20080445b4247372ec639a2133558441111cdf54` is preserved on
`codex/pre-upstream-rebase-20261027`. Five unfinished RLP proof files were
saved in stash `0d43ada2a12374ec0432fd3f46edfef512bdce99` and restored with
stash apply; the stash remains available. A separate older review stash is
also retained. The entire committed Solver tree is byte-identical to the
pre-rebase checkpoint; this is preservation evidence, not port correctness.
The fixed Guest/InitE/ROM/proof library, Solution and claim match new main.
The claim remains infinity.

## Progress estimate

Best estimate: **40% of the total effort complete**, plausible range **30–50%**,
relative to current official main. This is judgment about remaining work,
not a theorem-coverage measurement or a count of passing files. It replaces
the old 65% estimate for a different program.

Whitespace-normalized comparison of generated declarations finds 811 unchanged
out of 928 old declarations; 68 changed, 49 removed, and 11 added, giving
890 new declarations. The precise name lists are in
`upstream-rebase-declarations.json`. This comparison does not establish the
new installed-code facts, memory invariants, cost bounds or certificate.

Reusable work includes generic evaluator/clock/frame/target-cost lemmas and
many local arithmetic, decoder, RLP and MPT helper arguments. The following
cannot be counted as completed for the new challenge:

- Installed-code catalogues still use `Guest.guestAst`, while the challenge
  uses `Guest.Software.guestAst`; declaration positions also changed.
- Open-addressing MutableTable invariants and collision/probe bounds describe
  the replaced implementation. New Patricia-map invariants and all-outcome
  lookup/insert/delete/growth/copy bounds are needed.
- Current heap, scratch, globals, input/output and startup constants differ.
  Arena ownership, reachable memory states and bootstrap facts need rederiving.
- Cryptographic foreign calls were replaced by software computation, requiring
  bounds for the actual software bodies and their callers.
- Full trie serialization/hash/root traversal, actual global gas and lifetime
  accounting, entry-to-target composition, an evaluated finite K and official
  verification were already unfinished before the rebase.

## Validation and next plan

`upstream-rebase-generic-v1.log` is a diagnostic representative build under
8 GiB host-used-memory and two-process guards. It includes WeightedTrace,
Input.ClockCostCurrent, and InitE.SourceSemantics. The new fixed AST and source
semantics built, and WeightedTrace replayed. Old dependent modules already
show real incompatibilities: Input.Framing, WitnessRadix.KeccakOracle,
WitnessRadix.AllocationDomain and WitnessRadix.PersistentAlloc. The build
finished with exit code 1 (1325/1356 jobs reached). This log is not a successful proof checkpoint
and must not be passed to record-proof-build.py. No whole Solver/Solution or
submission verification is claimed.

The prior proof-checks.json is explicitly marked historical and requiring
revalidation. The inventory reference now points to new main, and its old
helper roots are explicitly historical. Prior policy/full-verification
reports do not validate the new dependency closure.

1. Retarget code/declaration catalogues to the actual software guest and
   separate generic helpers from obsolete map/accelerator dependencies.
2. Reestablish actual current startup, arena/heap and allocation facts; port
   unchanged helper proofs with successful current-dependency builds.
3. Prove the current Patricia maps and bound software cryptography.
4. Finish actual serializer/hash/root traversal, caller lifetimes and complete
   EVM/gas/rollback/global accounting on the current program.
5. Compose weighted compiler/target costs and derive a concrete finite K.
6. Remove obsolete old-map/accelerator/generated code after extracting shared
   lemmas; retain only helpers needed for the final certificate.
7. Run policy/axiom/build checks and the full official verifier, and report
   completion only after a successful finite certificate and verification.

Continue pushing checkpoints to georg. Publish the preserved old branch before
updating the rebased branch, and guard the history update with an explicit
force-with-lease against the observed old remote head.
