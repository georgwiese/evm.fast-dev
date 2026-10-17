#!/usr/bin/env python3
"""Exact conditional chain scenarios, never a whole-program runtime bound.

These scenarios isolate nested delete-set propagation waves. Earlier produced
keys are available at every ancestor without charging their propagation/setup
work. A greedy repeated-wave scenario returns unused child gas and retains
earlier keys; it illustrates why the single-wave maximum is not a forest bound.
None covers arbitrary forests, schedules, rehashes, rollback or target prices.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def literal(path, name):
    text = (ROOT/path).read_text()
    return int(re.search(r'^#define\s+'+re.escape(name)+r'\s+([0-9]+)\s*$', text, re.M)[1])


def cap(remaining):
    return remaining-remaining//64


def curve(root, minimum_access, maximum_depth):
    gas = root
    points = [(0, gas)]
    for depth in range(1, maximum_depth+1):
        if gas < minimum_access:
            break
        gas = cap(gas-minimum_access)
        points.append((depth, gas))
    return points


def scenarios(root, access, production, maximum_depth):
    empty = dict(units=0, depth=0, child_distinct=0)
    points = curve(root, access, maximum_depth)
    for depth, remaining in points[1:]:
        count = remaining//production
        units = depth*count*count
        if units > empty['units']:
            empty = dict(units=units, depth=depth, child_distinct=count,
                         child_budget=remaining)
    relaxed = dict(units=0, depth=0, earlier_distinct=0, child_distinct=0)
    examined = 0
    for earlier in range(root//production+1):
        remaining = root-production*earlier
        for depth, child_budget in curve(remaining, access, maximum_depth)[1:]:
            current = child_budget//production
            units = depth*(earlier+current)*current
            examined += 1
            if units > relaxed['units']:
                relaxed = dict(units=units, depth=depth, earlier_distinct=earlier,
                               child_distinct=current, child_budget=child_budget,
                               root_after_earlier_production=remaining)
    repeated = dict(units=0, depth=0, waves=0, produced_keys=0)
    for fixed_depth in range(1, len(points)):
        remaining, earlier, units, waves = root, 0, 0, 0
        while remaining >= access*fixed_depth:
            child_budget = remaining
            for _ in range(fixed_depth):
                if child_budget < access:
                    child_budget = 0
                    break
                child_budget = cap(child_budget-access)
            current = child_budget//production
            if not current:
                break
            consumed = production*current+access*fixed_depth
            assert consumed <= remaining
            units += fixed_depth*(earlier+current)*current
            earlier += current
            remaining -= consumed
            waves += 1
        if units > repeated['units']:
            repeated = dict(units=units, depth=fixed_depth, waves=waves,
                            produced_keys=earlier, gas_remaining=remaining)
    return dict(root_budget=root,
        last_affordable_edge=len(points)-1,
        last_child_budget=points[-1][1],
        empty_ancestor_single_wave=empty,
        earlier_keys_available_at_every_ancestor=relaxed,
        largest_greedy_repeated_wave_scenario=repeated,
        earlier_key_placement_pairs_examined=examined,
        depth_times_independent_root_square=maximum_depth*(root//production)**2,
        hypothetical_price_sensitivity={str(price):relaxed['units']*price
                                        for price in (512,1000,3552)},
        target_prices_verified=False, runtime_wave_coupling_proved=False)


def main():
    fork = 'guest/src/fork.pnk'
    evm = 'guest/src/evm.pnk'
    user = literal(fork, 'TX_MAX_GAS_LIMIT')
    system = literal(fork, 'SYSTEM_TRANSACTION_GAS')
    access = literal(evm, 'G_WARM_ACCESS')
    production = literal(evm, 'G_SELFDESTRUCT_BASE')
    depth = literal(evm, 'STACK_DEPTH_LIMIT')
    sources = [fork, evm, 'guest/src/evm_calls.pnk','guest/src/state.pnk',
               'guest/src/lib/htab.pnk',
               'submission/InitECandidate/Solver/GasBudget/NestedDecay.lean']
    result = dict(whole_bound=False, certificate=False, runtime_work_bound=False,
        model='Single-wave and greedy repeated-wave chain scenarios; exact integer arithmetic, no arbitrary-schedule optimum.',
        parameters=dict(user_regular_cap_literal=user, system_regular_literal=system,
            minimum_access_literal=access, production_price_literal=production,
            maximum_depth_literal=depth),
        sources={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
        checked_algebra=dict(log='gas-nested-decay-v1.log',
            uniform_child='child <= capNat(parent-100)',
            shifted_contraction='64*(child+6237) <= 63*(parent+6237)',
            maximum_depth_from30M=538,
            status='Conditional Lean facts; actual edge/root budget invariants remain open.'),
        cases=dict(user=scenarios(user,access,production,depth),
                   system=scenarios(system,access,production,depth)),
        remaining_premises=[
            'Actual parent regular budget bounded by its root seed through all success/failure paths.',
            'Every nested call/create pays the required fee; stipends are funded by its value fee.',
            'Root initial regular gas at most the parsed constants on every reachable entry.',
            'Delete-set key production and propagation are coupled to actual charged events.',
            'All parent/child/earlier-key configurations and arbitrary forests, not only one wave.',
            'Hash-table searches, raw insertions, growth, deletion and copy multiplicities.',
            'Protected gas cells across logs, table merges, memory allocation and rollback.',
            'Aggregate roots, signed state/refund ledger, block counters and final target prices.'
        ],
        decision='Useful conditional scale check; no global go or finite K.')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
