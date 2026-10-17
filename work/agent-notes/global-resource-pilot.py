#!/usr/bin/env python3
"""Exact offline feasibility submodels; not a whole-guest bound or proof.

The optimizer accounts jointly for costly first touches and repeated warm
queries. Every scenario still needs its stated runtime/charging premises.
"""
import argparse
from fractions import Fraction
from math import gcd
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
KMAX = 9007199254740984


def optimize(gas, cold, warm, preexisting=0, first_price=1, repeat_price=1):
    # Cost: a*(B*D + D*(D-1)/2) + b*(B+D)*W.
    # cold*D + warm*W <= gas; all variables natural.
    assert gas >= 0 and cold > 0 and warm > 0
    assert min(preexisting, first_price, repeat_price) >= 0
    period = warm // gcd(cold, warm)
    assert period <= 10000
    best = dict(cost=0, distinct=0, warm_queries=gas // warm)
    for residue in range(period):
        high = (gas // cold - residue) // period
        if high < 0:
            continue
        # Along one residue, W is affine. Recover the integer quadratic
        # 2*objective = A*t*t+B*t+C from three exact evaluations.
        def twice(t):
            d = residue + period * t
            w = (gas-cold*d)//warm
            return first_price*(2*preexisting*d+d*(d-1)) + 2*repeat_price*(preexisting+d)*w
        c = twice(0)
        a = (twice(2)-2*twice(1)+c)//2
        b = twice(1)-c-a
        points = {0, high}
        if a < 0:
            vertex = Fraction(-b, 2*a)
            floor = vertex.numerator // vertex.denominator
            points |= {floor-1, floor, floor+1, floor+2}
        for t in points:
            if not 0 <= t <= high:
                continue
            d = residue + period*t
            w = (gas-cold*d)//warm
            value = twice(t)//2
            if value > best['cost']:
                best = dict(cost=value, distinct=d, warm_queries=w)
    d, w = best['distinct'], best['warm_queries']
    best.update(gas=gas, cold=cold, warm=warm, preexisting=preexisting,
                first_price=first_price, repeat_price=repeat_price,
                spent=cold*d+warm*w,
                note='Dimension relaxation only; runtime multiplicities and global gas conservation are unproved.')
    return best


def self_test():
    checked = 0
    for gas in range(0, 140, 7):
        for cold in (3, 7, 12, 21):
            for warm in (1, 2, 5):
                for base in (0, 1, 9):
                    for fp, rp in ((1, 1), (2, 1), (1, 3)):
                        result = optimize(gas,cold,warm,base,fp,rp)
                        brute = max(fp*(base*d+d*(d-1)//2)+rp*(base+d)*w
                                    for d in range(gas//cold+1)
                                    for w in range((gas-cold*d)//warm+1))
                        assert result['cost'] == brute, (result, brute)
                        checked += 1
    return checked


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    checks = self_test() if args.self_test else None
    sources = ['guest/src/evm.pnk','guest/src/evm_calls.pnk','guest/src/tx.pnk','guest/src/fork.pnk','guest/src/block.pnk',
               'guest/src/state.pnk','guest/src/mpt.pnk','guest/src/lib/htab.pnk',
               'guest/src/lib/rlp.pnk','guest/src/config.h','guest/src/types.h']
    block_size = 8388608
    withdrawal_min_rlp = 25
    max_withdrawals = block_size // withdrawal_min_rlp
    heap_bytes = 33806089496-2713714688
    cases = {}
    # 380M = user 200M + 6 system allowances of30M. This is a scenario,
    # NOT a proved total executed-gas allowance: refunds/state gas remain open.
    for gas in (380000000,500000000):
        for cold in (2100,3000):
            key = f'gas{gas}-cold{cold}'
            joint = optimize(gas,cold,100)
            independent_d = gas//cold
            independent_q = gas//100
            cases[key] = dict(joint=joint,
                independent_product=independent_d*independent_q,
                joint_priced_sensitivity={str(price):joint['cost']*price for price in (512,1000,3552)},
                max_target_price_if_only_cost=KMAX//max(joint['cost'],1))
    cases['post-withdrawal-system-window'] = optimize(120000000,3000,100,max_withdrawals)
    result = dict(whole_bound=False, certificate=False,
        sources={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sources},
        exact_arithmetic=dict(block_size=block_size,withdrawal_min_rlp=withdrawal_min_rlp,
            withdrawal_count_relaxation=max_withdrawals,persistent_heap_bytes=heap_bytes,
            hypothetical_one_query_per32_allocated_bytes=heap_bytes//32),
        arithmetic_status='The integers are exact. Their full-run premises below are unproved.',
        self_test_cases=checks, cases=cases,
        checked_local_evidence=dict(block_guard_log='input-block-guard-v3.log',gas_refund_refill_log='gas-refund-calls-v1.log',gas_state_charge_log='gas-state-charge-call-v1.log',
            regular_budget='gas_left + regular_gas_used + outstanding_state_spill',
            gas_local_premises='Actual mapped/stored frame and message cells, code, clock affordability, gas_left+spill<2^64; state_left+gas_left<2^64 for charge; reservoir cell separation for refill.',
            global_initialization=False,whole_gas_conservation=False,target_steps=False),
        source_observations=[
            'The actual cold account constant is3000, not2600; warm100 and cold storage2100.',
            'EV_STATE_GAS_SPILLED is offset192; actual refund and rollback refill preserve regular gas_left+used+spill under checked local premises.',
            'CALL/CALLCODE subtract forwarded gas including a2300 stipend from EV_REGULAR_GAS_USED; nonzero-value overhead is11300, so raw cumulative charge_gas amounts are not net regular consumption.',
            'calculate_intrinsic_cost currently returns regular,0,floor; process_transaction block regular accounting occurs before its ordinary refund subtraction.',
            'htab_del uses backward shifts, not repeated full reinsertions.',
            'block_rlp_length precedes block-content trie construction and process_withdrawals; cap8MiB.',
            'withdrawal_rlp_len contains fixed address cost21, three positive scalar lengths and positive list header.',
            '_decode_step rejects empty extension paths and allocates record arrays; _decode_witness_node releases scratch, not persistent heap.',
            'ws_storage_trie decodes before the temporary key-hash heap_mark/heap_release scope.',
        ],
        required_unproved_premises=[
            'Root decoder/builder entry, byte-pointer arenas, fresh-buffer placement, runtime code and clock premises of the checked whole block-call/withdrawal-guard theorem.',
            'Whole-run conservation of executed regular/state gas over six system calls, child transfers/stipends, signed state use and block counters; actual refund/refill local conservation now checks.',
            'Joint cold/warm resources for every map, including access-list warming and free withdrawals.',
            'All table probe/rehash/backward-delete/copy multiplicities and inter-phase cache sizes.',
            'Persistent allocation accounting excludes only scoped temporary arenas with separate cumulative bounds.',
            'Pair every nonterminal immutable-db query with appropriate successful persistent allocation or bounded root call.',
            'Nonzero trie path progress and acyclic returned mutable graphs derived from execution, not crypto assumptions.',
            'Actual weighted compiler/target pricing and final budget for all other work, events, bootstrap and terminals.',
        ],
        decision='No new impossibility or reachable runtime counterexample established. Global go remains unearned. Use joint resource accounting; do not multiply independent maxima or treat scenarios as K.')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
