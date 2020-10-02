import functools
import json
import re
import sys
import time

import claripy

MAX_ROUNDS = 8

num_players = int(sys.argv[1])
num_teams_w_rando = 4 - num_players % 4 if num_players % 4 else 0
num_teams = (num_players + num_teams_w_rando) // 4
assert num_teams_w_rando <= num_teams
num_teams_normal = num_teams - num_teams_w_rando

res_external = []

with open(f'out_stage1/{num_players}.txt', 'r') as f:
    while True:
        line = f.readline()
        if not line:
            break
        line = line.strip()

        reobj = re.match(r'^Solved # rounds = (\d+) in ([0-9.]+)s$', line)
        if not reobj:
            continue

        res_external.clear()

        num_rounds = int(reobj.group(1))
        for i in range(num_rounds):
            line = f.readline().strip()
            assert line == f'Round {i+1}'

            res_external_round = []
            res_external.append(res_external_round)
            for j in range(num_teams):
                line = f.readline().strip()
                prefix = f'Team {j+1}: '
                assert line.startswith(prefix)

                line = line[len(prefix):]

                team = line.split(', ')
                team = [int(p) if p != 'R' else p for p in team]

                assert len(team) == 4
                res_external_round.append(team)


constrained_solution = []

for rnd in res_external:
    def cmp(a, b):
        ar, br = a[3], b[3]
        if ar == 'R' and br != 'R':
            return 1
        if ar != 'R' and br == 'R':
            return -1
        return 0

    rnd = list(sorted(rnd, key=functools.cmp_to_key(cmp)))
    rnd = [p for team in rnd for p in team]

    for i in range(num_players):
        constrained_solution.append(rnd.index(i))

    for i in range(num_teams_w_rando):
        ind = rnd.index('R')
        assert ind / 4 > num_teams_normal
        rnd[ind] = 'U'
        constrained_solution.append(ind)

results = constrained_solution[:]

assert len(constrained_solution) % (4 * num_teams) == 0
rounds_constrained = len(constrained_solution) // (4 * num_teams)

if rounds_constrained and rounds_constrained != MAX_ROUNDS:
    print(f'Constraining {rounds_constrained} rounds')
    bit_length = max((num_teams * 4 + 1).bit_length(), (MAX_ROUNDS + 1).bit_length())

    all_round_symbols = []
    all_symbols = []

    s = claripy.Solver()

    def ite(cond, iftrue, iffalse):
        return claripy.ite_cases([(cond, iftrue)], iffalse)

    def bool_to_bv(val):
        return ite(val, claripy.BVV(1, bit_length), claripy.BVV(0, bit_length))

    def min_bv(lst):
        it = iter(lst)
        cum = next(it)
        for elem in it:
            cum = ite(elem < cum, elem, cum)

        return cum

    def max_bv(lst):
        it = iter(lst)
        cum = next(it)
        for elem in it:
            cum = ite(elem > cum, elem, cum)

        return cum

    for roundnum in range(MAX_ROUNDS):
        player_symbols = []
        for i in range(num_players):
            player_symbols.append(claripy.BVS(f'player-{i}-round_{roundnum}', bit_length))

        rando_symbols = []
        for i in range(num_teams_w_rando):
            rando_symbols.append(claripy.BVS(f'rando-{i}-round_{roundnum}', bit_length))

        round_symbols = [*player_symbols, *rando_symbols]

        # symbols must be in range
        for sym in round_symbols:
            s.add(sym < num_teams * 4)

        # symbols cannot represent the same slot
        for i in range(len(round_symbols)):
            for j in range(len(round_symbols)):
                if i <= j:
                    continue

                s.add(round_symbols[i] != round_symbols[j])

        # players cannot use rando slots
        for sym in player_symbols:
            for i in range(num_teams_w_rando):
                s.add(sym != (num_teams_normal + i) * 4 + 3)

        all_symbols.extend(round_symbols)
        all_round_symbols.append((player_symbols, rando_symbols))

    for sym, val in zip(all_symbols, constrained_solution):
        s.add(sym == val)

    def solve(player_buf, rando_buf):
        extra_constraints = []

        # players be on the same team
        tl = []
        for i in range(num_players):
            for j in range(num_players):
                if i <= j:
                    continue

                sym_temp = 0
                for past_player_syms, _ in all_round_symbols:
                    sym_temp += bool_to_bv(past_player_syms[i] / 4 == past_player_syms[j] / 4)

                tl.append(sym_temp)

        extra_constraints.append(max_bv(tl) - min_bv(tl) <= player_buf)

        # players play with rando
        if num_teams_w_rando:
            tl = []
            for i in range(num_players):
                sym_temp = 0
                for past_player_syms, _ in all_round_symbols:
                    sym_temp += bool_to_bv(past_player_syms[i] / 4 >= num_teams_normal)

                tl.append(sym_temp)

            extra_constraints.append(max_bv(tl) - min_bv(tl) <= rando_buf)

        return s.batch_eval(
            all_symbols, 1,
            extra_constraints=extra_constraints)[0]

    unsats = set()
    last_good = None

    def solve_wrapper(player_buf, rando_buf):
        if not rando_buf and (3 * num_teams_w_rando * MAX_ROUNDS) % num_players:
            return None

        if not player_buf and ((num_teams_w_rando * 3 + num_teams_normal * 6) * MAX_ROUNDS) % ((num_players * (num_players - 1)) // 2):
            return None

        if (player_buf, rando_buf) in unsats:
            return None

        starttime = time.monotonic()

        try:
            results = solve(player_buf, rando_buf)
        except claripy.UnsatError:
            print(f'Unsat # player_buf = {player_buf}, rando_buf = {rando_buf} in {time.monotonic() - starttime:#.02f}s')
            unsats.add((player_buf, rando_buf))
            return None
        else:
            print(f'Solved # player_buf = {player_buf}, rando_buf = {rando_buf} in {time.monotonic() - starttime:#.02f}s')
            global last_good
            last_good = results
            return results

    player_buf = rando_buf = 0

    while True:
        if solve_wrapper(player_buf, rando_buf):
            break

        if solve_wrapper(player_buf + 1, rando_buf):
            player_buf += 1
            break

        if num_teams_w_rando and solve_wrapper(player_buf, rando_buf + 1):
            rando_buf += 1
            break

        player_buf += 1
        if num_teams_w_rando:
            rando_buf += 1

    while True:
        if num_teams_w_rando and rando_buf and solve_wrapper(player_buf, rando_buf - 1):
            rando_buf -= 1
            continue

        if player_buf and solve_wrapper(player_buf - 1, rando_buf):
            player_buf -= 1
            continue

        break

    results = last_good


slot_major = []
for i in range(MAX_ROUNDS):
    print(f'Round {i+1}')

    teams = [[] for j in range(num_teams)]
    assignment = results[i * (num_teams * 4):(i+1) * (num_teams * 4)]

    for j, a in enumerate(assignment):
        teams[a // 4].append(j)

    # Unordered transforms
    for j, t in enumerate(teams):
        teams[j] = list(sorted(t))
    teams = list(sorted(teams, key=lambda t: t[0]))

    for j, t in enumerate(teams):
        teams[j] = [str(p) if p < num_players else 'R' for p in t]
        slot_major.extend([p if p < num_players else 'R' for p in t])

    for j, p in enumerate(teams):
        print(f'Team {j+1}: {", ".join(p)}')


with open(f'out_stage2/{num_players}.json', 'w') as f:
    json.dump(slot_major, f)
