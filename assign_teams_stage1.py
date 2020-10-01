import sys
import time

import claripy

MAX_ROUNDS = 8

num_players = int(sys.argv[1])
num_teams_w_rando = 4 - num_players % 4 if num_players % 4 else 0
num_teams = (num_players + num_teams_w_rando) // 4
assert num_teams_w_rando <= num_teams
num_teams_normal = num_teams - num_teams_w_rando

bit_length = max((num_teams * 4 + 1).bit_length(), (MAX_ROUNDS + 1).bit_length())

all_round_symbols = []
all_symbols = []

results = []

s = claripy.Solver()


def ite(cond, iftrue, iffalse):
    return claripy.ite_cases([(cond, iftrue)], iffalse)


def bool_to_bv(val):
    return ite(val, claripy.BVV(1, bit_length), claripy.BVV(0, bit_length))


def do_round(roundnum):
    global results

    starttime = time.monotonic()

    player_symbols = []
    for i in range(num_players):
        player_symbols.append(claripy.BVS(f'player-{i}-round_{roundnum}', bit_length))

    rando_symbols = []
    for i in range(num_teams_w_rando):
        rando_symbols.append(claripy.BVS(f'rando-{i}-round_{roundnum}', bit_length))

    round_symbols = [*player_symbols, *rando_symbols]

    iter_constraints = []

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

    # players be on the same team
    for i in range(num_players):
        for j in range(num_players):
            if i <= j:
                continue

            sym_temp = bool_to_bv(player_symbols[i] / 4 == player_symbols[j] / 4)
            for past_player_syms, _ in all_round_symbols:
                sym_temp += bool_to_bv(past_player_syms[i] / 4 == past_player_syms[j] / 4)

            iter_constraints.append(sym_temp <= 1)

    # players play with rando
    if num_teams_w_rando:
        for i in range(num_players):
            sym_temp = bool_to_bv(player_symbols[i] / 4 >= num_teams_normal)
            for past_player_syms, _ in all_round_symbols:
                sym_temp += bool_to_bv(past_player_syms[i] / 4 >= num_teams_normal)

            iter_constraints.append(sym_temp <= 1)

    # JX's request
    if not roundnum:
        for i in range(num_players - 1):
            iter_constraints.append(player_symbols[i] < player_symbols[i+1])

    all_symbols.extend(round_symbols)
    all_round_symbols.append((player_symbols, rando_symbols))

    results_t = results
    while True:
        stacked_contraints = [sym == val for sym, val in zip(all_symbols, results_t)]
        try:
            results = s.batch_eval(
                all_symbols, 1,
                extra_constraints=iter_constraints + stacked_contraints)[0]
        except claripy.UnsatError:
            results_t = results_t[:-num_teams * 4]
            if not results_t:
                print(f'Unsat # rounds = {roundnum+1} in {time.monotonic() - starttime:#.02f}s')
                print('=' * 64)
                raise
            else:
                print('Unsat Backtracking...')
        else:
            break

    print(f'Solved # rounds = {roundnum+1} in {time.monotonic() - starttime:#.02f}s')
    for i in range(roundnum+1):
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

        for j, p in enumerate(teams):
            print(f'Team {j+1}: {", ".join(p)}')

    print('=' * 64)


rounds_possible = min(MAX_ROUNDS, (num_players - 1) // 3)
if num_teams_w_rando:
    rounds_possible = min(rounds_possible, num_players // (num_teams_w_rando * 3))

for i in range(rounds_possible):
    try:
        do_round(i)
    except claripy.UnsatError:
        break
