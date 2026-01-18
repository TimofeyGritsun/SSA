from collections import defaultdict
from copy import deepcopy
from itertools import product
import random
import cProfile
import pstats

def zero_column(matrix, col):
    M = deepcopy(matrix)
    for row in M:
        row[col] = 0
    return M

def generate_random_code(k, n):
    assert n > k

    G = []

    for i in range(k):
        row = [0]*n
        row[i] = 1 
        for j in range(k, n):
            row[j] = random.randint(0, 1)
        G.append(row)

    return G

def generate_linear_space(basis):
    if not basis:
        return []

    k = len(basis)
    n = len(basis[0])
    space = []

    for coeffs in product([0, 1], repeat=k):
        v = [0] * n
        for c, b in zip(coeffs, basis):
            if c:
                for i in range(n):
                    v[i] ^= b[i]
        space.append(v)

    return space

def weight_distribution(vectors, max_weight):
    dist = [0] * (max_weight + 1)

    for v in vectors:
        w = sum(v)
        dist[w] += 1

    return tuple(dist)


def invariant_for_position(G, col, extra_zero_cols=None):
    H = deepcopy(G)

    Hz = zero_column(H, col)

    if extra_zero_cols:
        for c in extra_zero_cols:
            Hz = zero_column(Hz, c)

    vectors = generate_linear_space(Hz)

    n = len(G[0])
    
    return weight_distribution(vectors, max_weight=n)

def sort_groups(groups, invariants):
    def group_key(g):
        inv = invariants[g[0]]
        return (len(g), tuple(-x for x in reversed(inv)))

    return sorted(groups, key=group_key)

def iterative_weight_refinement(G):
    n = len(G[0])

    invariants = {}
    groups_dict = defaultdict(list)

    for j in range(n):
        inv = invariant_for_position(G, j)
        invariants[j] = inv
        groups_dict[inv].append(j)

    

    groups = list(groups_dict.values())
    groups = sort_groups(groups, invariants)

    print("ШАГ 1:")
    for g in groups:
        print(f"{[p+1 for p in g]} - {invariants[g[0]]}")

    used_pivots = set()
    iteration = 1
    current_invariants = dict(invariants)

    while iteration < 2:

        pivot = None
        for g in groups:
            if len(g) == 1 and g[0] not in used_pivots:
                pivot = g[0]
                break

        if pivot is None:
            print("\nНет одиночных групп — остановка.")
            break

        used_pivots.add(pivot)

        print(f"\nШАГ {iteration + 1}, опорная позиция: {pivot+1}")

        new_groups = []

        for g in groups:
            if len(g) == 1:
                new_groups.append(g)
                continue

            sub = defaultdict(list)

            for p in g:
                inv = invariant_for_position(
                    G,
                    p,
                    extra_zero_cols=[pivot]
                )
                sub[inv].append(p)

            subgroups = list(sub.values())

            new_inv = {}

            for sg in subgroups:
                for p in sg:
                    new_inv[p] = invariant_for_position(G, p, [pivot])

            subgroups = sort_groups(subgroups, new_inv)

            for p, inv in new_inv.items():
                current_invariants[p] = inv

            new_groups.extend(subgroups)

        groups = new_groups

        print("Группы после шага:")
        for g in groups:
            print(f"{[p+1 for p in g]} - {current_invariants[g[0]]}")


        if all(len(g) == 1 for g in groups):
            print("\nВсе позиции уникальны.")
            break

        iteration += 1

    return groups

def get_res(j):
    mres = 0
    for i in range(j):
        G1 = generate_random_code(10, 20)
        for v in G1:
            print(v)
        res = iterative_weight_refinement(G1)
        l = 0
        for r in res:
            l += len(r)
        mres += l/len(res)
    print(mres/j)

get_res(100)
