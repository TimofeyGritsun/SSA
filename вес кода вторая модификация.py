from collections import defaultdict
from copy import deepcopy
from itertools import product
import random

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
        if isinstance(inv[0], tuple):
            w = inv[-1]   
        else:
            w = inv     

        return (len(g), tuple(-x for x in reversed(w)))

    return sorted(groups, key=group_key)

def iterative_weight_refinement(G, max_iterations=5):
    n = len(G[0])

    base_inv = {}
    groups_dict = defaultdict(list)

    for j in range(n):
        inv = invariant_for_position(G, j)
        base_inv[j] = inv
        groups_dict[inv].append(j)

    groups = list(groups_dict.values())
    groups = sort_groups(groups, base_inv)

    current_inv = {p: (base_inv[p],) for p in range(n)}

    frozen = set()
    for g in groups:
        if len(g) == 1:
            frozen.add(g[0])

    used_pivots = set()
    iteration = 1

    while iteration <= max_iterations:

        pivot = None
        for g in groups:
            if len(g) == 1:
                p = g[0]
                if p not in used_pivots:
                    pivot = p
                    break

        if pivot is None:
            break

        used_pivots.add(pivot)

        new_groups = []

        for g in groups:
            if len(g) == 1:
                new_groups.append(g)
                continue

            sub = defaultdict(list)

            for p in g:
                if p in frozen:
                    key = current_inv[p]
                else:
                    new_w = invariant_for_position(
                        G,
                        p,
                        extra_zero_cols=[pivot]
                    )
                    current_inv[p] = current_inv[p] + (new_w,)
                    key = current_inv[p]

                sub[key].append(p)

            subgroups = list(sub.values())
            subgroups = sort_groups(subgroups, current_inv)
            new_groups.extend(subgroups)

        groups = new_groups

        for g in groups:
            if len(g) == 1:
                frozen.add(g[0])

        if all(len(g) == 1 for g in groups):
            break

        iteration += 1

    return current_inv

def match_positions_by_invariants(G, G1):
    inv_G  = iterative_weight_refinement(G, len(G[0]) - 2)
    inv_G1 = iterative_weight_refinement(G1, len(G1[0]) - 2)

    groups_G  = defaultdict(list)
    groups_G1 = defaultdict(list)

    for p, inv in inv_G.items():
        groups_G[inv].append(p)

    for p, inv in inv_G1.items():
        groups_G1[inv].append(p)

    matching = []

    for inv in groups_G:
        if inv in groups_G1:
            matching.append((
                groups_G[inv],
                groups_G1[inv]
            ))

    return matching

def apply_permutation(G, perm):
    k = len(G)
    n = len(G[0])

    Gp = [[0]*n for _ in range(k)]
    for i in range(k):
        for j in range(n):
            Gp[i][perm[j]] = G[i][j]

    return Gp

def inverse_permutation(perm):
    inv = [0]*len(perm)
    for i, p in enumerate(perm):
        inv[p] = i
    return inv

def generator(n, k, manual_perm=None):
    G = generate_random_code(k, n)

    if manual_perm is not None:
        perm = manual_perm
    else:
        perm = list(range(n))
        random.shuffle(perm)

    G1 = apply_permutation(G, perm)
    inv_perm = inverse_permutation(perm)

    return G, G1, inv_perm

from typing import Iterable, List, Tuple, Union, Dict, Any
def permutation_match_score(
    matching: List[Tuple[List[int], List[int]]],
    true_perm: Union[List[int], Dict[int, int]],
    *,
    ambiguous_divisor: float = 2.0,
    return_details: bool = False,
) -> Union[float, Tuple[float, List[Dict[str, Any]]]]:
    if isinstance(true_perm, list):
        n = len(true_perm)
        def tp(i: int) -> int:
            return true_perm[i]
    else:
        if not true_perm:
            raise ValueError("true_perm dict пустой — невозможно определить n")
        n = max(true_perm.keys()) + 1
        def tp(i: int) -> int:
            return true_perm[i]

    all_positions = []
    for a, b in matching:
        all_positions.extend(a)
        all_positions.extend(b)

    if not all_positions:
        score = 0.0
        return (score, []) if return_details else score

    one_based = any(p >= n for p in all_positions)

    def norm(p: int) -> int:
        return p - 1 if one_based else p

    total_credit = 0.0
    details: List[Dict[str, Any]] = []

    for group_G, group_G1 in matching:
        A = [norm(x) for x in group_G]
        B = [norm(x) for x in group_G1]

        for x in A:
            if x < 0 or x >= n:
                raise ValueError(f"Индекс в group_G вне диапазона: {x} (n={n})")
        for y in B:
            if y < 0 or y >= n:
                raise ValueError(f"Индекс в group_G1 вне диапазона: {y} (n={n})")

        true_images = {tp(x) for x in A}
        Bset = set(B)

        successes = len(true_images & Bset)
        ambiguous = (len(A) > 1) or (len(B) > 1)

        if ambiguous:
            credit = successes / float(ambiguous_divisor)
        else:
            credit = float(successes)

        total_credit += credit

        if return_details:
            details.append({
                "group_G": group_G,
                "group_G1": group_G1,
                "normalized_G": A,
                "normalized_G1": B,
                "true_images_of_G": sorted(true_images),
                "successes": successes,
                "ambiguous": ambiguous,
                "credit": credit,
            })

    percent = (total_credit / float(n)) * 100.0
    return (percent, details) if return_details else percent

def get_res(n, k, choice):

    if choice == 'n':
        perm = list(map(int, input(f"Введите перестановку из {n} элементов (0-based): ").split()))
    else:
        perm = None

    G, G1, true_perm = generator(n, k, perm)
    
    print("\nМатрица G:")
    for r in G:
        print(r)

    print("\nМатрица G1 (переставленная):")
    for r in G1:
        print(r)

    print("\nИстинная перестановка (G -> G1):")
    print(true_perm)
    print("\nОбратная перестановка (G1 -> G):")
    print(inverse_permutation(true_perm))

    print("\nЗапуск сопоставления...\n")
    matching = match_positions_by_invariants(G, G1)

    print("Найденные соответствия:")
    for l, r in matching:
        print(f"{[x for x in l]} -> {[x for x in r]}")

    score = permutation_match_score(matching, inverse_permutation(true_perm))
    print(f"\nПроцент правильного восстановления: {score:.2f}%")
    return score


it = int(input("Количество итераций: "))
n = int(input("Введите n (длина кодового слова): "))
k = int(input("Введите k (размерность кода): "))

choice = input("Случайная перестановка? (y/n): ").strip().lower()
res = 0
for i in range(it):
    res += get_res(n, k, choice=None)

print(f"\nCРЕДНИЙ процент правильного восстановления: {res/it:.2f}%")
