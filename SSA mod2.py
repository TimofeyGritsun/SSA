from collections import Counter, defaultdict
from copy import deepcopy
from itertools import product

from typing import Optional
import sys
import os
from q_2 import HullCustomGF2Context, hull

class PrintToFile:
    def __init__(self, filepath="C:\\SSA\\out.txt"):
        self.filepath = filepath
        self.original_stdout = sys.stdout
        self.ensure_directory()
        
    def ensure_directory(self):
        directory = os.path.dirname(self.filepath)
        if directory and not os.path.exists(directory):
            os.makedirs(directory)
    
    def start(self):
        self.file = open(self.filepath, 'w', encoding='utf-8')
        sys.stdout = self.file
        print(f"=== Начало записи в файл: {self.filepath} ===")
        print(f"Время: {__import__('datetime').datetime.now()}")
        print("=" * 50)
    
    def stop(self):
        if hasattr(self, 'file') and not self.file.closed:
            print("\n" + "=" * 50)
            print(f"=== Конец записи ===")
            print(f"Файл сохранен: {self.filepath}")
            self.file.close()
        sys.stdout = self.original_stdout
    
    def __enter__(self):
        self.start()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        self.stop()

printer = PrintToFile()

def zero_column(matrix, col):
    M = deepcopy(matrix)
    for row in M:
        row[col] = 0
    return M

def rref_gf2(matrix):
    A = deepcopy(matrix)
    m = len(A)
    n = len(A[0])

    pivot_cols = []
    row = 0

    for col in range(n):
        if row >= m:
            break

        pivot = None
        for r in range(row, m):
            if A[r][col] == 1:
                pivot = r
                break

        if pivot is None:
            continue

        A[row], A[pivot] = A[pivot], A[row]
        pivot_cols.append(col)

        for r in range(m):
            if r != row and A[r][col] == 1:
                for c in range(n):
                    A[r][c] ^= A[row][c]

        row += 1

    return A, pivot_cols

def orthogonal_complement(matrix):
    if not matrix:
        return []

    m = len(matrix)
    n = len(matrix[0])

    rref, pivots = rref_gf2(matrix)
    pivots = set(pivots)

    free_cols = [j for j in range(n) if j not in pivots]

    basis = []

    for free in free_cols:
        v = [0] * n
        v[free] = 1

        for i, pivot_col in enumerate(sorted(pivots)):
            if rref[i][free] == 1:
                v[pivot_col] = 1

        basis.append(v)

    return basis

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

def weight_distribution_to_poly(counter):
    terms = []

    for w in sorted(counter.keys(), reverse=True):
        c = counter[w]

        if w == 0:
            terms.append(str(c))
        elif w == 1:
            terms.append("x" if c == 1 else f"{c}x")
        else:
            terms.append(f"x^{w}" if c == 1 else f"{c}x^{w}")

    return " + ".join(terms)

def weight_distribution(space, n):
    counter = Counter()

    for v in space:
        counter[sum(v)] += 1

    return counter

def weight_poly(matrix, col, hull, *, hull_ctx: Optional[HullCustomGF2Context] = None):
    if hull_ctx is not None:
        basis = hull_ctx.hull_zeroed([col], hull_fallback=hull)
    else:
        Mz = zero_column(matrix, col)
        basis = hull(Mz, 2)

    if not basis:
        space = [[0] * len(matrix[0])]
    else:
        space = generate_linear_space(basis)

    counter = weight_distribution(space, len(matrix[0]))
    return weight_distribution_to_poly(counter)

def choose_pivot(groups):
    return min(groups.items(), key=lambda x: len(x[1]))[1][0]

def extend_invariants_with_pivot(G, hull, pivot, frozen, current_invariants):
    G_dual = orthogonal_complement(G)

    result = dict(current_invariants)  

    G_u = zero_column(G, pivot)
    G_u_dual = orthogonal_complement(G_u)

    Gd_u = zero_column(G_dual, pivot)
    Gd_u_dual = orthogonal_complement(Gd_u)

    # Build contexts once per pivot-stage matrix to avoid repeating systematic/RtR for every j.
    ctx_G_u: Optional[HullCustomGF2Context] = None
    ctx_G_u_dual: Optional[HullCustomGF2Context] = None
    ctx_Gd_u: Optional[HullCustomGF2Context] = None
    ctx_Gd_u_dual: Optional[HullCustomGF2Context] = None
    try:
        ctx_G_u = HullCustomGF2Context.from_generator_ll(G_u)
        ctx_G_u_dual = HullCustomGF2Context.from_generator_ll(G_u_dual)
        ctx_Gd_u = HullCustomGF2Context.from_generator_ll(Gd_u)
        ctx_Gd_u_dual = HullCustomGF2Context.from_generator_ll(Gd_u_dual)
    except Exception:
        ctx_G_u = ctx_G_u_dual = ctx_Gd_u = ctx_Gd_u_dual = None

    n = len(G[0])

    for j in range(n):
        if j in frozen:
            continue

        P1 = weight_poly(G_u, j, hull, hull_ctx=ctx_G_u)
        P2 = weight_poly(G_u_dual, j, hull, hull_ctx=ctx_G_u_dual)
        P3 = weight_poly(Gd_u, j, hull, hull_ctx=ctx_Gd_u)
        P4 = weight_poly(Gd_u_dual, j, hull, hull_ctx=ctx_Gd_u_dual)

        result[j] = (P1, P2, P3, P4)

    return result

def group_and_print(base_inv, extended_inv, G, pivot):
    groups = defaultdict(list)

    for j in range(len(G[0])):
        key = (base_inv[j], extended_inv[j])
        groups[key].append(j + 1)

    print(f"Опорная позиция: {pivot + 1}\n")

    for (_, ext), positions in groups.items():
        print(f"Позиции {', '.join(map(str, positions))}")
        print(f"Имеют значение {ext}\n")

def weight_poly_for_position(G, col, hull, *, hull_ctx: Optional[HullCustomGF2Context] = None):
    if hull_ctx is not None:
        basis = hull_ctx.hull_zeroed([col], hull_fallback=hull)
    else:
        Gz = zero_column(G, col)
        basis = hull(Gz, 2)

    if not basis:
        space = [[0] * len(G[0])]
    else:
        space = generate_linear_space(basis)

    counter = weight_distribution(space, len(G[0]))
    return weight_distribution_to_poly(counter)

def analyze_G_and_dual(G, hull):
    G1 = orthogonal_complement(G)

    # Precompute contexts for the repeated single-column queries in SSA.
    ctx_G: Optional[HullCustomGF2Context] = None
    ctx_G1: Optional[HullCustomGF2Context] = None
    try:
        ctx_G = HullCustomGF2Context.from_generator_ll(G)
        ctx_G1 = HullCustomGF2Context.from_generator_ll(G1)
    except Exception:
        # If systematic form can't be built for some reason, fall back to the original path.
        ctx_G = None
        ctx_G1 = None

    n = len(G[0])
    groups = defaultdict(list)

    for j in range(n):
        poly_G = weight_poly_for_position(G, j, hull, hull_ctx=ctx_G)
        poly_G1 = weight_poly_for_position(G1, j, hull, hull_ctx=ctx_G1)

        key = (poly_G, poly_G1)
        groups[key].append(j)

    return groups

def print_groups(groups):
    for (p1, p2), positions in groups.items():
        pos_str = ", ".join(str(i + 1) for i in positions)
        print(f"Позиции {pos_str}")
        print(f"Имеют значение ({p1}, {p2})\n")

def poly_degree(poly_str):
    if poly_str == "0":
        return 0
    max_deg = 0
    for term in poly_str.split("+"):
        term = term.strip()
        if term == "1":
            max_deg = max(max_deg, 0)
        elif term == "x":
            max_deg = max(max_deg, 1)
        elif term.startswith("x^"):
            max_deg = max(max_deg, int(term[2:]))
        else:
            if "x^" in term:
                max_deg = max(max_deg, int(term.split("x^")[1]))
    return max_deg

def poly_vector_signature(poly_tuple):
    return tuple(poly_degree(p) for p in poly_tuple)

def sort_groups(groups, invariants):
    def group_key(group):
        inv = invariants[group[0]]
        if isinstance(inv, tuple) and len(inv) > 0 and isinstance(inv[0], tuple):
            last_layer = inv[-1]
        else:
            last_layer = inv

        sig = poly_vector_signature(last_layer)

        return (len(group), sig)

    return sorted(groups, key=group_key)

def print_groups_with_polynomials(groups, invariants, title=None):
    if title:
        print(title)
        print("-" * len(title))

    for i, g in enumerate(groups):
        pos_str = ", ".join(str(p + 1) for p in g)
        print(f"Группа {i}: позиции {pos_str}")

        inv = invariants.get(g[0])
        if inv is not None:
            print(f"  Полиномы: {inv}")
        else:
            print("  Полиномы: <не вычислены>")

        print()

def print_groups_with_polynomials(groups, invariants, title=None):
    if title:
        print(title)
        print("-" * len(title))

    for i, g in enumerate(groups):
        pos_str = ", ".join(str(p + 1) for p in g)
        inv = invariants[g[0]]

        print(f"Группа {i}: позиции {pos_str}")
        print(f"  Полиномы: {inv}")
        print()

def iterative_refinement_with_ordering(G, hull, max_iterations=5):
    n = len(G[0])

    base_groups_dict = analyze_G_and_dual(G, hull)

    base_invariants = {}
    groups = []
    for inv, positions in base_groups_dict.items():
        groups.append(list(positions))
        for p in positions:
            base_invariants[p] = inv

    current_invariants = {
        p: (base_invariants[p],)
        for p in range(n)
    }

    groups = sort_groups(groups, current_invariants)

    print_groups_with_polynomials(
        groups,
        {p: current_invariants[p][-1] for p in range(n)},
        title="ШАГ 0: базовые инварианты"
    )

    print("ШАГ 0:")
    for i, g in enumerate(groups):
        print(f"Группа {i}: {[p+1 for p in g]}")

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
            print("\nКОНЧИЛИСЬ ОПОРНЫЕ ПОЗИЦИИ")
            break

        used_pivots.add(pivot)

        print(f"\nШАГ {iteration + 1}: опорная позиция {pivot+1}")

        new_layer = extend_invariants_with_pivot(
            G,
            hull,
            pivot,
            frozen,
            current_invariants
        )

        extended_invariants = {}

        for p in range(n):
            if p in frozen:
                extended_invariants[p] = current_invariants[p]
            else:
                extended_invariants[p] = current_invariants[p] + (new_layer[p],)

        new_groups = []

        for g in groups:
            if len(g) == 1:
                new_groups.append(g)
                continue

            sub = {}
            for p in g:
                sub.setdefault(extended_invariants[p], []).append(p)

            subgroups = list(sub.values())
            subgroups = sort_groups(subgroups, extended_invariants)
            new_groups.extend(subgroups)

        groups = new_groups
        current_invariants = extended_invariants

        for g in groups:
            if len(g) == 1:
                frozen.add(g[0])

        print("Группы после шага:")
        for i, g in enumerate(groups):
            print(f"  Группа {i}: {[p+1 for p in g]}")

        print_groups_with_polynomials(
            groups,
            {p: current_invariants[p][-1] for p in range(n)},
            title=f"Результат после шага {iteration}"
        )

        if all(len(g) == 1 for g in groups):
            print("\nВсе позиции уникальны.")
            break

        iteration += 1

    return current_invariants


def match_positions_by_invariants(G, G1, hull, i):
    inv_G  = iterative_refinement_with_ordering(G, hull, i)
    inv_G1 = iterative_refinement_with_ordering(G1, hull, i)

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

import random

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

from typing import List, Tuple, Union, Dict, Any

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

def get_res(hull, n, k, choice):

    if choice == 'n':
        perm = list(map(int, input(f"Введите перестановку из {n} элементов (0-based): ").split()))
    else:
        perm = None

    G, G1, true_perm = generator(n, k, perm)
    
    printer.start()
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
    matching = match_positions_by_invariants(G, G1, hull, len(G[0]) - 2)

    print("Найденные соответствия:")
    for l, r in matching:
        print(f"{[x for x in l]} -> {[x for x in r]}")

    score = permutation_match_score(matching, inverse_permutation(true_perm))
    print(f"\nПроцент правильного восстановления: {score:.2f}%")
    printer.stop()
    return score


it = int(input("Количество итераций: "))
n = int(input("Введите n (длина кодового слова): "))
k = int(input("Введите k (размерность кода): "))

choice = input("Случайная перестановка? (y/n): ").strip().lower()
res = 0
for i in range(it):
    res += get_res(hull, n, k, choice)

print(f"\nCРЕДНИЙ процент правильного восстановления: {res/it:.2f}%")
