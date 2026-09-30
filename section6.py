r"""
Computations for Section 6 of the paper

    G. N. Alfarano, "Additive codes arising from hypergraphs".

The program recomputes every entry of Tables 1, 2, 3 and 4 of the paper and
checks that it agrees with the value printed in the paper. It also checks the
statements about the tables made in the text of Section 6.

How to run it (with SageMath installed):

    sage section6.py            all tables (about 20 minutes)
    sage section6.py --quick    skips the linear programs for the split Cayley
                                hexagon, the slowest part (about 4 minutes)
    sage section6.py 5          only Table 4 (any of 1, 2, 3, 4 can be given)

All linear and integer programs are solved exactly, with rational numbers
(the "PPL" solver of SageMath).
"""
import sys
from itertools import combinations

try:
    from sage.all import *
except ImportError:                      # the pip distribution "passagemath"
    from sage.all__sagemath_polyhedra import *
    from sage.all__sagemath_graphs import *
    from sage.all__sagemath_combinat import *
from sage.numerical.mip import MIPSolverException
from sage.version import version as SAGE_VERSION
import random as pyrandom             # Python's random module (Sage has its own 'random')

QUICK = '--quick' in sys.argv
TABLES = [int(a) for a in sys.argv[1:] if a in ('2', '3', '4', '5')] or [2, 3, 4, 5]

# ===========================================================================
# Small helpers for the output
# ===========================================================================
problems = []            # every disagreement with the paper is collected here

def compare(label, computed, paper):
    """Return 'ok' if the computed row is the one printed in the paper."""
    if computed == paper:
        return 'ok'
    problems.append((label, computed, paper))
    return 'DIFFERENT, paper has %s' % (paper,)

def claim(text, holds):
    """Print a statement of the text of Section 6 and whether it holds."""
    print('  - %s: %s' % (text, 'yes' if holds else 'NO'))
    if not holds:
        problems.append((text, False, True))

def show(x):
    return '-' if x is None else str(x)

def print_row(cells, widths):
    out = [str(cells[0]).ljust(widths[0])]
    out += [str(c).rjust(w) for c, w in zip(cells[1:], widths[1:])]
    print('  ' + ' '.join(out))

def smallest_t(condition):
    """Smallest integer t >= 0 with condition(t) true."""
    t = 0
    while not condition(t):
        t += 1
    return t

# ===========================================================================
# 1. Bounds that hold for every additive code (Section 6.1)
# ===========================================================================
def krawtchouk(Q, n, j, i):
    """The Q-ary Krawtchouk polynomial K_j evaluated at i."""
    return sum((-1)**l * (Q - 1)**(j - l) * binomial(i, l) * binomial(n - i, j - l)
               for l in range(j + 1))

def has_solution(q, h, n, k, d, dperp, integer=False, linear_image=False):
    """Does the linear system of Section 6.1 have a solution?

    Unknowns: A_0..A_n (weight distribution of the code) and B_0..B_n (of its
    dual), all >= 0, and integers if integer=True.  Equations:
        A_0 = B_0 = 1,   A_0 + ... + A_n = q^k,
        A_i = 0 for 1 <= i < d,   B_j = 0 for 1 <= j < dperp,
        q^k B_j = sum_i A_i K_j(i)   (MacWilliams identities).
    dperp = 1 means no condition on the dual (Delsarte's bound).
    linear_image=True adds Delsarte's inequalities for the associated linear
    code of length [h]_q n in which each subspace is replaced by its points."""
    Q = q**h
    p = MixedIntegerLinearProgram(maximization=False, solver="PPL")
    A = p.new_variable(nonnegative=True, integer=integer)
    B = p.new_variable(nonnegative=True, integer=integer)
    p.add_constraint(A[0] == 1)
    p.add_constraint(B[0] == 1)
    p.add_constraint(sum(A[i] for i in range(n + 1)) == q**k)
    for i in range(1, min(d, n + 1)):
        p.add_constraint(A[i] == 0)
    for j in range(1, min(dperp, n + 1)):
        p.add_constraint(B[j] == 0)
    for j in range(n + 1):
        p.add_constraint(q**k * B[j] == sum(A[i] * krawtchouk(Q, n, j, i) for i in range(n + 1)))
    if linear_image:
        L, w = ((q**h - 1) // (q - 1)) * n, q**(h - 1)
        for j in range(1, L + 1):
            expr = sum(A[i] * krawtchouk(q, L, j, w * i) for i in range(n + 1))
            p.add_constraint(expr == 0 if j == 1 else expr >= 0)
    p.set_objective(0)
    try:
        p.solve()
        return True
    except MIPSolverException:           # raised when there is no solution
        return False

def q_int(a, q):
    """[a]_q = (q^a - 1)/(q - 1)."""
    return (q**a - 1) // (q - 1)

def griesmer_function(q, k, D):
    """g_q(k, D) = sum_{i<k} ceil(D / q^i)."""
    return sum(-(-D // q**i) for i in range(k))

def singleton_bound(n, k, h):
    return n - ceil(k / h) + 1

def griesmer_bound(q, n, k, h):
    """Largest d allowed by the additive Griesmer bound [h]_q n >= g_q(k, q^(h-1) d)."""
    return max(d for d in range(1, n + 1) if griesmer_function(q, k, q**(h - 1) * d) <= q_int(h, q) * n)

def lp_bound(q, n, k, h, dperp):
    """Largest d <= Singleton bound for which the linear system has a real solution.
    A larger d only adds conditions, so we can use binary search."""
    lo, hi = 1, singleton_bound(n, k, h)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if has_solution(q, h, n, k, mid, dperp):
            lo = mid
        else:
            hi = mid - 1
    assert has_solution(q, h, n, k, lo, dperp)
    return lo

# ===========================================================================
# 2. Hypergraphs (Sections 2, 4, 5 and 6.2)
# ===========================================================================
def complete_hypergraph(N, r):
    """K_N^(r): all r-subsets of an N-set."""
    return list(range(N)), [tuple(S) for S in Subsets(range(N), r)]

def from_design(D):
    return list(D.ground_set()), [tuple(b) for b in D.blocks()]

def lines_of(G):
    """Points and lines of a generalised quadrangle or hexagon, from its
    collinearity graph G: the lines are the maximal cliques."""
    return list(G.vertices(sort=True)), [tuple(c) for c in G.cliques_maximal()]

def pasch():
    """Points: the 6 edges of K_4. Lines: the 4 stars of the vertices of K_4."""
    E = graphs.CompleteGraph(4).edges(sort=True, labels=False)
    return list(range(6)), [tuple(i for i, e in enumerate(E) if v in e) for v in range(4)]

def desargues():
    """Points: the 2-subsets of {0,..,4}. Lines: the 3-subsets."""
    V = [tuple(S) for S in Subsets(range(5), 2)]
    return V, [tuple(P for P in V if set(P) <= set(T)) for T in Subsets(range(5), 3)]

def split_cayley_hexagon():
    """GH(2,2): points of X0X4 + X1X5 + X2X6 = X3^2 in PG(6,2), and the lines of
    this quadric satisfying the conditions on the Grassmann coordinates given
    in the paper (Example 'catalogue', item (d))."""
    F = GF(2)
    quadric = lambda x: x[0]*x[4] + x[1]*x[5] + x[2]*x[6] + x[3]**2
    points = [tuple(F(c) for c in v) for v in ProjectiveSpace(6, F).rational_points()
              if quadric(v) == 0]
    point_set = set(points)
    lines = set()
    for a, b in combinations(points, 2):
        c = tuple(x + y for x, y in zip(a, b))       # third point of the line ab
        if c not in point_set:
            continue
        p = lambda i, j: a[i]*b[j] - a[j]*b[i]        # Grassmann coordinates
        if all(p(*u) == p(*v) for u, v in [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
                                             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]):
            lines.add(frozenset([a, b, c]))
    return points, [tuple(l) for l in lines]

def build_hypergraph(name):
    """The hypergraphs of Tables 2 and 3, built with SageMath's own constructions
    where they exist."""
    if name == 'H0':        return [1, 2, 3, 4], [(1, 2, 3), (1, 2, 4), (1, 3, 4)]
    if name == 'H1':        return list(range(6)), [(2, 3, 4, 5), (0, 1, 4, 5), (0, 1, 2, 3)]
    if name == 'K4^(3)':    return complete_hypergraph(4, 3)
    if name == 'K5^(3)':    return complete_hypergraph(5, 3)
    if name == 'K6^(3)':    return complete_hypergraph(6, 3)
    if name == 'K9^(3)':    return complete_hypergraph(9, 3)
    if name == 'K5^(4)':    return complete_hypergraph(5, 4)
    if name == 'Pasch':     return pasch()
    if name == 'Fano':      return from_design(designs.ProjectiveGeometryDesign(2, 1, GF(2)))
    if name == 'PG(2,3)':   return from_design(designs.ProjectiveGeometryDesign(2, 1, GF(3)))
    if name == 'AG(2,3)':   return from_design(designs.AffineGeometryDesign(2, 1, GF(3)))
    if name == 'Desargues': return desargues()
    if name == 'GQ(2,1)':   return lines_of(graphs.RookGraph([3, 3]))
    if name == 'GQ(2,2)':   return lines_of(graphs.SymplecticPolarGraph(4, 2))
    if name == 'GQ(2,4)':   return lines_of(graphs.OrthogonalPolarGraph(6, 2, '-'))
    if name == 'GQ(4,2)':   return lines_of(graphs.UnitaryPolarGraph(4, 2))
    if name == 'GH(2,2)':   return split_cayley_hexagon()
    raise ValueError(name)

# generalised polygons: (s, t, n) = (points per line - 1, lines per point - 1,
# half the girth of the incidence graph), used to check the constructions
POLYGONS = {'GQ(2,1)': (2, 1, 4), 'GQ(2,2)': (2, 2, 4), 'GQ(2,4)': (2, 4, 4),
            'GQ(4,2)': (4, 2, 4), 'GH(2,2)': (2, 2, 6)}

class Hypergraph:
    def __init__(self, name):
        V, E = build_hypergraph(name)
        self.name, self.V, self.E = name, list(V), [tuple(e) for e in E]
        self.N, self.m = len(self.V), len(self.E)
        sizes = {len(e) for e in self.E}
        assert len(sizes) == 1, "the hypergraph must be uniform"
        self.r = sizes.pop()
        self.h = self.r - 1              # the code C_H lives in F_{q^h}^m
        self.k = self.N - 1              # its F_q-dimension
        self.incidence = Graph([(('v', v), ('e', i)) for i, e in enumerate(self.E) for v in e])
        assert self.incidence.is_connected() and self.incidence.order() == self.N + self.m
        degrees = [sum(1 for e in self.E if v in e) for v in self.V]
        self.min_degree, self.max_degree = min(degrees), max(degrees)
        if name in POLYGONS:             # check that we built the right geometry
            s, t, n = POLYGONS[name]
            assert self.r == s + 1 and self.min_degree == self.max_degree == t + 1
            assert self.incidence.girth() == 2*n and self.incidence.diameter() == n

    def berge_girth(self):
        """Half the girth of the incidence graph (= dual distance of C_H)."""
        g = self.incidence.girth()
        return Infinity if g == Infinity else g // 2

    def edge_connectivity(self):
        """lambda(H) (= minimum distance of C_H), as a minimum cut: each edge of H
        becomes an arc of capacity 1, and we compute maximum flows."""
        D = DiGraph()
        big = self.m + 1
        for i, e in enumerate(self.E):
            D.add_edge(('in', i), ('out', i), 1)
            for v in e:
                D.add_edge(('v', v), ('in', i), big)
                D.add_edge(('out', i), ('v', v), big)
        s = self.V[0]
        return min(D.flow(('v', s), ('v', t)) for t in self.V[1:])

    def spectral_bound(self):
        """Lower bound of the Laplacian theorem, computed exactly."""
        index = {v: a for a, v in enumerate(self.V)}
        L = matrix(ZZ, self.N, self.N)
        for e in self.E:
            for u, w in combinations(e, 2):
                a, b = index[u], index[w]
                L[a, b] -= 1; L[b, a] -= 1; L[a, a] += 1; L[b, b] += 1
        eigenvalues = sorted(x for x, mult in L.charpoly().roots(AA) for _ in range(mult))
        mu2 = eigenvalues[1]
        return ceil(mu2 * (self.N - 1) / (self.N * floor(self.r**2 / 4)))

    def weak_chromatic_number(self):
        colouring = IncidenceStructure(self.V, self.E).coloring()
        colour = {v: c for c, cls in enumerate(colouring) for v in cls}
        assert all(len({colour[v] for v in e}) > 1 for e in self.E)   # no monochromatic edge
        return len(colouring)

    def weak_independence_number(self):
        """Largest set of vertices containing no edge."""
        p = MixedIntegerLinearProgram(maximization=True)
        x = p.new_variable(binary=True)
        for e in self.E:
            p.add_constraint(sum(x[v] for v in e) <= len(e) - 1)
        p.set_objective(sum(x[v] for v in self.V))
        return int(round(p.solve()))

    def tau_is_minimal(self, tries=2000):
        """Check tau(H) = ceil((N-1)/h), by finding a connected spanning
        subhypergraph with that many edges (fewer edges are impossible)."""
        sigma = ceil((self.N - 1) / self.h)
        rnd = pyrandom.Random(0)
        for _ in range(tries):
            covered, used = set(self.E[rnd.randrange(self.m)]), 1
            while len(covered) < self.N:
                touching = [e for e in self.E if covered & set(e)]
                most = max(len(set(e) - covered) for e in touching)
                covered |= set(rnd.choice([e for e in touching if len(set(e) - covered) == most]))
                used += 1
            if used == sigma:
                return True
        return False

def girth_distance_bound(k, h, g):
    """Largest d allowed by parts (i) and (ii) of the girth-distance bound."""
    if g == Infinity or g <= 2:
        return None
    def allowed(d):
        for t in range(1, g + 1):
            S = sum((h * (d - 1))**j for j in range(t))
            if g >= 2*t + 1 and k < h * d * S:
                return False
            if g >= 2*t and k < (h + 1) * S - 1:
                return False
        return True
    d = 1
    while allowed(d + 1):
        d += 1
    return d

# ===========================================================================
# 3. Table 1: minimum distance of hypergraphic codes
# ===========================================================================
# values printed in the paper:
#   h, N, m, dperp, d, spectral, degree, girth-distance, Singleton, Griesmer, LP
TABLE2 = {
    'H0':        (2, 4, 3, 2, 2, 2, 2, None, 2, 2, 2),
    'K4^(3)':    (2, 4, 4, 2, 3, 3, 3, None, 3, 3, 3),
    'K5^(3)':    (2, 5, 10, 2, 6, 6, 6, None, 9, 8, 8),
    'K6^(3)':    (2, 6, 20, 2, 10, 10, 10, None, 18, 15, 15),
    'Pasch':     (2, 6, 4, 3, 2, 2, 2, 2, 2, 2, 2),
    'Fano':      (2, 7, 7, 3, 3, 3, 3, 3, 5, 4, 4),
    'AG(2,3)':   (2, 9, 12, 3, 4, 4, 4, 4, 9, 8, 7),
    'Desargues': (2, 10, 10, 3, 3, 3, 3, 4, 6, 6, 6),
    'GQ(2,1)':   (2, 9, 6, 4, 2, 2, 2, 2, 3, 3, 2),
    'GQ(2,2)':   (2, 15, 15, 4, 3, 3, 3, 3, 9, 8, 7),
    'GQ(2,4)':   (2, 27, 45, 4, 5, 5, 5, 5, 33, 28, 25),
    'GH(2,2)':   (2, 63, 63, 6, 3, 2, 3, 3, 33, 32, 24),
    'H1':        (3, 6, 3, 2, 2, 2, 2, None, 2, 2, 2),
    'K5^(4)':    (3, 5, 5, 2, 4, 3, 4, None, 4, 4, 4),
    'PG(2,3)':   (3, 13, 13, 3, 4, 3, 4, 4, 10, 10, 9),
    'GQ(4,2)':   (4, 45, 27, 4, 3, 2, 3, 3, 17, 23, 16)}

def table2():
    print('\nTABLE 2. Minimum distance of the hypergraphic codes C_H (Griesmer and LP for q = 2)\n')
    widths = [10, 2, 3, 3, 6, 3, 9, 7, 15, 10, 9, 4, 0]
    print_row(['H', 'h', 'N', 'm', 'dperp', 'd', 'spectral', 'degree', 'girth-distance',
               'Singleton', 'Griesmer', 'LP', '  paper?'], widths)
    lp_same_with_dperp_2, lambda_is_degree, tau_ok = True, True, True
    for name in TABLE2:
        H = Hypergraph(name)
        gB, lam = H.berge_girth(), H.edge_connectivity()
        skip = QUICK and name == 'GH(2,2)'
        dperp = gB if gB != Infinity else H.m + 1
        lp = None if skip else lp_bound(2, H.m, H.k, H.h, dperp)
        row = (H.h, H.N, H.m, gB, lam, H.spectral_bound(), H.min_degree,
               girth_distance_bound(H.k, H.h, gB), singleton_bound(H.m, H.k, H.h),
               griesmer_bound(2, H.m, H.k, H.h), lp)
        if skip:
            status = compare('Table 2, ' + name, row[:-1], TABLE2[name][:-1]) + ' (LP skipped)'
        else:
            status = compare('Table 2, ' + name, row, TABLE2[name])
            lp_same_with_dperp_2 &= (lp_bound(2, H.m, H.k, H.h, 2) == lp)
        print_row([name] + [show(x) for x in row] + ['  ' + status], widths)
        lambda_is_degree &= (lam == H.min_degree)
        tau_ok &= H.tau_is_minimal()
    print('\n  Statements in the text:')
    claim('lambda(H) = minimum degree in every row', lambda_is_degree)
    claim('tau(H) = ceil((N-1)/h) in every row', tau_ok)
    claim('the LP column does not change with dperp = 2' + (' (GH(2,2) skipped)' if QUICK else ''),
          lp_same_with_dperp_2)

# ===========================================================================
# 4. Table 2: critical exponent of hypergraphic codes
# ===========================================================================
# values printed in the paper:
#   N, chi_w, crit, alpha-bound, Delta-bound, t0, Kung-type, k-h+1
TABLE3 = {
    'K5^(3)':    (5, 3, 2, 2, 3, 2, None, 3),
    'K6^(3)':    (6, 3, 2, 2, 4, 3, None, 4),
    'K9^(3)':    (9, 5, 3, 3, 5, 4, None, 7),
    'Fano':      (7, 3, 2, 1, 2, 2, 4, 5),
    'AG(2,3)':   (9, 3, 2, 2, 3, 2, 6, 7),
    'Desargues': (10, 2, 1, 1, 2, 2, 7, 8),
    'GQ(2,2)':   (15, 2, 1, 1, 2, 2, 10, 13),
    'GQ(2,4)':   (27, 2, 1, 1, 3, 3, 22, 25),
    'GH(2,2)':   (63, 2, 1, 1, 2, 3, 54, 61),
    'PG(2,3)':   (13, 2, 1, 1, 3, 2, 8, 10),
    'GQ(4,2)':   (45, 2, 1, 1, 2, 2, 34, 41)}

def table3():
    print('\nTABLE 3. Critical exponent of the hypergraphic codes C_H for q = 2\n')
    widths = [10, 3, 6, 5, 12, 12, 3, 10, 6, 0]
    print_row(['H', 'N', 'chi_w', 'crit', 'alpha-bound', 'Delta-bound', 't0', 'Kung-type',
               'k-h+1', '  paper?'], widths)
    for name in TABLE3:
        H = Hypergraph(name)
        gB = H.berge_girth()
        chi, alpha = H.weak_chromatic_number(), H.weak_independence_number()
        row = (H.N, chi,
               smallest_t(lambda t: 2**t >= chi),                          # crit (Helgason-Whittle)
               smallest_t(lambda t: 2**t >= ceil(H.N / alpha)),            # lower bound
               smallest_t(lambda t: 2**t >= H.max_degree + 1),             # upper bound
               smallest_t(lambda t: t >= 1 and H.m < 2**(t * H.h)),        # t0
               H.k - H.h * (gB - 1) + 2 if 3 <= gB < Infinity else None,   # Kung-type
               H.k - H.h + 1)
        print_row([name] + [show(x) for x in row]
                  + ['  ' + compare('Table 3, ' + name, row, TABLE3[name])], widths)

# ===========================================================================
# 5. Table 3: some additive codes that are not hypergraphic codes
# ===========================================================================
# The two codes found by Kurz (arXiv:2412.14615, Section F): each pair of
# binary vectors spans one of the lines (2-dimensional subspaces) of F_2^7.
KURZ_22 = ("0001001,0000010 0100011,0000110 0100010,0010100 0100110,0011110 0101101,0010010 "
           "0101100,0010111 1001100,0000001 1000011,0011000 1001011,0011011 1001110,0010001 "
           "1011010,0000100 1000110,0100001 1000001,0110001 1000010,0110000 1010111,0100000 "
           "1011101,0110101 1011000,0111100 1100010,0001011 1100101,0001000 1101010,0011111 "
           "1110001,0001110 1110100,0001100")
KURZ_25 = ("0010100,0001010 0011001,0000101 0010111,0001111 0100111,0011010 0101110,0010101 "
           "0101001,0011111 1000100,0010001 1001100,0010011 1001000,0010010 1000101,0101011 "
           "1001111,0100110 1001010,0101101 1010111,0101000 1011110,0100100 1010110,0101010 "
           "1011101,0100101 1011011,0101111 1011001,0101100 1010100,0110001 1011100,0110011 "
           "1011000,0110010 1100011,0000111 1100010,0001110 1100001,0001001 0001000,0000100")

class AdditiveCode:
    """An additive code given by its blocks: blocks[i] is a k x h matrix over
    F_q whose columns span the subspace U_i of the projective system."""
    def __init__(self, q, h, blocks):
        self.q, self.h, self.n, self.blocks = q, h, len(blocks), blocks
        self.G = block_matrix([blocks], subdivide=False)       # expanded generator matrix
        self.k = self.G.nrows()
        assert self.G.rank() == self.k and all(b.rank() == h for b in blocks)   # faithful
        # supports of all codewords, as bit masks
        self.supports = []
        for x in VectorSpace(GF(q), self.k):
            c = x * self.G
            self.supports.append(sum(1 << i for i in range(self.n) if c[h*i:h*i + h] != 0))
        self.A = [0] * (self.n + 1)                            # weight distribution
        for s in self.supports:
            self.A[bin(s).count('1')] += 1

    def minimum_distance(self):
        return min(i for i in range(1, self.n + 1) if self.A[i])

    def dual_distance(self):
        """Computed in two ways: from the MacWilliams identities, and as the
        smallest number of blocks whose columns are linearly dependent."""
        Q, n, k = self.q**self.h, self.n, self.k
        B = [sum(self.A[i] * krawtchouk(Q, n, j, i) for i in range(n + 1)) / QQ(self.q**k)
             for j in range(n + 1)]
        assert all(b in ZZ and b >= 0 for b in B)
        dperp = min((j for j in range(1, n + 1) if B[j]), default=Infinity)
        t = next(t for t in range(1, n + 1) if any(
            block_matrix([[self.blocks[i] for i in S]], subdivide=False).rank() < self.h * t
            for S in combinations(range(n), t)))
        assert t == dperp
        return dperp

    def critical_exponent(self):
        """Smallest number of codewords whose supports cover all coordinates."""
        full = (1 << self.n) - 1
        S = sorted(set(s for s in self.supports if s), reverse=True)
        def cover(t, current, start):
            if current == full:
                return True
            return t > 0 and any(cover(t - 1, current | S[j], j + 1) for j in range(start, len(S)))
        return smallest_t(lambda t: t >= 1 and cover(t, 0, 0))

def spread_code(q, h):
    """The Desarguesian spread of F_q^(2h): the points of PG(1, q^h)."""
    F = GF(q**h, 'a'); a = F.gen()
    V, from_V, to_V = F.vector_space(map=True)
    points = [(F(1), x) for x in F] + [(F(0), F(1))]
    blocks = [matrix(GF(q), [list(to_V(a**j * x)) + list(to_V(a**j * y)) for j in range(h)]).transpose()
              for (x, y) in points]
    return AdditiveCode(q, h, blocks)

def hexacode():
    """The hexacode, an F_4-linear [6,3,4] code, as an additive code over F_2."""
    F = GF(4, 'w'); w = F.gen()
    V, from_V, to_V = F.vector_space(map=True)
    G = matrix(F, [[1, 0, 0, 1, w, w], [0, 1, 0, w, 1, w], [0, 0, 1, w, w, 1]])
    assert LinearCode(G).minimum_distance() == 4
    rows = [g for r in G.rows() for g in (r, w * r)]           # an F_2-basis of the code
    M = matrix(GF(2), [[c for x in r for c in to_V(x)] for r in rows])
    return AdditiveCode(2, 2, [M[:, 2*i:2*i + 2] for i in range(6)])

def kurz_code(data):
    blocks = [matrix(GF(2), [[int(c) for c in u] for u in pair.split(',')]).transpose()
              for pair in data.split()]
    return AdditiveCode(2, 2, blocks)

# values printed in the paper:
#   q, h, n, k, d, dperp, Singleton, Griesmer, LP, crit, t0, Kung-type, k-h+1
TABLE4 = {
    'spread q=2 h=2': (2, 2, 5, 4, 4, 3, 4, 4, 4, 2, 2, 2, 3),
    'spread q=3 h=2': (3, 2, 10, 4, 9, 3, 9, 9, 9, 2, 2, 2, 3),
    'spread q=2 h=3': (2, 3, 9, 6, 8, 3, 8, 8, 8, 2, 2, 2, 4),
    'hexacode':       (2, 2, 6, 6, 4, 4, 4, 4, 4, 1, 2, 2, 5),
    'Kurz [22,7/2]':  (2, 2, 22, 7, 16, 2, 19, 16, 16, 2, 3, None, 6),
    'Kurz [25,7/2]':  (2, 2, 25, 7, 18, 3, 22, 18, 18, 2, 3, 5, 6)}

def table4():
    print('\nTABLE 4. Some additive codes that are not hypergraphic codes C_H\n')
    widths = [15, 2, 2, 3, 2, 3, 6, 10, 9, 4, 5, 3, 10, 6, 0]
    print_row(['code', 'q', 'h', 'n', 'k', 'd', 'dperp', 'Singleton', 'Griesmer', 'LP',
               'crit', 't0', 'Kung-type', 'k-h+1', '  paper?'], widths)
    codes = {'spread q=2 h=2': lambda: spread_code(2, 2), 'spread q=3 h=2': lambda: spread_code(3, 2),
             'spread q=2 h=3': lambda: spread_code(2, 3), 'hexacode': hexacode,
             'Kurz [22,7/2]': lambda: kurz_code(KURZ_22), 'Kurz [25,7/2]': lambda: kurz_code(KURZ_25)}
    for name, make in codes.items():
        C = make()
        q, h, n, k = C.q, C.h, C.n, C.k
        dperp = C.dual_distance()
        row = (q, h, n, k, C.minimum_distance(), dperp, singleton_bound(n, k, h),
               griesmer_bound(q, n, k, h), lp_bound(q, n, k, h, dperp if dperp != Infinity else n + 1),
               C.critical_exponent(), smallest_t(lambda t: t >= 1 and n < q**(t * h)),
               k - h * (dperp - 1) + 2 if 3 <= dperp < Infinity else None, k - h + 1)
        print_row([name] + [show(x) for x in row]
                  + ['  ' + compare('Table 4, ' + name, row, TABLE4[name])], widths)

# ===========================================================================
# 6. Table 4: upper bounds on the optimal length n_2(k,2;s)
# ===========================================================================
def n2_kurz(k, s):
    """The exact values n_2(k,2;s), taken from Kurz, arXiv:2412.14615,
    Theorems 12-15 (not computed here)."""
    if k == 5:
        t = -(-s // 7)
        return 31*t - [0, 5, 10, 15, 20, 23, 28][7*t - s]
    if k == 6:
        if s == 3: return 9
        t = -(-s // 5)
        return 21*t - [0, 5, 10, 15, 20][5*t - s]
    if k == 7:
        special = {5: 17, 4: 12, 3: 7, 2: 2}
        if s in special: return special[s]
        t = -(-s // 31)
        off = [0, 5, 10, 15, 20, 21, 26, 31, 36, 41, 42, 47, 52, 55, 60, 63, 68, 73, 76, 81, 84,
               87, 92, 95, 100, 105, 108, 113, 116, 121, 126]
        return 127*t - off[31*t - s]
    if k == 8:
        special = {15: 55, 11: 40, 10: 36, 8: 28, 29: 113, 7: 23, 28: 108, 6: 18, 4: 10, 3: 5, 2: 2}
        if s in special: return special[s]
        t = -(-s // 21)
        off = [0, 5, 10, 15, 20, 21, 26, 31, 36, 41, 42, 47, 52, 55, 60, 63, 68, 73, 76, 81, 84]
        return 85*t - off[21*t - s]

# values printed in the paper (Table 5 for k = 7, 8; the text for k = 5, 6):
#   (k, s): Griesmer, LP, ILP
TABLE5 = {
    (5, 2): (8, 8, 8), (5, 3): (11, 13, 13), (5, 4): (16, 17, 17), (5, 5): (21, 22, 21),
    (5, 6): (26, 26, 26), (5, 7): (31, 31, 31), (5, 8): (34, 35, 35), (5, 9): (39, 39, 39),
    (5, 10): (42, 44, 44), (5, 11): (47, 48, 48), (5, 12): (52, 53, 52),
    (6, 2): (6, 6, 6), (6, 3): (11, 11, 11), (6, 4): (16, 16, 16), (6, 5): (21, 21, 21),
    (6, 6): (22, 25, 24), (6, 7): (27, 29, 29), (6, 8): (32, 33, 33), (6, 9): (37, 37, 37),
    (6, 10): (42, 42, 42), (6, 11): (43, 46, 45), (6, 12): (48, 50, 50),
    (7, 3): (11, 9, 9), (7, 4): (14, 14, 14), (7, 5): (19, 18, 18), (7, 6): (22, 23, 22),
    (7, 7): (27, 27, 27), (7, 8): (32, 32, 32), (7, 9): (35, 36, 36), (7, 10): (40, 40, 40),
    (7, 11): (43, 45, 44), (7, 12): (46, 49, 48),
    (8, 3): (9, 5, 5), (8, 4): (12, 11, 11), (8, 5): (17, 17, 17), (8, 6): (22, 22, 22),
    (8, 7): (25, 26, 26), (8, 8): (30, 30, 30), (8, 9): (33, 34, 34), (8, 10): (38, 38, 38),
    (8, 11): (43, 43, 42), (8, 12): (44, 47, 47)}

def largest_n(k, s, top, **options):
    """Largest n <= top for which the linear system with d = n - s has a solution."""
    return next((n for n in range(top, s, -1) if has_solution(2, 2, n, k, n - s, **options)), None)

def table5():
    print('\nTABLE 5. Upper bounds on n_2(k,2;s), the largest length of a faithful additive code')
    print('         over F_4 of F_2-dimension k with n - d <= s\n')
    widths = [2, 3, 9, 4, 4, 13, 9, 11, 17, 0]
    print_row(['k', 's', 'Griesmer', 'LP', 'ILP', 'n_2 (Kurz)', 'Delsarte', 'divisible',
               'simple bound', '  paper?'], widths)
    rows = {}
    for (k, s) in TABLE5:
        griesmer = max(n for n in range(s + 1, 400)
                       if griesmer_function(2, k, 2 * (n - s)) <= 3 * n)
        simple = (q_int(k, 2) * s) // q_int(k - 2, 2)      # Kurz, Lemma 16: no solution above it
        lp = largest_n(k, s, simple + 2, dperp=2)
        ilp = largest_n(k, s, lp, dperp=2, integer=True)
        delsarte = largest_n(k, s, simple + 2, dperp=1)           # without B_1 = 0
        divisible = largest_n(k, s, lp, dperp=2, linear_image=True)
        rows[(k, s)] = (griesmer, lp, ilp, n2_kurz(k, s), delsarte, divisible, simple)
        print_row([k, s, griesmer, lp, ilp, n2_kurz(k, s), delsarte, divisible, simple,
                   '  ' + compare('Table 5, %s' % ((k, s),), (griesmer, lp, ilp), TABLE5[(k, s)])],
                  widths)
    print('\n  Statements in the text:')
    claim('Delsarte variant and divisible-code variant give the same values as LP',
          all(r[4] == r[1] and r[5] == r[1] for r in rows.values()))
    claim('for k = 5, 6 the Griesmer bound equals n_2, except n_2(6,2;3) = 9 < 11',
          all((r[0] == r[3]) == ((k, s) != (6, 3)) for (k, s), r in rows.items() if k in (5, 6)))
    claim('for k = 5, 6 neither LP nor ILP is below the Griesmer bound',
          all(r[1] >= r[0] and r[2] >= r[0] for (k, s), r in rows.items() if k in (5, 6)))
    claim('LP is below the Griesmer bound in exactly 4 cases',
          sum(r[1] < r[0] for r in rows.values()) == 4)
    claim('ILP is below the Griesmer bound in exactly 5 cases, the new one being (8,11)',
          [ks for ks, r in rows.items() if r[2] < r[0] and r[1] >= r[0]] == [(8, 11)]
          and sum(r[2] < r[0] for r in rows.values()) == 5)
    claim('LP and ILP give n_2(8,2;3) = 5', rows[(8, 3)][1] == rows[(8, 3)][2] == 5)
    claim('ILP is below LP in exactly 8 of the 42 cases', sum(r[2] < r[1] for r in rows.values()) == 8)
    claim('LP equals the simple bound for k = 5, for k = 6 with s >= 4, for k = 7 with s >= 8',
          all(r[1] == r[6] for (k, s), r in rows.items()
              if k == 5 or (k == 6 and s >= 4) or (k == 7 and s >= 8)))

# ===========================================================================
if __name__ == '__main__':
    print('SageMath version', SAGE_VERSION, '- tables', ', '.join(map(str, TABLES)),
          '(quick mode)' if QUICK else '')
    for number in TABLES:
        {2: table2, 3: table3, 4: table4, 5: table5}[number]()
    print()
    if problems:
        print('%d DISAGREEMENTS WITH THE PAPER:' % len(problems))
        for p in problems:
            print('  ', p)
    else:
        print('All computed values agree with the paper.')
