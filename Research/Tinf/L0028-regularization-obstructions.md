# L_0028 — regularization can destroy closure preservation

Use the real line, x = -3/2, I = [-2,-1], and n ≥ 2. Set
K_n = I ∪ {0} ∪ [1/n,1]. Every nonempty finite subfamily has
closed union. Every infinite subfamily has union I ∪ [0,1],
since its indices are unbounded. Thus the K_n form a CP family.

Adjoin J_n = [x-1/(4n), x+1/(4n)] for n ≥ 2. Each nonempty
subfamily of the J_n has a largest member (least index), so
these form a CP family. The union of the two families is CP
by finite union of closed sets, and the J_n make it a closed
neighborhood base at x. The real line meets the other L_0028
hypotheses, with an enumeration of rationals giving singleton
closed discrete levels whose union is dense.

But cl(int K_n) = I ∪ [1/n,1]. These regularized members have
union I ∪ (0,1], which is not closed. Adding the J_n cannot
repair this failure because CP quantifies over all subfamilies.

This is a counterexample to the pointwise operation on the
given base, not to existence of a CP regular closed base.
In this example the J_n alone already give such a base.

## Completion by intersections

For a CP family F of closed sets, its completion under arbitrary
intersections is still CP. For a point y missed by a chosen union
of intersections, each of the chosen intersections has at least
one factor in F missing y. Their entire union is therefore inside
the union of all factors in F missing y. This latter union is
closed by CP and misses y. The empty intersection is the entire
space and cannot occur in a union missing y.

This allows imposing finite meet closure on the input neighborhood
base while keeping its original cofinality and CP property. Arbitrary
intersections need not remain neighborhoods. Finite meet closure
alone does not fix the regularization example above, because the
original bad subfamily is still present after completion.

## Reduce the regularization test to thin points

Write R(K) = cl(int K). For each y and a CP family F of closed
sets, let A_y be the union of all K in F missing y. This is closed
and misses y. On the open neighborhood X minus A_y, all K missing
y disappear, as do their subsets R(K).

By the pointwise CP criterion, R[F] is CP exactly when, for every y,
y is outside the closure of the union of R(K) over members K with
y in K minus R(K). Indeed, among all K whose R(K) misses y, the
remaining class consists exactly of K missing y, and its union
lies in A_y. Closure distributes over this two-way union.

Thus any repair by thinning the input base only needs to control
members with y in their non-regular part. In the real-line example
the offending y is zero. This criterion does not assert existence
of a cofinal subfamily satisfying it.

## Canonical neighborhoods for the completed closed family

For each point y, define V(y) to be the complement of the union of
all original members missing y. Then V(y) is open, contains y, and
z ∈ V(y) means that every original member containing z contains y.
Consequently z ∈ V(y) implies V(z) ⊆ V(y), by transitivity.

Call a set downward closed when z in the set and z ∈ V(y) imply
that y is in the set. The original closed family consists of such
sets. Every downward closed set S is closed in the original
topology: if y is outside S, then V(y) is disjoint from S. The
downward closed sets are stable under all unions and intersections.
In particular the family obtained by allowing both operations,
in any order, consists of closed sets and is CP.

For L_0028, this gives an auxiliary topology with the V(y) as
smallest open neighborhoods. Regularizing a closed member in the
original topology need not produce a closed member of this auxiliary
topology. Indeed, in the real-line example each positive z ≤ 1 is
in V(0), while R(K_n) contains some such z and omits 0. A route via
the auxiliary topology therefore needs an additional comparison
between its order and the original interiors.

## The supplied dense set need not capture the thin boundary

In the same real-line example take D = Q minus {0}, enumerated as
singleton levels. This D is dense, all its levels satisfy the closed
discrete assumption, and all its points even have CP open local bases
by first countability. For each K_n, however, zero is isolated in
K_n and is absent from both int K_n and K_n ∩ D. Hence
K_n ⊄ cl(int K_n ∪ (K_n ∩ D)). In particular, applying
L0028_of_boundary_cp_trace from the parent research branch directly
with the supplied K and D fails even in a metric space. A proof via
that lemma must change the input family or construct a different
trace. The J_n subfamily shows why this obstruction does not refute
L_0028: a change of closed base can remove the thin point.

## Isolating the obstruction for the specific L_0021 construction

Use the notation of Proofs/L_0021.lean: W_n is the decreasing open
neighborhood obtained by excluding the closed unions of closures
missing x at levels at most n. Write B_n(x) for the members of level n
containing x. Try the open local base
V = { B ∩ W_n : B ∈ B_n(x), n ∈ N }.
It is cofinal because each B can be chosen inside the target open
neighborhood before intersecting. At a point y ≠ x, the localization in
L_0021 gives a neighborhood missing cl W_n for all sufficiently large
n. At x every member contains x. Thus this particular proposed V is CP
if and only if every fixed-level family
V_n = { B ∩ W_n : B ∈ B_n(x) } is CP: the forward implication is
heredity, and for the reverse implication localization reduces the
closure of any selected union at y ≠ x to finitely many levels.

Inside W_n, CP for V_n follows from CP for the original level and
openness of W_n. Outside cl W_n there is no accumulation. Consequently
the remaining question for this construction is exactly the fixed-level
boundary: whenever y ∈ cl W_n minus W_n and lies in the closure of a
selected union of B ∩ W_n, some selected B ∩ W_n must already have y
in its closure. This isolates where the proof of L_0021 for
cl B ∩ cl W_n cannot pass through to its open analogue. The fixed-level
CP condition here is for the specific W_n and original B_n(x);
generic counterexamples for intersecting with arbitrary open masks do
not decide it.

### Counterexample with the actual level-zero mask

On the real line let x = -3/2, A = (0,1), and
B_j = (-2,-1/j) ∪ A for integers j ≥ 2. Use
{A} ∪ {B_j : j ≥ 2} as level zero, and put an enumeration of the
rational open intervals in later singleton levels. This is a
sigma-CP open base: in level zero any finite subfamily is CP for
the union identity, and any infinite subfamily contains B_j with
unbounded j. Its union is (-2,0) ∪ (0,1), and both the closure of
that union and the union of the individual closures equal [-2,1].
The later levels are singleton families.

A is the only member of level zero whose closure misses x.
Therefore W_0 = R minus [0,1] by the actual L_0021 definition,
and B_j ∩ W_0 = (-2,-1/j). The closure of their union contains
zero, which is in none of their individual closures. By heredity,
adding the other levels cannot make the proposed family CP.
This rules out the unmodified open analogue for general input
sigma-CP bases. It leaves L_0028 and the possibility of first
choosing a different input basis open.

### Normalizing the layers does not repair the mask

The preceding example persists under two standard normalizations of
the sigma-CP basis. Replace each level by the family of arbitrary
unions of members of the first n+1 original levels. A finite union
of CP families is CP, and the family of arbitrary unions of a CP
family is CP: for any selected unions, collect their constituent
members and apply the original closure identity both to the total
union and to each selected union. The new levels are increasing,
closed under arbitrary unions, and still contain a basis.

At level zero the only new sets whose closures miss x are ∅ and A.
Indeed, a union using any B_j contains x. Thus the normalized layer
has the same W_0 and contains all the original B_j, so the same
subfamily violates CP after clipping. Moreover A, every B_j,
and W_0 are regular open. The additional nonempty union at level
zero is (-2,0) ∪ (0,1), whose regular-open hull is (-2,1).
Replacing every normalized level-zero element by its regular-open
hull also leaves A, B_j and W_0 unchanged. This rules out fixing
the boundary failure merely by these normalizations.

## Mosaic route and the remaining open-neighborhood requirement

Mizokami's 2003 survey, Lemma 1.2 (https://arxiv.org/pdf/math/0312457),
gives a sigma-discrete closed cover subordinate to the membership
patterns of any CP closed family in an M3 space, with open expansions
V(F) such that V(F) meets a member K only if F is contained in K.
Thus the cover detects every point of K, including the thin boundary
points which a fixed dense set can miss.

At each individual discrete layer, a CP open outer base for each F
restricted to a locally finite open expansion would give a CP open
family when the chosen pieces are unioned: near any point only finitely
many cells contribute, and within each cell its outer base is CP.
Even decreasing countable outer bases of the cells would suffice for
this part, since any subfamily of a decreasing sequence has a largest
member. The distinction is that a stratification of F only separates
individual exterior points. Its countable sequence need not refine
every open superset of F. For example, in the metric disjoint sum
N × R with F = N × {0}, for any sequence U_n of open supersets of F
choose a nonzero t_n with (n,t_n) in U_n. The set of these points is
closed and misses F, so its open complement contains none of the U_n.
The mosaic theorem alone therefore does not supply the outer bases
needed for this argument. The open expansion of each cell inside an
arbitrary target, with closure preservation across targets, remains
a separate obligation.

## Monotone expansion away from a closed set

A stratification gives a direct construction for the boundary estimate
in Mizokami's survey Lemma 1.5 (https://arxiv.org/pdf/math/0312457).
Let G_n(C) be a decreasing monotone stratification on closed inputs C.
For a fixed closed M, put O_n = X minus cl G_n(M) and define

    S_M(C) = union_n (O_n ∩ G_n(C)).

Each O_n is open, its closure misses M (it is contained in the
complement of G_n(M)), and the O_n cover X minus M. Thus S_M(C)
is open in X, contains C minus M and misses M. The operator is
monotone in C. For any CP closed family H, put C* = union H,
which is closed by CP. Then

    cl(union_{C ∈ H} S_M(C)) ∩ M ⊆ C* ∩ M.

In fact the union of expansions is contained in S_M(C*). If y is
in M minus C*, choose m with y outside cl G_m(C*). The tail of
S_M(C*) is contained in G_m(C*). The first m pieces are contained
in the finite union of the O_n for n < m, whose closure misses M.
This proves the estimate by the finite union law for closures.

For L_0028 this isolates what must be handled on M: all closure
failures of these expansions on M can occur only at points of
selected original closed members. If additionally every original
member is contained in the closure of its own part outside M,
each such point is captured by an individual expansion, so there
is no CP failure on M. By itself this does not give control on
X minus M or arbitrary containment in a prescribed open target.

### Fixed stratified expansions can fail away from M

In the real Hilbert space ℓ² take x = 10e₀, M = {x}, and let
G_n(C) be the open distance neighborhood of radius 1/(n+1).
Take K_j = closedBall(x,1) ∪ {c_j} for j ≥ 1, where
c_j = (1+1/j)e_j. The c_j are uniformly separated, so every
subfamily of the K_j has closed union. Adjoin the decreasing
closed balls centered at x with radii 1/(j+1). These form a CP
closed neighborhood base together with the K_j, as each subfamily
of the balls has a largest member and a finite union of two closed
unions is closed. The space is metrizable and separable, so it has
a sigma-CP open basis and singleton levels of a countable dense set.

For O_n and S_M from the preceding section, O_0 contains the open
ball of radius 2 centered at 0. For j ≥ 2, p_j = (2/j)e_j lies
in that ball and has distance 1-1/j from c_j. Thus p_j is in
S_M(K_j), and p_j → 0. For any fixed j, however,
S_M(K_j) ⊆ G_0(K_j), and the distance of 0 from K_j is strictly
larger than 1. Hence 0 misses every individual closure. Even an
unmodified stratification in a metric space with nonempty M can
therefore give a CP failure off M. To repair this route, the choice
of open expansions away from M must exploit additional structure
beyond the stratification conditions used by BoundaryExpansion.lean.

## A common meagre set contains every thin defect

Apply the mosaic cover from Mizokami's survey Lemma 1.2 to the
original CP closed family K. Write the cover as the union of discrete
closed families C_n. Define M_n as the union of the boundaries of
the cells in C_n. Each M_n is closed nowhere dense. In fact the
boundary cells are closed nowhere dense and form a discrete family.
Locally, at most one can meet a sufficiently small neighborhood,
which proves both closedness and empty interior of their union.

If y belongs to K minus cl(int K) for some original member K,
choose any cover cell C containing y. Membership compatibility gives
C ⊆ K. If y were in int C it would be in int K, so y lies in the
boundary of C. Thus every thin defect of every K lies in the same
union of the M_n.

Consequently the family {cl(int K) : K in K} already has the CP
union identity at every point outside this countable union, by the
thin-point criterion above. This gives fixed nowhere dense closed
sets on which to seek a simultaneous repair, rather than a different
exceptional set for every K. The estimate does not provide a repair
on those sets or guarantee that separate repairs compose.

## Construct a dense trace adapted to the whole family

The arbitrary D in L_0028 need not be a dense trace. However a new
sigma-closed-discrete D can be constructed from a mosaic and a
sigma-discrete closed network, as follows.

Let C_n be the discrete closed layers of a mosaic for the given
CP family K. Let N_m be the discrete closed layers of an ambient
network. For each n,m and every nonempty intersection C ∩ N
with C in C_n and N in N_m, select one point. The intersections
are a discrete closed family: at a point intersect a neighborhood
meeting at most one C with a neighborhood meeting at most one N.
Hence the selected points at fixed n,m have all subsets closed.
Their union E over n,m is sigma-closed-discrete.

For y in K and open U containing y, take a C containing y and
a network element N with y in N ⊆ U. Then C ⊆ K by the mosaic
condition, so the selected point of C ∩ N lies in U ∩ K ∩ E.
Consequently K = cl(K ∩ E) for every original member.
This supplies the trace hypothesis of the parent branch's Ito
construction. It leaves the hypothesis of a CP open local base
at the selected points. Asking for that property at every point
would reinstate the general theorem; the remaining question is
whether compatible representatives can be chosen, or replaced
with weaker closure witnesses.

Tamano 2008, Lemma 2, uses this type of adapted trace and convergent
sequences outside a closed set to produce regularization pieces.
Its convergence hypothesis must be supplied separately; density
alone provides closure membership, not such sequences.
https://topology.nipissingu.ca/tp/reprints/v32/tp32023.pdf

## A supplied dense set may fail on every cofinal subfamily

Take X = R, x = 0, D = Q enumerated by singleton layers, and
K_n = [-1/(4n),1/(4n)] ∪ {sqrt(2)/n} for n ≥ 1.
The K_n form a closed neighborhood base at 0. Their intervals
are decreasing, so the interval part of any nonempty selected
union is the interval for the least selected index. The only
possible accumulation point of the other part, the selected
isolated points sqrt(2)/n, is 0, already in that interval.
Thus every selected union is closed, proving CP.

For every n its isolated point sqrt(2)/n is irrational and lies
outside the interval. Both int K_n and K_n ∩ D lie in the closed
interval, so their union does not approximate that isolated point.
In particular no cofinal subfamily of this prescribed CP base
satisfies the parent trace condition with the prescribed D.
This strengthens the earlier real-line example, where throwing away
the decorated sets and retaining the J_n did give a cofinal trace.
The common mosaic construction can change the representative set
and is unaffected by this counterexample.

## A discrete family of slots can replace a sequence in the local patch

Tamano 2008, Lemma 2 uses CP closed quasi-neighborhood bases at
auxiliary points, rather than CP open bases at the trace points.
For the local patch, the relevant properties can be separated as
follows. At a trace point p on a closed wall M, suppose there is a
set A in X minus M with p in cl A, and for each a in A an open
slot O_a containing a. Assume cl O_a misses M, the closures of the
slots are locally finite on X minus {p}, and the union of those
closures has no accumulation on M minus {p}. Equip each a with a
CP closed neighborhood base consisting of sets inside O_a.

Given any open U containing p, take the centers A ∩ U, which still
accumulate at p. At each such center, choose one closed base member
inside U. Their union together with {p} is closed: at every other
point, local finiteness reduces the union to finitely many closed
members. It is also regular closed, since it is contained in the
closure of its interior at the centers and at p, with one additional
condition: the chosen members themselves must be regular closed.
Without that extra condition the patch is closed and still captures
p in the closure of its interior, which is what Tamano's stage needs.

For an arbitrary selection of patches all anchored at p, at any
other point only finitely many slots contribute, and inside each slot
the union of the selected closed neighborhoods is closed by its CP
property. At p the union already contains p if any patch is selected.
Thus the family of closed patches is CP even when the centers cannot
be presented as a sequence. The unproved input for general L_0028
is a supply of such slots at an adapted trace on each wall. In
particular p in cl(X minus M) alone does not give the locally finite
slot condition. See Tamano, Lemma 2, for the sequential construction.
https://topology.nipissingu.ca/tp/reprints/v32/tp32023.pdf

For a single p the slot hypothesis follows if A is closed discrete in
X minus {p} and that open subspace is paracompact and regular. Use
collectionwise normality there to get a discrete family of closures,
then shrink the slots inside X minus M. Ambient closures differ from
relative closures only at p, and individual slots can be chosen to
have ambient closure missing M, by first bounding them inside open
neighborhoods whose ambient closures miss M. This shifts the local
existence question to whether p is approached by a closed discrete
set in the punctured space. The step still needs compatibility
across the different trace points for a full L_0028 proof.
