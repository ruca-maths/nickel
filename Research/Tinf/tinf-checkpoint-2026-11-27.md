# Tinf research checkpoint — 2026-11-27

## Active route

The root goal is `Tinf_M3_imp_M1` (M3/stratifiable implies M1). Directly proving it
would settle the classical M3-versus-M1 problem. The current research route is a
formal audit of the Chen–Wang proposed counterexample, arXiv:1809.03763v2, rather
than another equivalent positive subgoal.

## Verified Lean results

- `OuterBaseToRegularClosed.lean` compiles. It proves that a CP open outer base
  at a point yields a regular-closed CP closed neighborhood base. This confirms
  the easy reverse bridge used in the L0027/L0028 equivalence.
- `CheckProposedCandidateReduction.lean` compiles. Its conditional reduction
  proves `¬Tinf` from an M3 space with one point having countably many clopen
  separators and no CP open local base.
- `ClosureFromConvergentCompanions.lean` compiles. Its endpoint lemma combines
  the stratification convergence criterion with companion-point membership to
  conclude `t ∈ closure (⋃ n, V n)`, the final contradiction target in
  Proposition 9.5(C).
- The reusable sequence convergence, prefix-box intersection, and unbounded
  almost-disjoint-family results are in the neighboring Lean files. These
  auxiliary results do not formalize the candidate space or its main theorem.

## Literature status and caution

The arXiv record shows v2 last revised 24 September 2018 and no journal
reference in its metadata. The abstract claims a stratifiable non-M1 example.
An earlier M3/M1 survey calls the implication one of the outstanding open
problems; this is evidence that the preprint must be treated as a proposed, not
independently verified, resolution. No error or correction has been established
here either.

## Remaining critical obligation

The bottleneck is Proposition 9.5(B), around HTML lines 2337–2357. The proof has
to extend the particular currently selected hole cell at every stage: choose a
higher-rank `theta`, retain a nonempty theta-hole subcell inside the current
cell after Construction 6.1(Q)'s subtraction by the earlier exclusion, and
also find its Proposition 8.4 companion inside the prescribed surviving
portion. The rank inequality alone does not imply any of those containment or
survival properties. Propositions 8.3–8.4 state fineness or consequences for
qualifying cells, but this audit has not yet derived the required local
extension invariant from them.

The next proof obligation is therefore to extract an exact lemma from
Construction 6.1(Q), Proposition 8.1, and Corollary 4.9 that implies this
nonempty local extension for every selected state. In the displayed text,
Corollary 4.9 (HTML 623–634) gives a cover sandwich, while Proposition 8.4
(HTML 2243–2258) gives conclusions for every qualifying pair. Neither displayed
statement explicitly asserts that a nonempty pair exists inside each particular
current selected cell after the new exclusion. This is an unfilled proof
obligation, not yet a demonstrated error: the construction's definitions may
imply the needed existence. If that implication fails,
the result must be a concrete countermodel to the exact cited assumptions, not
just a generic observation that arbitrary cover data are insufficient.

## Provenance

Research files are under the ignored local scratch directory
`work/codex-child/`; no synced `sources/` content or remote repository refs were
changed. No proof for the main Tinf claim has been submitted or shared by this
checkpoint.

## Sharing cadence

Publish a research checkpoint after each substantive result and once per hour
during active research, even when the main proof remains open. Include the
Lean verification status and the precise outstanding proof obligation.
