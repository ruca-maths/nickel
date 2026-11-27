# L0031 audit: `BoxFan I` cannot supply the stratifiable witness

## Result

The `BoxFan I := Option (N × (I → Bool))` construction in PR #11 proves the clopen-Gδ apex and failure of a CP outer base when `I` is uncountable, but it cannot satisfy the missing stratifiability clause. Every fixed-level slice is a closed subspace homeomorphic to the uncountable Cantor cube `2^I`.

If `BoxFan I` were stratifiable, hereditary stratifiability would make each closed slice stratifiable. Since each slice is compact Hausdorff, the classical theorem that compact stratifiable spaces are metrizable would make `2^I` metrizable. For uncountable `I`, `2^I` is not metrizable: it is compact and has no countable base (at the zero point, a basic neighborhood only constrains finitely many coordinates, so a countable local base could mention only countably many coordinates). Contradiction.

Thus `boxFan_not_hasCPOuterBase` is a valid obstruction result, but the model is not a candidate proof of `Specs.L_0031.stmt`. The missing stratifiability condition is impossible for this topology as currently defined, rather than an unproved detail of its apex neighborhoods.

## Check of the closed-slice claim

In `Research/ChenWang_NonCP_Model.lean`, the open-set definition gives product-open neighborhoods at each non-apex point. The level slice

`S_k = { some (k, f) | f : I → Bool }`

is open by `boxFan_slice_isOpen`. Its complement is open too: around `none`, use the tail neighborhood `boxFanW (k+1)`, and around every point at another level use a slice neighborhood. The induced topology on `S_k` is exactly the product topology on `I → Bool`, by the same non-apex clause. Hence `S_k` is closed and homeomorphic to `2^I`.

## Consequence for the research plan

Do not spend further effort trying to prove `BoxFan I` stratifiable. Any construction that keeps a closed copy of `2^I` has the same obstruction. A viable replacement must preserve the Δ-system escape argument while removing the non-stratifiable compact fiber; that requires a different topology or a different source of the uncountable finite-support family.

This audits only the PR #11 candidate. It does not refute L0031 or the Chen–Wang theorem.

## References

- PR #11 candidate: <https://github.com/ruca-maths/nickel/pull/11>
- Borges, “On stratifiable spaces” (1966), stating hereditary stratifiability and related results: <https://msp.org/pjm/1966/17-1/pjm-v17-n1-p01-s.pdf>
- A topology reference explicitly using the theorem that compact stratifiable spaces are metrizable: <https://topology.nipissingu.ca/tp/reprints/v22/tp22113.pdf>

Status: mathematical audit note; not Lean-checked. The claim is limited to `BoxFan I` as defined in PR #11.
