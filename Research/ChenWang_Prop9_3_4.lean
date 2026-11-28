import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Chen–Wang (arXiv:1809.03763v2) Section 9: Proposition 9.3, Corollary 9.4, and Unbounded Tree-Splitting

This file formalizes the combinatorial Baire-tree splitting dichotomy that drives the
inductive construction in Chen–Wang's Proposition 9.5 (zero `sorry`, standard axioms only):

1. **`IsBoundedSeqFamily ℱ`**: `ℱ ⊆ (ℕ → ℕ)` is `≤*`-bounded in `(ℕ^ℕ, ≤*)`.
2. **`Cylinder ℱ p`**: `{ f ∈ ℱ | ∀ k < p.length, f k = p[k] }` (paper's `[n_1, ..., n_h]'`).
3. **`prop_9_3`**: If there exists `b : ℕ` such that for every `h ≥ b` and every length-`h`
   prefix `p`, `{ f h | f ∈ Cylinder ℱ p }` is bounded above in `ℕ`, then `IsBoundedSeqFamily ℱ`.
4. **`cor_9_4`**: Contrapositive — if `ℱ` is unbounded in `(ℕ^ℕ, ≤*)`, then for every `b : ℕ`,
   there exist `h ≥ b` and a length-`h` prefix `p` such that for every `k : ℕ`, some
   `f ∈ Cylinder ℱ p` satisfies `f h ≥ k`.
5. **`cor_9_4_strict_seq`**: Extracts an infinite sequence `α : ℕ → (ℕ → ℕ)` in `Cylinder ℱ p`
   with strictly increasing `h`-th coordinate `α 0 h < α 1 h < α 2 h < ...` (the `α*` sequence
   used in Proposition 9.5).
6. **`cor_9_4_sets`**: Specialized corollary for any unbounded family `𝒜` of infinite subsets
   of `ℕ` enumerated via `Nat.nth (· ∈ A)`.
-/

namespace Research.ChenWangProp934

open Filter Set

/-- A family `ℱ ⊆ (ℕ → ℕ)` is eventually bounded (`≤*`-bounded). -/
def IsBoundedSeqFamily (ℱ : Set (ℕ → ℕ)) : Prop :=
  ∃ β : ℕ → ℕ, ∀ f ∈ ℱ, ∀ᶠ n in atTop, f n ≤ β n

/-- `f` extends the finite prefix `p : List ℕ`. -/
def PrefixEq (f : ℕ → ℕ) (p : List ℕ) : Prop :=
  ∀ k : Fin p.length, f k.1 = p[k]

/-- Cylinder `[n_1, ..., n_h]' = { f ∈ ℱ | f extends p }`. -/
def Cylinder (ℱ : Set (ℕ → ℕ)) (p : List ℕ) : Set (ℕ → ℕ) :=
  { f ∈ ℱ | PrefixEq f p }

/-- Length-`h` prefix of `f : ℕ → ℕ` as a `List ℕ`. -/
def takePrefix (f : ℕ → ℕ) (h : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin h => f i.1)

theorem takePrefix_length (f : ℕ → ℕ) (h : ℕ) : (takePrefix f h).length = h := by
  simp [takePrefix]

theorem takePrefix_getElem (f : ℕ → ℕ) (h i : ℕ) (hi : i < (takePrefix f h).length) :
    (takePrefix f h)[i]'hi = f i := by
  simp only [takePrefix, List.getElem_ofFn]

theorem prefixEq_takePrefix (f : ℕ → ℕ) (h : ℕ) : PrefixEq f (takePrefix f h) := by
  intro k
  exact (takePrefix_getElem f h k.1 k.2).symm

theorem takePrefix_eq_of_prefixEq {f : ℕ → ℕ} {p : List ℕ} {h : ℕ}
    (hlen : p.length = h) (hp : PrefixEq f p) :
    takePrefix f h = p := by
  apply List.ext_getElem
  · simp [takePrefix, hlen]
  · intro i hi1 hi2
    rw [takePrefix_getElem f h i hi1]
    exact hp ⟨i, hi2⟩

theorem takePrefix_succ (f : ℕ → ℕ) (h : ℕ) :
    takePrefix f (h + 1) = takePrefix f h ++ [f h] := by
  apply List.ext_getElem
  · simp [takePrefix]
  · intro i hi1 hi2
    have hlt : i < h + 1 := by simpa [takePrefix] using hi1
    rw [takePrefix_getElem f (h + 1) i hi1]
    by_cases hi : i < h
    · have hlen : i < (takePrefix f h).length := by simpa [takePrefix] using hi
      rw [List.getElem_append_left hlen, takePrefix_getElem f h i hlen]
    · have heq : i = h := by omega
      subst heq
      have hlen : (takePrefix f i).length = i := takePrefix_length f i
      rw [List.getElem_append_right (by omega)]
      simp [hlen]

/-- Explicit injective encoding `List ℕ → ℕ` via `Nat.pair`. -/
def encodeList : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (encodeList l) + 1

theorem encodeList_injective : Function.Injective encodeList := by
  intro l₁ l₂ h
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp [encodeList] at h
  | cons a as ih =>
    cases l₂ with
    | nil => simp [encodeList] at h
    | cons b bs =>
      simp only [encodeList, Nat.succ.injEq] at h
      have hp := Nat.pair_eq_pair.mp h
      rw [hp.1, ih hp.2]

section Prop93Proof

variable {ℱ : Set (ℕ → ℕ)}

/-- Finite level-`d` tree of prefixes extending `p₀` bounded coordinatewise by `B`. -/
private def levelPrefixes (B : List ℕ → ℕ) (p₀ : List ℕ) : ℕ → Finset (List ℕ)
  | 0 => {p₀}
  | d + 1 => (levelPrefixes B p₀ d).biUnion fun p =>
      (Finset.range (B p + 1)).image (fun x => p ++ [x])

private theorem mem_levelPrefixes_takePrefix (B : List ℕ → ℕ) {b : ℕ}
    (hB : ∀ p : List ℕ, b ≤ p.length → ∀ f ∈ Cylinder ℱ p, f p.length ≤ B p)
    {p₀ : List ℕ} (hp₀ : p₀.length = b) {f : ℕ → ℕ} (hf : f ∈ Cylinder ℱ p₀) :
    ∀ d : ℕ, takePrefix f (b + d) ∈ levelPrefixes B p₀ d := by
  intro d
  induction d with
  | zero =>
    simp only [Nat.add_zero, levelPrefixes, Finset.mem_singleton]
    exact takePrefix_eq_of_prefixEq hp₀ hf.2
  | succ d ih =>
    rw [← Nat.add_assoc, takePrefix_succ]
    simp only [levelPrefixes, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    refine ⟨takePrefix f (b + d), ih, f (b + d), ?_, rfl⟩
    have hlen : (takePrefix f (b + d)).length = b + d := takePrefix_length f (b + d)
    have hcyl : f ∈ Cylinder ℱ (takePrefix f (b + d)) := ⟨hf.1, prefixEq_takePrefix f (b + d)⟩
    have hle := hB (takePrefix f (b + d)) (by omega) f hcyl
    rw [hlen] at hle
    omega

/-- Chen–Wang Proposition 9.3:
If there exists `b : ℕ` such that every cylinder of length `h ≥ b` has bounded `h`-th coordinate,
then `ℱ` is eventually bounded (`IsBoundedSeqFamily ℱ`). -/
theorem prop_9_3 (ℱ : Set (ℕ → ℕ))
    (hbound : ∃ b : ℕ, ∀ h ≥ b, ∀ p : List ℕ, p.length = h →
      ∃ K : ℕ, ∀ f ∈ Cylinder ℱ p, f h ≤ K) :
    IsBoundedSeqFamily ℱ := by
  classical
  obtain ⟨b, hb⟩ := hbound
  let B : List ℕ → ℕ := fun p =>
    if h : b ≤ p.length then (hb p.length h p rfl).choose else 0
  have hB : ∀ p : List ℕ, b ≤ p.length → ∀ f ∈ Cylinder ℱ p, f p.length ≤ B p := by
    intro p hp f hf
    simp only [B, hp, ↓reduceDIte]
    exact (hb p.length hp p rfl).choose_spec f hf
  -- Bound for each fixed length-`b` prefix `p₀`
  let β_pref : List ℕ → ℕ → ℕ := fun p₀ n =>
    if b ≤ n then (levelPrefixes B p₀ (n - b)).sup B else 0
  have hβ_pref : ∀ p₀ : List ℕ, p₀.length = b → ∀ f ∈ Cylinder ℱ p₀,
      ∀ n ≥ b, f n ≤ β_pref p₀ n := by
    intro p₀ hp₀ f hf n hn
    simp only [β_pref, hn, ↓reduceIte]
    have hmem := mem_levelPrefixes_takePrefix B hB hp₀ hf (n - b)
    have hsub : b + (n - b) = n := by omega
    rw [hsub] at hmem
    have hcyl : f ∈ Cylinder ℱ (takePrefix f n) := ⟨hf.1, prefixEq_takePrefix f n⟩
    have hle := hB (takePrefix f n) (by rw [takePrefix_length]; exact hn) f hcyl
    rw [takePrefix_length] at hle
    exact le_trans hle (Finset.le_sup (f := B) hmem)
  -- Index length-`b` prefixes by `ℕ` via `encodeList` and diagonalize
  let β_nat : ℕ → ℕ → ℕ := fun m n =>
    if h : ∃ p₀ : List ℕ, p₀.length = b ∧ encodeList p₀ = m then
      β_pref h.choose n
    else 0
  refine ⟨fun n => (Finset.range (n + 1)).sup (fun m => β_nat m n), ?_⟩
  intro f hf
  let p₀ := takePrefix f b
  have hp₀_len : p₀.length = b := takePrefix_length f b
  have hf_cyl : f ∈ Cylinder ℱ p₀ := ⟨hf, prefixEq_takePrefix f b⟩
  let m₀ := encodeList p₀
  have hEx : ∃ p : List ℕ, p.length = b ∧ encodeList p = m₀ := ⟨p₀, hp₀_len, rfl⟩
  have hchoose : hEx.choose = p₀ := encodeList_injective hEx.choose_spec.2
  rw [Filter.eventually_atTop]
  refine ⟨max b m₀, fun n hn => ?_⟩
  have hnb : b ≤ n := le_trans (le_max_left b m₀) hn
  have hnm : m₀ ≤ n := le_trans (le_max_right b m₀) hn
  have h1 : f n ≤ β_pref p₀ n := hβ_pref p₀ hp₀_len f hf_cyl n hnb
  have h2 : β_pref p₀ n = β_nat m₀ n := by
    simp only [β_nat, hEx, ↓reduceDIte, hchoose]
  have h3 : β_nat m₀ n ≤ (Finset.range (n + 1)).sup (fun m => β_nat m n) :=
    Finset.le_sup (f := fun m => β_nat m n) (Finset.mem_range.mpr (by omega))
  exact le_trans h1 (h2 ▸ h3)

/-- Chen–Wang Corollary 9.4:
If `ℱ` is unbounded in `(ℕ^ℕ, ≤*)`, then for every `b : ℕ`, there exist `h ≥ b` and a
length-`h` prefix `p` such that `{ f h | f ∈ Cylinder ℱ p }` is unbounded in `ℕ`. -/
theorem cor_9_4 (ℱ : Set (ℕ → ℕ)) (hunb : ¬ IsBoundedSeqFamily ℱ) (b : ℕ) :
    ∃ h ≥ b, ∃ p : List ℕ, p.length = h ∧ ∀ K : ℕ, ∃ f ∈ Cylinder ℱ p, K ≤ f h := by
  by_contra hnot
  push Not at hnot
  apply hunb
  apply prop_9_3 ℱ
  refine ⟨b, fun h hh p hp => ?_⟩
  obtain ⟨K, hK⟩ := hnot h hh p hp
  exact ⟨K, fun f hf => le_of_lt (hK f hf)⟩

/-- Strict-sequence extraction from Corollary 9.4 (constructing `α* = {α_m}` in Proposition 9.5):
every unbounded `ℱ` has, for any `b : ℕ`, a level `h ≥ b`, a length-`h` prefix `p`, and a
sequence `seq : ℕ → (ℕ → ℕ)` inside `Cylinder ℱ p` with `seq 0 h < seq 1 h < ...`. -/
theorem cor_9_4_strict_seq (ℱ : Set (ℕ → ℕ)) (hunb : ¬ IsBoundedSeqFamily ℱ) (b : ℕ) :
    ∃ h ≥ b, ∃ p : List ℕ, p.length = h ∧
      ∃ seq : ℕ → (ℕ → ℕ),
        (∀ m, seq m ∈ Cylinder ℱ p) ∧
        StrictMono (fun m => seq m h) := by
  classical
  obtain ⟨h, hh, p, hp, hsplit⟩ := cor_9_4 ℱ hunb b
  let step : ℕ → (ℕ → ℕ) := fun k => (hsplit k).choose
  have hstep_mem : ∀ k, step k ∈ Cylinder ℱ p := fun k => (hsplit k).choose_spec.1
  have hstep_ge : ∀ k, k ≤ step k h := fun k => (hsplit k).choose_spec.2
  let seq : ℕ → (ℕ → ℕ) := Nat.rec (step 0) (fun _ prev => step (prev h + 1))
  refine ⟨h, hh, p, hp, seq, ?_, ?_⟩
  · intro m
    induction m with
    | zero => exact hstep_mem 0
    | succ m _ => exact hstep_mem (seq m h + 1)
  · exact strictMono_nat_of_lt_succ fun m => by
      have hge := hstep_ge (seq m h + 1)
      show seq m h < step (seq m h + 1) h
      omega

end Prop93Proof

section InfiniteSubsetsBridge

/-- Specialization to families of infinite subsets of `ℕ` enumerated via `Nat.nth (· ∈ A)`. -/
noncomputable def enumSetFamily (𝒜 : Set (Set ℕ)) : Set (ℕ → ℕ) :=
  (fun A : Set ℕ => Nat.nth (· ∈ A)) '' 𝒜

theorem cor_9_4_sets (𝒜 : Set (Set ℕ))
    (hunb : ¬ ∃ g : ℕ → ℕ, ∀ A ∈ 𝒜, ∀ᶠ k in atTop, Nat.nth (· ∈ A) k ≤ g k) (b : ℕ) :
    ∃ h ≥ b, ∃ p : List ℕ, p.length = h ∧
      ∃ seq : ℕ → Set ℕ,
        (∀ m, seq m ∈ 𝒜) ∧
        (∀ m, PrefixEq (Nat.nth (· ∈ seq m)) p) ∧
        StrictMono (fun m => Nat.nth (· ∈ seq m) h) := by
  classical
  have hunb' : ¬ IsBoundedSeqFamily (enumSetFamily 𝒜) := by
    rintro ⟨β, hβ⟩
    exact hunb ⟨β, fun A hA => hβ _ ⟨A, hA, rfl⟩⟩
  obtain ⟨h, hh, p, hp, seq, hmem, hmono⟩ := cor_9_4_strict_seq (enumSetFamily 𝒜) hunb' b
  have hex : ∀ m, ∃ A ∈ 𝒜, Nat.nth (· ∈ A) = seq m := fun m => (hmem m).1
  choose A hA hAeq using hex
  refine ⟨h, hh, p, hp, A, hA, ?_, ?_⟩
  · intro m
    rw [hAeq m]
    exact (hmem m).2
  · intro i j hij
    dsimp only
    rw [hAeq i, hAeq j]
    exact hmono hij

end InfiniteSubsetsBridge

end Research.ChenWangProp934
