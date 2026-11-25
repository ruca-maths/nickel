import Targets.Defs

/-!
# 目標命題（ロック領域・人間のみ編集）

各目標は `Prop` 型の定数として書き、DB の根ノードはこの定数を命題とする。
空間は `Type`（宇宙 0）上で量化している。位相空間論の命題としては制限にならない。

段階:
* T1 … 動作確認用（易）
* T2 … 中難度・実用補題
* T3 … M₂ = M₃（Gruenhage / Junnila）の M₃ ⇒ M₂ 側
* T4 … 既知の部分結果（原論文を人間が確認してから追加する。現在は空）
* Tinf … 本題。肯定・否定の両方を受け付ける
-/

namespace MSpace.Goals

open MSpace

/-- T1a: 局所有限族は closure-preserving。 -/
def T1a_closurePreserving_of_locallyFinite : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (𝓕 : Set (Set X)),
    LocallyFinite (fun s : 𝓕 => (s : Set X)) → ClosurePreserving 𝓕

/-- T1b: M₁ ⇒ M₂。 -/
def T1b_M1_imp_M2 : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsM1 X → IsM2 X

/-- T1c: M₂ ⇒ M₃。 -/
def T1c_M2_imp_M3 : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsM2 X → IsM3 X

/-- T2a: M₃ ⇔ stratifiable（Borges）。 -/
def T2a_M3_iff_stratifiable : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsM3 X ↔ IsStratifiable X

/-- T2b: stratifiable ⇒ パラコンパクト。 -/
def T2b_stratifiable_paracompact : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsStratifiable X → ParacompactSpace X

/-- T2c: stratifiable ⇒ 完全正規。 -/
def T2c_stratifiable_perfectlyNormal : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsStratifiable X → IsPerfectlyNormal X

/-- T2d: 距離化可能 ⇒ M₁。 -/
def T2d_metrizable_M1 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X], IsM1 X

/-- T3: M₃ ⇒ M₂（Gruenhage 1976 / Junnila 1978）。 -/
def T3_M3_imp_M2 : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsM3 X → IsM2 X

/-- Tinf: 任意の M₃ 空間は M₁ か（Ceder 1961, 未解決）。
DB では「この命題」と「その否定」の両方が証明対象として登録される。 -/
def Tinf_M3_imp_M1 : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsM3 X → IsM1 X

end MSpace.Goals
