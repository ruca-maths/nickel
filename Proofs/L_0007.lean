import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Metrizable.Uniformity
import Specs.L_0007
import Proofs.L_0001

namespace Proofs.L_0007

open Set TopologicalSpace Metric

theorem main : Specs.L_0007.stmt := by
  unfold Specs.L_0007.stmt MSpace.Goals.T2d_metrizable_M1
  intro X _ _
  let _ : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have hr : ∀ n : ℕ, (0:ℝ) < (1/2:ℝ)^n := fun n => by positivity
  have href : ∀ n : ℕ, ∃ v : X → Set X, (∀ a, IsOpen (v a)) ∧ (⋃ i, v i = univ) ∧
      LocallyFinite v ∧ ∀ a, v a ⊆ ball a ((1/2:ℝ)^n) := by
    intro n
    refine precise_refinement (fun x => ball x ((1/2:ℝ)^n)) (fun _ => isOpen_ball) ?_
    exact eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, mem_ball_self (hr n)⟩
  choose v hvo hvc hvl hvs using href
  refine ⟨inferInstance, ⋃ n, range (v n), ?_, ?_⟩
  · apply isTopologicalBasis_of_isOpen_of_nhds
    · intro u hu
      obtain ⟨n, hn⟩ := mem_iUnion.1 hu
      obtain ⟨a, rfl⟩ := hn
      exact hvo n a
    · intro x U hx hU
      obtain ⟨ε, hε, hεU⟩ := isOpen_iff.1 hU x hx
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1/2:ℝ) < 1)
      have : x ∈ ⋃ i, v n i := by rw [hvc n]; trivial
      obtain ⟨a, ha⟩ := mem_iUnion.1 this
      refine ⟨v n a, mem_iUnion.2 ⟨n, a, rfl⟩, ha, ?_⟩
      intro y hy
      apply hεU
      have h1 := hvs n a ha
      have h2 := hvs n a hy
      rw [mem_ball] at h1 h2 ⊢
      calc dist y x ≤ dist y a + dist x a := dist_triangle_right _ _ _
        _ < (1/2:ℝ)^n + (1/2:ℝ)^n := add_lt_add h2 h1
        _ < ε := by linarith
  · refine ⟨fun n => range (v n), fun n => ?_, rfl⟩
    apply Proofs.L_0001.main
    have := (hvl n).comp_injective (rangeSplitting_injective (v n))
    convert this using 1
    funext s
    exact (apply_rangeSplitting (v n) s).symm

end Proofs.L_0007
