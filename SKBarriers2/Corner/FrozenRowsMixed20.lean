module

public import SKBarriers2.Corner.FrozenRowsMixed15

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set OAI.SK.Analytic
namespace SKBarriers2.StepCalculus
local notation "X" => (Fin 3 → ℝ)

theorem spatialNoiseTransportBudget_uniform (r q : ℕ) (B L K : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ A : X →L[ℝ] X, ‖A‖ ≤ K →
      affineNoiseAverageCoefficient r q B A ≤ T ∧
        spatialFirstNoiseTransportBudget r q B L A ≤ T ∧
          spatialSecondNoiseTransportBudget r q B L A ≤ T := by
  let f : (X →L[ℝ] X) → ℝ := fun A => 1+
    |affineNoiseAverageCoefficient r q B A|+
    |spatialFirstNoiseTransportBudget r q B L A|+
    |spatialSecondNoiseTransportBudget r q B L A|
  have hf : Continuous f := by
    dsimp only [f,spatialFirstNoiseTransportBudget,spatialSecondNoiseTransportBudget,
      affineNoiseAverageCoefficient]
    fun_prop
  obtain ⟨S,hS⟩ := (isCompact_closedBall (0 : X →L[ℝ] X) (max K 0)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨1+|S|, by linarith [abs_nonneg S], ?_⟩
  intro A hA
  have hmem : A ∈ Metric.closedBall (0 : X →L[ℝ] X) (max K 0) := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact hA.trans (le_max_left _ _)
  have hbound : f A ≤ 1+|S| := by
    have H := hS A hmem
    change |f A| ≤ S at H
    exact (le_abs_self _).trans (H.trans (by linarith [le_abs_self S]))
  have hval : affineNoiseAverageCoefficient r q B A ≤ f A := by
    dsimp only [f]
    linarith [le_abs_self (affineNoiseAverageCoefficient r q B A),
      abs_nonneg (spatialFirstNoiseTransportBudget r q B L A),
      abs_nonneg (spatialSecondNoiseTransportBudget r q B L A)]
  have hfirst : spatialFirstNoiseTransportBudget r q B L A ≤ f A := by
    dsimp only [f]
    linarith [le_abs_self (spatialFirstNoiseTransportBudget r q B L A),
      abs_nonneg (affineNoiseAverageCoefficient r q B A),
      abs_nonneg (spatialSecondNoiseTransportBudget r q B L A)]
  have hsecond : spatialSecondNoiseTransportBudget r q B L A ≤ f A := by
    dsimp only [f]
    linarith [le_abs_self (spatialSecondNoiseTransportBudget r q B L A),
      abs_nonneg (affineNoiseAverageCoefficient r q B A),
      abs_nonneg (spatialFirstNoiseTransportBudget r q B L A)]
  exact ⟨hval.trans hbound,hfirst.trans hbound,hsecond.trans hbound⟩

theorem spatialNoiseTransportBudget_uniform_order (d q : ℕ) (B L K : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ r ≤ d, ∀ A : X →L[ℝ] X, ‖A‖ ≤ K →
      affineNoiseAverageCoefficient r q B A ≤ T ∧
        spatialFirstNoiseTransportBudget r q B L A ≤ T ∧
          spatialSecondNoiseTransportBudget r q B L A ≤ T := by
  choose T hT using (fun i : Fin (d+1) => spatialNoiseTransportBudget_uniform i.val q B L K)
  let U := 1+∑ i : Fin (d+1), |T i|
  have hU : 1 ≤ U := by
    dsimp only [U]
    have H : 0 ≤ ∑ i : Fin (d+1), |T i| := Finset.sum_nonneg (fun i _ => abs_nonneg (T i))
    linarith
  refine ⟨U,hU,?_⟩
  intro r hr A hA
  let i : Fin (d+1) := ⟨r,by omega⟩
  have hle : T i ≤ U := by
    have HS : |T i| ≤ ∑ j : Fin (d+1), |T j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (T j)) (Finset.mem_univ i)
    exact (le_abs_self _).trans (HS.trans (by dsimp only [U]; linarith))
  obtain ⟨hv,hf,hs⟩ := (hT i).2 A hA
  exact ⟨hv.trans hle,hf.trans hle,hs.trans hle⟩

theorem spatialNoiseTransportBudget_uniform_order_family (d q : ℕ) (B L : ℕ → ℝ) (K : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ r ≤ d, ∀ A : X →L[ℝ] X, ‖A‖ ≤ K →
      affineNoiseAverageCoefficient r q (B r) A ≤ T ∧
        spatialFirstNoiseTransportBudget r q (B r) (L r) A ≤ T ∧
          spatialSecondNoiseTransportBudget r q (B r) (L r) A ≤ T := by
  choose T hT using (fun i : Fin (d+1) => spatialNoiseTransportBudget_uniform i.val q (B i.val) (L i.val) K)
  let U := 1+∑ i : Fin (d+1), |T i|
  have hU : 1 ≤ U := by
    dsimp only [U]
    have H : 0 ≤ ∑ i : Fin (d+1), |T i| := Finset.sum_nonneg (fun i _ => abs_nonneg (T i))
    linarith
  refine ⟨U,hU,?_⟩
  intro r hr A hA
  let i : Fin (d+1) := ⟨r,by omega⟩
  have hle : T i ≤ U := by
    have HS : |T i| ≤ ∑ j : Fin (d+1), |T j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (T j)) (Finset.mem_univ i)
    exact (le_abs_self _).trans (HS.trans (by dsimp only [U]; linarith))
  obtain ⟨hv,hf,hs⟩ := (hT i).2 A hA
  exact ⟨hv.trans hle,hf.trans hle,hs.trans hle⟩

end SKBarriers2.StepCalculus
