module

public import SKConstants.Completion.N9Z2.MixedMean
public import SKConstants.Completion.Blueprint5.FineStatements
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N9Z2
open SKConstantsOAI.ZeroTemperatureSK M1 LFine N9 N9c LQ Blueprint5
variable {Ω : Type*} [MeasurableSpace Ω]

theorem freshEndpointMean_eq_posterior_integral (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (B D : ScalarContinuousPath a) (x : ℝ) :
    freshEndpointMean W β hβ a h f B D x =
      ∫ c, ∫ b, ∫ d, actualParisiFullMagnetization β (a+(h+f))
        (freshRowTerminalField W β hβ a h f B D (x,(c,(b,(d,0)))))
        ∂scalarPrimitiveBrownianPathLaw W (h+f)
        ∂scalarPrimitiveBrownianPathLaw W f
        ∂scalarPrimitiveBridgePathLaw W h := by
  have hi : ∀ {A : Type} [MeasurableSpace A] (ν : Measure A) [IsFiniteMeasure ν]
      (v : A → FreshRowSeed h f), Measurable v →
      Integrable (fun y => if freshRowSign W β hβ a h f B D (x,v y) then (1 : ℝ) else -1) ν := by
    intro A _ ν _ v hv
    apply Integrable.of_bound
      (((measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
        ((measurable_freshRowSign W β hβ a h f B D).comp
          (measurable_const.prodMk hv))).aestronglyMeasurable) 1
    exact ae_of_all _ fun y => by
      change ‖if freshRowSign W β hβ a h f B D (x,v y) then (1 : ℝ) else -1‖ ≤ 1
      split <;> norm_num
  unfold freshEndpointMean freshRowSeedLaw
  rw [integral_prod _ (hi _ (fun v => v) measurable_id)]
  apply integral_congr_ae
  filter_upwards [] with c
  rw [integral_prod _ (hi _ (fun v => (c,v)) (by fun_prop))]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [integral_prod _ (hi _ (fun v => (c,(b,v))) (by fun_prop))]
  apply integral_congr_ae
  filter_upwards [] with d
  exact N9b.freshRowSign_threshold_mean W β hβ a h f B D x c b d

theorem fineCellMixedMean_nonneg (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) (i : Fin (r+K)) :
    0 ≤ fineCellMixedMean W β hβ δ hδ r K e z i := by
  rw [fineCellMixedMean, frozenQueryMixedMean_eq_row]
  exact freshRowMixedMean_nonneg W β hβ _ _ _ _ _

theorem fineCellMixedMean_le_one (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) (i : Fin (r+K)) :
    fineCellMixedMean W β hβ δ hδ r K e z i ≤ 1 := by
  rw [fineCellMixedMean, frozenQueryMixedMean_eq_row]
  exact freshRowMixedMean_le_one W β hβ _ _ _ _ _

def FreshEndpointLipschitzStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0), 0 < h → (h : ℝ) ≤ 1/8 →
    ∀ (B D : ScalarContinuousPath a),
      LipschitzWith (Real.toNNReal
        (Real.exp h * Real.sqrt h * actualParisiQueryRho W β a))
        (freshEndpointMean W β hβ a h f B D)

theorem actual_growing_exp_mixed_scale_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ)
    (hp : meshDuration δ j ≤ 1/8) (hc : meshDuration δ (j+1) ≤ 1/8) :
    Real.exp (meshDuration δ (j+1)) * Real.sqrt (meshDuration δ (j+1)) *
      actualParisiQueryRho W β (growingQueryTime δ (j+1)) ≤
        2*β*actualFineScale W β δ j := by
  let R := actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ (j+1))
  have hR : 0 ≤ R := (actualParisiFullSusceptibilitySquareExpected_bounds W β _).1
  have hd := (meshDuration_pos δ hδ j).le
  have hs := (actualFineScale_pos W β hβ δ hδ j).le
  have hbase := actualFineScale_endpoint_lower W β hβ δ hδ j _ le_rfl
  have hsq : (Real.sqrt (meshDuration δ j)*Real.sqrt R)^2 = meshDuration δ j*R := by
    rw [mul_pow, Real.sq_sqrt hd, Real.sq_sqrt hR]
  have hb : Real.sqrt (meshDuration δ j)*Real.sqrt R ≤ actualFineScale W β δ j := by
    have hn := mul_nonneg (Real.sqrt_nonneg (meshDuration δ j)) (Real.sqrt_nonneg R)
    change meshDuration δ j*R ≤ _ at hbase
    nlinarith
  have hratio := (div_le_iff₀ (Real.sqrt_pos.mpr (meshDuration_pos δ hδ j))).mp
    (growingCell_sqrt_ratio_le δ hδ j (1/8) hp)
  have hcur : Real.sqrt (meshDuration δ (j+1))*Real.sqrt R ≤
      Real.exp ((1/8 : ℝ)/8)*actualFineScale W β δ j := by
    calc
      _ ≤ (Real.exp ((1/8 : ℝ)/8)*Real.sqrt (meshDuration δ j))*Real.sqrt R :=
        mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg R)
      _ = Real.exp ((1/8 : ℝ)/8)*(Real.sqrt (meshDuration δ j)*Real.sqrt R) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
  have hexp : Real.exp (meshDuration δ (j+1))*Real.exp ((1/8 : ℝ)/8) ≤ 2 := by
    rw [← Real.exp_add]
    have hx : meshDuration δ (j+1)+(1/8 : ℝ)/8 ≤ 1/4 := by linarith
    apply (Real.exp_le_exp.mpr hx).trans
    have he := Real.exp_le_two_add_div_two_sub (x := (1/4 : ℝ)) (by norm_num) (by norm_num)
    norm_num at he
    linarith
  have hβ0 := (zero_lt_one.trans hβ).le
  rw [actual_rho_eq W β hβ _ (growingQueryTime δ (j+1)).coe_nonneg]
  change Real.exp (meshDuration δ (j+1))*Real.sqrt (meshDuration δ (j+1))*
    (β*Real.sqrt R) ≤ _
  calc
    _ = (Real.exp (meshDuration δ (j+1))*β)*
        (Real.sqrt (meshDuration δ (j+1))*Real.sqrt R) := by ring
    _ ≤ (Real.exp (meshDuration δ (j+1))*β)*
        (Real.exp ((1/8 : ℝ)/8)*actualFineScale W β δ j) :=
      mul_le_mul_of_nonneg_left hcur (mul_nonneg (Real.exp_pos _).le hβ0)
    _ = (Real.exp (meshDuration δ (j+1))*Real.exp ((1/8 : ℝ)/8))*
        (β*actualFineScale W β δ j) := by ring
    _ ≤ 2*(β*actualFineScale W β δ j) :=
      mul_le_mul_of_nonneg_right hexp (mul_nonneg hβ0 hs)
    _ = _ := by ring

theorem fineMixedEnvelopeStatement_holds (hL : FreshEndpointLipschitzStatement) :
    Blueprint5.FineMixedEnvelopeStatement := by
  intro Ω _ W β hβ δ hδ r K hr hsmall e z i
  refine ⟨fineCellMixedMean_nonneg W β hβ δ hδ r K e z i, ?_⟩
  have hpos : 0 ≤ Real.exp (growingQueryDuration δ (e.val+1))*
      Real.sqrt (growingQueryDuration δ (e.val+1))*
      actualParisiQueryRho W β (growingQueryTime δ (e.val+1)) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
      (actualParisiQueryRho_bounds W β hβ _).1
  have hh := freshRowMixedMean_le_of_lipschitz W β hβ
    (growingQueryTime δ (e.val+1)) (growingQueryDuration δ (e.val+1))
    (Horizon δ K-growingQueryTime δ (e.val+2))
    (fineCellPastB W β hβ δ hδ r K e z i) (fineCellPastD W β hβ δ hδ r K e z i) _
    (hL W β hβ _ _ _ (growingQueryDuration_pos δ hδ _) (hsmall _ (by omega)) _ _)
  rw [Real.coe_toNNReal _ hpos] at hh
  rw [fineCellMixedMean, frozenQueryMixedMean_eq_row]
  exact hh.trans (actual_growing_exp_mixed_scale_le W β hβ δ hδ e.val
    (hsmall _ (by omega)) (hsmall _ (by omega)))

end SKConstants.Completion.N9Z2
