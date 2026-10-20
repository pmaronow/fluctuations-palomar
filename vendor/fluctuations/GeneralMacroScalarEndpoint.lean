module

public import GeneralScalarCompetitors
public import MacroMonotonicityAndEndpoints

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def unitMassQuantiles : Set (ℝ → ℝ) := {q | MonotoneOn q (Icc (0:ℝ) 1) ∧
  ∀ u ∈ Icc (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1}

def generalScalarQuantileValue (b h q : ℝ → ℝ) : ℝ :=
  massStrengthObjective 1 (fun _ => 0) h b q

def generalScalarQuantileValues (b h : ℝ → ℝ) : Set ℝ :=
  generalScalarQuantileValue b h '' unitMassQuantiles

def generalScalarMinimum (b h : ℝ → ℝ) : ℝ := sInf (generalScalarQuantileValues b h)

theorem unitMassQuantiles_zero : (fun _ => (0:ℝ)) ∈ unitMassQuantiles :=
  ⟨fun _ _ _ _ _ => le_rfl,fun _ _ => ⟨le_rfl,zero_le_one⟩⟩

theorem generalScalarQuantileValues_nonempty (b h : ℝ → ℝ) :
    (generalScalarQuantileValues b h).Nonempty :=
  ⟨_,⟨_,unitMassQuantiles_zero,rfl⟩⟩

theorem generalScalarQuantileValues_bddBelow (b h : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W) (hh0 : 0 ≤ h 0) :
    BddBelow (generalScalarQuantileValues b h) := by
  refine ⟨generalScalarQuantileValue b h (fun _ => 0)-W,?_⟩
  rintro y ⟨q,hq,rfl⟩
  have hp := mass_strength_objective_l1_comparison 1 (by norm_num) (fun _ => 0) h b q
    (fun _ => 0) hW (fun _ _ _ _ _ => le_rfl) hh hb hq.1 unitMassQuantiles_zero.1
    hbb hq.2 unitMassQuantiles_zero.2 le_rfl hh0
  have hint : (∫u in (0:ℝ)..1,|q u-(0:ℝ)|) ≤ 1 := by
    exact (le_abs_self _).trans (intervalIntegral_abs_le_unit_bound
      (f := fun u => |q u-(0:ℝ)|) (C := 1) (fun u hu => by
        simpa only [sub_zero,abs_abs,abs_of_nonneg (hq.2 u hu).1] using (hq.2 u hu).2))
  have hh' := hp.trans (by simpa using mul_le_mul_of_nonneg_left hint hW)
  have hl := neg_abs_le (massStrengthObjective 1 (fun _ => 0) h b q-
    massStrengthObjective 1 (fun _ => 0) h b (fun _ => 0))
  dsimp only [generalScalarQuantileValue]
  linarith

theorem generalScalarMinimum_le (b h q : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W) (hh0 : 0 ≤ h 0)
    (hq : q ∈ unitMassQuantiles) : generalScalarMinimum b h ≤ generalScalarQuantileValue b h q :=
  csInf_le (generalScalarQuantileValues_bddBelow b h hW hb hh hbb hh0) ⟨q,hq,rfl⟩

theorem macroInterpolationObjective_scalar_general_one (n : ℕ) (hn : 0 < n)
    (b h q : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W) (hh0 : 0 ≤ h 0)
    (hq : q ∈ unitMassQuantiles) :
    macroInterpolationObjective n b h q 1=generalScalarQuantileValue b h q := by
  have hf : MonotoneOn (fun u => h u+b u*q u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (hb hu hv huv) (hq.1 hu hv huv) (hq.2 u hu).1 (hbb v hv).1)
  have h00 : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  simp only [macroInterpolationObjective,generalScalarQuantileValue,massStrengthObjective,
    sub_self,zero_mul,one_mul]
  rw [realOrderedSKPathPressure_pure_field n hn _ hf
    (add_nonneg hh0 (mul_nonneg (hbb 0 h00).1 (hq.2 0 h00).1))]

def generalMacroScalarEndpoint (b h : ℝ → ℝ) (n : ℕ) : ℝ :=
  if hn : 1 < n then macroMinimumValue (macroDensityFloor_pos (n := n) (by omega))
    (macroDensityCap_gt_one hn) n b h 1 else generalScalarMinimum b h

theorem generalMacroScalarEndpoint_lower (b h : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u) (n : ℕ) :
    generalScalarMinimum b h ≤ generalMacroScalarEndpoint b h n := by
  by_cases hn : 1 < n
  · let hη := macroDensityFloor_pos (by omega : 0 < n)
    let hQ := macroDensityCap_gt_one hn
    obtain ⟨α,he,_⟩ := macroMinimumValue_attained hη (macroDensityFloor_lt_one hn) hQ n (by omega)
      b h hW hb hh hbb hhn (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1)
    rw [generalMacroScalarEndpoint,dif_pos hn,← he,
      macroInterpolationObjective_scalar_general_one n (by omega) b h _ hW hb hh hbb
        (hhn 0 (by norm_num)) ⟨macroInverseQuantile_monotone hη hQ α,
          fun u _ => macroInverseQuantile_bounds hη hQ α u⟩]
    exact generalScalarMinimum_le b h _ hW hb hh hbb (hhn 0 (by norm_num))
      ⟨macroInverseQuantile_monotone hη hQ α,fun u _ => macroInverseQuantile_bounds hη hQ α u⟩
  · simp [generalMacroScalarEndpoint,hn]

theorem generalMacroScalarEndpoint_tendsto (b h : ℝ → ℝ) {W : ℝ} (hW : 0 < W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u) :
    Tendsto (generalMacroScalarEndpoint b h) atTop (𝓝 (generalScalarMinimum b h)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hbelow := generalScalarQuantileValues_bddBelow b h hW.le hb hh hbb (hhn 0 (by norm_num))
  obtain ⟨v,hv,hvlt⟩ := (csInf_lt_iff hbelow (generalScalarQuantileValues_nonempty b h)).mp
    (show generalScalarMinimum b h < generalScalarMinimum b h+ε/2 by linarith)
  obtain ⟨q,hq,rfl⟩ := hv
  have hc := eventually_macro_objective_competitor (fun _ => 0) h b q hW
    (ε := ε/2) (by positivity) (fun _ _ _ _ _ => le_rfl) hh hb hq.1 hbb hq.2 le_rfl
    (hhn 0 (by norm_num))
  have hevent : ∀ᶠ n : ℕ in atTop, dist (generalMacroScalarEndpoint b h n) (generalScalarMinimum b h)<ε := by
    filter_upwards [hc,eventually_gt_atTop (1:ℕ)] with n hn hn1
    let hη := macroDensityFloor_pos (by omega : 0 < n)
    let hQ := macroDensityCap_gt_one hn1
    obtain ⟨γ,hγ⟩ := hn hη hQ
    obtain ⟨α,he,hmin⟩ := macroMinimumValue_attained hη (macroDensityFloor_lt_one hn1) hQ n (by omega)
      b h hW.le hb hh hbb hhn (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1)
    have hupper := hmin γ
    rw [macroInterpolationObjective_scalar_general_one n (by omega) b h _ hW.le hb hh hbb
      (hhn 0 (by norm_num)) ⟨macroInverseQuantile_monotone hη hQ γ,
        fun u _ => macroInverseQuantile_bounds hη hQ γ u⟩] at hupper
    have hnear := hγ 1 (by norm_num)
    change |generalScalarQuantileValue b h (macroInverseQuantile hη hQ γ)-
      generalScalarQuantileValue b h q|<ε/2 at hnear
    have hlo := generalMacroScalarEndpoint_lower b h hW.le hb hh hbb hhn n
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hlo)]
    rw [generalMacroScalarEndpoint,dif_pos hn1]
    have hdiff := le_abs_self (generalScalarQuantileValue b h (macroInverseQuantile hη hQ γ)-
      generalScalarQuantileValue b h q)
    linarith
  exact eventually_atTop.mp hevent

end OAI.SKFluctuations.LaplaceWindowFormalization
