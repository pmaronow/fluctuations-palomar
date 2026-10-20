module

public import MacroProfileRegularization
public import ScalarProfileL1Stability
public import ScalarLipschitzCDFApproximation
public import SKFluctuationsOAI.Probability.SKFluctuations.RealSKPressureL1

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def macroDensityFloor (n : ℕ) : ℝ := (n:ℝ)^(-(1:ℝ)/8)
def macroDensityCap (n : ℕ) : ℝ := (n:ℝ)^((1:ℝ)/8)

theorem macroDensityFloor_pos {n : ℕ} (hn : 0 < n) : 0 < macroDensityFloor n :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem macroDensityCap_gt_one {n : ℕ} (hn : 1 < n) : 1 < macroDensityCap n := by
  exact Real.one_lt_rpow (by exact_mod_cast hn : (1:ℝ) < n) (by norm_num)

theorem macroDensityFloor_lt_one {n : ℕ} (hn : 1 < n) : macroDensityFloor n < 1 := by
  unfold macroDensityFloor
  rw [neg_div,Real.rpow_neg (show 0 ≤ (n:ℝ) by positivity)]
  exact inv_lt_one_of_one_lt₀ (macroDensityCap_gt_one hn)

theorem floorRegularized_scalar_error {T : ℝ} (hT : 0 < T) (G : boundedMassProfiles)
    {η : ℝ} (hη : η ∈ Icc (0:ℝ) 1) :
    |scalarParisiValue hT (floorRegularizedProfile G hη)-scalarParisiValue hT G| ≤ T*η := by
  have h := scalarParisiValue_L1_comparison hT (floorRegularizedProfile G hη) G
  have hint := intervalIntegral_abs_le_unit_bound
    (f := fun u => |(floorRegularizedProfile G hη).val u-G.val u|) (C := η)
    (fun u _ => by simpa only [abs_abs] using floorRegularizedProfile_pointwise_error G hη u)
  exact h.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hint) hT.le)

theorem eventually_macro_scalar_competitor_of_Lipschitz {T : ℝ} (hT : 0 < T)
    (G : boundedMassProfiles) {L : ℝ≥0} (hGL : LipschitzWith L G.val)
    (hG0 : G.val 0=0) (hG1 : G.val 1=1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (hη : 0 < macroDensityFloor n) (hQ : 1 < macroDensityCap n),
      ∃ γ : MacroInverseClass (macroDensityFloor n) (macroDensityCap n),
        scalarParisiValue hT (quantileMassProfile (macroInverseQuantile hη hQ γ)
          (fun u _ => macroInverseQuantile_bounds hη hQ γ u)) ≤ scalarParisiValue hT G+ε := by
  have hfloor : Tendsto macroDensityFloor atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n:ℝ)^(-(1:ℝ)/8)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/8)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hcap : Tendsto macroDensityCap atTop atTop := by
    change Tendsto (fun n : ℕ => (n:ℝ)^((1:ℝ)/8)) atTop atTop
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  have hη1 := hfloor.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
  have hηsmall := hfloor.eventually (eventually_lt_nhds (div_pos hε hT))
  have hQbig := hcap.eventually (eventually_ge_atTop ((L:ℝ)+1))
  filter_upwards [hη1,hηsmall,hQbig] with n hn1 hnsmall hnQ
  intro hη hQ
  let hηI : macroDensityFloor n ∈ Icc (0:ℝ) 1 := ⟨hη.le,hn1.le⟩
  let γ := floorRegularizedInverse hGL hG0 hG1 hηI hnQ
  refine ⟨γ,?_⟩
  rw [macroInverseQuantile_massProfile_eq hη hQ γ]
  have herr := floorRegularized_scalar_error hT G hηI
  have hsmall : T*macroDensityFloor n ≤ ε :=
    (mul_le_mul_of_nonneg_left hnsmall.le hT.le).trans_eq (mul_div_cancel₀ _ hT.ne')
  have hupper := (le_abs_self _).trans herr
  change scalarParisiValue hT (floorRegularizedProfile G hηI) ≤ scalarParisiValue hT G+ε
  linarith

theorem eventually_macro_scalar_competitor {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (hη : 0 < macroDensityFloor n) (hQ : 1 < macroDensityCap n),
      ∃ γ : MacroInverseClass (macroDensityFloor n) (macroDensityCap n),
        scalarParisiValue hT (quantileMassProfile (macroInverseQuantile hη hQ γ)
          (fun u _ => macroInverseQuantile_bounds hη hQ γ u)) ≤ scalarParisiValue hT α+ε := by
  obtain ⟨G,L,hGm,hGL,hG0,hG1,hGb,happrox⟩ :=
    exists_scalarLipschitzCDF_approximation α.val α.property.2
      (fun r _ => α.property.1 r) (ε := ε/(2*T)) (by positivity)
  let Gb : boundedMassProfiles := ⟨G,hGb,hGm⟩
  have hP := scalarParisiValue_L1_comparison hT Gb α
  have herr : scalarParisiValue hT Gb ≤ scalarParisiValue hT α+ε/2 := by
    have hmul := mul_lt_mul_of_pos_left happrox hT
    have he : T*(ε/(2*T)) = ε/2 := by field_simp
    rw [he] at hmul
    have hupper := (le_abs_self _).trans hP
    linarith
  filter_upwards [eventually_macro_scalar_competitor_of_Lipschitz hT Gb hGL hG0 hG1
    (ε := ε/2) (by positivity)] with n hn
  intro hη hQ
  obtain ⟨γ,hγ⟩ := hn hη hQ
  exact ⟨γ,by linarith⟩

theorem eventually_macro_scalar_reference_competitor {β : ℝ≥0} (hβ : 0 < β)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (hη : 0 < macroDensityFloor n) (hQ : 1 < macroDensityCap n),
      ∃ γ : MacroInverseClass (macroDensityFloor n) (macroDensityCap n),
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ))
          (quantileMassProfile (macroInverseQuantile hη hQ γ)
            (fun u _ => macroInverseQuantile_bounds hη hQ γ u)) ≤
          normalizedScalarParisiReference β+ε := by
  obtain ⟨α,_,hα,_⟩ := exists_scalarProfile_eq_normalizedScalarParisiReference hβ
  have h := eventually_macro_scalar_competitor (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α hε
  rwa [hα] at h

end OAI.SKFluctuations.LaplaceWindowFormalization
