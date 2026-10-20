module

public import MacroInverseDuality
public import MacroScalarCompetitors

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem macroDensityFloor_reciprocal (n : ℕ) :
    macroDensityFloor n=1/macroDensityCap n := by
  simp only [macroDensityFloor,macroDensityCap,neg_div,one_div]
  rw [Real.rpow_neg (Nat.cast_nonneg n)]

theorem eventually_macro_quantile_competitor (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (hqb : ∀ u ∈ Icc (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (hη : 0 < macroDensityFloor n) (hQ : 1 < macroDensityCap n),
      ∃ γ : MacroInverseClass (macroDensityFloor n) (macroDensityCap n),
        (∫u in (0:ℝ)..1,|macroInverseQuantile hη hQ γ u-q u|)<ε := by
  obtain ⟨G,K,hGm,hGL,hG0,hG1,hGb,herr⟩ := exists_scalarLipschitzCDF_approximation_on
    q hq hqb (ε := ε/2) (by positivity)
  let Gb : boundedMassProfiles := ⟨G,hGb,hGm⟩
  let L := (K:ℝ)+2
  have hL : 1 < L := by dsimp [L]; linarith [K.coe_nonneg]
  have hfloor : Tendsto macroDensityFloor atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n:ℝ)^(-(1:ℝ)/8)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/8)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hfloor.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hfloor.eventually (eventually_lt_nhds (show (0:ℝ)<1/L by positivity)),
    hfloor.eventually (eventually_lt_nhds (show (0:ℝ)<ε/2 by positivity))] with n hη1 hηL hηε
  intro hη hQ
  let hηI : macroDensityFloor n ∈ Icc (0:ℝ) 1 := ⟨hη.le,hη1.le⟩
  let A : MacroInverseClass (macroDensityFloor n) L :=
    floorRegularizedInverse (G := Gb) hGL hG0 hG1 hηI (by dsimp [L]; linarith)
  have hrecip : 1/macroDensityFloor n ≤ macroDensityCap n := by
    rw [macroDensityFloor_reciprocal,one_div_one_div]
  let γ := macroInverseDual hη hL A hηL.le hrecip
  refine ⟨γ,?_⟩
  have hqi : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0:ℝ) 1) by simpa using hq).intervalIntegrable
  have hGi : IntervalIntegrable G volume 0 1 := hGm.intervalIntegrable
  have hAi : IntervalIntegrable A.val.val volume 0 1 := A.val.property.2.intervalIntegrable
  have hγq (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : macroInverseQuantile hη hQ γ u=A.val.val u :=
    macroInverseDual_quantile hη hL A hηL.le hrecip hη hQ hu
  have htri : (∫u in (0:ℝ)..1,|A.val.val u-q u|) ≤
      (∫u in (0:ℝ)..1,|A.val.val u-G u|)+(∫u in (0:ℝ)..1,|G u-q u|) := by
    rw [← intervalIntegral.integral_add (hAi.sub hGi).abs (hGi.sub hqi).abs]
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one (hAi.sub hqi).abs
      ((hAi.sub hGi).abs.add (hGi.sub hqi).abs)
    intro u _
    have h := abs_add_le (A.val.val u-G u) (G u-q u)
    have he : A.val.val u-G u+(G u-q u)=A.val.val u-q u := by ring
    rwa [he] at h
  have hAG : (∫u in (0:ℝ)..1,|A.val.val u-G u|) ≤ macroDensityFloor n := by
    have h := intervalIntegral_abs_le_unit_bound (f := fun u => |A.val.val u-G u|)
      (C := macroDensityFloor n) (fun u _ => by
        simpa only [A,floorRegularizedInverse,Gb,abs_abs] using
          floorRegularizedProfile_pointwise_error Gb hηI u)
    exact (le_abs_self _).trans h
  have heq : (∫u in (0:ℝ)..1,|macroInverseQuantile hη hQ γ u-q u|) =
      ∫u in (0:ℝ)..1,|A.val.val u-q u| := by
    apply intervalIntegral.integral_congr
    intro u hu
    change |macroInverseQuantile hη hQ γ u-q u|=|A.val.val u-q u|
    rw [hγq u (by simpa only [uIcc_of_le zero_le_one] using hu)]
  rw [heq]
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
