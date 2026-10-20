module

public import VariableEndpointStrengthEnvelope
public import PiecewisePartitionSum

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def omittedStrengthCoefficient (d u0 : ℝ) (R : ℝ → ℝ) (lam u : ℝ) : ℝ :=
  if u0 ≤ u then laplaceComparisonStrength d lam (R u) else 0

def omittedStrengthParameterDeriv (d u0 : ℝ) (R : ℝ → ℝ) (lam u : ℝ) : ℝ :=
  if u0 ≤ u then laplaceStrengthParameterDeriv d lam (R u) else 0

def omittedStrengthSweepObjective (n : ℕ) (b h : ℝ → ℝ) (d u0 : ℝ)
    (R : ℝ → ℝ) (lam : ℝ) : ℝ :=
  realOrderedSKPathPressure n
    (fun u => b u-omittedStrengthCoefficient d u0 R lam u)
    (fun u => h u+omittedStrengthCoefficient d u0 R lam u*R u) 0 +
    (1/4:ℝ)*(∫ u in (0:ℝ)..1, omittedStrengthCoefficient d u0 R lam u*(R u)^2)

theorem omittedStrengthCoefficient_displacement (d u0 : ℝ) (R : ℝ → ℝ)
    (lam lam' u : ℝ) :
    |omittedStrengthCoefficient d u0 R lam u-
      omittedStrengthCoefficient d u0 R lam' u| ≤ |lam-lam'| := by
  by_cases hu : u0 ≤ u
  · simpa [omittedStrengthCoefficient,hu] using
      laplaceStrength_parameter_displacement d (R u) lam lam'
  · simp [omittedStrengthCoefficient,hu]

theorem omittedStrengthSweep_clocks_admissible (b h R : ℝ → ℝ)
    {d u0 lam : ℝ} (hu0 : u0 ∈ Icc (0:ℝ) 1) (hd : d ≠ 0)
    (hlam : 0 ≤ lam) (hlcut : lam ≤ b u0)
    (hcross : ∀ u ∈ Ico (0:ℝ) u0, b u+lam ≤ b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0 ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc u0 1))
    (hRb : ∀ u ∈ Icc u0 1, R u ∈ Icc (0:ℝ) 1) :
    MonotoneOn (fun u => b u-omittedStrengthCoefficient d u0 R lam u) (Icc (0:ℝ) 1) ∧
    MonotoneOn (fun u => h u+omittedStrengthCoefficient d u0 R lam u*R u) (Icc (0:ℝ) 1) ∧
    (∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u-omittedStrengthCoefficient d u0 R lam u) ∧
    (∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u+omittedStrengthCoefficient d u0 R lam u*R u) := by
  have hm := laplaceComparisonStrength_monotonicities_nonneg hd hlam
  refine ⟨?_,?_,?_,?_⟩
  · intro u hu v hv huv
    by_cases hv0 : u0 ≤ v
    · by_cases hu0' : u0 ≤ u
      · simpa only [omittedStrengthCoefficient,ite_eq_left hu0',ite_eq_left hv0] using
          sub_le_sub (hb hu hv huv) (hm.1 (hRb u ⟨hu0',hu.2⟩)
            (hRb v ⟨hv0,hv.2⟩) (hR ⟨hu0',hu.2⟩ ⟨hv0,hv.2⟩ huv))
      · have hc := hcross u ⟨hu.1,lt_of_not_ge hu0'⟩
        have he := laplaceComparisonStrength_le d hlam (R v)
        have hbv := hb hu0 hv hv0
        simp only [omittedStrengthCoefficient,ite_eq_right hu0',ite_eq_left hv0,sub_zero]
        linarith
    · have hu0' : ¬u0 ≤ u := fun he => hv0 (he.trans huv)
      simpa only [omittedStrengthCoefficient,ite_eq_right hu0',ite_eq_right hv0,sub_zero] using hb hu hv huv
  · intro u hu v hv huv
    by_cases hv0 : u0 ≤ v
    · by_cases hu0' : u0 ≤ u
      · simpa only [omittedStrengthCoefficient,ite_eq_left hu0',ite_eq_left hv0] using
          add_le_add (hh hu hv huv) (hm.2 (hRb u ⟨hu0',hu.2⟩)
            (hRb v ⟨hv0,hv.2⟩) (hR ⟨hu0',hu.2⟩ ⟨hv0,hv.2⟩ huv))
      · have he := mul_nonneg (laplaceComparisonStrength_nonneg d (R v) hlam) (hRb v ⟨hv0,hv.2⟩).1
        simp only [omittedStrengthCoefficient,ite_eq_right hu0',ite_eq_left hv0,zero_mul,add_zero]
        linarith [hh hu hv huv]
    · have hu0' : ¬u0 ≤ u := fun he => hv0 (he.trans huv)
      simpa only [omittedStrengthCoefficient,ite_eq_right hu0',ite_eq_right hv0,zero_mul,add_zero] using hh hu hv huv
  · intro u hu
    by_cases hu0' : u0 ≤ u
    · have he := laplaceComparisonStrength_le d hlam (R u)
      have hbu := hb hu0 hu hu0'
      simp only [omittedStrengthCoefficient,ite_eq_left hu0']
      linarith
    · simpa only [omittedStrengthCoefficient,ite_eq_right hu0',sub_zero] using hb0.trans (hb (by norm_num) hu hu.1)
  · intro u hu
    have hhu := hh0.trans (hh (by norm_num) hu hu.1)
    by_cases hu0' : u0 ≤ u
    · simpa only [omittedStrengthCoefficient,ite_eq_left hu0'] using
        add_nonneg hhu (mul_nonneg (laplaceComparisonStrength_nonneg d (R u) hlam) (hRb u ⟨hu0',hu.2⟩).1)
    · simpa only [omittedStrengthCoefficient,ite_eq_right hu0',zero_mul,add_zero] using hhu

theorem omittedStrengthCoefficient_mul_integrable {d u0 lam : ℝ}
    (hu0 : u0 ∈ Icc (0:ℝ) 1) (R : ℝ → ℝ)
    (hRc : ContinuousOn R (Icc u0 1)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc u0 1)) :
    IntervalIntegrable (fun u => omittedStrengthCoefficient d u0 R lam u*f u) volume 0 1 := by
  apply cutoff_eq_intervalIntegrable hu0
    (((laplaceComparisonStrength_contDiff d lam).continuous.comp_continuousOn hRc).mul hf)
  intro u _
  by_cases he : u0 ≤ u <;> simp [omittedStrengthCoefficient,he]

theorem omittedStrengthParameterDeriv_mul_integrable {d u0 lam : ℝ}
    (hu0 : u0 ∈ Icc (0:ℝ) 1) (R : ℝ → ℝ)
    (hRc : ContinuousOn R (Icc u0 1)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc u0 1)) :
    IntervalIntegrable (fun u => omittedStrengthParameterDeriv d u0 R lam u*f u) volume 0 1 := by
  apply cutoff_eq_intervalIntegrable hu0
    (((laplaceStrengthParameterDeriv_continuous_radius d lam).comp_continuousOn hRc).mul hf)
  intro u _
  by_cases he : u0 ≤ u <;> simp [omittedStrengthParameterDeriv,he]

theorem omittedStrengthSweepObjective_lipschitz (n : ℕ) (hn : 0 < n)
    (b h R : ℝ → ℝ) {d u0 L : ℝ} (hu0 : u0 ∈ Icc (0:ℝ) 1) (hd : d ≠ 0)
    (hLcut : L ≤ b u0) (hcross : ∀ u ∈ Ico (0:ℝ) u0, b u+L ≤ b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0 ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc u0 1))
    (hRb : ∀ u ∈ Icc u0 1, R u ∈ Icc (0:ℝ) 1)
    (hRc : ContinuousOn R (Icc u0 1)) :
    LipschitzOnWith 1 (omittedStrengthSweepObjective n b h d u0 R) (Icc (0:ℝ) L) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro lam hl lam' hl'
  have ha (l : ℝ) (hl : l ∈ Icc (0:ℝ) L) := omittedStrengthSweep_clocks_admissible b h R hu0 hd hl.1
    (hl.2.trans hLcut) (fun u hu => by linarith [hcross u hu,hl.2]) hb hb0 hh hh0 hR hRb
  have hdisp := omittedStrengthCoefficient_displacement d u0 R lam lam'
  have hfdisp (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      |(h u+omittedStrengthCoefficient d u0 R lam u*R u)-
        (h u+omittedStrengthCoefficient d u0 R lam' u*R u)| ≤ |lam-lam'| := by
    by_cases hu0' : u0 ≤ u
    · have he : (h u+omittedStrengthCoefficient d u0 R lam u*R u)-
          (h u+omittedStrengthCoefficient d u0 R lam' u*R u)=
          (omittedStrengthCoefficient d u0 R lam u-omittedStrengthCoefficient d u0 R lam' u)*R u := by ring
      rw [he,abs_mul,abs_of_nonneg (hRb u ⟨hu0',hu.2⟩).1]
      exact (mul_le_mul_of_nonneg_right (hdisp u) (hRb u ⟨hu0',hu.2⟩).1).trans
        (mul_le_of_le_one_right (abs_nonneg _) (hRb u ⟨hu0',hu.2⟩).2)
    · simp [omittedStrengthCoefficient,hu0']
  have hpdisp (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      |omittedStrengthCoefficient d u0 R lam u*(R u)^2-
        omittedStrengthCoefficient d u0 R lam' u*(R u)^2| ≤ |lam-lam'| := by
    by_cases hu0' : u0 ≤ u
    · rw [← sub_mul,abs_mul,abs_of_nonneg (sq_nonneg (R u))]
      exact (mul_le_mul_of_nonneg_right (hdisp u) (sq_nonneg _)).trans
        (mul_le_of_le_one_right (abs_nonneg _) (by nlinarith [(hRb u ⟨hu0',hu.2⟩).1,(hRb u ⟨hu0',hu.2⟩).2]))
    · simp [omittedStrengthCoefficient,hu0']
  have hp := realOrderedSKPathPressure_uniform_comparison n hn _ _ _ _
    (ha lam hl).1 (ha lam hl).2.1 (ha lam' hl').1 (ha lam' hl').2.1
    ((ha lam hl).2.2.1 0 (by norm_num)) ((ha lam hl).2.2.2 0 (by norm_num))
    ((ha lam' hl').2.2.1 0 (by norm_num)) ((ha lam' hl').2.2.2 0 (by norm_num))
    (fun u _ => by
      have he : b u-omittedStrengthCoefficient d u0 R lam u-
          (b u-omittedStrengthCoefficient d u0 R lam' u)=
          -(omittedStrengthCoefficient d u0 R lam u-omittedStrengthCoefficient d u0 R lam' u) := by ring
      rw [he,abs_neg]; exact hdisp u) hfdisp 0
  have hi (l : ℝ) := omittedStrengthCoefficient_mul_integrable (d:=d) (lam:=l) hu0 R hRc
    (fun u => (R u)^2) (hRc.pow 2)
  have hip := intervalIntegral_abs_le_unit_bound hpdisp
  rw [Real.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul]
  unfold omittedStrengthSweepObjective
  have he (p q a c : ℝ) : (p+1/4*a)-(q+1/4*c)=(p-q)+1/4*(a-c) := by ring
  rw [he,← intervalIntegral.integral_sub (hi lam) (hi lam')]
  calc
    |_ + _| ≤ |_ - _| + |(1/4:ℝ)*(∫ u in (0:ℝ)..1,
      omittedStrengthCoefficient d u0 R lam u*(R u)^2-
      omittedStrengthCoefficient d u0 R lam' u*(R u)^2)| := abs_add_le _ _
    _ ≤ |lam-lam'|/4+|lam-lam'|/2+(1/4:ℝ)*|lam-lam'| := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
      exact add_le_add hp (mul_le_mul_of_nonneg_left hip (by norm_num))
    _ = |lam-lam'| := by ring

theorem omittedStrengthSweepObjective_zero (n : ℕ) (b h R : ℝ → ℝ) (d u0 : ℝ) :
    omittedStrengthSweepObjective n b h d u0 R 0=realOrderedSKPathPressure n b h 0 := by
  have he : omittedStrengthCoefficient d u0 R 0 = 0 := by
    ext u
    simp [omittedStrengthCoefficient,laplaceComparisonStrength_zero]
  simp [omittedStrengthSweepObjective,he]

end OAI.SKFluctuations.LaplaceWindowFormalization
