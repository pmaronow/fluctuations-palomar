module

public import MacroQuantileCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def unitLinearMassProfile : boundedMassProfiles :=
  affineInverseProfile 0 0 (by norm_num) (by norm_num)

theorem unitLinearMassProfile_on {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    unitLinearMassProfile.val r = r := by
  simpa [unitLinearMassProfile,affineInverseProfile] using affineInverse_on (r₀ := 0) (u₀ := 0) hr

def floorRegularizedProfile (G : boundedMassProfiles) {η : ℝ} (hη : η ∈ Icc (0:ℝ) 1) :
    boundedMassProfiles :=
  ⟨fun r => (1-η)*G.val r+η*unitLinearMassProfile.val r, by
    constructor
    · intro r
      have hG := G.property.1 r
      have hI := unitLinearMassProfile.property.1 r
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hη.2) hG.1) (mul_nonneg hη.1 hI.1)
      · calc
          (1-η)*G.val r+η*unitLinearMassProfile.val r ≤ (1-η)*1+η*1 :=
            add_le_add (mul_le_mul_of_nonneg_left hG.2 (sub_nonneg.mpr hη.2))
              (mul_le_mul_of_nonneg_left hI.2 hη.1)
          _ = 1 := by ring
    · intro r s hrs
      exact add_le_add
        (mul_le_mul_of_nonneg_left (G.property.2 hrs) (sub_nonneg.mpr hη.2))
        (mul_le_mul_of_nonneg_left (unitLinearMassProfile.property.2 hrs) hη.1)⟩

theorem floorRegularizedProfile_gap {G : boundedMassProfiles} {L : ℝ≥0}
    (hGL : LipschitzWith L G.val) {η : ℝ} (hη : η ∈ Icc (0:ℝ) 1)
    {r s : ℝ} (hr : r ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) (hrs : r ≤ s) :
    η*(s-r) ≤ (floorRegularizedProfile G hη).val s-(floorRegularizedProfile G hη).val r ∧
    (floorRegularizedProfile G hη).val s-(floorRegularizedProfile G hη).val r ≤
      ((1-η)*(L:ℝ)+η)*(s-r) := by
  have hG := G.property.2 hrs
  have hLip := hGL.dist_le_mul s r
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hG),
    abs_of_nonneg (sub_nonneg.mpr hrs)] at hLip
  change η*(s-r) ≤ _ ∧ _ ≤ _
  simp only [floorRegularizedProfile,unitLinearMassProfile_on hr,unitLinearMassProfile_on hs]
  have hnon := sub_nonneg.mpr hη.2
  constructor
  · nlinarith [mul_nonneg hnon (sub_nonneg.mpr hG)]
  · nlinarith [mul_le_mul_of_nonneg_left hLip hnon]

def floorRegularizedInverse {G : boundedMassProfiles} {L : ℝ≥0}
    (hGL : LipschitzWith L G.val) (hG0 : G.val 0=0) (hG1 : G.val 1=1)
    {η Q : ℝ} (hη : η ∈ Icc (0:ℝ) 1) (hQ : (L:ℝ)+1 ≤ Q) : MacroInverseClass η Q :=
  ⟨floorRegularizedProfile G hη, by
    refine ⟨?_,?_,?_⟩
    · simp [floorRegularizedProfile,hG0,unitLinearMassProfile_on (r := 0) (by norm_num)]
    · simp [floorRegularizedProfile,hG1,unitLinearMassProfile_on (r := 1) (by norm_num)]
    · intro r hr s hs hrs
      have hgap := floorRegularizedProfile_gap hGL hη hr hs hrs
      have hcoef : (1-η)*(L:ℝ)+η ≤ Q := by
        have hηL := mul_nonneg hη.1 L.coe_nonneg
        nlinarith [hη.2]
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      exact ⟨by simpa only [mul_comm] using hgap.1,
        hgap.2.trans (by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hrs))⟩⟩

theorem floorRegularizedProfile_pointwise_error (G : boundedMassProfiles)
    {η : ℝ} (hη : η ∈ Icc (0:ℝ) 1) (r : ℝ) :
    |(floorRegularizedProfile G hη).val r-G.val r| ≤ η := by
  have hG := G.property.1 r
  have hI := unitLinearMassProfile.property.1 r
  change |(1-η)*G.val r+η*unitLinearMassProfile.val r-G.val r| ≤ η
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hG.1 hη.1,
    mul_le_mul_of_nonneg_left hG.2 hη.1,mul_le_mul_of_nonneg_left hI.1 hη.1,
    mul_le_mul_of_nonneg_left hI.2 hη.1]

end OAI.SKFluctuations.LaplaceWindowFormalization
