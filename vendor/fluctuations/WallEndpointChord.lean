module

public import ActualWallDerivative

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

section
variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin ≤ 1) (hs1 : s ≤ 1) (hc : 0 < c)
variable (hk : ContinuousOn k (Icc rmin 1))
variable (hkc : ∀ t ∈ Icc rmin 1, c ≤ k t)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

def wallResidualStrength (T ε : ℝ) (α : inverseIntegralConstraints rmin s k M) (u : ℝ) : ℝ :=
  if u < s then wallLowStrength T ε/2 else wallHighCoefficient hr hs1 hc hk hkc hm hM g hg α u

def wallResidualRadius (τ d ε : ℝ) (α : inverseIntegralConstraints rmin s k M) (u : ℝ) : ℝ :=
  if u < s then 2*wallLowRadius d rmin ε*wallPsi s τ u
    else IccExtend hs1 (constrainedQuantileMap hr hc hk hkc hm hM α) u

def wallResidualPenalty (T ε τ d : ℝ) (α : inverseIntegralConstraints rmin s k M) (u : ℝ) : ℝ :=
  if u < s then 2*wallLowStrength T ε*(wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2
    else wallHighCoefficient hr hs1 hc hk hkc hm hM (fun r => g r*r^2)
      (hg.mul (continuous_id.pow 2)) α u

theorem wallHighCoefficient_radius_mul (α : inverseIntegralConstraints rmin s k M) (u : ℝ) :
    wallHighCoefficient hr hs1 hc hk hkc hm hM g hg α u *
      IccExtend hs1 (constrainedQuantileMap hr hc hk hkc hm hM α) u =
      wallHighCoefficient hr hs1 hc hk hkc hm hM (fun r => g r*r)
        (hg.mul continuous_id) α u := by
  by_cases hu : s ≤ u <;>
    simp [wallHighCoefficient, omittedExtension, IccExtend, hu, constrainedCoefficient,
      constrainedQuantileMap, Function.comp_def]

theorem wallHighCoefficient_radius_sq (α : inverseIntegralConstraints rmin s k M) (u : ℝ) :
    wallHighCoefficient hr hs1 hc hk hkc hm hM g hg α u *
      (IccExtend hs1 (constrainedQuantileMap hr hc hk hkc hm hM α) u)^2 =
      wallHighCoefficient hr hs1 hc hk hkc hm hM (fun r => g r*r^2)
        (hg.mul (continuous_id.pow 2)) α u := by
  by_cases hu : s ≤ u <;>
    simp [wallHighCoefficient, omittedExtension, IccExtend, hu, constrainedCoefficient,
      constrainedQuantileMap, Function.comp_def]

theorem wallResidual_child_matrix (T ε : ℝ) (α : inverseIntegralConstraints rmin s k M) :
    (fun u => wallBareMatrix T ε (1/2) s u-wallResidualStrength hr hs1 hc hk hkc hm hM g hg T ε α u) =
      wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε 1 α := by
  funext u
  by_cases hu : u < s
  · rw [wallChangedMatrix_below hr hs1 hc hk hkc hm hM g hg T ε 1 α hu]
    simp only [wallBareMatrix, wallResidualStrength, ite_eq_left hu]
    ring
  · simp only [wallBareMatrix, wallResidualStrength, wallChangedMatrix, ite_eq_right hu]

theorem wallResidual_child_field (T ε τ d : ℝ) (α : inverseIntegralConstraints rmin s k M) :
    (fun u => (0 : ℝ)+wallResidualStrength hr hs1 hc hk hkc hm hM g hg T ε α u*
      wallResidualRadius hr hs1 hc hk hkc hm hM τ d ε α u) =
      wallChangedField hr hs1 hc hk hkc hm hM g hg T ε 1 τ d α := by
  funext u
  by_cases hu : u < s
  · rw [wallChangedField_below hr hs1 hc hk hkc hm hM g hg T ε 1 τ d α hu]
    simp only [wallResidualStrength, wallResidualRadius, ite_eq_left hu]
    ring
  · simp only [wallResidualStrength, wallResidualRadius, ite_eq_right hu, zero_add,
      wallChangedField, wallBareField]
    exact wallHighCoefficient_radius_mul hr hs1 hc hk hkc hm hM g hg α u

theorem wallResidual_penalty (T ε τ d : ℝ) (α : inverseIntegralConstraints rmin s k M) :
    (fun u => wallResidualStrength hr hs1 hc hk hkc hm hM g hg T ε α u*
      (wallResidualRadius hr hs1 hc hk hkc hm hM τ d ε α u)^2) =
      wallResidualPenalty hr hs1 hc hk hkc hm hM g hg T ε τ d α := by
  funext u
  by_cases hu : u < s
  · simp only [wallResidualStrength, wallResidualRadius, wallResidualPenalty, ite_eq_left hu]
    ring
  · simp only [wallResidualStrength, wallResidualRadius, wallResidualPenalty, ite_eq_right hu]
    exact wallHighCoefficient_radius_sq hr hs1 hc hk hkc hm hM g hg α u

theorem wall_low_radius_le_half {T ε d : ℝ} (hε : ε ∈ Ioo 0 T)
    (hrmin : 0 ≤ rmin) (hdepsilon : d^2 ≤ ε) :
    wallLowRadius d rmin ε ≤ rmin/2 := by
  unfold wallLowRadius
  apply (div_le_iff₀ (by linarith [hε.1] : 0 < 2*ε)).mpr
  have hh := mul_le_mul_of_nonneg_right hdepsilon hrmin
  nlinarith

theorem wallLipschitzConstant_le_fixed {T ε d : ℝ}
    (hr1 : rmin ≤ 1) (hrmin : 0 ≤ rmin) (hε : ε ∈ Ioo 0 T) (hdepsilon : d^2 ≤ ε) :
    wallLipschitzConstant T ε d rmin ≤ 9*T/64 := by
  have hcB := wallLowStrength_bounds hε
  have hcT : wallLowStrength T ε ≤ T/4 := by linarith [hcB.2.1, hcB.2.2]
  have hr0 : 0 ≤ wallLowRadius d rmin ε :=
    div_nonneg (mul_nonneg (sq_nonneg d) hrmin) (by linarith [hε.1])
  have hrhalf : wallLowRadius d rmin ε ≤ 1/2 :=
    (wall_low_radius_le_half (rmin := rmin) hε hrmin hdepsilon).trans (by linarith [hr1])
  have hfactor : 1/4+wallLowRadius d rmin ε/2+(wallLowRadius d rmin ε)^2/4 ≤ 9/16 := by
    nlinarith
  unfold wallLipschitzConstant
  exact (mul_le_mul_of_nonneg_left hfactor hcB.1).trans (by nlinarith)

theorem wallResidualPenalty_monotone {T ε τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hg0 : ∀ r ∈ Icc rmin 1, 0 ≤ g r)
    (α : inverseIntegralConstraints rmin s k M) :
    MonotoneOn (wallResidualPenalty hr hs1 hc hk hkc hm hM g hg T ε τ d α) (Icc 0 1) := by
  have hc0 := (wallLowStrength_bounds hε).1
  have hr0 : 0 ≤ wallLowRadius d rmin ε :=
    div_nonneg (mul_nonneg (sq_nonneg d) hrmin) (by linarith [hε.1])
  have hgr2 : MonotoneOn (fun r => g r*r^2) (Icc rmin 1) := by
    intro a ha b hb hab
    have hga := mul_nonneg (hg0 a ha) (hrmin.trans ha.1)
    have hgb := mul_nonneg (hg0 b hb) (hrmin.trans hb.1)
    have hh := mul_le_mul (hgrmono ha hb hab) hab (hrmin.trans ha.1) hgb
    convert hh using 1 <;> ring
  have hrhalf := wall_low_radius_le_half (rmin := rmin) hε hrmin hdepsilon
  have hamp := wall_low_amplitude_bound (d := d) hε (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hrmin
  have hcross : 2*wallLowStrength T ε*(wallLowRadius d rmin ε)^2 ≤ d^2*rmin^2 := by
    have hprod := mul_le_mul hamp.2 hrhalf hr0 (by positivity : 0 ≤ d^2*rmin/4)
    nlinarith [mul_nonneg (sq_nonneg d) (sq_nonneg rmin)]
  intro u hu v hv huv
  by_cases hus : u < s
  · simp only [wallResidualPenalty, ite_eq_left hus]
    by_cases hvs : v < s
    · simp only [ite_eq_left hvs]
      have hp := wallPsi_monotoneOn hs hτ ⟨hu.1, hus.le⟩ ⟨hv.1, hvs.le⟩ huv
      have hpu := (wallPsi_mem hs hτ ⟨hu.1, hus.le⟩).1
      have hpv := (wallPsi_mem hs hτ ⟨hv.1, hvs.le⟩).1
      exact mul_le_mul_of_nonneg_left (by nlinarith : (wallPsi s τ u)^2 ≤ (wallPsi s τ v)^2)
        (by positivity)
    · simp only [ite_eq_right hvs]
      have hvhi : v ∈ Icc s 1 := ⟨le_of_not_gt hvs, hv.2⟩
      rw [wallHighCoefficient_on hr hs1 hc hk hkc hm hM (fun r => g r*r^2)
        (hg.mul (continuous_id.pow 2)) α hvhi]
      have hh := hgr2 ⟨le_rfl, hr⟩
        (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hvhi⟩).property
        (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hvhi⟩).property.1
      dsimp only at hh
      rw [hginitial] at hh
      have hp := wallPsi_mem hs hτ ⟨hu.1, hus.le⟩
      have hhpsi : (wallPsi s τ u)^2 ≤ 1 := by nlinarith [hp.1, hp.2]
      exact (mul_le_of_le_one_right (by positivity) hhpsi).trans (hcross.trans hh)
  · have hvs : ¬v < s := by linarith
    simp only [wallResidualPenalty, ite_eq_right hus, ite_eq_right hvs]
    have huhi : u ∈ Icc s 1 := ⟨le_of_not_gt hus, hu.2⟩
    have hvhi : v ∈ Icc s 1 := ⟨le_of_not_gt hvs, hv.2⟩
    rw [wallHighCoefficient_on hr hs1 hc hk hkc hm hM (fun r => g r*r^2)
      (hg.mul (continuous_id.pow 2)) α huhi,
      wallHighCoefficient_on hr hs1 hc hk hkc hm hM (fun r => g r*r^2)
      (hg.mul (continuous_id.pow 2)) α hvhi]
    exact hgr2
      (constrainedQuantile hr hc hk hkc hm hM α ⟨u, huhi⟩).property
      (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hvhi⟩).property
      ((inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.monotone huv)

theorem wall_endpoint_chord {T ε τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hg0 : ∀ r ∈ Icc rmin 1, 0 ≤ g r)
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (n : ℕ) (hn : 0 < n) (x : OrderedFeatureIndex n → ℝ)
    (α : inverseIntegralConstraints rmin s k M) :
    realOrderedSKPathPressure n (wallBareMatrix T ε (1/2) s) (fun _ => 0) x ≤
      wallObjective hr hs1 hc hk hkc hm hM g hg T ε 1 τ d n x α +
        wallLowStrength T ε/4*
          (∫ u in (0 : ℝ)..s, (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) := by
  have hc0 := (wallLowStrength_bounds hε).1
  have ha := wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hdepsilon hginitial
    hganti hgrmono hgbound α
  have hb : MonotoneOn (wallBareMatrix T ε (1/2) s) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    by_cases hus : u < s
    · by_cases hvs : v < s
      · simp [wallBareMatrix, hus, hvs]
      · simp [wallBareMatrix, hus, hvs]; linarith [hε.1]
    · have hvs : ¬v < s := by linarith
      simp [wallBareMatrix, hus, hvs]
  have hb0 : 0 ≤ wallBareMatrix T ε (1/2) s 0 := by
    have hh := wall_low_matrix_bound hε (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    simp only [wallBareMatrix, ite_eq_left hs]
    linarith [hε.2]
  have hp := wallResidualPenalty_monotone hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hdepsilon hginitial hgrmono hg0 α
  have hc' := pathCompensatedPressure_lower n hn (wallBareMatrix T ε (1/2) s) (fun _ => 0)
    (wallResidualStrength hr hs1 hc hk hkc hm hM g hg T ε α)
    (wallResidualRadius hr hs1 hc hk hkc hm hM τ d ε α)
    (by
      intro u hu
      by_cases hus : u < s
      · simp only [wallResidualStrength, ite_eq_left hus]
        positivity
      · simp only [wallResidualStrength, ite_eq_right hus]
        rw [wallHighCoefficient_on hr hs1 hc hk hkc hm hM g hg α ⟨le_of_not_gt hus, hu.2⟩]
        exact hg0 _ (constrainedQuantile hr hc hk hkc hm hM α ⟨u, ⟨le_of_not_gt hus, hu.2⟩⟩).property)
    hb (fun _ _ _ _ _ => le_rfl) hb0 (by norm_num)
    (by rw [wallResidual_child_matrix hr hs1 hc hk hkc hm hM g hg]; exact ha.1)
    (by rw [wallResidual_child_field hr hs1 hc hk hkc hm hM g hg]; exact ha.2.1)
    (by
      change 0 ≤ (fun u => wallBareMatrix T ε (1/2) s u-
        wallResidualStrength hr hs1 hc hk hkc hm hM g hg T ε α u) 0
      rw [wallResidual_child_matrix hr hs1 hc hk hkc hm hM g hg]
      exact ha.2.2.1)
    (by
      change 0 ≤ (fun u => (0 : ℝ)+wallResidualStrength hr hs1 hc hk hkc hm hM g hg T ε α u*
        wallResidualRadius hr hs1 hc hk hkc hm hM τ d ε α u) 0
      rw [wallResidual_child_field hr hs1 hc hk hkc hm hM g hg]
      exact ha.2.2.2)
    (by rw [wallResidual_penalty hr hs1 hc hk hkc hm hM g hg]; exact hp) x
  unfold pathCompensatedPressure at hc'
  rw [wallResidual_child_matrix hr hs1 hc hk hkc hm hM g hg,
    wallResidual_child_field hr hs1 hc hk hkc hm hM g hg,
    wallResidual_penalty hr hs1 hc hk hkc hm hM g hg] at hc'
  have hhigh : IntervalIntegrable
      (wallHighCoefficient hr hs1 hc hk hkc hm hM (fun r => g r*r^2)
        (hg.mul (continuous_id.pow 2)) α) volume 0 1 :=
    omittedExtension_intervalIntegrable hs1 _ 0 1
  have hlow : IntervalIntegrable
      (fun u => (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) volume 0 s := by
    have hcpsi : ContinuousOn (wallPsi s τ) (uIcc (0 : ℝ) s) := by
      simpa only [uIcc_of_le hs.le] using wallPsi_continuousOn hs hτ
    exact ((hcpsi.pow 2).const_mul _).intervalIntegrable
  have hlowcut : IntervalIntegrable
      (fun u => if u < s then 2*wallLowStrength T ε*(wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2 else 0)
      volume 0 1 := by
    have hlo : IntervalIntegrable
        (fun u => if u < s then 2*wallLowStrength T ε*(wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2 else 0)
        volume 0 s := by
      apply (hlow.const_mul (2*wallLowStrength T ε)).congr_uIoo
      intro u hu
      rw [uIoo_of_le hs.le] at hu
      simp [hu.2, mul_assoc]
    have hhi : IntervalIntegrable
        (fun u => if u < s then 2*wallLowStrength T ε*(wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2 else 0)
        volume s 1 := by
      apply (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo
      intro u hu
      rw [uIoo_of_le hs1] at hu
      simp [not_lt.mpr hu.1.le]
    exact hlo.trans hhi
  have hsplit : wallResidualPenalty hr hs1 hc hk hkc hm hM g hg T ε τ d α =
      fun u => wallHighCoefficient hr hs1 hc hk hkc hm hM (fun r => g r*r^2)
        (hg.mul (continuous_id.pow 2)) α u +
        (if u < s then 2*wallLowStrength T ε*(wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2 else 0) := by
    funext u
    by_cases hu : u < s
    · simp only [wallResidualPenalty, ite_eq_left hu, wallHighCoefficient]
      rw [omittedExtension_before hs1 _ hu, zero_add]
    · simp only [wallResidualPenalty, ite_eq_right hu, add_zero]
  rw [hsplit, intervalIntegral.integral_add hhigh hlowcut] at hc'
  have hcost : (∫ u in (0 : ℝ)..1,
      if u < s then 2*wallLowStrength T ε*(wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2 else 0) =
      2*wallLowStrength T ε*(∫ u in (0 : ℝ)..s, (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) := by
    have heq : (fun u => 2*wallLowStrength T ε*(wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) =
        fun u => (2*wallLowStrength T ε)*((wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) := by
      funext u
      ring
    rw [integral_below_wall hs hs1 (by simpa only [heq] using hlow.const_mul (2*wallLowStrength T ε)),
      heq, intervalIntegral.integral_const_mul]
  rw [hcost] at hc'
  rw [wallObjective_eq hr hs1 hc hk hkc hm hM g hg]
  linarith

end
end OAI.SKFluctuations.LaplaceWindowFormalization
