module

public import SKFluctuationsOAI.Probability.SKFluctuations.RealSKPressureL1
public import UpperWallIteration
public import SKFluctuationsOAI.Probability.SKFluctuations.InverseConstraintNonempty

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology

def wallPsi (s τ u : ℝ) : ℝ :=
  (Real.log (s+τ)-Real.log (s-u+τ))/Real.log ((s+τ)/τ)

theorem wallPsi_log_pos {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ) :
    0 < Real.log ((s+τ)/τ) := by
  apply Real.log_pos
  apply (lt_div_iff₀ hτ).mpr
  linarith

theorem wallPsi_eq_ratio {s τ u : ℝ} (hs : 0 < s) (hτ : 0 < τ) (hu : u ≤ s) :
    wallPsi s τ u =
      Real.log ((s+τ)/(s-u+τ))/Real.log ((s+τ)/τ) := by
  unfold wallPsi
  rw [Real.log_div (by positivity : s+τ ≠ 0) (by linarith : s-u+τ ≠ 0)]

theorem wallPsi_zero (s τ : ℝ) : wallPsi s τ 0 = 0 := by
  simp [wallPsi]

theorem wallPsi_at_wall {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ) : wallPsi s τ s = 1 := by
  unfold wallPsi
  rw [Real.log_div (by positivity : s+τ ≠ 0) hτ.ne']
  simp only [sub_self, zero_add]
  have hne := (wallPsi_log_pos hs hτ).ne'
  rw [Real.log_div (by positivity : s+τ ≠ 0) hτ.ne'] at hne
  exact div_self hne

theorem wallPsi_monotoneOn {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ) :
    MonotoneOn (wallPsi s τ) (Icc 0 s) := by
  intro u hu v hv huv
  unfold wallPsi
  apply div_le_div_of_nonneg_right _ (wallPsi_log_pos hs hτ).le
  have hden : 0 < s-v+τ := by linarith [hv.2]
  have hlogs := Real.log_le_log hden (show s-v+τ ≤ s-u+τ by linarith)
  linarith

theorem wallPsi_mem {s τ u : ℝ} (hs : 0 < s) (hτ : 0 < τ) (hu : u ∈ Icc 0 s) :
    wallPsi s τ u ∈ Icc 0 1 := by
  have hmono := wallPsi_monotoneOn hs hτ
  have hlo := hmono ⟨le_rfl, hs.le⟩ hu hu.1
  have hhi := hmono hu ⟨hs.le, le_rfl⟩ hu.2
  rw [wallPsi_zero] at hlo
  rw [wallPsi_at_wall hs hτ] at hhi
  exact ⟨hlo, hhi⟩

theorem wallPsi_hasDerivAt {s τ u : ℝ} (_hs : 0 < s) (hτ : 0 < τ) (hu : u ≤ s) :
    HasDerivAt (wallPsi s τ) (1/((s-u+τ)*Real.log ((s+τ)/τ))) u := by
  have hden : 0 < s-u+τ := by linarith
  have hd := ((hasDerivAt_const u (Real.log (s+τ))).sub
    ((Real.hasDerivAt_log hden.ne').comp u
      (((hasDerivAt_const u s).sub (hasDerivAt_id u)).add_const τ))).div_const
        (Real.log ((s+τ)/τ))
  change HasDerivAt (wallPsi s τ)
    ((0-(s-u+τ)⁻¹*(0-1))/Real.log ((s+τ)/τ)) u at hd
  convert hd using 1
  simp only [zero_sub, mul_neg, mul_one, neg_neg,
    div_eq_mul_inv, mul_inv_rev]
  ring

theorem wallPsi_continuousOn {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ) :
    ContinuousOn (wallPsi s τ) (Icc 0 s) := by
  intro u hu
  exact (wallPsi_hasDerivAt hs hτ hu.2).continuousAt.continuousWithinAt

theorem wallPsi_deriv_lower {s τ u : ℝ} (hs : 0 < s) (hτ : 0 < τ)
    (hgap : τ ≤ s-u) :
    1/(2*(s-u)*Real.log ((s+τ)/τ)) ≤ deriv (wallPsi s τ) u := by
  have hden : 0 < s-u+τ := by linarith
  have hgap0 : 0 < s-u := hτ.trans_le hgap
  have hlog := wallPsi_log_pos hs hτ
  rw [(wallPsi_hasDerivAt hs hτ (by linarith)).deriv]
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_right (by linarith) hlog.le

theorem wallPsi_log_le_nat {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (hlogn : 1 ≤ Real.log (n : ℝ)) :
    Real.log ((s+(n : ℝ)^(-(10 : ℝ)))/(n : ℝ)^(-(10 : ℝ))) ≤
      11*Real.log (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hτpos : 0 < (n : ℝ)^(-(10 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hτone : (n : ℝ)^(-(10 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnR (by norm_num)
  have hsumpos : 0 < s+(n : ℝ)^(-(10 : ℝ)) := by positivity
  have hsumtwo : s+(n : ℝ)^(-(10 : ℝ)) ≤ 2 := by linarith
  have hlogsum := Real.log_le_log hsumpos hsumtwo
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [Real.log_div hsumpos.ne' hτpos.ne', Real.log_rpow hnpos]
  nlinarith

theorem wallPsi_deriv_lower_nat {s u : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hgap : (n : ℝ)^(-(10 : ℝ)) ≤ s-u) :
    1/(22*(s-u)*Real.log (n : ℝ)) ≤
      deriv (wallPsi s ((n : ℝ)^(-(10 : ℝ)))) u := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hτpos : 0 < (n : ℝ)^(-(10 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hgap0 : 0 < s-u := hτpos.trans_le hgap
  have hL := wallPsi_log_pos hs hτpos
  have hLupper := wallPsi_log_le_nat hs hs1 hn hlogn
  apply le_trans _ (wallPsi_deriv_lower hs hτpos hgap)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hLupper (show 0 ≤ 2*(s-u) by positivity)]

def wallLowStrength (T ε : ℝ) : ℝ := min ε (T-ε)/2

theorem wallLowStrength_bounds {T ε : ℝ} (hε : ε ∈ Ioo 0 T) :
    0 ≤ wallLowStrength T ε ∧ wallLowStrength T ε ≤ ε/2 ∧
      wallLowStrength T ε ≤ (T-ε)/2 := by
  unfold wallLowStrength
  have hlo : 0 ≤ min ε (T-ε) := le_min hε.1.le (by linarith [hε.2])
  have hleft := min_le_left ε (T-ε)
  have hright := min_le_right ε (T-ε)
  constructor
  · positivity
  constructor <;> linarith

def wallLowRadius (d rmin ε : ℝ) : ℝ := d^2*rmin/(2*ε)

theorem wall_low_amplitude_bound {T ε θ d rmin : ℝ}
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc 0 1) (hrmin : 0 ≤ rmin) :
    0 ≤ θ*wallLowStrength T ε*wallLowRadius d rmin ε ∧
      θ*wallLowStrength T ε*wallLowRadius d rmin ε ≤ d^2*rmin/4 := by
  have hc := wallLowStrength_bounds hε
  have hradius : 0 ≤ wallLowRadius d rmin ε := by
    unfold wallLowRadius
    exact div_nonneg (mul_nonneg (sq_nonneg d) hrmin) (by linarith [hε.1])
  constructor
  · exact mul_nonneg (mul_nonneg hθ.1 hc.1) hradius
  · have hθc : θ*wallLowStrength T ε ≤ ε/2 := by
      have hh := mul_le_mul_of_nonneg_right hθ.2 hc.1
      nlinarith [hc.2.1]
    have hm := mul_le_mul_of_nonneg_right hθc hradius
    have heq : ε/2*wallLowRadius d rmin ε = d^2*rmin/4 := by
      unfold wallLowRadius
      field_simp [hε.1.ne']
      ring
    rw [heq] at hm
    exact hm

theorem wall_low_matrix_bound {T ε θ : ℝ} (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc 0 1) :
    (T-ε)/2 ≤ T-ε-θ*wallLowStrength T ε := by
  have hc := wallLowStrength_bounds hε
  have hh := mul_le_mul_of_nonneg_right hθ.2 hc.1
  nlinarith [hc.2.2]

theorem wall_low_matrix_fixed_margin {T ε θ : ℝ} (hε : ε ∈ Ioo 0 T)
    (hθ : θ ∈ Icc 0 1) (hsmall : ε ≤ T/4) :
    5*T/8 ≤ T-ε-θ*wallLowStrength T ε := by
  have hc := wallLowStrength_bounds hε
  have hh := mul_le_mul_of_nonneg_right hθ.2 hc.1
  nlinarith [hc.2.1]

def wallBareMatrix (T ε θ s u : ℝ) : ℝ :=
  if u < s then T-ε-θ*wallLowStrength T ε else T

def wallBareField (T ε θ s τ d rmin u : ℝ) : ℝ :=
  if u < s then θ*wallLowStrength T ε*wallLowRadius d rmin ε*wallPsi s τ u else 0

theorem wallComparisonConstraints_nonempty
    {N δ U L E d rmin s : ℝ} (hN : 0 < N) (hU : 0 < U) (hL : 0 < L)
    (hLU : L ≤ U) (hE : 0 < E) (hd : 0 ≤ d) (hq : 2 ≤ N^δ)
    (hrmin : rmin ∈ Icc (0 : ℝ) (1/2)) (hs : s ∈ Icc (0 : ℝ) (1/2)) :
    (inverseIntegralConstraints rmin s (comparisonFloor N δ U)
      (comparisonCap N δ U L E d)).Nonempty := by
  have hne := comparisonConstraints_nonempty hN hU hL hLU hE hd hq hrmin hs
  rw [inverseDifferentialConstraints_eq rmin s (by linarith [hrmin.2]) _ _
    (comparisonFloor_continuousOn (δ := δ) hN hU hrmin.1)
    (comparisonCap_continuous N δ U L E d)
    (comparisonCap_monotoneOn (δ := δ) hN hU.le hL hE hd)
    (comparisonCap_nonneg (δ := δ) hN hU.le hL hE hd (by norm_num))] at hne
  exact hne

theorem wallBareMatrix_theta_bound {T ε θ θ' s u : ℝ}
    (hε : ε ∈ Ioo 0 T) :
    |wallBareMatrix T ε θ s u-wallBareMatrix T ε θ' s u| ≤
      |θ-θ'| *wallLowStrength T ε := by
  have hc := (wallLowStrength_bounds hε).1
  by_cases hu : u < s
  · simp only [wallBareMatrix, ite_eq_left hu]
    have heq : T-ε-θ*wallLowStrength T ε-(T-ε-θ'*wallLowStrength T ε) =
        -(θ-θ')*wallLowStrength T ε := by ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg hc]
  · simp only [wallBareMatrix, ite_eq_right hu, sub_self, abs_zero]
    exact mul_nonneg (abs_nonneg _) hc

theorem wallBareField_theta_bound {T ε θ θ' s τ d rmin u : ℝ}
    (hε : ε ∈ Ioo 0 T) (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    |wallBareField T ε θ s τ d rmin u-wallBareField T ε θ' s τ d rmin u| ≤
      |θ-θ'| *wallLowStrength T ε*wallLowRadius d rmin ε := by
  have hc := (wallLowStrength_bounds hε).1
  have hr : 0 ≤ wallLowRadius d rmin ε := by
    unfold wallLowRadius
    exact div_nonneg (mul_nonneg (sq_nonneg d) hrmin) (by linarith [hε.1])
  by_cases hus : u < s
  · have hp := wallPsi_mem hs hτ ⟨hu.1, hus.le⟩
    simp only [wallBareField, ite_eq_left hus]
    have heq : θ*wallLowStrength T ε*wallLowRadius d rmin ε*wallPsi s τ u-
        θ'*wallLowStrength T ε*wallLowRadius d rmin ε*wallPsi s τ u =
        (θ-θ')*wallLowStrength T ε*wallLowRadius d rmin ε*wallPsi s τ u := by ring
    rw [heq, abs_mul, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hr,
      abs_of_nonneg hp.1]
    exact mul_le_of_le_one_right (by positivity) hp.2
  · simp only [wallBareField, ite_eq_right hus, sub_self, abs_zero]
    positivity

section HighComparison

variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin ≤ 1) (hs1 : s ≤ 1) (hc : 0 < c)
variable (hk : ContinuousOn k (Icc rmin 1))
variable (hkc : ∀ t ∈ Icc rmin 1, c ≤ k t)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

def wallHighCoefficient (α : inverseIntegralConstraints rmin s k M) (u : ℝ) : ℝ :=
  omittedExtension hs1 (constrainedCoefficient hr hc hk hkc hm hM g hg α) u

theorem wallHighCoefficient_on (α : inverseIntegralConstraints rmin s k M)
    {u : ℝ} (hu : u ∈ Icc s 1) :
    wallHighCoefficient hr hs1 hc hk hkc hm hM g hg α u =
      g (constrainedQuantile hr hc hk hkc hm hM α ⟨u, hu⟩) := by
  exact omittedExtension_on hs1 (constrainedCoefficient hr hc hk hkc hm hM g hg α) ⟨u, hu⟩

def wallChangedMatrix (T ε θ : ℝ) (α : inverseIntegralConstraints rmin s k M) (u : ℝ) : ℝ :=
  wallBareMatrix T ε θ s u - wallHighCoefficient hr hs1 hc hk hkc hm hM g hg α u

def wallChangedField (T ε θ τ d : ℝ) (α : inverseIntegralConstraints rmin s k M) (u : ℝ) : ℝ :=
  wallBareField T ε θ s τ d rmin u +
    wallHighCoefficient hr hs1 hc hk hkc hm hM (fun r => g r*r) (hg.mul continuous_id) α u

theorem wallChangedMatrix_below (T ε θ : ℝ) (α : inverseIntegralConstraints rmin s k M)
    {u : ℝ} (hu : u < s) :
    wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u =
      T-ε-θ*wallLowStrength T ε := by
  unfold wallChangedMatrix wallBareMatrix wallHighCoefficient
  rw [ite_eq_left hu, omittedExtension_before hs1 _ hu, sub_zero]

theorem wallChangedMatrix_on (T ε θ : ℝ) (α : inverseIntegralConstraints rmin s k M)
    {u : ℝ} (hu : u ∈ Icc s 1) :
    wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u =
      T-g (constrainedQuantile hr hc hk hkc hm hM α ⟨u, hu⟩) := by
  unfold wallChangedMatrix wallBareMatrix
  rw [ite_eq_right (not_lt.mpr hu.1), wallHighCoefficient_on hr hs1 hc hk hkc hm hM g hg α hu]

theorem wallChangedField_below (T ε θ τ d : ℝ) (α : inverseIntegralConstraints rmin s k M)
    {u : ℝ} (hu : u < s) :
    wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α u =
      θ*wallLowStrength T ε*wallLowRadius d rmin ε*wallPsi s τ u := by
  unfold wallChangedField wallBareField wallHighCoefficient
  rw [ite_eq_left hu, omittedExtension_before hs1 _ hu, add_zero]

theorem wallChangedField_on (T ε θ τ d : ℝ) (α : inverseIntegralConstraints rmin s k M)
    {u : ℝ} (hu : u ∈ Icc s 1) :
    wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α u =
      g (constrainedQuantile hr hc hk hkc hm hM α ⟨u, hu⟩)*
        (constrainedQuantile hr hc hk hkc hm hM α ⟨u, hu⟩) := by
  unfold wallChangedField wallBareField
  rw [ite_eq_right (not_lt.mpr hu.1),
    wallHighCoefficient_on hr hs1 hc hk hkc hm hM (fun r => g r*r)
      (hg.mul continuous_id) α hu, zero_add]

theorem wallChangedMatrix_theta_bound {T ε θ θ' : ℝ}
    (hε : ε ∈ Ioo 0 T) (α : inverseIntegralConstraints rmin s k M) (u : ℝ) :
    |wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u-
      wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ' α u| ≤
      |θ-θ'| *wallLowStrength T ε := by
  simp only [wallChangedMatrix, sub_sub_sub_cancel_right]
  exact wallBareMatrix_theta_bound hε

theorem wallChangedField_theta_bound {T ε θ θ' τ d : ℝ}
    (hε : ε ∈ Ioo 0 T) (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (α : inverseIntegralConstraints rmin s k M) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α u-
      wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ' τ d α u| ≤
      |θ-θ'| *wallLowStrength T ε*wallLowRadius d rmin ε := by
  simp only [wallChangedField, add_sub_add_right_eq_sub]
  exact wallBareField_theta_bound hε hs hτ hrmin hu

theorem wallChangedMatrix_high_lower {T ε θ d : ℝ}
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (α : inverseIntegralConstraints rmin s k M) {u : ℝ} (hu : u ∈ Icc s 1) :
    T-d^2 ≤ wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u := by
  rw [wallChangedMatrix_on hr hs1 hc hk hkc hm hM g hg T ε θ α hu]
  exact sub_le_sub_left
    (hgbound _ (constrainedQuantile hr hc hk hkc hm hM α ⟨u, hu⟩).property) T

theorem wallChangedMatrix_wall_gap {T ε θ d : ℝ}
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc 0 1)
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (α : inverseIntegralConstraints rmin s k M)
    {u v : ℝ} (hu : u < s) (hv : v ∈ Icc s 1) :
    ε-d^2 ≤ wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v-
      wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u := by
  have hh := wallChangedMatrix_high_lower hr hs1 hc hk hkc hm hM g hg (T := T) (ε := ε) (θ := θ) hgbound α hv
  have hθc := mul_nonneg hθ.1 (wallLowStrength_bounds hε).1
  rw [wallChangedMatrix_below hr hs1 hc hk hkc hm hM g hg T ε θ α hu]
  linarith

theorem wall_changed_clocks_admissible {T ε θ τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc 0 1)
    (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (α : inverseIntegralConstraints rmin s k M) :
    MonotoneOn (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α) (Icc 0 1) ∧
    MonotoneOn (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α) (Icc 0 1) ∧
    0 ≤ wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α 0 ∧
    0 ≤ wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α 0 := by
  have hamp := wall_low_amplitude_bound (d := d) hε hθ hrmin
  have hc0 := (wallLowStrength_bounds hε).1
  have hthetaC : 0 ≤ θ*wallLowStrength T ε := mul_nonneg hθ.1 hc0
  have hmatrix : MonotoneOn
      (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α) (Icc 0 1) := by
    intro u hu v hv huv
    by_cases hus : u < s
    · rw [wallChangedMatrix_below hr hs1 hc hk hkc hm hM g hg T ε θ α hus]
      by_cases hvs : v < s
      · rw [wallChangedMatrix_below hr hs1 hc hk hkc hm hM g hg T ε θ α hvs]
      · have hvhi : v ∈ Icc s 1 := ⟨le_of_not_gt hvs, hv.2⟩
        rw [wallChangedMatrix_on hr hs1 hc hk hkc hm hM g hg T ε θ α hvhi]
        have hbound := hgbound _ (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hvhi⟩).property
        linarith
    · have huhi : u ∈ Icc s 1 := ⟨le_of_not_gt hus, hu.2⟩
      have hvhi : v ∈ Icc s 1 := ⟨huhi.1.trans huv, hv.2⟩
      rw [wallChangedMatrix_on hr hs1 hc hk hkc hm hM g hg T ε θ α huhi,
        wallChangedMatrix_on hr hs1 hc hk hkc hm hM g hg T ε θ α hvhi]
      exact sub_le_sub_left (hganti
        (constrainedQuantile hr hc hk hkc hm hM α ⟨u, huhi⟩).property
        (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hvhi⟩).property
        ((inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.monotone huv)) T
  have hfield : MonotoneOn
      (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α) (Icc 0 1) := by
    intro u hu v hv huv
    by_cases hus : u < s
    · rw [wallChangedField_below hr hs1 hc hk hkc hm hM g hg T ε θ τ d α hus]
      by_cases hvs : v < s
      · rw [wallChangedField_below hr hs1 hc hk hkc hm hM g hg T ε θ τ d α hvs]
        exact mul_le_mul_of_nonneg_left
          (wallPsi_monotoneOn hs hτ ⟨hu.1, hus.le⟩ ⟨hv.1, hvs.le⟩ huv) hamp.1
      · have hvhi : v ∈ Icc s 1 := ⟨le_of_not_gt hvs, hv.2⟩
        rw [wallChangedField_on hr hs1 hc hk hkc hm hM g hg T ε θ τ d α hvhi]
        have hpsi := (wallPsi_mem hs hτ ⟨hu.1, hus.le⟩).2
        have hlow := mul_le_mul_of_nonneg_left hpsi hamp.1
        have hhigh := hgrmono ⟨le_rfl, hr⟩
          (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hvhi⟩).property
          (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hvhi⟩).property.1
        dsimp only at hhigh
        rw [hginitial] at hhigh
        have hdmin : 0 ≤ d^2*rmin := mul_nonneg (sq_nonneg d) hrmin
        nlinarith
    · have huhi : u ∈ Icc s 1 := ⟨le_of_not_gt hus, hu.2⟩
      have hvhi : v ∈ Icc s 1 := ⟨huhi.1.trans huv, hv.2⟩
      rw [wallChangedField_on hr hs1 hc hk hkc hm hM g hg T ε θ τ d α huhi,
        wallChangedField_on hr hs1 hc hk hkc hm hM g hg T ε θ τ d α hvhi]
      exact hgrmono
        (constrainedQuantile hr hc hk hkc hm hM α ⟨u, huhi⟩).property
        (constrainedQuantile hr hc hk hkc hm hM α ⟨v, hvhi⟩).property
        ((inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.monotone huv)
  refine ⟨hmatrix, hfield, ?_, ?_⟩
  · rw [wallChangedMatrix_below hr hs1 hc hk hkc hm hM g hg T ε θ α hs]
    have hh := wall_low_matrix_bound hε hθ
    have hgap := hε.2
    linarith
  · rw [wallChangedField_below hr hs1 hc hk hkc hm hM g hg T ε θ τ d α hs,
      wallPsi_zero, mul_zero]

def wallObjective (T ε θ τ d : ℝ) (n : ℕ) (x : OrderedFeatureIndex n → ℝ)
    (α : inverseIntegralConstraints rmin s k M) : ℝ :=
  inverseCompensatedPressure hr hs1 hc hk hkc hm hM g hg n
    (wallBareMatrix T ε θ s) (wallBareField T ε θ s τ d rmin) x α +
      θ*wallLowStrength T ε/4 *
        (∫ u in (0 : ℝ)..s, (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2)

theorem wallObjective_minimum {T ε θ τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc 0 1)
    (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints rmin s k M).Nonempty)
    (n : ℕ) (hn : 0 < n) (x : OrderedFeatureIndex n → ℝ) :
    ∃ α : inverseIntegralConstraints rmin s k M,
      ∀ β : inverseIntegralConstraints rmin s k M,
        wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n x α ≤
          wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n x β := by
  have hadmissible := fun α => wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound α
  obtain ⟨α, hα⟩ := inverseCompensatedPressure_minimum hr hs1 hc hk hkc hm hM g hg
    hMc hne n hn (wallBareMatrix T ε θ s) (wallBareField T ε θ s τ d rmin)
    (fun α => (hadmissible α).1) (fun α => (hadmissible α).2.1)
    (fun α => (hadmissible α).2.2.1) (fun α => (hadmissible α).2.2.2) x
  refine ⟨α, fun β => ?_⟩
  unfold wallObjective
  exact add_le_add (hα β) le_rfl

end HighComparison

end OAI.SKFluctuations.LaplaceWindowFormalization
