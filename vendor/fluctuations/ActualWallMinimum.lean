module

public import WallClockGeometry
public import WallEnvelope

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def wallLipschitzConstant (T ε d rmin : ℝ) : ℝ :=
  wallLowStrength T ε *
    (1/4 + wallLowRadius d rmin ε/2 + (wallLowRadius d rmin ε)^2/4)

theorem wallLipschitzConstant_nonneg {T ε d rmin : ℝ}
    (hε : ε ∈ Ioo 0 T) (hrmin : 0 ≤ rmin) :
    0 ≤ wallLipschitzConstant T ε d rmin := by
  have hc := (wallLowStrength_bounds hε).1
  have hr : 0 ≤ wallLowRadius d rmin ε :=
    div_nonneg (mul_nonneg (sq_nonneg d) hrmin) (by linarith [hε.1])
  unfold wallLipschitzConstant
  positivity

theorem wallLowPenalty_abs_bound {s τ d rmin ε : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hτ : 0 < τ) :
    |∫ u in (0 : ℝ)..s, (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2| ≤
      (wallLowRadius d rmin ε)^2 := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := s) (C := (wallLowRadius d rmin ε)^2)
    (f := fun u => (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) (fun u hu => by
      have hu' : u ∈ Icc (0 : ℝ) s := by
        have hu' : u ∈ Ioc (0 : ℝ) s := by simpa [uIoc_of_le hs.le] using hu
        exact ⟨hu'.1.le, hu'.2⟩
      have hp := wallPsi_mem hs hτ hu'
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      apply mul_le_of_le_one_right (sq_nonneg _)
      nlinarith [hp.1, hp.2])
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hs] at hh
  exact hh.trans (by nlinarith [sq_nonneg (wallLowRadius d rmin ε)])

section
variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin ≤ 1) (hs1 : s ≤ 1) (hc : 0 < c)
variable (hk : ContinuousOn k (Icc rmin 1))
variable (hkc : ∀ t ∈ Icc rmin 1, c ≤ k t)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

theorem wallObjective_eq (T ε θ τ d : ℝ) (n : ℕ) (x : OrderedFeatureIndex n → ℝ)
    (α : inverseIntegralConstraints rmin s k M) :
    wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n x α =
      realOrderedSKPathPressure n
        (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α)
        (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α) x +
      (1/4 : ℝ) * (∫ u in (0 : ℝ)..1,
        wallHighCoefficient hr hs1 hc hk hkc hm hM
          (fun r => g r*r^2) (hg.mul (continuous_id.pow 2)) α u) +
      θ*wallLowStrength T ε/4 *
        (∫ u in (0 : ℝ)..s, (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) := rfl

theorem wallObjective_lipschitzOn {T ε τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (n : ℕ) (hn : 0 < n) (x : OrderedFeatureIndex n → ℝ)
    (α : inverseIntegralConstraints rmin s k M) :
    LipschitzOnWith (Real.toNNReal (wallLipschitzConstant T ε d rmin))
      (fun θ => wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n x α)
      (Icc (0 : ℝ) 1) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro θ hθ θ' hθ'
  have ha := wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound α
  have hb := wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hθ' hdepsilon hginitial hganti hgrmono hgbound α
  have hp := realOrderedSKPathPressure_uniform_comparison n hn
    (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α)
    (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α)
    (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ' α)
    (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ' τ d α)
    ha.1 ha.2.1 hb.1 hb.2.1 ha.2.2.1 ha.2.2.2 hb.2.2.1 hb.2.2.2
    (fun u _ => wallChangedMatrix_theta_bound hr hs1 hc hk hkc hm hM g hg hε α u)
    (fun u hu => wallChangedField_theta_bound hr hs1 hc hk hkc hm hM g hg
      hε hs hτ hrmin α hu) x
  have hi := wallLowPenalty_abs_bound (d := d) (rmin := rmin) (ε := ε) hs hs1 hτ
  have hc0 := (wallLowStrength_bounds hε).1
  rw [Real.dist_eq, Real.dist_eq,
    Real.coe_toNNReal _ (wallLipschitzConstant_nonneg (d := d) hε hrmin)]
  rw [wallObjective_eq hr hs1 hc hk hkc hm hM g hg,
    wallObjective_eq hr hs1 hc hk hkc hm hM g hg]
  have heq (a b H I : ℝ) :
      (a+H+θ*wallLowStrength T ε/4*I)-(b+H+θ'*wallLowStrength T ε/4*I) =
      (a-b)+(θ-θ')*wallLowStrength T ε/4*I := by ring
  rw [heq]
  calc
    |(_ - _) + _| ≤ |_ - _| + |(θ-θ')*wallLowStrength T ε/4*
      (∫ u in (0 : ℝ)..s, (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2)| := abs_add_le _ _
    _ ≤ |θ-θ'| *wallLowStrength T ε/4 +
          |θ-θ'| *wallLowStrength T ε*wallLowRadius d rmin ε/2 +
          |θ-θ'| *wallLowStrength T ε/4*(wallLowRadius d rmin ε)^2 := by
      rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hc0, abs_of_pos (by norm_num : (0:ℝ)<4)]
      exact add_le_add hp (mul_le_mul_of_nonneg_left hi (by positivity))
    _ = wallLipschitzConstant T ε d rmin * |θ-θ'| := by
      unfold wallLipschitzConstant
      ring

def wallMinimumValue (T ε τ d : ℝ) (n : ℕ) (x : OrderedFeatureIndex n → ℝ) (θ : ℝ) : ℝ :=
  sInf (Set.range (wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n x))

theorem wallMinimumValue_minimum {T ε θ τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints rmin s k M).Nonempty)
    (n : ℕ) (hn : 0 < n) (x : OrderedFeatureIndex n → ℝ) :
    ∃ α : inverseIntegralConstraints rmin s k M,
      wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n x α =
        wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n x θ ∧
      ∀ β : inverseIntegralConstraints rmin s k M,
        wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n x θ ≤
          wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n x β := by
  obtain ⟨α, hα⟩ := wallObjective_minimum hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound hMc hne n hn x
  have heq : wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n x θ =
      wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n x α := by
    apply IsLeast.csInf_eq
    refine ⟨Set.mem_range_self α, ?_⟩
    rintro y ⟨β, rfl⟩
    exact hα β
  exact ⟨α, heq.symm, fun β => heq.symm ▸ hα β⟩

theorem wallMinimumValue_lipschitzOn {T ε τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints rmin s k M).Nonempty)
    (n : ℕ) (hn : 0 < n) (x : OrderedFeatureIndex n → ℝ) :
    LipschitzOnWith (Real.toNNReal (wallLipschitzConstant T ε d rmin))
      (wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n x) (Icc (0 : ℝ) 1) := by
  apply WallSweep.minimum_lipschitzOn
    (fun θ α => wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n x α)
  · intro θ hθ
    exact wallMinimumValue_minimum hr hs1 hc hk hkc hm hM g hg
      hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound hMc hne n hn x
  · intro α
    exact wallObjective_lipschitzOn hr hs1 hc hk hkc hm hM g hg
      hs hτ hrmin hε hdepsilon hginitial hganti hgrmono hgbound n hn x α

end

end OAI.SKFluctuations.LaplaceWindowFormalization
