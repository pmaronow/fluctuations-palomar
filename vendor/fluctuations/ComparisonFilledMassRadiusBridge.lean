module

public import ComparisonSelectedCutTrace
public import RadiusCellEnergyDensity
public import PhysicalComparisonSampledCell

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal Topology

theorem radiusCellEnergyDensity_deriv_integral {A : ℝ≥0}
    (f R : ℝ → ℝ) (hf : LipschitzOnWith A f (Icc (0:ℝ) 1))
    (hR : Monotone R) (hRb : ∀u∈Icc (0:ℝ) 1,R u∈Icc (0:ℝ) 1)
    (hinv : ∀u∈Icc (0:ℝ) 1,f (R u)=u)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) (as : List PositiveMass)
    (ho : MassOrdered u as) (C : ℕ → ℝ) :
    Integrable (fun r=>deriv f r*radiusCellEnergyDensity R u as C r) ∧
    (∫r,deriv f r*radiusCellEnergyDensity R u as C r)=massCellSum as u C := by
  induction as generalizing u C with
  | nil=>simp [radiusCellEnergyDensity,massCellSum]
  | cons a as ih=>
    have ha : a.val∈Icc (0:ℝ) 1 := massOrdered_bounds ho.2.2
    have hRua : R u ≤ R a.val := hR ho.2.1
    have hsub : uIcc (R u) (R a.val)⊆Icc (0:ℝ) 1 := by
      rw [uIcc_of_le hRua]
      exact Icc_subset_Icc (hRb u hu).1 (hRb a.val ha).2
    have hac : AbsolutelyContinuousOnInterval f (R u) (R a.val) :=
      (hf.mono hsub).absolutelyContinuousOnInterval
    have hI : IntegrableOn (deriv f) (Ioc (R u) (R a.val)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hRua).mp hac.intervalIntegrable_deriv
    have heq : (fun r=>deriv f r*(Ioc (R u) (R a.val)).indicator (fun _=>C 0) r)=
        (Ioc (R u) (R a.val)).indicator (fun r=>deriv f r*C 0) := by
      funext r
      by_cases hr:r∈Ioc (R u) (R a.val) <;> simp [hr]
    have hhead : Integrable (fun r=>deriv f r*(Ioc (R u) (R a.val)).indicator (fun _=>C 0) r) := by
      rw [heq]
      apply (integrable_indicator_iff measurableSet_Ioc).mpr
      exact hI.mul_const (C 0)
    have hheadEq : (∫r,deriv f r*(Ioc (R u) (R a.val)).indicator (fun _=>C 0) r)=
        (a.val-u)*C 0 := by
      rw [heq,integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le hRua,
        intervalIntegral.integral_mul_const,hac.integral_deriv_eq_sub,hinv a.val ha,hinv u hu]
    have htail := ih ha ho.2.2 (fun j=>C (j+1))
    have he (r : ℝ) : deriv f r*radiusCellEnergyDensity R u (a::as) C r=
        deriv f r*(Ioc (R u) (R a.val)).indicator (fun _=>C 0) r+
          deriv f r*radiusCellEnergyDensity R a.val as (fun j=>C (j+1)) r := by
      simp only [radiusCellEnergyDensity,mul_add]
    refine ⟨by simp_rw [he]; exact hhead.add htail.1,?_⟩
    simp_rw [he]
    rw [integral_add hhead htail.1,hheadEq,htail.2]
    rfl

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_filled_coefficients_mass_radius_eq
    (α : inverseIntegralConstraints 0 0 k M) {u : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (as : List PositiveMass) (ho : MassOrdered u as) (C : ℕ → ℝ) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    (∫r,deriv α.val.val r*radiusCellEnergyDensity R u as C r)=massCellSum as u C := by
  exact (radiusCellEnergyDensity_deriv_integral α.val.val _
    (inverseIntegralConstraints_lipschitz hm hM α.property)
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α)
    (fun v _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α v)
    (fun v hv=>comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hv) hu as ho C).2

theorem comparison_actual_filled_mass_radius_eq (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q0 : FeatureIndex (n+1) → ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (offset : ℕ)
    (α : inverseIntegralConstraints 0 0 k M) {u : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (as : List PositiveMass) (ho : MassOrdered u as) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    (∫r,deriv α.val.val r*physicalRadiusCellEnergyDensity n d e q0 pre tail ha offset R u as r)=
      massCellSum as u (fun j=>physicalRootedCapCellTrace n d e q0 pre tail ha (offset+j)) := by
  exact comparison_filled_coefficients_mass_radius_eq hc hk hkc hm hM α hu as ho _

end
end OAI.SKFluctuations.LaplaceWindowFormalization
