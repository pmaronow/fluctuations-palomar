module

public import ComparisonSignedCavityStarProjection
public import ComparisonNativeStarCapSaving

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy LaplaceWindowFormalization

theorem physical_projection_base_of_native_geometry (k dq : ℕ)
    {N ell count Q H D M g theta v L Cq H₀ : ℝ}
    (hN : 0<N) (hell : 0<ell) (hcount0 : 0≤count)
    (hL : 0≤L) (hCq : 0≤Cq) (hH₀ : 0≤H₀) (hH : 0≤H)
    (hM : 0<M) (hg : 0<g) (htheta : 0<theta) (hv : 0<v)
    (hcount : count≤L*ell) (hQ : Q^2≤Cq*ell^dq) (hanchor : H≤H₀/v)
    (hclock : g*theta*v/(3*M*ell)≤D) :
    count^4*(4*(projectionLpConstant k)^2*ell^4*Q^2*H/(N*D)) ≤
      (12*L^4*(projectionLpConstant k)^2*Cq*H₀)*ell^(dq+9)*
        (M/(N*g*v^4))/theta*v^2 := by
  have hD : 0<D := lt_of_lt_of_le (by positivity) hclock
  have hc4 := pow_le_pow_left₀ hcount0 hcount 4
  have hQH := mul_le_mul hQ hanchor hH (by positivity : 0≤Cq*ell^dq)
  have hnum : count^4*(4*(projectionLpConstant k)^2*ell^4*Q^2*H) ≤
      (L*ell)^4*(4*(projectionLpConstant k)^2*ell^4*(Cq*ell^dq)*(H₀/v)) := by
    have hmid := mul_le_mul_of_nonneg_left hQH
      (by positivity : 0≤4*(projectionLpConstant k)^2*ell^4)
    have hmid' : 4*(projectionLpConstant k)^2*ell^4*Q^2*H ≤
        4*(projectionLpConstant k)^2*ell^4*(Cq*ell^dq)*(H₀/v) := by
      simpa only [mul_assoc] using hmid
    exact mul_le_mul hc4 hmid' (by positivity) (by positivity)
  have hden : N*(g*theta*v/(3*M*ell))≤N*D := mul_le_mul_of_nonneg_left hclock hN.le
  calc
    _ = (count^4*(4*(projectionLpConstant k)^2*ell^4*Q^2*H))/(N*D) := by ring
    _ ≤ ((L*ell)^4*(4*(projectionLpConstant k)^2*ell^4*(Cq*ell^dq)*(H₀/v)))/(N*D) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((L*ell)^4*(4*(projectionLpConstant k)^2*ell^4*(Cq*ell^dq)*(H₀/v)))/
        (N*(g*theta*v/(3*M*ell))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      rw [pow_add]
      field_simp
      <;> ring

theorem eventually_comparison_actual_star_projection (k dq : ℕ)
    (Bclock : ℝ) {m deltaCap gamma c₁ saving Cprof Lcount Cq H₀ : ℝ}
    (hm : 0 < m) (hdeltaCap : 0≤deltaCap) (hgamma : 0 < gamma) (hCprof : 0≤Cprof)
    (hLcount : 0≤Lcount) (hCq : 0≤Cq) (hH₀ : 0≤H₀)
    (hmargin : 2*saving<3*m-deltaCap-c₁) :
    ∀ᶠ n : ℕ in atTop,∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs H v theta d lam E x : ℝ),
      0<D₀ → 0<xs → 0≤H → OrderedSteps c steps →
      0<d → 0<lam → lam≤d^2 → 0<E →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d≤E → E≤d^2/Real.sqrt n →
      0<x → (n:ℝ)^deltaCap*Real.sqrt n*E/Real.sqrt lam≤x → x≤v →
      (n:ℝ)^(-c₁)≤theta →
      laplaceComparisonStrength d lam v*theta*v/
        (3*comparisonCap n deltaCap (comparisonSmallMass n E)
          (comparisonConstraintLength n E d) E d (Cprof*v)*Real.log (n:ℝ))≤D₀ →
      H≤H₀/v →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ] (z : P→FeatureIndex n→ℝ) (hz : Measurable z)
      (fork t u : ℕ) (cs : List (ℝ×ℕ)) (a D : Fin cs.length→ℝ) (a₀ Dshort : ℝ),
      t ≤ u → u ≤ steps.length+1 → lastLayerCut cs u=steps.length+1 →
      0<a₀ → D₀≤Dshort → Dshort≤Bclock →
      PhysicalProjectionClock n steps fork t u a₀ Dshort →
      xs+physicalCutMass c steps u≤H*a₀^2 →
      (∀j,cutPredecessor cs u j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) →
      (∀j,0<a j ∧ D₀≤D j ∧ D j≤Bclock ∧
        PhysicalProjectionClock n steps fork (cutPredecessor cs u j) (cs.get j).2 (a j) (D j)) →
      (∀i j,i≤j.succ → xs+physicalCutMass c steps (overlapComponentEnd cs u i)≤H*(a j)^2) →
      ((cs.length+2:ℕ):ℝ)≤Lcount*Real.log (n:ℝ) →
      (physicalRawRatio n (k+1) steps c xs μ z hz)^2≤Cq*(Real.log (n:ℝ))^dq →
      physicalOverlapProjectionErrorMoment n (k+1) steps μ z hz fork t≤
        ((n:ℝ)^(-saving)*v)^(2*(k+1)) := by
  let R : ℝ := (2*(Cprof+1)+(Cprof+1)^2)/gamma^3
  let C : ℝ := 12*Lcount^4*(projectionLpConstant k)^2*Cq*H₀*R
  filter_upwards [eventually_comparison_star_actual_cap_saving hm hdeltaCap hgamma hCprof,
    eventually_physical_projection_error_short_and_later k (dq+9) Bclock C hmargin,
    eventually_gt_atTop (1:ℕ)] with n hcap hproj hn
  intro P _ steps c D₀ xs H v theta d lam E x hD₀ hxs hH hs hd hlam hld hE hlo hup
    hx hrange hxv htheta hduration hanchor μ _ z hz fork t u cs a D a₀ Dshort
    htu hu hlast ha₀ hDshort hDB hshort hfirst hends hclock hscale hcount hQ
  have hN1 : 1<(n:ℝ) := by exact_mod_cast hn
  have hN : 0<(n:ℝ) := zero_lt_one.trans hN1
  have hv : 0<v := hx.trans_le hxv
  have hg : 0<laplaceComparisonStrength d lam v := laplaceComparisonStrength_pos d hlam v
  have htheta0 : 0<theta := (Real.rpow_pos_of_pos hN (-c₁)).trans_le htheta
  have hlog0 : 0<Real.log (n:ℝ) := Real.log_pos hN1
  have hU : 0<comparisonSmallMass n E := by unfold comparisonSmallMass; positivity
  have hLc : 0<comparisonConstraintLength n E d := comparisonConstraintLength_pos hN hE hd
  have hM : 0<comparisonCap n deltaCap (comparisonSmallMass n E)
      (comparisonConstraintLength n E d) E d (Cprof*v) := by
    unfold comparisonCap
    positivity
  have hbase := physical_projection_base_of_native_geometry k dq hN hlog0
    (Nat.cast_nonneg (cs.length+2)) hLcount hCq hH₀ hH hM hg htheta0 hv
    hcount hQ hanchor hduration
  have hactual := hcap d lam E x v hd hlam hld hE hlo hup hx hrange hxv
  have hR : 0≤R := by dsimp [R]; positivity
  have hratio : comparisonCap n deltaCap (comparisonSmallMass n E)
      (comparisonConstraintLength n E d) E d (Cprof*v)/
      ((n:ℝ)*laplaceComparisonStrength d lam v*v^4)/theta ≤
        R*(n:ℝ)^(-(3*m-deltaCap-c₁)) := by
    have h1 := div_le_div_of_nonneg_right hactual htheta0.le
    have h2 := div_le_div_of_nonneg_left
      (by positivity : 0≤R*(n:ℝ)^(-(3*m-deltaCap)))
      (Real.rpow_pos_of_pos hN (-c₁)) htheta
    apply h1.trans (h2.trans_eq _)
    rw [mul_div_assoc,←Real.rpow_sub hN]
    congr 1
    ring
  have hbudget : ((cs.length+2:ℕ):ℝ)^4*
      (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
        (physicalRawRatio n (k+1) steps c xs μ z hz)^2*H/((n:ℝ)*D₀)) ≤
      C*(Real.log (n:ℝ))^(dq+9)*(n:ℝ)^(-(3*m-deltaCap-c₁))*v^2 := by
    apply hbase.trans
    have H := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio
        (by positivity : 0≤(12*Lcount^4*(projectionLpConstant k)^2*Cq*H₀)*(Real.log (n:ℝ))^(dq+9)))
      (sq_nonneg v)
    simpa only [C,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using H
  exact hproj P steps c D₀ xs H v hD₀ hxs hH hs μ z hz fork t u cs a D a₀ Dshort
    htu hu hlast ha₀ hDshort hDB hshort hfirst hends hclock hscale hbudget

end OAI.SKFluctuations
