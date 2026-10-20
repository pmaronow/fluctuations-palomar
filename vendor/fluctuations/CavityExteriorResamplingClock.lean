module

public import CavityExteriorResampling
public import CavityProjectionErrorPrefixTransport

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

theorem eventually_physical_exterior_resampling_polynomial (k d : ℕ) (B C : ℝ)
    {kappa delta : ℝ} (hgap : 2*delta<kappa) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (pre tail : List (GaussianStep (FeatureIndex n))) (c D₀ xs H v : ℝ),
      0<D₀ → 0<xs → 0≤H → OrderedSteps c (pre++tail) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
      (a D : Fin cs.length → ℝ),
      lastLayerCut cs pre.length=(pre++tail).length+1 →
      (∀ j : Fin cs.length, cutPredecessor cs pre.length j≤(cs.get j).2 ∧
        (cs.get j).2≤(pre++tail).length+1) →
      (∀ j, 0<a j ∧ D₀≤D j ∧ D j≤B ∧
        PhysicalProjectionClock n (pre++tail) 0 (cutPredecessor cs pre.length j)
          (cs.get j).2 (a j) (D j)) →
      (∀ i j, i≤j.succ → xs+physicalCutMass c (pre++tail)
        (overlapComponentEnd cs pre.length i)≤H*(a j)^2) →
      ((physicalOverlapResidualPairs cs).card:ℝ)^2 *
        (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4 *
          (physicalRawRatio n (k+1) (pre++tail) c xs μ x hx)^2*H/((n:ℝ)*D₀))≤
        C*(Real.log (n:ℝ))^d*(n:ℝ)^(-kappa)*v^2 →
    physicalExteriorResamplingMoment n (k+1) (pre++tail) μ x hx pre.length≤
      (2*(n:ℝ)^(-delta)*v)^(2*(k+1)) := by
  filter_upwards [eventually_physical_projection_error_polynomial k d B C hgap] with n hn
  intro P _ pre tail c D₀ xs H v hD₀ hxs hH hs μ _ x hx cs a D
    hlast hends hclock hscale hbase
  have hm := hn P (pre++tail) c D₀ xs H v hD₀ hxs hH hs μ x hx cs 0 pre.length a D
    (by simp only [List.length_append]; omega) hlast hends hclock hscale hbase
  apply (physical_exterior_resampling_moment_le n (k+1) (Nat.succ_pos k)
    pre tail hs μ x hx).trans
  calc
    _≤(2:ℝ)^(2*(k+1))*(((n:ℝ)^(-delta)*v)^(2*(k+1))) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _=_ := by rw [←mul_pow]; congr 1; ring

theorem resampling_coefficient_from_primitives (dc dq : ℕ)
    {N L J P Q H D₀ A Cq H₀ c W v : ℝ}
    (hN : 0<N) (hL : 0<L) (hD₀ : 0<D₀) (hc : 0<c)
    (hW : 0<W) (hv : 0<v) (hA : 0≤A) (hCq : 0≤Cq) (hH₀ : 0≤H₀) (hH : 0≤H)
    (hcount : J^2≤A*L^dc) (hraw : Q^2≤Cq*L^dq) (hanchor : H≤H₀/v)
    (hclock : c*W^3/L≤D₀) :
    J^2*(4*P^2*L^4*Q^2*H/(N*D₀))≤
      (4*P^2*A*Cq*H₀/c)*L^(dc+dq+5)/(N*W^3*v) := by
  have hnum : J^2*(4*P^2*L^4*Q^2*H)≤
      (A*L^dc)*(4*P^2*L^4*(Cq*L^dq)*(H₀/v)) := by
    apply mul_le_mul hcount _ (by positivity) (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hraw (by positivity)) hanchor hH
      (by positivity)
  calc
    _=(J^2*(4*P^2*L^4*Q^2*H))/(N*D₀) := by ring
    _≤((A*L^dc)*(4*P^2*L^4*(Cq*L^dq)*(H₀/v)))/(N*(c*W^3/L)) := by
      apply div_le_div₀ (by positivity) hnum (by positivity)
      exact mul_le_mul_of_nonneg_left hclock hN.le
    _=_ := by
      rw [pow_add,pow_add]
      field_simp

def savedExteriorScale (x W v : ℝ) : ℝ := x^3/Real.sqrt (W^3*v)

theorem savedExteriorScale_sq {x W v : ℝ} (hW : 0<W) (hv : 0<v) :
    savedExteriorScale x W v ^2=x^6/(W^3*v) := by
  unfold savedExteriorScale
  rw [div_pow,Real.sq_sqrt (by positivity)]
  congr 1
  ring

theorem resampling_coefficient_scale {N C L x W v : ℝ} (d : ℕ)
    (hN : 0<N) (hx : 0<x) (hW : 0<W) (hv : 0<v) :
    C*L^d/(N*W^3*v)=C*L^d/(N*x^6)*savedExteriorScale x W v ^2 := by
  rw [savedExteriorScale_sq hW hv]
  field_simp

theorem reciprocal_sixth_small_scale {N x m : ℝ}
    (hN : 0<N) (hx : 0<x) (hlow : N^(-(1:ℝ)/6+m)≤x) :
    1/(N*x^6)≤N^(-6*m) := by
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hlow 6
  rw [←Real.rpow_mul_natCast hN.le] at hp
  apply (div_le_iff₀ (by positivity : 0<N*x^6)).2
  have he : N^(-6*m)*(N*N^((-(1:ℝ)/6+m)*(6:ℕ)))=1 := by
    calc
      _=N^(-6*m)*(N^(1:ℝ)*N^((-(1:ℝ)/6+m)*(6:ℕ))) := by simp
      _=N^(-6*m+(1+(-(1:ℝ)/6+m)*(6:ℕ))) := by
        rw [←Real.rpow_add hN,←Real.rpow_add hN]
      _=1 := by convert Real.rpow_zero N using 1 <;> ring
  calc
    1=N^(-6*m)*(N*N^((-(1:ℝ)/6+m)*(6:ℕ))) := he.symm
    _≤N^(-6*m)*(N*x^6) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hN.le)
        (Real.rpow_nonneg hN.le _)

theorem eventually_physical_exterior_resampling_from_primitives
    (k dc dq : ℕ) (B A Cq H₀ c₀ : ℝ)
    (hA : 0≤A) (hCq : 0≤Cq) (hH₀ : 0≤H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (pre tail : List (GaussianStep (FeatureIndex n))) (c D₀ xs H r W v : ℝ),
      0<D₀ → 0<xs → 0≤H → 0<r → 0<W → 0<v →
      (n:ℝ)^(-(1:ℝ)/6+m)≤r → OrderedSteps c (pre++tail) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
      (a D : Fin cs.length → ℝ),
      lastLayerCut cs pre.length=(pre++tail).length+1 →
      (∀ j : Fin cs.length, cutPredecessor cs pre.length j≤(cs.get j).2 ∧
        (cs.get j).2≤(pre++tail).length+1) →
      (∀ j, 0<a j ∧ D₀≤D j ∧ D j≤B ∧
        PhysicalProjectionClock n (pre++tail) 0 (cutPredecessor cs pre.length j)
          (cs.get j).2 (a j) (D j)) →
      (∀ i j, i≤j.succ → xs+physicalCutMass c (pre++tail)
        (overlapComponentEnd cs pre.length i)≤H*(a j)^2) →
      ((physicalOverlapResidualPairs cs).card:ℝ)^2≤A*(Real.log (n:ℝ))^dc →
      (physicalRawRatio n (k+1) (pre++tail) c xs μ x hx)^2≤Cq*(Real.log (n:ℝ))^dq →
      H≤H₀/v → c₀*W^3/Real.log (n:ℝ)≤D₀ →
    physicalExteriorResamplingMoment n (k+1) (pre++tail) μ x hx pre.length≤
      (2*(n:ℝ)^(-delta)*savedExteriorScale r W v)^(2*(k+1)) := by
  let C := 4*(projectionLpConstant k)^2*A*Cq*H₀/c₀
  filter_upwards [eventually_physical_exterior_resampling_polynomial k (dc+dq+5) B C hgap,
    eventually_gt_atTop (1:ℕ)] with n hn hnpos
  intro P _ pre tail c D₀ xs H r W v hD₀ hxs hH hr hW hv hlow hs μ _ x hx cs a D
    hlast hends hclock hscale hcount hraw hanchor hduration
  have hN : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hnpos)
  apply hn P pre tail c D₀ xs H (savedExteriorScale r W v) hD₀ hxs hH hs
    μ x hx cs a D hlast hends hclock hscale
  have hf := resampling_coefficient_from_primitives dc dq (P:=projectionLpConstant k) hN hL hD₀ hc₀ hW hv
    hA hCq hH₀ hH hcount hraw hanchor hduration
  apply hf.trans
  rw [resampling_coefficient_scale (dc+dq+5) hN hr hW hv]
  have hh := reciprocal_sixth_small_scale hN hr hlow
  have hC : 0≤C*(Real.log (n:ℝ))^(dc+dq+5) := by dsimp [C]; positivity
  have Hsave := mul_le_mul_of_nonneg_left hh hC
  simpa only [C,div_eq_mul_inv,mul_assoc,one_mul,neg_mul] using
    mul_le_mul_of_nonneg_right Hsave (sq_nonneg (savedExteriorScale r W v))

end OAI.SKFluctuations
