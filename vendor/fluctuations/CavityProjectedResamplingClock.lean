module

public import CavityRootProjectedResampling

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def savedProjectedScale (x W v : ℝ) : ℝ := x^3/(W*v)

theorem savedProjectedScale_sq (x W v : ℝ) :
    savedProjectedScale x W v ^2=x^6/(W^2*v^2) := by
  unfold savedProjectedScale
  rw [div_pow,mul_pow]
  congr 1
  ring

theorem projected_coefficient_from_primitives (dq : ℕ)
    {N L P Q H D₀ Cq H₀ c W v : ℝ}
    (hN : 0<N) (hL : 0<L) (hD₀ : 0<D₀) (hc : 0<c)
    (hW : 0<W) (hv : 0<v) (hCq : 0≤Cq) (hH₀ : 0≤H₀) (hH : 0≤H)
    (hraw : Q^2≤Cq*L^dq) (hanchor : H≤H₀*W/v^2) (hclock : c*W^3/L≤D₀) :
    4*P^2*L^4*Q^2*H/(N*D₀)≤
      (4*P^2*Cq*H₀/c)*L^(dq+5)/(N*W^2*v^2) := by
  have ha : H≤(H₀*W/v)/v := by convert hanchor using 1 <;> field_simp
  have Hbound := resampling_coefficient_from_primitives 0 dq (J:=1) (A:=1) (P:=P)
    hN hL hD₀ hc hW hv (by norm_num) hCq (by positivity) hH
    (by simp) hraw ha hclock
  simp only [one_pow,one_mul,zero_add] at Hbound
  apply Hbound.trans_eq
  field_simp

theorem projected_coefficient_scale {N C L x W v : ℝ} (d : ℕ)
    (hN : 0<N) (hx : 0<x) (hW : 0<W) (hv : 0<v) :
    C*L^d/(N*W^2*v^2)=C*L^d/(N*x^6)*savedProjectedScale x W v ^2 := by
  rw [savedProjectedScale_sq]
  field_simp

theorem eventually_physical_root_projected_from_primitives
    (k dq : ℕ) (B Cq H₀ c₀ : ℝ) (hCq : 0≤Cq) (hH₀ : 0≤H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (a c D D₀ xs H r W v : ℝ),
      0<a → 0<D₀ → D₀≤D → D≤B → 0<xs → 0≤H → 0<r → 0<W → 0<v →
      (n:ℝ)^(-(1:ℝ)/6+m)≤r → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cut : ℕ),
      PhysicalProjectionClock n steps 0 cut (steps.length+1) a D →
      xs+physicalCutMass c steps 0≤H*a^2 →
      (physicalRawRatio n (k+1) steps c xs μ x hx)^2≤Cq*(Real.log (n:ℝ))^dq →
      H≤H₀*W/v^2 → c₀*W^3/Real.log (n:ℝ)≤D₀ →
    physicalRootProjectedResamplingMoment n (k+1) steps μ x hx cut≤
      (2*(n:ℝ)^(-delta)*savedProjectedScale r W v)^(2*(k+1)) := by
  let C := 4*(projectionLpConstant k)^2*Cq*H₀/c₀
  filter_upwards [eventually_physical_root_projected_clock_bound k B,
    eventually_log_polynomial_saving (dq+5) hgap C,
    eventually_gt_atTop (1:ℕ)] with n hn hlog hnpos
  intro P _ steps a c D D₀ xs H r W v ha hD₀ hD hDB hxs hH hr hW hv hlow hs
    μ _ x hx cut hc hscale hraw hanchor hduration
  have hN : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hnpos)
  have hm := hn P steps a c D D₀ xs H ha hD₀ hD hDB hxs hH hs μ x hx cut hc hscale
  have hf := projected_coefficient_from_primitives dq (P:=projectionLpConstant k)
    hN hL hD₀ hc₀ hW hv hCq hH₀ hH hraw hanchor hduration
  have hsmall := reciprocal_sixth_small_scale hN hr hlow
  have hco : 0≤C*(Real.log (n:ℝ))^(dq+5) := by dsimp [C]; positivity
  have hbase : 4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
      (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀)≤
      (n:ℝ)^(-2*delta)*savedProjectedScale r W v ^2 := by
    apply hf.trans
    rw [projected_coefficient_scale (dq+5) hN hr hW hv]
    have Hsave := mul_le_mul_of_nonneg_left hsmall hco
    have Hsave' : C*(Real.log (n:ℝ))^(dq+5)/((n:ℝ)*r^6)≤
        C*(Real.log (n:ℝ))^(dq+5)*(n:ℝ)^(-(6*m)) := by
      simpa only [div_eq_mul_inv,mul_assoc,one_mul,neg_mul] using Hsave
    have Hfinal := Hsave'.trans hlog
    exact mul_le_mul_of_nonneg_right Hfinal (sq_nonneg (savedProjectedScale r W v))
  have he : (n:ℝ)^(-2*delta)*savedProjectedScale r W v ^2=
      ((n:ℝ)^(-delta)*savedProjectedScale r W v)^2 := by
    rw [mul_pow,←Real.rpow_mul_natCast hN.le]
    congr 1
    ring
  rw [he] at hbase
  apply hm.trans
  calc
    _≤(2:ℝ)^(2*(k+1))*(((n:ℝ)^(-delta)*savedProjectedScale r W v)^2)^(k+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)
    _=_ := by rw [←pow_mul,←mul_pow]; congr 1; ring

end OAI.SKFluctuations
