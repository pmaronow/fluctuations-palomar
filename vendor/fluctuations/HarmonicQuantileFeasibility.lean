module

public import ForwardQuantileFeasibility
public import ConstrainedForwardGeometry
public import HarmonicBarrierInterpolation
public import PositiveReciprocalLipschitz

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

private theorem real_const_mul_lipschitzOn {C : ℝ≥0} {s : Set ℝ} {f : ℝ→ℝ}
    (hf : LipschitzOnWith C f s) (t : ℝ) :
    LipschitzOnWith (‖t‖₊*C) (fun u=>t*f u) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hh := mul_le_mul_of_nonneg_left (hf.dist_le_mul x hx y hy) (norm_nonneg t)
  simpa only [Real.dist_eq,←mul_sub,abs_mul,Real.norm_eq_abs,NNReal.coe_mul,coe_nnnorm,mul_assoc] using hh

theorem harmonicBarrierRadius_mem {B t r v : ℝ}
    (hB : 0<B) (ht : t∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) :
    harmonicBarrierRadius B t r v∈Icc (0:ℝ) 1 := by
  let d := (1-t)/(r+B)+t/(v+B)
  have hd : 0<d := harmonicBarrierDenominator_pos hB ht hr.1 hv.1
  have hR : 0<r+B := by linarith [hr.1]
  have hV : 0<v+B := by linarith [hv.1]
  have hBB : 0<1+B := by linarith
  have hrlo : (1+B)⁻¹≤(r+B)⁻¹ := (inv_le_inv₀ hBB hR).mpr (by linarith [hr.2])
  have hvlo : (1+B)⁻¹≤(v+B)⁻¹ := (inv_le_inv₀ hBB hV).mpr (by linarith [hv.2])
  have hrhi : (r+B)⁻¹≤B⁻¹ := (inv_le_inv₀ hR hB).mpr (by linarith [hr.1])
  have hvhi : (v+B)⁻¹≤B⁻¹ := (inv_le_inv₀ hV hB).mpr (by linarith [hv.1])
  have hlo : (1+B)⁻¹≤d := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hrlo (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hvlo ht.1)
    dsimp [d]
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hhi : d≤B⁻¹ := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hrhi (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hvhi ht.1)
    dsimp [d]
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hir : B≤d⁻¹ := by simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr hB) hd).mpr hhi
  have hil : d⁻¹≤1+B := by simpa only [inv_inv] using (inv_le_inv₀ hd (inv_pos.mpr hBB)).mpr hlo
  change d⁻¹-B∈Icc (0:ℝ) 1
  constructor <;> linarith

theorem harmonicBarrierRadius_diagonal {B t r : ℝ} (hB : 0<B) (hr : 0≤r) :
    harmonicBarrierRadius B t r r=r := by
  have hR : r+B≠0 := (by linarith : 0<r+B).ne'
  have hd : (1-t)/(r+B)+t/(r+B)=(r+B)⁻¹ := by field_simp;ring
  unfold harmonicBarrierRadius
  rw [hd,inv_inv]
  ring

theorem harmonicBarrierRadius_lipschitz {B t : ℝ} (hB : 0<B) (ht : t∈Icc (0:ℝ) 1)
    {r v : ℝ→ℝ} {Cr Cv : ℝ≥0}
    (hr : LipschitzOnWith Cr r (Icc (0:ℝ) 1)) (hv : LipschitzOnWith Cv v (Icc (0:ℝ) 1))
    (hrb : MapsTo r (Icc (0:ℝ) 1) (Icc (0:ℝ) 1))
    (hvb : MapsTo v (Icc (0:ℝ) 1) (Icc (0:ℝ) 1)) :
    ∃ C : ℝ≥0,LipschitzOnWith C (fun u=>harmonicBarrierRadius B t (r u) (v u)) (Icc (0:ℝ) 1) := by
  have hrc : LipschitzOnWith Cr (fun u=>r u+B) (Icc (0:ℝ) 1) := by
    simpa using hr.add (LipschitzWith.const B).lipschitzOnWith
  have hvc : LipschitzOnWith Cv (fun u=>v u+B) (Icc (0:ℝ) 1) := by
    simpa using hv.add (LipschitzWith.const B).lipschitzOnWith
  have hri := (positiveReciprocal_lipschitzOn hB).comp hrc (fun u hu=>by
    change B≤r u+B
    linarith [(hrb hu).1])
  have hvi := (positiveReciprocal_lipschitzOn hB).comp hvc (fun u hu=>by
    change B≤v u+B
    linarith [(hvb hu).1])
  let d := fun u=>(1-t)/(r u+B)+t/(v u+B)
  have hdl := (real_const_mul_lipschitzOn hri (1-t)).add (real_const_mul_lipschitzOn hvi t)
  have hdl' : LipschitzOnWith
      (‖1-t‖₊*(⟨(B^2)⁻¹,inv_nonneg.mpr (sq_nonneg B)⟩*Cr)+
        ‖t‖₊*(⟨(B^2)⁻¹,inv_nonneg.mpr (sq_nonneg B)⟩*Cv)) d (Icc (0:ℝ) 1) := by
    simpa only [Function.comp_def,div_eq_mul_inv,d] using hdl
  have hBB : 0<(1+B)⁻¹ := inv_pos.mpr (by linarith)
  have hdlow : MapsTo d (Icc (0:ℝ) 1) (Ici ((1+B)⁻¹)) := by
    intro u hu
    have hrlo := (inv_le_inv₀ (by linarith : 0<1+B)
      (by linarith [(hrb hu).1] : 0<r u+B)).mpr (by linarith [(hrb hu).2] : r u+B≤1+B)
    have hvlo := (inv_le_inv₀ (by linarith : 0<1+B)
      (by linarith [(hvb hu).1] : 0<v u+B)).mpr (by linarith [(hvb hu).2] : v u+B≤1+B)
    have h := add_le_add (mul_le_mul_of_nonneg_left hrlo (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hvlo ht.1)
    change (1+B)⁻¹≤d u
    dsimp [d]
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hfinal := ((positiveReciprocal_lipschitzOn hBB).comp hdl' hdlow).add
    (LipschitzWith.const (-B)).lipschitzOnWith
  exact ⟨_,by simpa only [Function.comp_def,harmonicBarrierRadius,sub_eq_add_neg,d] using hfinal⟩

theorem reciprocalSquareFloor_continuousOn {A B : ℝ} (hB : 0<B) :
    ContinuousOn (reciprocalSquareFloor A B) (Icc (0:ℝ) 1) := by
  intro r hr
  have hR : 0<r+B := by linarith [hr.1]
  unfold reciprocalSquareFloor
  fun_prop (disch := positivity)

theorem harmonic_comparison_trial_feasible {A B c t : ℝ} {M : ℝ→ℝ}
    (hA : 0<A) (hB : 0<B) (hc : 0<c) (ht : t∈Icc (0:ℝ) 1)
    (hkc : ∀r∈Icc (0:ℝ) 1,c≤reciprocalSquareFloor A B r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
    (α β : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M) :
    ∃ γ : inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M,
      ∀u∈Icc (0:ℝ) 1,γ.val.val (harmonicBarrierRadius B t
        (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB)
          hkc hm (hMp 1 (by norm_num)).le α u)
        (comparisonSweepQuantile hc (reciprocalSquareFloor_continuousOn hB)
          hkc hm (hMp 1 (by norm_num)).le β u))=u := by
  let k := reciprocalSquareFloor A B
  have hk : ContinuousOn k (Icc (0:ℝ) 1) := reciprocalSquareFloor_continuousOn hB
  have hM1 : 0<M 1 := hMp 1 (by norm_num)
  let r := comparisonSweepQuantile hc hk hkc hm hM1.le α
  let v := comparisonSweepQuantile hc hk hkc hm hM1.le β
  let q := fun u=>harmonicBarrierRadius B t (r u) (v u)
  have hrb : MapsTo r (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM1.le α u
  have hvb : MapsTo v (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM1.le β u
  have hrl := comparisonSweepQuantile_lipschitzOn hc hk hkc hm hM1.le α
  have hvl := comparisonSweepQuantile_lipschitzOn hc hk hkc hm hM1.le β
  obtain ⟨C,hql⟩ := harmonicBarrierRadius_lipschitz hB ht hrl hvl hrb hvb
  have hqb : MapsTo q (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := fun u hu=>harmonicBarrierRadius_mem hB ht (hrb hu) (hvb hu)
  have hq0 : q 0=0 := by
    dsimp [q,r,v]
    rw [comparisonSweepQuantile_zero hc hk hkc hm hM1.le α,
      comparisonSweepQuantile_zero hc hk hkc hm hM1.le β]
    exact harmonicBarrierRadius_diagonal hB le_rfl
  have hq1 : q 1=1 := by
    dsimp [q,r,v]
    rw [comparisonSweepQuantile_one hc hk hkc hm hM1.le α,
      comparisonSweepQuantile_one hc hk hkc hm hM1.le β]
    exact harmonicBarrierRadius_diagonal hB zero_le_one
  have hacr : AbsolutelyContinuousOnInterval r 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨c⁻¹,inv_nonneg.mpr hc.le⟩)
    simpa only [uIcc_of_le zero_le_one] using hrl
  have hacv : AbsolutelyContinuousOnInterval v 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨c⁻¹,inv_nonneg.mpr hc.le⟩)
    simpa only [uIcc_of_le zero_le_one] using hvl
  have hder : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → (M u)⁻¹≤deriv q u ∧ deriv q u≤(k (q u))⁻¹ := by
    filter_upwards [comparisonSweepQuantile_ae_slope hc hk hkc hm hM1.le α hMc hMp,
      comparisonSweepQuantile_ae_slope hc hk hkc hm hM1.le β hMc hMp,
      hacr.ae_differentiableAt,hacv.ae_differentiableAt] with u hr hv hdr hdv hu
    have hu' : u∈uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hu
    have hD := harmonicBarrierRadius_derivative (hdr hu').hasDerivAt (hdv hu').hasDerivAt
      (by linarith [(hrb hu).1] : r u+B≠0) (by linarith [(hvb hu).1] : v u+B≠0)
      (harmonicBarrierDenominator_pos hB ht (hrb hu).1 (hvb hu).1).ne'
    have hbounds := harmonicBarrierDerivative_slope_bounds hA hB ht (hrb hu).1 (hvb hu).1
      (inv_nonneg.mpr (hMp u hu).le) (hr hu) (hv hu)
    change (M u)⁻¹≤deriv q u ∧ deriv q u≤(k (q u))⁻¹
    rw [hD.deriv]
    exact hbounds
  have hlow : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → (M 1)⁻¹≤deriv q u := by
    filter_upwards [hder] with u hd hu
    exact ((inv_le_inv₀ hM1 (hMp u hu)).mpr (hm hu (by norm_num) hu.2)).trans (hd hu).1
  have hgap := (lipschitz_ae_deriv_lower_iff zero_le_one hql continuousOn_const).mp hlow
  have hgap' : ∀u∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,u≤v → (M 1)⁻¹*(v-u)≤q v-q u := by
    intro u hu v hv huv
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hgap u hu v hv huv
  have hqs : StrictMonoOn q (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    have hh := hgap' u hu v hv huv.le
    have hp := mul_pos (inv_pos.mpr hM1) (sub_pos.mpr huv)
    linarith
  have hqp := hql.continuousOn
  have ha := forwardInverseProfile_feasible hqp hqs hqb hq0 hq1 hql (inv_pos.mpr hM1) hgap'
    hk hMc hm hM1.le (fun y hy=>hc.trans_le (hkc y hy)) hMp hder
  refine ⟨⟨forwardInverseProfile q hqp hqs hqb hq0 hq1,ha⟩,?_⟩
  intro u hu
  exact forwardInverseProfile_inverse hqp hqs hqb hq0 hq1 hu

end OAI.SKFluctuations.LaplaceWindowFormalization
