module
public import SKConstants.ParisiFullConditionalMGF
public import SKConstants.ParisiTanhPointMGF

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullPredictableMGF_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

lemma actualParisiFullProcess_post_predictable_mgf_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) (a v : ℝ≥0)
    (ha : parisiEquilibriumPhysicalEndpoint β≤a)
    (F A : ScalarContinuousPath a → ℝ) (hF : Measurable F) (hA : Measurable A)
    (hF0 : ∀p,0≤F p) (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (hFC : ∀p,F p≤C) (hAD : ∀p,|A p|≤D) (θ : ℝ) :
    (∫w,F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*Real.exp
      (θ*A (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*
        (actualParisiFullMagnetization β (a+v) (actualParisiFullScalarProcess W β (a+v) w)-
          actualParisiFullMagnetization β a (actualParisiFullScalarProcess W β a w))) ∂W.law)≤
      ∫w,F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*Real.exp
        (θ^2*A (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)^2*(v:ℝ)/2) ∂W.law := by
  apply boundedDrift_observable_predictable_mgf_test W (actualParisiFullScalarDrift β) a v
    (actualParisiFullMagnetization β a) (actualParisiFullMagnetization β (a+v))
    ((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable
    ((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable
    (fun x => (actualParisiFullMagnetization_curvature_bounds β a x).1)
    (fun x => (actualParisiFullMagnetization_curvature_bounds β (a+v) x).1)
    (fun past θ => by simpa only [NNReal.coe_add, mul_comm (v:ℝ) (θ^2)] using
      actualParisiFullRestart_post_mgf W β hβ a v ha past θ) F A hF hA hF0 C D hC hD hFC hAD θ

lemma scalarPredictableExp_increment_bound {E : Type*} (F A X Y : E → ℝ)
    (hF0 : ∀p,0≤F p) (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (hFC : ∀p,F p≤C) (hAD : ∀p,|A p|≤D) (hX : ∀p,|X p|≤1) (hY : ∀p,|Y p|≤1)
    (θ : ℝ) (p : E) :
    F p*Real.exp (θ*A p*(X p-Y p))≤C*Real.exp (2* |θ| *D) := by
  apply mul_le_mul (hFC p) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC
  have hdiff : |X p-Y p|≤2 := by
    have HA := abs_le.mp (hX p)
    have HB := abs_le.mp (hY p)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  calc θ*A p*(X p-Y p)≤|θ*A p*(X p-Y p)| := le_abs_self _
    _=|θ| * |A p| * |X p-Y p| := by rw [abs_mul,abs_mul]
    _≤|θ| *D*2 := mul_le_mul (mul_le_mul_of_nonneg_left (hAD p) (abs_nonneg θ)) hdiff (abs_nonneg _) (by positivity)
    _=2* |θ| *D := by ring

lemma scalarPredictableExp_variance_bound {E : Type*} (F A : E → ℝ)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hFC : ∀p,F p≤C) (hAD : ∀p,|A p|≤D)
    (θ : ℝ) (v : ℝ≥0) (p : E) :
    F p*Real.exp (θ^2*A p^2*(v:ℝ)/2)≤C*Real.exp (θ^2*D^2*(v:ℝ)/2) := by
  apply mul_le_mul (hFC p) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC
  have HA := abs_le.mp (hAD p)
  have HAsq : A p^2≤D^2 := by nlinarith
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HAsq (sq_nonneg θ)) v.coe_nonneg) (by positivity)

theorem actualParisiFullProcess_predictable_mgf_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) (a v : ℝ≥0)
    (F A : ScalarContinuousPath a → ℝ) (hF : Measurable F) (hA : Measurable A)
    (hF0 : ∀p,0≤F p) (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (hFC : ∀p,F p≤C) (hAD : ∀p,|A p|≤D) (θ : ℝ) :
    (∫w,F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*Real.exp
      (θ*A (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*
        (actualParisiFullMagnetization β (a+v) (actualParisiFullScalarProcess W β (a+v) w)-
          actualParisiFullMagnetization β a (actualParisiFullScalarProcess W β a w))) ∂W.law)≤
      ∫w,F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*Real.exp
        (θ^2*A (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)^2*(v:ℝ)/2) ∂W.law := by
  let V := parisiEquilibriumPhysicalEndpoint β
  by_cases hav : a+v≤V
  · exact actualParisiFullProcess_pre_predictable_mgf_test W β hβ a v hav F A hF hA hF0 C D hC hD hFC hAD θ
  by_cases ha : V≤a
  · exact actualParisiFullProcess_post_predictable_mgf_test W β hβ a v ha F A hF hA hF0 C D hC hD hFC hAD θ
  have haV : a≤V := (lt_of_not_ge ha).le
  have hVa : V≤a+v := (lt_of_not_ge hav).le
  let d := V-a
  let e := a+v-V
  have had : a+d=V := by dsimp [d]; exact add_tsub_cancel_of_le haV
  have hVe : V+e=a+v := by dsimp [e]; exact add_tsub_cancel_of_le hVa
  have hde : d+e=v := by
    apply add_left_cancel (a:=a)
    calc a+(d+e)=(a+d)+e := (add_assoc _ _ _).symm
      _=V+e := by rw [had]
      _=a+v := hVe
  let b := actualParisiFullScalarDrift β
  let P (t : ℝ≥0) := boundedDriftPastPath W b t
  let M (t : ℝ≥0) (w : Ω) := actualParisiFullMagnetization β t (actualParisiFullScalarProcess W β t w)
  let R := scalarContinuousPathRestrict a V haV
  have hR : Measurable R := measurable_scalarContinuousPathRestrict a V haV
  let Ma (p : ScalarContinuousPath a) := actualParisiFullMagnetization β a (p ⟨a,a.coe_nonneg,le_rfl⟩)
  let MV (p : ScalarContinuousPath V) := actualParisiFullMagnetization β V (p ⟨V,V.coe_nonneg,le_rfl⟩)
  have hMa : Measurable Ma :=
    (((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable).comp
      (ContinuousMap.measurable_eval _)
  have hMV : Measurable MV :=
    (((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable).comp
      (ContinuousMap.measurable_eval _)
  have hMaB (p : ScalarContinuousPath a) : |Ma p|≤1 := (actualParisiFullMagnetization_curvature_bounds β a _).1
  have hMVB (p : ScalarContinuousPath V) : |MV p|≤1 := (actualParisiFullMagnetization_curvature_bounds β V _).1
  let J := A ∘ R
  let G : ScalarContinuousPath V → ℝ := fun p => F (R p)*Real.exp (θ*J p*(MV p-Ma (R p)))
  have hJ : Measurable J := hA.comp hR
  have hG : Measurable G := (hF.comp hR).mul
    (Real.continuous_exp.measurable.comp ((hJ.const_mul θ).mul (hMV.sub (hMa.comp hR))))
  have hG0 (p : ScalarContinuousPath V) : 0≤G p := mul_nonneg (hF0 _) (Real.exp_pos _).le
  have hGB (p : ScalarContinuousPath V) : G p≤C*Real.exp (2* |θ| *D) :=
    scalarPredictableExp_increment_bound (F ∘ R) J MV (Ma ∘ R) (fun p => hF0 _) C D hC hD
      (fun p => hFC _) (fun p => hAD _) hMVB (fun p => hMaB _) θ p
  let B : ScalarContinuousPath a → ℝ := fun p => F p*Real.exp (θ^2*A p^2*(e:ℝ)/2)
  have hB : Measurable B := hF.mul (Real.continuous_exp.measurable.comp
    ((((hA.pow_const 2).const_mul (θ^2)).mul_const (e:ℝ)).div_const 2))
  have hB0 (p : ScalarContinuousPath a) : 0≤B p := mul_nonneg (hF0 _) (Real.exp_pos _).le
  have hBB (p : ScalarContinuousPath a) : B p≤C*Real.exp (θ^2*D^2*(e:ℝ)/2) :=
    scalarPredictableExp_variance_bound F A C D hC hD hFC hAD θ e p
  have Hpost := actualParisiFullProcess_post_predictable_mgf_test W β hβ V e le_rfl G J hG hJ hG0
    (C*Real.exp (2* |θ| *D)) D (mul_nonneg hC (Real.exp_pos _).le) hD hGB (fun p => hAD _) θ
  have Hpre := actualParisiFullProcess_pre_predictable_mgf_test W β hβ a d (by rw [had]) B A hB hA hB0
    (C*Real.exp (θ^2*D^2*(e:ℝ)/2)) D (mul_nonneg hC (Real.exp_pos _).le) hD hBB hAD θ
  have hVer : (V:ℝ)+(e:ℝ)=(a:ℝ)+(v:ℝ) := by exact_mod_cast hVe
  have hadr : (a:ℝ)+(d:ℝ)=(V:ℝ) := by exact_mod_cast had
  rw [hVe,hVer] at Hpost
  rw [had,hadr] at Hpre
  change (∫w,G (P V w)*Real.exp (θ*J (P V w)*(M (a+v) w-M V w)) ∂W.law)≤
    ∫w,G (P V w)*Real.exp (θ^2*J (P V w)^2*(e:ℝ)/2) ∂W.law at Hpost
  change (∫w,B (P a w)*Real.exp (θ*A (P a w)*(M V w-M a w)) ∂W.law)≤
    ∫w,B (P a w)*Real.exp (θ^2*A (P a w)^2*(d:ℝ)/2) ∂W.law at Hpre
  change (∫w,F (P a w)*Real.exp (θ*A (P a w)*(M (a+v) w-M a w)) ∂W.law)≤
    ∫w,F (P a w)*Real.exp (θ^2*A (P a w)^2*(v:ℝ)/2) ∂W.law
  have hPast := boundedDriftPastPath_restrict W b a V haV
  have hMaactual : ∀ᵐ w ∂W.law,Ma (P a w)=M a w := by
    filter_upwards [boundedDriftPastPath_version W b a] with w hw
    dsimp only [Ma,P,M]
    rw [hw]
    rfl
  have hMVactual : ∀ᵐ w ∂W.law,MV (P V w)=M V w := by
    filter_upwards [boundedDriftPastPath_version W b V] with w hw
    dsimp only [MV,P,M]
    rw [hw]
    rfl
  calc
    _=(∫w,G (P V w)*Real.exp (θ*J (P V w)*(M (a+v) w-M V w)) ∂W.law) := by
      apply integral_congr_ae
      filter_upwards [hPast,hMaactual,hMVactual] with w hp hma hmv
      dsimp only [G,J,Function.comp_def]
      rw [show R (P V w)=P a w from hp,hma,hmv]
      rw [mul_assoc (F (P a w)) (Real.exp (θ*A (P a w)*(M V w-M a w)))
        (Real.exp (θ*A (P a w)*(M (a+v) w-M V w))),←Real.exp_add]
      congr 1
      congr 1
      ring
    _≤_ := Hpost
    _=(∫w,B (P a w)*Real.exp (θ*A (P a w)*(M V w-M a w)) ∂W.law) := by
      apply integral_congr_ae
      filter_upwards [hPast,hMaactual,hMVactual] with w hp hma hmv
      dsimp only [G,J,B,Function.comp_def]
      rw [show R (P V w)=P a w from hp,hma,hmv]
      ring
    _≤_ := Hpre
    _=_ := by
      apply integral_congr_ae
      apply ae_of_all
      intro w
      dsimp only [B]
      rw [mul_assoc,←Real.exp_add]
      congr 1
      congr 1
      have Hde : (d:ℝ)+(e:ℝ)=(v:ℝ) := by exact_mod_cast hde
      rw [←Hde]
      ring

end SKConstants
