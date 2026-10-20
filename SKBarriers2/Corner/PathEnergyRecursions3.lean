module

public import SKBarriers2.Corner.PathEnergyRecursions2
public import SKBarriers2.Corner.PathEnergyInner2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

private theorem directional_eq_coordinate_sum (L : E →L[ℝ] ℝ) (v : E) :
    L v = ∑ i : Fin 3, v i*L (Pi.single i 1) := by
  have hv : v = ∑ i : Fin 3, v i • Pi.single i 1 := by
    ext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]

theorem hasDerivAt_moving_spatial_of_uniform_jets
    {F G : ℝ → E → ℝ} {v : ℝ → E} {v₁ : E} {B k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hd : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (G t x) t)
    (hG : ∀ᶠ t in 𝓝 k, QBoundedJets 2 B (G t))
    (hv : HasDerivAt v v₁ k) (x : E) :
    HasDerivAt (fun t => fderiv ℝ (F t) x (v t))
      (fderiv ℝ (G k) x (v k)+fderiv ℝ (F k) x v₁) k := by
  have H := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    (fun i _ =>
      ((ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt k hv).mul
        (hasDerivAt_spatial_of_uniform_jets hF hd hG x (Pi.single i 1)))
  have he : (fun t => ∑ i : Fin 3, v t i*fderiv ℝ (F t) x (Pi.single i 1)) =
      (fun t => fderiv ℝ (F t) x (v t)) := by
    funext t
    exact (directional_eq_coordinate_sum _ _).symm
  simp only [Function.comp_def,Pi.mul_apply,ContinuousLinearMap.proj_apply] at H
  rw [he] at H
  convert H using 1
  rw [directional_eq_coordinate_sum (fderiv ℝ (G k) x),
    directional_eq_coordinate_sum (fderiv ℝ (F k) x),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def innerCorrectionJet (F f F₁ F₂ : E → ℝ) (v v₁ v₂ : E) : Fin 3 → E → ℝ :=
  let U := fun x => fderiv ℝ F x v-fderiv ℝ f x v
  let V := fun x => fderiv ℝ F x v+fderiv ℝ f x v
  let U₁ := fun x => fderiv ℝ F₁ x v+fderiv ℝ F x v₁-fderiv ℝ f x v₁
  let V₁ := fun x => fderiv ℝ F₁ x v+fderiv ℝ F x v₁+fderiv ℝ f x v₁
  let U₂ := fun x => fderiv ℝ F₂ x v+2*fderiv ℝ F₁ x v₁+
    fderiv ℝ F x v₂-fderiv ℝ f x v₂
  let V₂ := fun x => fderiv ℝ F₂ x v+2*fderiv ℝ F₁ x v₁+
    fderiv ℝ F x v₂+fderiv ℝ f x v₂
  ![fun x => U x*V x,
    fun x => U₁ x*V x+U x*V₁ x,
    fun x => U₂ x*V x+2*(U₁ x*V₁ x)+U x*V₂ x]

theorem innerCorrectionJet_zero (F f F₁ F₂ : E → ℝ) (v v₁ v₂ x : E) :
    innerCorrectionJet F f F₁ F₂ v v₁ v₂ 0 x =
      (fderiv ℝ F x v)^2-(fderiv ℝ f x v)^2 := by
  simp only [innerCorrectionJet,Matrix.cons_val_zero]
  ring

theorem moving_spatial_twoJet {F F₁ F₂ : ℝ → E → ℝ}
    {v v₁ v₂ : ℝ → E} {A H k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hd₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (F₁ t x) t)
    (hd₁ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F₁ q x) (F₂ t x) t)
    (hF₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 A (F₁ t))
    (hF₂ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 H (F₂ t))
    (hv : ∀ᶠ t in 𝓝 k, HasDerivAt v (v₁ t) t)
    (hv₁ : HasDerivAt v₁ (v₂ k) k) (x : E) :
    deriv (fun t => fderiv ℝ (F t) x (v t)) k =
        fderiv ℝ (F₁ k) x (v k)+fderiv ℝ (F k) x (v₁ k) ∧
      deriv (deriv (fun t => fderiv ℝ (F t) x (v t))) k =
        fderiv ℝ (F₂ k) x (v k)+2*fderiv ℝ (F₁ k) x (v₁ k)+
          fderiv ℝ (F k) x (v₂ k) := by
  have hfirst := hasDerivAt_moving_spatial_of_uniform_jets hF hd₀ hF₁ hv.self_of_nhds x
  have he : deriv (fun t => fderiv ℝ (F t) x (v t)) =ᶠ[𝓝 k]
      (fun t => fderiv ℝ (F₁ t) x (v t)+fderiv ℝ (F t) x (v₁ t)) := by
    filter_upwards [eventually_eventually_nhds.mpr hF,
      eventually_eventually_nhds.mpr hd₀,eventually_eventually_nhds.mpr hF₁,hv] with
      t hFt hdt hF₁t hvt
    exact (hasDerivAt_moving_spatial_of_uniform_jets hFt hdt hF₁t hvt x).deriv
  have hF₁diff : ∀ᶠ t in 𝓝 k, ∀ y, DifferentiableAt ℝ (F₁ t) y := by
    filter_upwards [hF₁] with t ht y
    exact ht.smooth.differentiable (by norm_num) y
  have hleft := hasDerivAt_moving_spatial_of_uniform_jets hF₁diff hd₁ hF₂
    hv.self_of_nhds x
  have hright := hasDerivAt_moving_spatial_of_uniform_jets hF hd₀ hF₁ hv₁ x
  refine ⟨hfirst.deriv,?_⟩
  rw [he.deriv_eq]
  convert! (hleft.add hright).deriv using 1
  ring

theorem innerCorrectionJet_eq_iteratedDeriv {F : ℝ → E → ℝ}
    {f F₁ F₂ : E → ℝ} {v : ℝ → E} {v₁ v₂ : E} {k : ℝ} (x : E)
    (hA : ContDiffAt ℝ 2 (fun t => fderiv ℝ (F t) x (v t)) k)
    (ha : ContDiffAt ℝ 2 (fun t => fderiv ℝ f x (v t)) k)
    (hA₁ : deriv (fun t => fderiv ℝ (F t) x (v t)) k =
      fderiv ℝ F₁ x (v k)+fderiv ℝ (F k) x v₁)
    (hA₂ : deriv (deriv (fun t => fderiv ℝ (F t) x (v t))) k =
      fderiv ℝ F₂ x (v k)+2*fderiv ℝ F₁ x v₁+fderiv ℝ (F k) x v₂)
    (ha₁ : deriv (fun t => fderiv ℝ f x (v t)) k = fderiv ℝ f x v₁)
    (ha₂ : deriv (deriv (fun t => fderiv ℝ f x (v t))) k = fderiv ℝ f x v₂)
    (c : Fin 3) :
    innerCorrectionJet (F k) f F₁ F₂ (v k) v₁ v₂ c x =
      iteratedDeriv c.val (fun t => (fderiv ℝ (F t) x (v t))^2-
        (fderiv ℝ f x (v t))^2) k := by
  let U := fun t => fderiv ℝ (F t) x (v t)-fderiv ℝ f x (v t)
  let V := fun t => fderiv ℝ (F t) x (v t)+fderiv ℝ f x (v t)
  have hU : ContDiffAt ℝ 2 U k := hA.sub ha
  have hV : ContDiffAt ℝ 2 V k := hA.add ha
  have he : (fun t => (fderiv ℝ (F t) x (v t))^2-(fderiv ℝ f x (v t))^2) =
      fun t => U t*V t := by funext t; dsimp only [U,V]; ring
  rw [he]
  fin_cases c
  · simp [innerCorrectionJet,U,V]
  · rw [iteratedDeriv_fun_mul (hU.of_le (by norm_num)) (hV.of_le (by norm_num))]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,
      Nat.choose_zero_right,Nat.choose_self,iteratedDeriv_zero,iteratedDeriv_one,
      Nat.sub_zero,Nat.sub_self,Nat.cast_one,one_mul,zero_add]
    dsimp only [U,V]
    rw [deriv_fun_sub (hA.differentiableAt (by norm_num)) (ha.differentiableAt (by norm_num)),
      deriv_fun_add (hA.differentiableAt (by norm_num)) (ha.differentiableAt (by norm_num)),hA₁,ha₁]
    norm_num [innerCorrectionJet]
    ring
  · rw [iteratedDeriv_fun_mul hU hV]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,
      Nat.choose_zero_right,Nat.choose_self,iteratedDeriv_zero,
      zero_add,Nat.cast_one,one_mul]
    have hUd := iteratedDeriv_fun_sub hA ha
    have hVd := iteratedDeriv_fun_add hA ha
    dsimp only [U,V]
    rw [hUd,hVd]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rw [deriv_fun_sub (hA.differentiableAt (by norm_num)) (ha.differentiableAt (by norm_num)),
      deriv_fun_add (hA.differentiableAt (by norm_num)) (ha.differentiableAt (by norm_num)),
      hA₁,hA₂,ha₁,ha₂]
    norm_num [innerCorrectionJet]
    ring

theorem qBoundedJets_innerCorrectionJet {B H d : ℝ} {F f F₁ F₂ : E → ℝ}
    (hF : QPotential 7 B F) (hf : QPotential 7 B f)
    (hsub : QBoundedJets 7 H (fun x => F x-f x))
    (hF₁ : QBoundedJets 5 H F₁) (hF₂ : QBoundedJets 3 H F₂)
    (hd : 0 ≤ d) (v v₁ v₂ : E)
    (hv : ‖v‖ ≤ d) (hv₁ : ‖v₁‖ ≤ d) (hv₂ : ‖v₂‖ ≤ d) :
    QBoundedJets 6 (256*(1+B+H)*H*d^2) (innerCorrectionJet F f F₁ F₂ v v₁ v₂ 0) ∧
    QBoundedJets 4 (256*(1+B+H)*H*d^2) (innerCorrectionJet F f F₁ F₂ v v₁ v₂ 1) ∧
    QBoundedJets 2 (256*(1+B+H)*H*d^2) (innerCorrectionJet F f F₁ F₂ v v₁ v₂ 2) := by
  have hB := hf.nonneg
  have hH := hsub.nonneg
  have hHd : 0 ≤ H*d := mul_nonneg hH hd
  have hsmall (w : E) (hw : ‖w‖ ≤ d) :
      QBoundedJets 6 (H*d) (fun x => fderiv ℝ F x w-fderiv ℝ f x w) := by
    have H' := (hsub.derivativeJets.apply_const w).mono
      (mul_le_mul_of_nonneg_left hw hH)
    have he : (fun x => fderiv ℝ (fun y => F y-f y) x w) =
        (fun x => fderiv ℝ F x w-fderiv ℝ f x w) := by
      funext x
      rw [fderiv_fun_sub (hF.smooth.differentiable (by norm_num) x)
        (hf.smooth.differentiable (by norm_num) x),sub_apply]
    rwa [he] at H'
  have hlarge (w : E) (hw : ‖w‖ ≤ d) :
      QBoundedJets 6 (2*B*d) (fun x => fderiv ℝ F x w+fderiv ℝ f x w) := by
    apply ((hF.derivativeJets.apply_const w).add (hf.derivativeJets.apply_const w)).mono
    nlinarith only [mul_le_mul_of_nonneg_left hw hB]
  have hfirst (w : E) (hw : ‖w‖ ≤ d) :
      QBoundedJets 4 (H*d) (fun x => fderiv ℝ F₁ x w) :=
    (hF₁.derivativeJets.apply_const w).mono (mul_le_mul_of_nonneg_left hw hH)
  have hsecond : QBoundedJets 2 (H*d) (fun x => fderiv ℝ F₂ x v) :=
    (hF₂.derivativeJets.apply_const v).mono (mul_le_mul_of_nonneg_left hv hH)
  have hU := hsmall v hv
  have hV := hlarge v hv
  have hU₁ := (hfirst v hv).add ((hsmall v₁ hv₁).of_le (by norm_num : 4 ≤ 6))
  have hV₁ := (hfirst v hv).add ((hlarge v₁ hv₁).of_le (by norm_num : 4 ≤ 6))
  have hU₂ := (hsecond.add (((hfirst v₁ hv₁).of_le (by norm_num : 2 ≤ 4)).const_smul 2)).add
    ((hsmall v₂ hv₂).of_le (by norm_num : 2 ≤ 6))
  have hV₂ := (hsecond.add (((hfirst v₁ hv₁).of_le (by norm_num : 2 ≤ 4)).const_smul 2)).add
    ((hlarge v₂ hv₂).of_le (by norm_num : 2 ≤ 6))
  simp only [smul_eq_mul] at hU₂ hV₂
  have hzero := hU.mul hV
  have hone := (hU₁.mul (hV.of_le (by norm_num : 4 ≤ 6))).add
    ((hU.of_le (by norm_num : 4 ≤ 6)).mul hV₁)
  have hcross := ((hU₁.of_le (by norm_num : 2 ≤ 4)).mul
    (hV₁.of_le (by norm_num : 2 ≤ 4))).const_smul 2
  have htwo := ((hU₂.mul (hV.of_le (by norm_num : 2 ≤ 6))).add hcross).add
    ((hU.of_le (by norm_num : 2 ≤ 6)).mul hV₂)
  simp only [smul_eq_mul] at htwo
  refine ⟨?_,?_,?_⟩
  · convert hzero.mono (show (2:ℝ)^6*(H*d)*(2*B*d) ≤ 256*(1+B+H)*H*d^2 by
      nlinarith [mul_nonneg hHd hd,
        mul_nonneg (mul_nonneg hH (sq_nonneg d)) hB,
        mul_nonneg (mul_nonneg hH (sq_nonneg d)) hH]) using 1
    funext x
    simp only [innerCorrectionJet,Matrix.cons_val_zero]
  · have hm : (2:ℝ)^4*((H*d)+(H*d))*(2*B*d)+
        (2:ℝ)^4*(H*d)*((H*d)+(2*B*d)) ≤ 256*(1+B+H)*H*d^2 := by
      nlinarith [mul_nonneg hHd hd,
        mul_nonneg (mul_nonneg hH (sq_nonneg d)) hB,
        mul_nonneg (mul_nonneg hH (sq_nonneg d)) hH]
    convert hone.mono hm using 1
    funext x
    norm_num [innerCorrectionJet]
    ring
  · have hm : (2:ℝ)^2*((H*d)+|2| * (H*d)+(H*d))*(2*B*d)+
        |2| * ((2:ℝ)^2*((H*d)+(H*d))*((H*d)+(2*B*d)))+
        (2:ℝ)^2*(H*d)*((H*d)+|2| * (H*d)+(2*B*d)) ≤
        256*(1+B+H)*H*d^2 := by
      norm_num
      nlinarith [mul_nonneg hHd hd,
        mul_nonneg (mul_nonneg hH (sq_nonneg d)) hB,
        mul_nonneg (mul_nonneg hH (sq_nonneg d)) hH]
    convert htwo.mono hm using 1
    funext x
    norm_num [innerCorrectionJet]
    ring

theorem qBoundedJets_movingInnerCorrection {F : ℝ → E → ℝ} {f : E → ℝ}
    {v : ℝ → E} {B H d k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hp : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun q => F q x) t)
    (hgrad : ∀ x w, ContDiffAt ℝ 2 (fun t => fderiv ℝ (F t) x w) k)
    (hfirst : ∀ᶠ t in 𝓝 k, QBoundedJets 5 H (fun x => deriv (fun q => F q x) t))
    (hsecond : ∀ᶠ t in 𝓝 k, QBoundedJets 3 H (fun x => deriv (deriv (fun q => F q x)) t))
    (hFk : QPotential 7 B (F k)) (hf : QPotential 7 B f)
    (hsub : QBoundedJets 7 H (fun x => F k x-f x))
    (hv : ContDiffAt ℝ 2 v k) (hd : 0 ≤ d)
    (hv₀ : ‖v k‖ ≤ d) (hv₁ : ‖deriv v k‖ ≤ d) (hv₂ : ‖deriv (deriv v) k‖ ≤ d) :
    let delta := fun t x => (fderiv ℝ (F t) x (v t))^2-(fderiv ℝ f x (v t))^2
    (∀ x, ContDiffAt ℝ 2 (fun t => delta t x) k) ∧
    QBoundedJets 6 (256*(1+B+H)*H*d^2) (delta k) ∧
    QBoundedJets 4 (256*(1+B+H)*H*d^2) (fun x => deriv (fun t => delta t x) k) ∧
    QBoundedJets 2 (256*(1+B+H)*H*d^2) (fun x => deriv (deriv (fun t => delta t x)) k) := by
  dsimp only
  have hd₀ : ∀ᶠ t in 𝓝 k, ∀ x,
      HasDerivAt (fun q => F q x) (deriv (fun q => F q x) t) t := by
    filter_upwards [hp] with t ht x
    exact ((ht x).differentiableAt (by norm_num)).hasDerivAt
  have hd₁ : ∀ᶠ t in 𝓝 k, ∀ x,
      HasDerivAt (fun q => deriv (fun a => F a x) q)
        (deriv (deriv (fun q => F q x)) t) t := by
    filter_upwards [hp] with t ht x
    exact (((ht x).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hvnear : ∀ᶠ t in 𝓝 k, HasDerivAt v (deriv v t) t := by
    filter_upwards [hv.eventually (by norm_num)] with t ht
    exact (ht.differentiableAt (by norm_num)).hasDerivAt
  have hvd := ((hv.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hjet (x : E) := moving_spatial_twoJet hF hd₀ hd₁
    (hfirst.mono (fun _ h => h.of_le (by norm_num : 2 ≤ 5)))
    (hsecond.mono (fun _ h => h.of_le (by norm_num : 2 ≤ 3))) hvnear hvd x
  have hA (x : E) : ContDiffAt ℝ 2 (fun t => fderiv ℝ (F t) x (v t)) k := by
    have H := ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun i _ => ((ContinuousLinearMap.proj i).contDiff.contDiffAt.comp k hv).mul
        (hgrad x (Pi.single i 1)))
    have he : (fun t => ∑ i : Fin 3, v t i*fderiv ℝ (F t) x (Pi.single i 1)) =
        (fun t => fderiv ℝ (F t) x (v t)) := by
      funext t
      exact (directional_eq_coordinate_sum _ _).symm
    simp only [Function.comp_def,ContinuousLinearMap.proj_apply] at H
    rwa [he] at H
  have ha (x : E) : ContDiffAt ℝ 2 (fun t => fderiv ℝ f x (v t)) k :=
    (fderiv ℝ f x).contDiff.contDiffAt.comp k hv
  have ha₁ (x : E) : deriv (fun t => fderiv ℝ f x (v t)) k = fderiv ℝ f x (deriv v k) :=
    ((fderiv ℝ f x).hasFDerivAt.comp_hasDerivAt k hvnear.self_of_nhds).deriv
  have ha₂ (x : E) : deriv (deriv (fun t => fderiv ℝ f x (v t))) k =
      fderiv ℝ f x (deriv (deriv v) k) := by
    have he : deriv (fun t => fderiv ℝ f x (v t)) =ᶠ[𝓝 k]
        fun t => fderiv ℝ f x (deriv v t) := by
      filter_upwards [hvnear] with t ht
      exact ((fderiv ℝ f x).hasFDerivAt.comp_hasDerivAt t ht).deriv
    rw [he.deriv_eq]
    exact ((fderiv ℝ f x).hasFDerivAt.comp_hasDerivAt k hvd).deriv
  have he (c : Fin 3) : innerCorrectionJet (F k) f
      (fun x => deriv (fun t => F t x) k) (fun x => deriv (deriv (fun t => F t x)) k)
      (v k) (deriv v k) (deriv (deriv v) k) c =
      fun x => iteratedDeriv c.val (fun t => (fderiv ℝ (F t) x (v t))^2-
        (fderiv ℝ f x (v t))^2) k := by
    funext x
    exact innerCorrectionJet_eq_iteratedDeriv x (hA x) (ha x)
      (hjet x).1 (hjet x).2 (ha₁ x) (ha₂ x) c
  have H := qBoundedJets_innerCorrectionJet hFk hf hsub
    hfirst.self_of_nhds hsecond.self_of_nhds hd (v k) (deriv v k) (deriv (deriv v) k) hv₀ hv₁ hv₂
  simp_rw [he] at H
  simp only [show (0:Fin 3).val = 0 from rfl,show (1:Fin 3).val = 1 from rfl,
    show (2:Fin 3).val = 2 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at H
  exact ⟨fun x => ((hA x).pow 2).sub ((ha x).pow 2),H⟩

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem orderedInnerVariation_eq_iteratedDeriv_fun (β : ℝ) (α : ℝ → ℝ)
    (a p s h : ℝ) (N : ℕ) (lam : ℝ) (j : Fin (12*N)) (c : ℕ) (k : ℝ) :
    orderedInnerVariation β α a p s h N lam j c k =
      fun x => iteratedDeriv c (fun t => orderedInnerChain β α a p s h N lam j t x) k := rfl

private theorem correction_chainEnergy_le_variation (ps : List (ℝ → ℝ × E)) (k : ℝ) :
    chainEnergy (ps.map (fun p => p k)) ≤ variationEnergy (windowVariationEnergy k) ps := by
  rw [windowVariationEnergy_sum]
  have h₁ : 0 ≤ (ps.map (fun p => ‖deriv (fun t => (p t).2) k‖^2)).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
    exact sq_nonneg _
  have h₂ : 0 ≤ (ps.map (fun p => ‖deriv (deriv (fun t => (p t).2)) k‖^2)).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
    exact sq_nonneg _
  simp only [chainEnergy,List.map_map,Function.comp_def]
  linarith

theorem scalarData_orderedInner_sub_c7 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
      let α := cdf (D.μ : Measure ℝ)
      QBoundedJets 7 (C*h) (fun x =>
        orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k x-
          massVariationTerminal β α (r-h) h x) := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,a0,hV,hA,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D hl hu
    let K := spatialStepDifferenceCoefficient 6 B
    have hK : 0 ≤ K := spatialStepDifferenceCoefficient_nonneg 6 hB
    have hden : 0 < A*(2*B+1)+1 := by positivity
    refine ⟨K*A,min hV (min hE (1/(A*(2*B+1)+1))),min kapE (1/2),
      by positivity,lt_min hhV (lt_min hhE (by positivity)),lt_min hkapE (by norm_num),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let L := massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N) lam
    let f := massVariationTerminal β α (r-h) h
    have hL : ps.map (fun p => p k) = L := by
      dsimp only [ps,L]
      rw [windowKCurves_apply β _ (r-h) h k N hh.le,massPath_window_eq]
    obtain ⟨he,hinputs⟩ := hvar r hr h hh (hh0.trans (min_le_left _ _))
      N hN lam hlam k (hk.trans (min_le_right _ _))
    have henergy : chainEnergy L ≤ A*h := by
      rw [← hL]
      exact (correction_chainEnergy_le_variation ps k).trans he
    have hshort : (2*B+1)*chainEnergy L ≤ 1 := by
      have H := (le_div_iff₀ hden).mp
        (hh0.trans ((min_le_right _ _).trans (min_le_right _ _)))
      have H' := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 2*B+1 by positivity)
      nlinarith only [H,H',hh.le]
    have hm : ∀ p ∈ L, p.1 ∈ Icc (0 : ℝ) 1 := by
      rw [← hL]
      intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact ⟨ha0.le.trans (hinputs q hq).2.1.1,(hinputs q hq).2.1.2⟩
    have hv : ∀ p ∈ L, ‖p.2‖ ≤ 1 ∧ p.1*(B*‖p.2‖^2) ≤ 1/2 := by
      intro p hp
      have hs : ‖p.2‖^2 ≤ chainEnergy L := by
        exact List.single_le_sum (fun a ha => by
          obtain ⟨q,_,rfl⟩ := List.mem_map.mp ha
          exact sq_nonneg _) _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
      have hE := chainEnergy_nonneg L
      have hsmall : B*‖p.2‖^2 ≤ 1/2 := by
        have H := mul_le_mul_of_nonneg_left hs hB
        nlinarith only [H,hshort,hE]
      refine ⟨by nlinarith [norm_nonneg p.2, mul_nonneg hB hE],?_⟩
      exact (mul_le_of_le_one_left (by positivity) (hm p hp).2).trans hsmall
    obtain ⟨_,hEN⟩ := hentropy r hr h hh
      (hh0.trans ((min_le_right _ _).trans (min_le_left _ _)))
      k (hk.trans (min_le_left _ _)) N hN
    have hinner := (hEN lam hlam).1
    have hlen : 0 < L.length := by
      dsimp only [L]
      rw [massPath,List.length_map,windowMassPath_length]
      omega
    have hjets : SpatialChainJets 9 B (L.drop (j.val+1)) f := by
      apply strictSuffix_spatialChainJets hlen
      intro n hn
      exact (hinner n (by simpa only [L,massPath,List.length_map] using hn)).of_le (by norm_num)
    have hsub : ∀ p ∈ L.drop (j.val+1), p ∈ L :=
      fun p hp => List.mem_of_mem_drop hp
    have htail : chainEnergy (L.drop (j.val+1)) ≤ chainEnergy L := by
      have H := congrArg chainEnergy (List.take_append_drop (j.val+1) L)
      rw [chainEnergy_append] at H
      linarith only [chainEnergy_nonneg (L.take (j.val+1)),H]
    apply (qBoundedJets_chain_sub_order 6 (L.drop (j.val+1)) hjets
      (fun p hp => hm p (hsub p hp)) (fun p hp => hv p (hsub p hp))).mono
    calc
      _ ≤ K*(A*h) := mul_le_mul_of_nonneg_left (htail.trans henergy) hK
      _ = _ := by ring
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

private theorem correction_window_direction_bound (β : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (α : ℝ → ℝ) (s h : ℝ), 0 ≤ h → ∀ N : ℕ,
      ∀ p ∈ windowKCurves β α s h N, ∀ k : ℝ, |k| ≤ 1/2 →
      ‖(p k).2‖ ≤ L*Real.sqrt (h/(N : ℝ)) ∧
        ‖deriv (fun t => (p t).2) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) ∧
        ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := window_direction_budget
  refine ⟨A*|β|,by positivity,?_⟩
  intro α s h hh N p hp k hk
  obtain ⟨σ,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact (hbound β h hh N i k hk).2

theorem scalarData_orderedInnerCorrection_spatialJets {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
      let α := cdf (D.μ : Measure ℝ)
      let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
      let delta := fun t x =>
        (fderiv ℝ (orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t) x (p t).2)^2-
          (fderiv ℝ (massVariationTerminal β α (r-h) h) x (p t).2)^2
      (∀ x, ContDiffAt ℝ 2 (fun t => delta t x) k) ∧
      QBoundedJets 6 (C*h^2/(N:ℝ)) (delta k) ∧
        QBoundedJets 4 (C*h^2/(N:ℝ)) (fun x => deriv (fun t => delta t x) k) ∧
        QBoundedJets 2 (C*h^2/(N:ℝ)) (fun x => deriv (deriv (fun t => delta t x)) k) := by
  by_cases hlu : l ≤ u
  · obtain ⟨C₀,hS,kapS,hC₀,hhS,hkapS,hsub⟩ := scalarData_orderedInner_sub_c7 D hl hu
    obtain ⟨C₁,hJ,hC₁,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D hl hu
    obtain ⟨L,hL,hdir⟩ := correction_window_direction_bound β
    obtain ⟨V,a0,hV,hV0,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    let A := C₀+C₁
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    let C := 256*(1+B+A)*A*L^2
    refine ⟨C,min (min hS (min hJ (min hE 1))) hV,min kapS (min kapE (1/4)),by
      dsimp only [C]; positivity,
      lt_min (lt_min hhS (lt_min hhJ (lt_min hhE (by norm_num)))) hhV,
      lt_min hkapS (lt_min hkapE (by norm_num)),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
    let f := massVariationTerminal β α (r-h) h
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let d := L*Real.sqrt (h/(N:ℝ))
    have hhbase := hh0.trans (min_le_left _ _)
    have hhV' := hh0.trans (min_le_right _ _)
    have hhS' := hhbase.trans (min_le_left _ _)
    have hhJ' := hhbase.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhE' := hhbase.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hh1 : h ≤ 1 := hhbase.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hkquarter : |k| ≤ 1/4 := hk.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hkhalf : |k| ≤ 1/2 := hkquarter.trans (by norm_num)
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' k
      (hk.trans ((min_le_right _ _).trans (min_le_left _ _))) N hN
    have hinner := (hEN lam hlam).1
    have hF : QPotential 7 B F := by
      simpa only [F,orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
        (hinner j.val (by rw [windowMassPath_length]; exact j.isLt)).of_le (by norm_num : 7 ≤ 10)
    have hf : QPotential 7 B f := by
      have H := hinner (12*N-1) (by rw [windowMassPath_length]; omega)
      have hlen : (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N) lam).length = 12*N := by
        rw [massPath,List.length_map,windowMassPath_length]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ 12*N)] at H
      have hdrop : (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N) lam).drop (12*N) = [] :=
        List.drop_eq_nil_iff.mpr (by rw [hlen])
      rw [hdrop] at H
      exact H.of_le (by norm_num : 7 ≤ 10)
    have hdiff : QBoundedJets 7 (A*h) (fun x => F x-f x) :=
      (hsub r hr h hh hhS' N hN lam hlam j k (hk.trans (min_le_left _ _))).mono
        (by dsimp only [A]; nlinarith only [mul_nonneg hC₁.le hh.le])
    have hbound : C₁*h ≤ A*h := by
      dsimp only [A]
      nlinarith only [mul_nonneg hC₀ hh.le]
    have hp := orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    obtain ⟨hv,hv₁,hv₂⟩ := hdir _ _ _ hh.le N p hp k hkhalf
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let qs := ps.drop (j.val+1)
    let FF := fun t => orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t
    let w := fun t => (p t).2
    have heF (t : ℝ) : vectorIncrementChain (qs.map (fun p => p t)) f = FF t := by
      dsimp only [FF,qs,ps,orderedInnerChain]
      rw [List.map_drop,windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
    have hnear : ∀ᶠ t in 𝓝 k, |t| ≤ 1/2 := by
      filter_upwards [continuous_abs.continuousAt.eventually
        (gt_mem_nhds (show |k| < 1/2 by linarith))] with t ht
      exact ht.le
    have hreg (t : ℝ) (ht : |t| ≤ 1/2) : ∀ p ∈ qs, ContDiffAt ℝ 2 p t := by
      intro p hp
      exact ((hvar r hr h hh hhV' N hN lam hlam t ht).2 p (List.mem_of_mem_drop hp)).1
    have hpos (t : ℝ) (ht : |t| ≤ 1/2) : ∀ p ∈ qs, 0 < (p t).1 := by
      intro p hp
      exact ha0.trans_le
        ((hvar r hr h hh hhV' N hN lam hlam t ht).2 p (List.mem_of_mem_drop hp)).2.1.1
    have hjoint (t : ℝ) (ht : |t| ≤ 1/2) (x : E) :
        ContDiffAt ℝ 2 (fun z : ℝ × E => FF z.1 z.2) (t,x) := by
      have HT := ParamChain.contDiffAt_curveChain qs hf (by norm_num)
        (hreg t ht) (hpos t ht) x
      simp_rw [heF] at HT
      exact HT
    have hFspace : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (FF t) x := by
      filter_upwards [hnear] with t ht x
      exact ((hjoint t ht x).comp x (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)
    have hparam : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun q => FF q x) t := by
      filter_upwards [hnear] with t ht x
      exact (hjoint t ht x).comp t (contDiffAt_id.prodMk contDiffAt_const)
    have hgradient (x v : E) : ContDiffAt ℝ 2 (fun t => fderiv ℝ (FF t) x v) k := by
      have HT := (ParamChain.contDiffAt_curveChain_spatial qs hf (by norm_num)
        (hreg k hkhalf) (hpos k hkhalf) x v).comp k
        (contDiffAt_id.prodMk contDiffAt_const)
      simp_rw [heF] at HT
      exact HT
    have hfirstNear : ∀ᶠ t in 𝓝 k, QBoundedJets 5 (A*h) (fun x => deriv (fun q => FF q x) t) := by
      filter_upwards [hnear] with t ht
      have H := ((hjets r hr h hh hhJ' N hN lam hlam j t ht).1.of_le (by norm_num : 5 ≤ 6)).mono hbound
      change QBoundedJets 5 (A*h) (fun x => iteratedDeriv 1 (fun q => FF q x) t) at H
      simpa only [iteratedDeriv_one] using H
    have hsecondNear : ∀ᶠ t in 𝓝 k,
        QBoundedJets 3 (A*h) (fun x => deriv (deriv (fun q => FF q x)) t) := by
      filter_upwards [hnear] with t ht
      have H := ((hjets r hr h hh hhJ' N hN lam hlam j t ht).2.of_le (by norm_num : 3 ≤ 4)).mono hbound
      change QBoundedJets 3 (A*h) (fun x => iteratedDeriv 2 (fun q => FF q x) t) at H
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H
    have hw : ContDiffAt ℝ 2 w k :=
      ((hvar r hr h hh hhV' N hN lam hlam k hkhalf).2 p hp).1.snd
    have H := qBoundedJets_movingInnerCorrection hFspace hparam hgradient
      hfirstNear hsecondNear hF hf hdiff hw (by dsimp only [d]; positivity : 0 ≤ d) hv hv₁ hv₂
    have hscale : 256*(1+B+A*h)*(A*h)*d^2 ≤ C*h^2/(N:ℝ) := by
      have hAh : A*h ≤ A := mul_le_of_le_one_right hA hh1
      calc
        _ ≤ 256*(1+B+A)*(A*h)*d^2 := by gcongr
        _ = C*h^2/(N:ℝ) := by
          dsimp only [d,C]
          rw [mul_pow,Real.sq_sqrt (div_nonneg hh.le (Nat.cast_nonneg N))]
          ring
    exact ⟨H.1,H.2.1.mono hscale,H.2.2.1.mono hscale,H.2.2.2.mono hscale⟩
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

theorem scalarData_window_innerCorrection_weakBias_sources {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ i j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
      let α := cdf (D.μ : Measure ℝ)
      let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam i
      let v := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
      let delta := fun t x =>
        (fderiv ℝ (orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t) x (v t).2)^2-
          (fderiv ℝ (massVariationTerminal β α (r-h) h) x (v t).2)^2
      let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam i k
      let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam i c k
      let g := delta k
      let a := fun x => deriv (fun t => delta t x) k
      let q := fun x => deriv (deriv (fun t => delta t x)) k
      let dm := deriv (fun t => (p t).1) k
      let ddm := deriv (deriv (fun t => (p t).1)) k
      let w := deriv (fun t => (p t).2) k
      let b := deriv (deriv (fun t => (p t).2)) k
      let M := C*h^2/(N:ℝ)*windowVariationEnergy k p
      QBoundedJets 4 M (fun x => tiltedAverage (p k).1 (p k).2 F g x-g x) ∧
        QBoundedJets 2 M (fun x => firstTiltedAverageSource (p k).1 (p k).2
          F (G 1) g a dm w x-a x) ∧
        ∀ x, |secondMovingAverageSource (p k).1 dm ddm (p k).2 w b
          F (G 1) (G 2) g a q x-q x| ≤ M := by
  obtain ⟨C,hC,kapC,hC0,hhC,hkapC,hjets⟩ :=
    scalarData_orderedInnerCorrection_spatialJets D hl hu
  obtain ⟨K,hK,kapK,hK0,hhK,hkapK,hsources⟩ := scalarData_window_weakBias_sources D hl hu
  refine ⟨3*K*C,min hC hK,min kapC kapK,by positivity,
    lt_min hhC hhK,lt_min hkapC hkapK,?_⟩
  intro r hr h hh hh0 N hN lam hlam i j k hk
  dsimp only
  obtain ⟨_,hg,ha,hq⟩ := hjets r hr h hh (hh0.trans (min_le_left _ _))
    N hN lam hlam j k (hk.trans (min_le_left _ _))
  have H := hsources r hr h hh (hh0.trans (min_le_right _ _)) N hN lam hlam i k
    (hk.trans (min_le_right _ _)) _ _ _ _ _ _ hg ha hq
  dsimp only at H
  have he := windowVariationEnergy_nonneg k
    (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
      (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam i)
  have hD : 0 ≤ C*h^2/(N:ℝ) := by positivity
  refine ⟨H.1.mono ?_,H.2.1.mono ?_,?_⟩
  · have hbase := mul_nonneg hK0 (mul_nonneg hD he)
    calc
      _ = K*(C*h^2/(N:ℝ)*windowVariationEnergy k
          (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam i)) := by ring
      _ ≤ 3*(K*(C*h^2/(N:ℝ)*windowVariationEnergy k
          (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam i))) := by linarith
      _ = _ := by ring
  · have hbase := mul_nonneg hK0 (mul_nonneg hD he)
    calc
      _ = 2*(K*(C*h^2/(N:ℝ)*windowVariationEnergy k
          (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam i))) := by ring
      _ ≤ 3*(K*(C*h^2/(N:ℝ)*windowVariationEnergy k
          (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam i))) := by linarith
      _ = _ := by ring
  · intro x
    exact (H.2.2 x).trans_eq (by ring)

end SKBarriers2.Corner
