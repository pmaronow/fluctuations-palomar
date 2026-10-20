module

public import SKBarriers2.Corner.PathEnergyGeneratorSum
public import SKBarriers2.Corner.PathEnergyInner2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem generator_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) x).hasFDerivAt
  have H := hd.clm_apply (hasFDerivAt_const v x)
  have H' := congrArg (fun D : E →L[ℝ] ℝ => D w) H.fderiv
  change fderiv ℝ (fun y => fderiv ℝ f y v) x w =
    fderiv ℝ f x 0 + fderiv ℝ (fderiv ℝ f) x w v at H'
  simpa only [map_zero, zero_add] using H'

theorem hasDerivAt_hessian_of_uniform_jets {F G : ℝ → E → ℝ} {B k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (F t))
    (hd : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (G t x) t)
    (hG : ∀ᶠ t in 𝓝 k, QBoundedJets 3 B (G t)) (x v w : E) :
    HasDerivAt (fun t => fderiv ℝ (fderiv ℝ (F t)) x v w)
      (fderiv ℝ (fderiv ℝ (G k)) x v w) k := by
  let H := fun t y => fderiv ℝ (F t) y w
  let J := fun t y => fderiv ℝ (G t) y w
  have hFdiff : ∀ᶠ t in 𝓝 k, ∀ y, DifferentiableAt ℝ (F t) y := by
    filter_upwards [hF] with t ht y
    exact ht.differentiable (by norm_num) y
  have hHdiff : ∀ᶠ t in 𝓝 k, ∀ y, DifferentiableAt ℝ (H t) y := by
    filter_upwards [hF] with t ht y
    exact (((ht.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)) y
  have hHJ : ∀ᶠ t in 𝓝 k, ∀ y, HasDerivAt (fun q => H q y) (J t y) t := by
    filter_upwards [eventually_eventually_nhds.mpr hFdiff,
      eventually_eventually_nhds.mpr hd, eventually_eventually_nhds.mpr hG] with t hFt hdt hGt y
    exact hasDerivAt_spatial_of_uniform_jets hFt hdt
      (hGt.mono (fun q hq => hq.of_le (by norm_num : 2 ≤ 3))) y w
  have hJ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 (B * ‖w‖) (J t) := by
    filter_upwards [hG] with t ht
    exact ht.derivativeJets.apply_const w
  have HH := hasDerivAt_spatial_of_uniform_jets hHdiff hHJ hJ x v
  have hleft : (fun t => fderiv ℝ (H t) x v) =ᶠ[𝓝 k]
      fun t => fderiv ℝ (fderiv ℝ (F t)) x v w := by
    filter_upwards [hF] with t ht
    exact generator_fderiv_apply ht x w v
  have hright := generator_fderiv_apply
    (hG.self_of_nhds.smooth.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) x w v
  rw [hright] at HH
  exact HH.congr_of_eventuallyEq hleft.symm

private theorem hessian_basis_sum (H : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    H v w = ∑ i : Fin 3, ∑ j : Fin 3, v i * w j * H (Pi.single i 1) (Pi.single j 1) := by
  have hv : v = ∑ i : Fin 3, v i • Pi.single i 1 := by
    ext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  have hw : w = ∑ i : Fin 3, w i • Pi.single i 1 := by
    ext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  have hx : H v = ∑ i : Fin 3, v i • H (Pi.single i 1) := by
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul]
  rw [hx]
  simp only [sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hy : H (Pi.single i 1) w =
      ∑ j : Fin 3, w j * H (Pi.single i 1) (Pi.single j 1) := by
    conv_lhs => rw [hw]
    simp only [map_sum,map_smul,smul_eq_mul]
  rw [hy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hasDerivAt_moving_bilinear {H H₁ : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {v w : ℝ → E} {v₁ w₁ : E} {k : ℝ}
    (hH : ∀ i j : Fin 3, HasDerivAt
      (fun t => H t (Pi.single i 1) (Pi.single j 1))
      (H₁ k (Pi.single i 1) (Pi.single j 1)) k)
    (hv : HasDerivAt v v₁ k) (hw : HasDerivAt w w₁ k) :
    HasDerivAt (fun t => H t (v t) (w t))
      (H₁ k (v k) (w k) + H k v₁ (w k) + H k (v k) w₁) k := by
  have hvi (i : Fin 3) := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt k hv
  have hwi (i : Fin 3) := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt k hw
  have HH := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    (fun i _ => HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
      (fun j _ => ((hvi i).mul (hwi j)).mul (hH i j)))
  have he : (fun t => ∑ i : Fin 3, ∑ j : Fin 3,
      v t i * w t j * H t (Pi.single i 1) (Pi.single j 1)) =
      fun t => H t (v t) (w t) := funext (fun t => (hessian_basis_sum _ _ _).symm)
  simp only [Function.comp_def, Pi.mul_apply, ContinuousLinearMap.proj_apply] at HH
  rw [he] at HH
  convert HH using 1
  rw [hessian_basis_sum (H₁ k), hessian_basis_sum (H k) v₁,
    hessian_basis_sum (H k) (v k) w₁, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hasDerivAt_moving_hessian_of_uniform_jets
    {F G : ℝ → E → ℝ} {v w : ℝ → E} {v₁ w₁ : E} {B k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (F t))
    (hd : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (G t x) t)
    (hG : ∀ᶠ t in 𝓝 k, QBoundedJets 3 B (G t))
    (hv : HasDerivAt v v₁ k) (hw : HasDerivAt w w₁ k) (x : E) :
    HasDerivAt (fun t => fderiv ℝ (fderiv ℝ (F t)) x (v t) (w t))
      (fderiv ℝ (fderiv ℝ (G k)) x (v k) (w k) +
        fderiv ℝ (fderiv ℝ (F k)) x v₁ (w k) +
        fderiv ℝ (fderiv ℝ (F k)) x (v k) w₁) k := by
  exact hasDerivAt_moving_bilinear
    (H := fun t => fderiv ℝ (fderiv ℝ (F t)) x)
    (H₁ := fun t => fderiv ℝ (fderiv ℝ (G t)) x)
    (fun i j => hasDerivAt_hessian_of_uniform_jets hF hd hG x
      (Pi.single i 1) (Pi.single j 1)) hv hw

theorem moving_hessian_twoJet {F F₁ F₂ : ℝ → E → ℝ}
    {v v₁ v₂ : ℝ → E} {A H k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (F t))
    (hd₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (F₁ t x) t)
    (hd₁ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F₁ q x) (F₂ t x) t)
    (hF₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 A (F₁ t))
    (hF₂ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 H (F₂ t))
    (hv : ∀ᶠ t in 𝓝 k, HasDerivAt v (v₁ t) t)
    (hv₁ : HasDerivAt v₁ (v₂ k) k) (x : E) :
    deriv (fun t => fderiv ℝ (fderiv ℝ (F t)) x (v t) (v t)) k =
        fderiv ℝ (fderiv ℝ (F₁ k)) x (v k) (v k) +
          2 * fderiv ℝ (fderiv ℝ (F k)) x (v k) (v₁ k) ∧
    deriv (deriv (fun t => fderiv ℝ (fderiv ℝ (F t)) x (v t) (v t))) k =
        fderiv ℝ (fderiv ℝ (F₂ k)) x (v k) (v k) +
          4 * fderiv ℝ (fderiv ℝ (F₁ k)) x (v k) (v₁ k) +
          2 * fderiv ℝ (fderiv ℝ (F k)) x (v₁ k) (v₁ k) +
          2 * fderiv ℝ (fderiv ℝ (F k)) x (v k) (v₂ k) := by
  have hfirst := hasDerivAt_moving_hessian_of_uniform_jets hF hd₀ hF₁
    hv.self_of_nhds hv.self_of_nhds x
  have he : deriv (fun t => fderiv ℝ (fderiv ℝ (F t)) x (v t) (v t)) =ᶠ[𝓝 k]
      fun t => fderiv ℝ (fderiv ℝ (F₁ t)) x (v t) (v t) +
        fderiv ℝ (fderiv ℝ (F t)) x (v₁ t) (v t) +
        fderiv ℝ (fderiv ℝ (F t)) x (v t) (v₁ t) := by
    filter_upwards [eventually_eventually_nhds.mpr hF,
      eventually_eventually_nhds.mpr hd₀,eventually_eventually_nhds.mpr hF₁,hv]
      with t hFt hdt hF₁t hvt
    exact (hasDerivAt_moving_hessian_of_uniform_jets hFt hdt hF₁t hvt hvt x).deriv
  have hF₁smooth : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (F₁ t) := by
    filter_upwards [hF₁] with t ht
    exact ht.smooth.of_le (by norm_num)
  have hleft := hasDerivAt_moving_hessian_of_uniform_jets hF₁smooth hd₁ hF₂
    hv.self_of_nhds hv.self_of_nhds x
  have hmiddle := hasDerivAt_moving_hessian_of_uniform_jets hF hd₀ hF₁
    hv₁ hv.self_of_nhds x
  have hright := hasDerivAt_moving_hessian_of_uniform_jets hF hd₀ hF₁
    hv.self_of_nhds hv₁ x
  have hs₀ : IsSymmSndFDerivAt ℝ (F k) x :=
    hF.self_of_nhds.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hs₁ : IsSymmSndFDerivAt ℝ (F₁ k) x :=
    hF₁smooth.self_of_nhds.contDiffAt.isSymmSndFDerivAt (by norm_num)
  refine ⟨?_,?_⟩
  · convert hfirst.deriv using 1
    rw [hs₀ (v₁ k) (v k)]
    ring
  · rw [he.deriv_eq]
    convert ((hleft.add hmiddle).add hright).deriv using 1
    rw [hs₁ (v₁ k) (v k),hs₀ (v₂ k) (v k)]
    ring

theorem generatorHessianJet_eq_iteratedDeriv {F F₁ F₂ : ℝ → E → ℝ}
    {v v₁ v₂ : ℝ → E} {A H k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (F t))
    (hd₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (F₁ t x) t)
    (hd₁ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F₁ q x) (F₂ t x) t)
    (hF₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 A (F₁ t))
    (hF₂ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 H (F₂ t))
    (hv : ∀ᶠ t in 𝓝 k, HasDerivAt v (v₁ t) t)
    (hv₁ : HasDerivAt v₁ (v₂ k) k) (c : Fin 3) (x : E) :
    generatorHessianJet (F k) (F₁ k) (F₂ k) (v k) (v₁ k) (v₂ k) c x =
      iteratedDeriv c.val
        (fun t => fderiv ℝ (fderiv ℝ (F t)) x (v t) (v t) / 2) k := by
  have Htwo := moving_hessian_twoJet hF hd₀ hd₁ hF₁ hF₂ hv hv₁ x
  fin_cases c
  · simp [generatorHessianJet]
  · rw [iteratedDeriv_div_const,iteratedDeriv_one,Htwo.1]
    norm_num [generatorHessianJet]
    ring
  · rw [iteratedDeriv_div_const]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rw [Htwo.2]
    norm_num [generatorHessianJet]
    ring

theorem hasDerivAt_generatorHessianJet_zero {F F₁ F₂ : ℝ → E → ℝ}
    {v v₁ v₂ : ℝ → E} {A k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (F t))
    (hd : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (F₁ t x) t)
    (hF₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 A (F₁ t))
    (hv : HasDerivAt v (v₁ k) k) (x : E) :
    HasDerivAt
      (fun t => generatorHessianJet (F t) (F₁ t) (F₂ t) (v t) (v₁ t) (v₂ t) 0 x)
      (generatorHessianJet (F k) (F₁ k) (F₂ k) (v k) (v₁ k) (v₂ k) 1 x) k := by
  have H := (hasDerivAt_moving_hessian_of_uniform_jets hF hd hF₁ hv hv x).div_const 2
  have hs : IsSymmSndFDerivAt ℝ (F k) x :=
    hF.self_of_nhds.contDiffAt.isSymmSndFDerivAt (by norm_num)
  simp only [generatorHessianJet,Matrix.cons_val_zero,Matrix.cons_val_one]
  convert H using 1
  rw [hs (v₁ k) (v k)]
  ring

theorem hasDerivAt_generatorHessianJet_one {F F₁ F₂ : ℝ → E → ℝ}
    {v v₁ v₂ : ℝ → E} {A H k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (F t))
    (hd₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (F₁ t x) t)
    (hd₁ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F₁ q x) (F₂ t x) t)
    (hF₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 A (F₁ t))
    (hF₂ : ∀ᶠ t in 𝓝 k, QBoundedJets 3 H (F₂ t))
    (hv : HasDerivAt v (v₁ k) k) (hv₁ : HasDerivAt v₁ (v₂ k) k) (x : E) :
    HasDerivAt
      (fun t => generatorHessianJet (F t) (F₁ t) (F₂ t) (v t) (v₁ t) (v₂ t) 1 x)
      (generatorHessianJet (F k) (F₁ k) (F₂ k) (v k) (v₁ k) (v₂ k) 2 x) k := by
  have hF₁smooth : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (F₁ t) := by
    filter_upwards [hF₁] with t ht
    exact ht.smooth.of_le (by norm_num)
  have HA := (hasDerivAt_moving_hessian_of_uniform_jets hF₁smooth hd₁ hF₂ hv hv x).div_const 2
  have HB := hasDerivAt_moving_hessian_of_uniform_jets hF hd₀ hF₁ hv hv₁ x
  have hs : IsSymmSndFDerivAt ℝ (F₁ k) x :=
    hF₁smooth.self_of_nhds.contDiffAt.isSymmSndFDerivAt (by norm_num)
  change HasDerivAt
    (fun t => fderiv ℝ (fderiv ℝ (F₁ t)) x (v t) (v t) / 2 +
      fderiv ℝ (fderiv ℝ (F t)) x (v t) (v₁ t))
    (fderiv ℝ (fderiv ℝ (F₂ k)) x (v k) (v k) / 2 +
      2 * fderiv ℝ (fderiv ℝ (F₁ k)) x (v k) (v₁ k) +
      fderiv ℝ (fderiv ℝ (F k)) x (v₁ k) (v₁ k) +
      fderiv ℝ (fderiv ℝ (F k)) x (v k) (v₂ k)) k
  convert HA.add HB using 1
  rw [hs (v₁ k) (v k)]
  ring

end SKBarriers2.StepCalculus
