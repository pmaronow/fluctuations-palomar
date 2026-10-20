module

public import SKBarriers2.Analysis.ParamStep4

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set Filter OAI.SK.Analytic
namespace SKBarriers2.Corner
open ParamChain
local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local instance movingSmoothLinearNormedAddCommGroup : NormedAddCommGroup (P × E →L[ℝ] ℝ) := inferInstance
local instance movingSmoothLinearNormedSpace : NormedSpace ℝ (P × E →L[ℝ] ℝ) := inferInstance

private theorem smooth_spatial_slice_jets {F : P × E → ℝ} (hF : ContDiff ℝ 2 F)
    (q u : P) (y w : E) :
    fderiv ℝ (fun z => F (q,z)) y w = fderiv ℝ F (q,y) (0,w) ∧
    fderiv ℝ (fderiv ℝ (fun z => F (q,z))) y w w =
      fderiv ℝ (fderiv ℝ F) (q,y) (0,w) (0,w) ∧
    fderiv ℝ (fun z => fderiv ℝ F (q,z) (u,0)) y w =
      fderiv ℝ (fderiv ℝ F) (q,y) (0,w) (u,0) := by
  let L : E →L[ℝ] P × E := ContinuousLinearMap.inr ℝ P E
  have heq (z : E) : L z + (q,0) = (q,z) := by ext <;> simp [L]
  have h1 := first_affine_apply hF L (q,0) y w
  have h2 := second_affine_apply hF L (q,0) y w w
  simp_rw [heq] at h1 h2
  have hp : HasFDerivAt (fun z : E => (q,z)) L y :=
    (hasFDerivAt_const q y).prodMk (hasFDerivAt_id y)
  have hd := (((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    (q,y)).hasFDerivAt.comp y hp).clm_apply (hasFDerivAt_const (u,(0 : E)) y)
  have h3 := congrArg (fun D : E →L[ℝ] ℝ => D w) hd.fderiv
  change fderiv ℝ (fun z => fderiv ℝ F (q,z) (u,0)) y w =
    fderiv ℝ F (q,y) 0 + fderiv ℝ (fderiv ℝ F) (q,y) (0,w) (u,0) at h3
  exact ⟨h1, h2, by simpa only [map_zero, zero_add] using h3⟩

private theorem smooth_mixed_parameter_spatial_jet {F : P × E → ℝ} (hF : ContDiff ℝ 2 F)
    (q u : P) (y w : E) (t : ℝ) :
    fderiv ℝ (fderiv ℝ F) (q,y) (u,t • w) (u,t • w) =
      fderiv ℝ (fderiv ℝ F) (q,y) (u,0) (u,0) +
        2 * t * fderiv ℝ (fun z => fderiv ℝ F (q,z) (u,0)) y w +
        t ^ 2 * fderiv ℝ (fderiv ℝ (fun z => F (q,z))) y w w := by
  have hsplit : (u,t • w) = (u,(0 : E)) + t • ((0 : P),w) := by ext <;> simp
  have hs := (hF.contDiffAt.isSymmSndFDerivAt (by norm_num) :
    IsSymmSndFDerivAt ℝ F (q,y)) (u,0) (0,w)
  obtain ⟨_, h2, h3⟩ := smooth_spatial_slice_jets hF q u y w
  rw [hsplit]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [hs, ← h2, ← h3]
  ring

private theorem second_composite_curve {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : Y → ℝ} (hF : ContDiff ℝ 2 F) {p : ℝ → Y} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) :
    deriv (deriv (fun t => F (p t))) k =
      fderiv ℝ (fderiv ℝ F) (p k) (deriv p k) (deriv p k) +
        fderiv ℝ F (p k) (deriv (deriv p) k) := by
  have hd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have heq : deriv (fun t => F (p t)) =ᶠ[𝓝 k] fun t => fderiv ℝ F (p t) (deriv p t) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact ((hF.differentiable (by norm_num) (p t)).hasFDerivAt.comp_hasDerivAt t
      (ht.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hD := ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    (p k)).hasFDerivAt.comp_hasDerivAt k hd
  rw [heq.deriv_eq]
  exact (hD.clm_apply hdd).deriv

theorem smooth_moving_endpoint_jets {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {F : P × (Fin 3 → ℝ) → ℝ}
    (hF : ContDiff ℝ 2 F) {p : ℝ → P} {x : ℝ → Fin 3 → ℝ} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (hx : ContDiffAt ℝ 2 x k) :
    let f := fun y => F (p k,y)
    let G := fun y => deriv (fun t => F (p t,y)) k
    let H := fun y => deriv (deriv (fun t => F (p t,y))) k
    deriv (fun t => F (p t,x t)) k = G (x k) + fderiv ℝ f (x k) (deriv x k) ∧
      deriv (deriv (fun t => F (p t,x t))) k =
        H (x k) + 2 * fderiv ℝ G (x k) (deriv x k) +
          fderiv ℝ (fderiv ℝ f) (x k) (deriv x k) (deriv x k) +
            fderiv ℝ f (x k) (deriv (deriv x) k) := by
  dsimp only
  let c : ℝ → P × E := fun t => (p t,x t)
  have hc : ContDiffAt ℝ 2 c k := hp.prodMk hx
  have hpd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hxd := (hx.differentiableAt (by norm_num)).hasDerivAt
  have hc₁ : deriv c k = (deriv p k,deriv x k) := (hpd.prodMk hxd).deriv
  have hnear : deriv c =ᶠ[𝓝 k] fun t => (deriv p t,deriv x t) := by
    filter_upwards [hp.eventually (by norm_num), hx.eventually (by norm_num)] with t ht hs
    exact (((ht.differentiableAt (by norm_num)).hasDerivAt).prodMk
      ((hs.differentiableAt (by norm_num)).hasDerivAt)).deriv
  have hc₂ : deriv (deriv c) k = (deriv (deriv p) k,deriv (deriv x) k) := by
    rw [hnear.deriv_eq]
    exact ((((hp.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt).prodMk
      (((hx.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt)).deriv
  have hG : (fun y => deriv (fun t => F (p t,y)) k) =
      fun y => fderiv ℝ F (p k,y) (deriv p k,0) := by
    funext y
    exact ((hF.differentiable (by norm_num) (p k,y)).hasFDerivAt.comp_hasDerivAt k
      (hpd.prodMk (hasDerivAt_const k y))).deriv
  have hsplit (u : P) (w : E) :
      fderiv ℝ F (p k,x k) (u,w) = fderiv ℝ F (p k,x k) (u,0) +
        fderiv ℝ (fun y => F (p k,y)) (x k) w := by
    have he : (u,w) = (u,(0 : E)) + ((0 : P),w) := by ext <;> simp
    rw [he, map_add, ← (smooth_spatial_slice_jets hF (p k) u (x k) w).1]
  constructor
  · rw [congrFun hG (x k)]
    exact (((hF.differentiable (by norm_num) (p k,x k)).hasFDerivAt.comp_hasDerivAt k
      (hpd.prodMk hxd)).deriv).trans (hsplit _ _)
  · have hmixed := smooth_mixed_parameter_spatial_jet hF (p k) (deriv p k)
      (x k) (deriv x k) 1
    simp only [one_smul, mul_one, one_pow, one_mul] at hmixed
    change deriv (deriv (fun t => F (c t))) k = _
    rw [second_composite_curve hF hc, hc₁, hc₂]
    change fderiv ℝ (fderiv ℝ F) (p k,x k) (deriv p k,deriv x k)
      (deriv p k,deriv x k) + fderiv ℝ F (p k,x k) (deriv (deriv p) k,deriv (deriv x) k) = _
    rw [hmixed, hsplit, hG, ParamChain.second_parameter_curve hF hp (x k)]
    ring

theorem paramSmooth_moving_endpoint_jets {F : P × E → ℝ}
    (hF : ParamSmooth F) {p : ℝ → P} {x : ℝ → E} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (hx : ContDiffAt ℝ 2 x k) :
    let f := fun y => F (p k,y)
    let G := fun y => deriv (fun t => F (p t,y)) k
    let H := fun y => deriv (deriv (fun t => F (p t,y))) k
    deriv (fun t => F (p t,x t)) k = G (x k) + fderiv ℝ f (x k) (deriv x k) ∧
      deriv (deriv (fun t => F (p t,x t))) k =
        H (x k) + 2 * fderiv ℝ G (x k) (deriv x k) +
          fderiv ℝ (fderiv ℝ f) (x k) (deriv x k) (deriv x k) +
            fderiv ℝ f (x k) (deriv (deriv x) k) :=
  smooth_moving_endpoint_jets hF.1 hp hx

end SKBarriers2.Corner
