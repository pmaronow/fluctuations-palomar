module

public import SKBarriers2.Corner.PathEnergyInner4

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem symmetric_quadratic_hasDerivAt (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) {v : ℝ → E} {w : E} {k : ℝ}
    (hv : HasDerivAt v w k) :
    HasDerivAt (fun t => H (v t) (v t)) (2*H (v k) w) k := by
  have h := (H.hasFDerivAt.comp_hasDerivAt k hv).clm_apply hv
  convert h using 1
  · rfl
  · change 2*H (v k) w = H w (v k)+H (v k) w
    rw [hs w (v k)]
    ring

theorem stepQuadraticIncrement_eq_hessian {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) (m : ℝ) (v x : E) :
    stepQuadraticIncrement m v f x =
      m*(fderiv ℝ f x v)^2/2+fderiv ℝ (fderiv ℝ f) x v v/2 := by
  dsimp only [stepQuadraticIncrement,directionalJet]
  rw [fderiv_directional_apply (hf.smooth.of_le (by norm_num))]

theorem hasDerivAt_stepQuadraticIncrement {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {p : ℝ → ℝ × E} {dp : ℝ × E} {k : ℝ}
    (hp : HasDerivAt p dp k) (x : E) :
    HasDerivAt (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x)
      (stepQuadraticFirstSource (p k).1 (p k).2 f (fun _ => 0) dp.1 dp.2 x) k := by
  let L := fderiv ℝ f x
  let H := fderiv ℝ (fderiv ℝ f) x
  have hs : ∀ v w, H v w = H w v :=
    hf.smooth.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hm : HasDerivAt (fun t => (p t).1) dp.1 k :=
    (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt k hp
  have hv : HasDerivAt (fun t => (p t).2) dp.2 k :=
    (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt k hp
  have hL := L.hasFDerivAt.comp_hasDerivAt k hv
  have hH := symmetric_quadratic_hasDerivAt H hs hv
  have h := ((hm.mul (hL.pow 2)).div_const 2).add (hH.div_const 2)
  convert h using 1
  · funext t
    exact stepQuadraticIncrement_eq_hessian hf (p t).1 (p t).2 x
  · simp only [stepQuadraticFirstSource,fderiv_fun_const,Pi.zero_apply,zero_apply,
      directionalJet,mul_zero,zero_add,add_zero,zero_div]
    dsimp only [directionSource,L,H,Function.comp_def,Pi.pow_apply,Pi.mul_apply,Pi.add_apply]
    ring

theorem contDiffAt_stepQuadraticIncrement {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {p : ℝ → ℝ × E} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : E) :
    ContDiffAt ℝ 2 (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x) k := by
  have hL := (fderiv ℝ f x).contDiff.contDiffAt.comp k hp.snd
  have hH := ((fderiv ℝ (fderiv ℝ f) x).contDiff.contDiffAt.comp k hp.snd).clm_apply hp.snd
  have H := ((hp.fst.mul (hL.pow 2)).div_const 2).add (hH.div_const 2)
  convert H using 1
  funext t
  exact stepQuadraticIncrement_eq_hessian hf (p t).1 (p t).2 x

theorem contDiffAt_pathQuadraticSum {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (x : E) :
    ContDiffAt ℝ 2 (fun t => pathQuadraticSum f (ps.map (fun p => p t)) x) k := by
  induction ps with
  | nil => exact contDiffAt_const
  | cons p ps ih =>
    exact (contDiffAt_stepQuadraticIncrement hf (hreg p (by simp)) x).add
      (ih (fun q hq => hreg q (by simp [hq])))

theorem stepQuadraticIncrement_twoJet {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {p : ℝ → ℝ × E} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : E) :
    let m := (p k).1
    let v := (p k).2
    let dm := deriv (fun t => (p t).1) k
    let ddm := deriv (deriv (fun t => (p t).1)) k
    let w := deriv (fun t => (p t).2) k
    let b := deriv (deriv (fun t => (p t).2)) k
    deriv (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x) k =
      stepQuadraticFirstSource m v f (fun _ => 0) dm w x ∧
    deriv (deriv (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x)) k =
      stepQuadraticSecondSource m v f (fun _ => 0) (fun _ => 0) dm ddm w b x := by
  dsimp only
  let L := fderiv ℝ f x
  let H := fderiv ℝ (fderiv ℝ f) x
  have hs : ∀ v w, H v w = H w v :=
    hf.smooth.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hm := (hp.fst.differentiableAt (by norm_num)).hasDerivAt
  have hv := (hp.snd.differentiableAt (by norm_num)).hasDerivAt
  have hdm := ((hp.fst.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hw := ((hp.snd.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hL := L.hasFDerivAt.comp_hasDerivAt k hv
  have hLw := L.hasFDerivAt.comp_hasDerivAt k hw
  have hH := (H.hasFDerivAt.comp_hasDerivAt k hv).clm_apply hw
  have hfirst : deriv (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x) =ᶠ[𝓝 k]
      fun t => (deriv (fun a => (p a).1) t/2)*(L (p t).2)^2+
        (p t).1*L (p t).2*L (deriv (fun a => (p a).2) t)+
        H (p t).2 (deriv (fun a => (p a).2) t) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    have h := hasDerivAt_stepQuadraticIncrement hf
      (ht.differentiableAt (by norm_num)).hasDerivAt x
    rw [h.deriv]
    simp only [stepQuadraticFirstSource,fderiv_fun_const,Pi.zero_apply,zero_apply,
      directionalJet,mul_zero,zero_add,add_zero,zero_div]
    dsimp only [directionSource,L,H,Function.comp_def,Pi.pow_apply,Pi.mul_apply,Pi.add_apply]
    rw [show (deriv p t).1 = deriv (fun a => (p a).1) t from
      ((ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t
        (ht.differentiableAt (by norm_num)).hasDerivAt).deriv.symm,
      show (deriv p t).2 = deriv (fun a => (p a).2) t from
      ((ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t
        (ht.differentiableAt (by norm_num)).hasDerivAt).deriv.symm]
    ring
  have hfirstAt := hfirst.self_of_nhds
  refine ⟨?_,?_⟩
  · rw [hfirstAt]
    simp only [stepQuadraticFirstSource,fderiv_fun_const,Pi.zero_apply,zero_apply,
      directionalJet,mul_zero,zero_add,add_zero,zero_div]
    dsimp only [directionSource,L,H,Function.comp_def,Pi.pow_apply,Pi.mul_apply,Pi.add_apply]
    ring
  · rw [hfirst.deriv_eq]
    have h := (((hdm.div_const 2).mul (hL.pow 2)).add
      ((hm.mul hL).mul hLw)).add hH
    convert h.deriv using 1
    · rfl
    · simp only [stepQuadraticSecondSource,mixedDirectionSource,fderiv_fun_const,fderiv_zero,Pi.zero_apply,
      zero_apply,directionalJet,zero_mul,mul_zero,
      zero_add,add_zero,zero_div]
      dsimp only [directionSource,L,H,Function.comp_def,Pi.mul_apply,Pi.add_apply,Pi.pow_apply]
      ring

theorem contDiffAt_pathGenerator_curve {f g : E → ℝ}
    (hg : ContDiff ℝ 2 g) {p : ℝ → ℝ × E} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : E) :
    ContDiffAt ℝ 2 (fun t => pathGenerator (p t).1 (p t).2 f g x) k := by
  have hL₀ := (fderiv ℝ f x).contDiff.contDiffAt.comp k hp.snd
  have hL₁ := (fderiv ℝ g x).contDiff.contDiffAt.comp k hp.snd
  have hH := ((fderiv ℝ (fderiv ℝ g) x).contDiff.contDiffAt.comp k hp.snd).clm_apply hp.snd
  have H := ((hp.fst.mul hL₀).mul hL₁).add (hH.div_const 2)
  convert H using 1
  funext t
  dsimp only [pathGenerator,directionalJet]
  rw [fderiv_directional_apply hg]
  dsimp only [Function.comp_def]

theorem contDiffAt_pathGeneratorSum_curve {f g : E → ℝ}
    (hg : ContDiff ℝ 2 g) (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (x : E) :
    ContDiffAt ℝ 2 (fun t => pathGeneratorSum f g (ps.map (fun p => p t)) x) k := by
  induction ps with
  | nil => exact contDiffAt_const
  | cons p ps ih =>
    exact (contDiffAt_pathGenerator_curve hg (hreg p (by simp)) x).add
      (ih (fun q hq => hreg q (by simp [hq])))

end SKBarriers2.StepCalculus
