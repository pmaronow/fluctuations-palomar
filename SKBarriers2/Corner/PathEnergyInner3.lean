module

public import SKBarriers2.Corner.PathEnergyInner2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

open SKBarriers2.Corner
local notation "E" => (Fin 3 → ℝ)

theorem chainEnergy_le_windowVariationEnergy (ps : List (ℝ → ℝ × E)) (k : ℝ) :
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

theorem fderiv_directional_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fderiv ℝ f) x w v := by
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) x).hasFDerivAt
  have H := hd.clm_apply (hasFDerivAt_const v x)
  have H' := congrArg (fun D : E →L[ℝ] ℝ => D w) H.fderiv
  change fderiv ℝ (fun y => fderiv ℝ f y v) x w =
    fderiv ℝ f x 0+fderiv ℝ (fderiv ℝ f) x w v at H'
  simpa only [map_zero,zero_add] using H'

theorem directional_fderiv_comm {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (v w x : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [fderiv_directional_apply hf,fderiv_directional_apply hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num) w v

theorem fderiv_directionalJet_two {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) (v w x : E) :
    fderiv ℝ (directionalJet v 2 f) x w =
      directionalJet v 2 (fun y => fderiv ℝ f y w) x := by
  have hv : ContDiff ℝ 2 (fun y => fderiv ℝ f y v) :=
    (hf.directional v).smooth
  have hi : (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y w) =
      fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v := by
    funext y
    exact directional_fderiv_comm (hf.smooth.of_le (by norm_num)) v w y
  change fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v) x w = _
  rw [directional_fderiv_comm hv v w x,hi]
  rfl

def stepQuadraticIncrement (m : ℝ) (v : E) (f : E → ℝ) (x : E) : ℝ :=
  m*(fderiv ℝ f x v)^2/2+directionalJet v 2 f x/2

theorem fderiv_stepQuadraticIncrement {B : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (m : ℝ) (v w x : E) :
    fderiv ℝ (stepQuadraticIncrement m v f) x w =
      pathGenerator m v f (fun y => fderiv ℝ f y w) x := by
  have hd : Differentiable ℝ (fun y => fderiv ℝ f y v) :=
    (hf.directional v).smooth.differentiable (by norm_num)
  have hh : Differentiable ℝ (directionalJet v 2 f) :=
    (directionalJet_smooth (r := 2) 1 hf v).smooth.differentiable (by norm_num)
  have he : stepQuadraticIncrement m v f = fun y =>
      (m/2)*(fderiv ℝ f y v*fderiv ℝ f y v)+(1/2:ℝ)*directionalJet v 2 f y := by
    funext y
    dsimp only [stepQuadraticIncrement]
    ring
  have H := ((((hd x).hasFDerivAt.mul (hd x).hasFDerivAt).const_mul (m/2)).add
    ((hh x).hasFDerivAt.const_mul (1/2:ℝ))).fderiv
  change fderiv ℝ (fun y => (m/2)*(fderiv ℝ f y v*fderiv ℝ f y v)+
    (1/2:ℝ)*directionalJet v 2 f y) x = _ at H
  rw [he,H]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [fderiv_directionalJet_two (hf.of_le (by norm_num)),
    directional_fderiv_comm (hf.smooth.of_le (by norm_num)) v w x]
  dsimp only [pathGenerator]
  ring

def pathQuadraticSum (f : E → ℝ) : List (ℝ × E) → E → ℝ
  | [], _ => 0
  | p::ps, x => stepQuadraticIncrement p.1 p.2 f x+pathQuadraticSum f ps x

theorem differentiable_pathQuadraticSum {B : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (ps : List (ℝ × E)) :
    Differentiable ℝ (pathQuadraticSum f ps) := by
  have hd (p : ℝ × E) : Differentiable ℝ (stepQuadraticIncrement p.1 p.2 f) := by
    have h₁ : Differentiable ℝ (fun y : E => fderiv ℝ f y p.2) :=
      (hf.directional p.2).smooth.differentiable (by norm_num)
    have h₂ : Differentiable ℝ (directionalJet p.2 2 f) :=
      (directionalJet_smooth (r := 2) 1 hf p.2).smooth.differentiable (by norm_num)
    have ha : Differentiable ℝ (fun y : E => p.1*(fderiv ℝ f y p.2)^2/2) :=
      by simpa only [div_eq_mul_inv,Pi.pow_apply] using ((h₁.pow 2).const_mul p.1).mul_const (2:ℝ)⁻¹
    have hb : Differentiable ℝ (fun y : E => directionalJet p.2 2 f y/2) :=
      by simpa only [div_eq_mul_inv] using h₂.mul_const (2:ℝ)⁻¹
    exact ha.add hb
  induction ps with
  | nil => exact differentiable_const 0
  | cons p ps ih => exact (hd p).add ih

theorem fderiv_pathQuadraticSum {B : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (ps : List (ℝ × E)) (x w : E) :
    fderiv ℝ (pathQuadraticSum f ps) x w =
      pathGeneratorSum f (fun y => fderiv ℝ f y w) ps x := by
  have hd (p : ℝ × E) : Differentiable ℝ (stepQuadraticIncrement p.1 p.2 f) := by
    simpa only [pathQuadraticSum,add_zero] using
      differentiable_pathQuadraticSum hf [p]
  have hs := differentiable_pathQuadraticSum hf
  induction ps with
  | nil => simp only [pathQuadraticSum,pathGeneratorSum,fderiv_fun_const,Pi.zero_apply,zero_apply]
  | cons p ps ih =>
    change fderiv ℝ (fun y => stepQuadraticIncrement p.1 p.2 f y+pathQuadraticSum f ps y) x w = _
    rw [fderiv_fun_add (hd p x) (hs ps x),add_apply,
      fderiv_stepQuadraticIncrement hf,ih]
    rfl

def chainFirstOrderRemainder (f : E → ℝ) (ps : List (ℝ × E)) (x : E) : ℝ :=
  vectorIncrementChain ps f x-f x-pathQuadraticSum f ps x

theorem fderiv_chainFirstOrderRemainder {B : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (ps : List (ℝ × E)) (x w : E) :
    fderiv ℝ (chainFirstOrderRemainder f ps) x w =
      fderiv ℝ (vectorIncrementChain ps f) x w-fderiv ℝ f x w-
        pathGeneratorSum f (fun y => fderiv ℝ f y w) ps x := by
  have hF := (vectorIncrementChain_regular ps (hf.boundedDerivs (by norm_num))).1.differentiable
    (by norm_num)
  have hfd := hf.smooth.differentiable (by norm_num)
  have hPd := differentiable_pathQuadraticSum hf ps
  change fderiv ℝ (fun y => vectorIncrementChain ps f y-f y-pathQuadraticSum f ps y) x w = _
  rw [fderiv_fun_sub (f := fun y => vectorIncrementChain ps f y-f y)
    (g := pathQuadraticSum f ps) ((hF x).sub (hfd x)) (hPd x),
    fderiv_fun_sub (f := vectorIncrementChain ps f) (g := f) (hF x) (hfd x),
    sub_apply,sub_apply,fderiv_pathQuadraticSum hf]

theorem directionalJet_two_sub {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QPotential 3 C g) (v : E) :
    directionalJet v 2 (fun y => f y-g y) =
      fun y => directionalJet v 2 f y-directionalJet v 2 g y := by
  have hdf := hf.smooth.differentiable (by norm_num)
  have hdg := hg.smooth.differentiable (by norm_num)
  have he : directionalJet v 1 (fun y => f y-g y) =
      fun y => fderiv ℝ f y v-fderiv ℝ g y v := by
    funext y
    change fderiv ℝ (fun z => f z-g z) y v = _
    rw [fderiv_fun_sub (hdf y) (hdg y)]
    rfl
  funext x
  change fderiv ℝ (directionalJet v 1 (fun y => f y-g y)) x v = _
  rw [he,fderiv_fun_sub
    ((hf.directional v).smooth.differentiable (by norm_num) x)
    ((hg.directional v).smooth.differentiable (by norm_num) x)]
  rfl

theorem abs_stepQuadraticIncrement_sub_le {B H : ℝ} {f F : E → ℝ}
    (hf : QPotential 3 B f) (hF : QPotential 3 B F)
    (hdiff : QBoundedJets 3 H (fun y => F y-f y))
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v x : E) :
    |stepQuadraticIncrement m v F x-stepQuadraticIncrement m v f x| ≤
      (B+1)*H*‖v‖^2 := by
  have hB := hf.nonneg
  have hH := hdiff.nonneg
  have h₀ := hf.directional_le (by norm_num) x v
  have h₁ := hF.directional_le (by norm_num) x v
  have hδ := (qBoundedJets_iff_qBddSmooth.mp hdiff).potential.directional_le
    (by norm_num) x v
  rw [fderiv_fun_sub (hF.smooth.differentiable (by norm_num) x)
    (hf.smooth.differentiable (by norm_num) x)] at hδ
  change |fderiv ℝ F x v-fderiv ℝ f x v| ≤ H*‖v‖ at hδ
  have hplus : |fderiv ℝ F x v+fderiv ℝ f x v| ≤ 2*B*‖v‖ := by
    exact (abs_add_le _ _).trans ((add_le_add h₁ h₀).trans_eq (by ring))
  have hsquare : |(fderiv ℝ F x v)^2-(fderiv ℝ f x v)^2| ≤
      2*B*H*‖v‖^2 := by
    calc
      _ = |(fderiv ℝ F x v-fderiv ℝ f x v)*
          (fderiv ℝ F x v+fderiv ℝ f x v)| := by congr 1; ring
      _ ≤ (H*‖v‖)*(2*B*‖v‖) := by rw [abs_mul]; gcongr
      _ = _ := by ring
  have hhess := (directionalJet_smooth (r := 1) 1
    (qBoundedJets_iff_qBddSmooth.mp hdiff).potential v).bound 0 (by norm_num) x
  have hhess' : |directionalJet v 2 F x-directionalJet v 2 f x| ≤ H*‖v‖^2 := by
    rw [← congrFun (directionalJet_two_sub hF hf v) x]
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hhess
  have he : stepQuadraticIncrement m v F x-stepQuadraticIncrement m v f x =
      (m/2)*((fderiv ℝ F x v)^2-(fderiv ℝ f x v)^2)+
        (1/2:ℝ)*(directionalJet v 2 F x-directionalJet v 2 f x) := by
    dsimp only [stepQuadraticIncrement]
    ring
  rw [he]
  calc
    _ ≤ |(m/2)*((fderiv ℝ F x v)^2-(fderiv ℝ f x v)^2)|+
        |(1/2:ℝ)*(directionalJet v 2 F x-directionalJet v 2 f x)| := abs_add_le _ _
    _ = |m/2| * |(fderiv ℝ F x v)^2-(fderiv ℝ f x v)^2|+
        |(1/2:ℝ)| * |directionalJet v 2 F x-directionalJet v 2 f x| := by
      rw [abs_mul,abs_mul]
    _ ≤ (1/2:ℝ)*(2*B*H*‖v‖^2)+(1/2:ℝ)*(H*‖v‖^2) := by
      rw [abs_div,abs_of_nonneg hm.1]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      gcongr
      exact hm.2
    _ ≤ (B+1)*H*‖v‖^2 := by nlinarith only [mul_nonneg hH (sq_nonneg ‖v‖)]

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

def orderedInnerValueRemainder (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (k : ℝ) : E → ℝ :=
  chainFirstOrderRemainder (massVariationTerminal β α s h)
    ((massPath (windowMassPath β α a (1/2) s h k N) lam).drop (j.val+1))

theorem orderedInnerGradientRemainder_eq_fderiv {β B : ℝ} {α : ℝ → ℝ}
    {a s h : ℝ} {N : ℕ} (lam : ℝ) (j : Fin (12*N)) (x : E) (k : ℝ)
    (hf : QPotential 4 B (massVariationTerminal β α s h)) :
    orderedInnerGradientRemainder β α a s h N lam j x k =
      fderiv ℝ (orderedInnerValueRemainder β α a s h N lam j k) x
        (orderedWindowCurve β α a s h N lam j k).2 := by
  dsimp only [orderedInnerValueRemainder]
  rw [fderiv_chainFirstOrderRemainder hf]
  rfl

theorem gradient_c2BoundAt_of_value_jets {F : ℝ → E → ℝ}
    {A B eps h k : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (heps : 0 ≤ eps)
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hp : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun q => F q x) t)
    (hjets : ∀ᶠ t in 𝓝 k, ∀ c : ℕ, c ≤ 2 →
      QBoundedJets 2 (B*h) (fun x => iteratedDeriv c (fun q => F q x) t))
    (hvalue : ∀ c : ℕ, c ≤ 2 → ∀ x,
      ‖iteratedDeriv c (fun q => F q x) k‖ ≤ A*h^2+eps*Real.sqrt h/3)
    (x w : E) (hs : ContDiffAt ℝ 2 (fun t => fderiv ℝ (F t) x w) k) :
    C2BoundAt (((3*A+B)*Real.sqrt h*h+eps)*‖w‖)
      (fun t => fderiv ℝ (F t) x w) k := by
  have hfirst : ∀ᶠ t in 𝓝 k,
      QBoundedJets 2 (B*h) (fun x => deriv (fun q => F q x) t) := by
    filter_upwards [hjets] with t ht
    simpa only [iteratedDeriv_one] using ht 1 (by norm_num)
  have hsecond : ∀ᶠ t in 𝓝 k,
      QBoundedJets 2 (B*h) (fun x => deriv (deriv (fun q => F q x)) t) := by
    filter_upwards [hjets] with t ht
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using ht 2 (by norm_num)
  have htwo := spatial_parameter_twoJet_of_contDiff hF hp hfirst hsecond x w
  have hsmall (c : ℕ) (hc : c ≤ 2) := QBoundedJets.firstOrder_spatial_interpolate
    hA hB heps hh hh1 (hjets.self_of_nhds c hc) (hvalue c hc)
  have hb (c : ℕ) (hc : c ≤ 2) :
      |fderiv ℝ (fun y => iteratedDeriv c (fun q => F q y) k) x w| ≤
        ((3*A+B)*Real.sqrt h*h+eps)*‖w‖ := by
    exact (qBoundedJets_iff_qBddSmooth.mp (hsmall c hc)).potential.directional_le
      (by norm_num) x w
  refine ⟨by positivity,hs,?_⟩
  intro c hc
  interval_cases c
  · simpa only [iteratedDeriv_zero] using hb 0 (by norm_num)
  · rw [iteratedDeriv_one,htwo.1]
    simpa only [iteratedDeriv_one] using hb 1 (by norm_num)
  · simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rw [htwo.2]
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb 2 (by norm_num)

theorem moving_gradient_c2BoundAt_of_value_jets {F : ℝ → E → ℝ}
    {v : ℝ → E} {A B eps h d k : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (heps : 0 ≤ eps) (hh : 0 < h) (hh1 : h ≤ 1)
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hp : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun q => F q x) t)
    (hjets : ∀ᶠ t in 𝓝 k, ∀ c : ℕ, c ≤ 2 →
      QBoundedJets 2 (B*h) (fun x => iteratedDeriv c (fun q => F q x) t))
    (hvalue : ∀ c : ℕ, c ≤ 2 → ∀ x,
      ‖iteratedDeriv c (fun q => F q x) k‖ ≤ A*h^2+eps*Real.sqrt h/3)
    (x : E) (hs : ∀ w, ContDiffAt ℝ 2 (fun t => fderiv ℝ (F t) x w) k)
    (hd : 0 ≤ d) (hv : ContDiffAt ℝ 2 v k)
    (hb : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c v k‖ ≤ d) :
    C2BoundAt (12*d*((3*A+B)*Real.sqrt h*h+eps))
      (fun t => fderiv ℝ (F t) x (v t)) k := by
  have hgrad (w : E) := gradient_c2BoundAt_of_value_jets hA hB heps hh hh1
    hF hp hjets hvalue x w (hs w)
  have H := moving_gradient_sub_c2BoundAt (F := F) (f := fun _ => 0) x hd hv hb
    (fun w => by simpa only [fderiv_fun_const,Pi.zero_apply,zero_apply,sub_zero] using hgrad w)
  simpa only [fderiv_fun_const,Pi.zero_apply,zero_apply,sub_zero] using H

end SKBarriers2.Corner
