module

public import SKBarriers2.Corner.PathEnergyInner
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

open SKBarriers2.Corner
local notation "E" => (Fin 3 → ℝ)

private theorem spatial_difference_quotient_error {B : ℝ} {f : E → ℝ}
    (hf : QBoundedJets 2 B f) (x w : E) {a : ℝ} (ha : a ≠ 0) :
    |(f (x+a • w)-f x)/a-fderiv ℝ f x w| ≤ B*|a| *‖w‖^2 := by
  have H := hf.linear_taylor_remainder_le x (a • w)
  have he : (f (x+a • w)-f x)/a-fderiv ℝ f x w =
      (f (x+a • w)-f x-fderiv ℝ f x (a • w))/a := by
    rw [map_smul,smul_eq_mul]
    field_simp
  rw [he,abs_div]
  calc
    _ ≤ (B*‖a • w‖^2)/|a| :=
      div_le_div_of_nonneg_right H (abs_nonneg a)
    _ = _ := by
      rw [norm_smul,Real.norm_eq_abs,mul_pow]
      field_simp

theorem hasDerivAt_spatial_of_uniform_jets {F G : ℝ → E → ℝ} {B k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hd : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (G t x) t)
    (hG : ∀ᶠ t in 𝓝 k, QBoundedJets 2 B (G t)) (x w : E) :
    HasDerivAt (fun t => fderiv ℝ (F t) x w) (fderiv ℝ (G k) x w) k := by
  let Q : ℝ → ℝ → ℝ := fun a t => (F t (x+a • w)-F t x)/a
  let Q' : ℝ → ℝ → ℝ := fun a t => (G t (x+a • w)-G t x)/a
  have hB : 0 ≤ B := (hG.self_of_nhds).nonneg
  have hne : ∀ᶠ a in 𝓝[≠] (0 : ℝ), a ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact ha
  have hconv : TendstoUniformlyOnFilter Q' (fun t => fderiv ℝ (G t) x w)
      (𝓝[≠] (0 : ℝ)) (𝓝 k) := by
    apply Metric.tendstoUniformlyOnFilter_iff.mpr
    intro ε hε
    let δ := ε/(B*‖w‖^2+1)
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    have hsmall : ∀ᶠ a in 𝓝[≠] (0 : ℝ), |a| < δ := by
      exact ((continuous_abs.continuousAt : ContinuousAt (fun a : ℝ => |a|) 0).eventually
        (gt_mem_nhds (by simpa using hδ))).filter_mono nhdsWithin_le_nhds
    apply eventually_prod_iff.mpr ⟨_,hne.and hsmall,_,hG,?_⟩
    intro a ha t ht
    rw [dist_comm,Real.dist_eq]
    calc
      |Q' a t-fderiv ℝ (G t) x w| ≤ B*|a| *‖w‖^2 :=
        spatial_difference_quotient_error ht x w ha.1
      _ < (B*‖w‖^2+1)*δ := by
        have H := mul_lt_mul_of_pos_left ha.2 (show 0 < B*‖w‖^2+1 by positivity)
        have H' : B*|a| *‖w‖^2 ≤ (B*‖w‖^2+1)*|a| := by
          nlinarith only [abs_nonneg a]
        exact H'.trans_lt H
      _ = ε := by dsimp only [δ]; field_simp
  have hqd : ∀ᶠ z : ℝ × ℝ in (𝓝[≠] (0 : ℝ)) ×ˢ 𝓝 k,
      HasDerivAt (Q z.1) (Q' z.1 z.2) z.2 := by
    apply eventually_prod_iff.mpr ⟨_,Eventually.of_forall (fun _ : ℝ => True.intro),_,hd,?_⟩
    intro a _ t ht
    exact ((ht (x+a • w)).sub (ht x)).div_const a
  have hqconv : ∀ᶠ t in 𝓝 k, Tendsto (fun a => Q a t) (𝓝[≠] (0 : ℝ))
      (𝓝 (fderiv ℝ (F t) x w)) := by
    filter_upwards [hF] with t ht
    have hl : HasDerivAt (fun a : ℝ => x+a • w) w (0 : ℝ) := by
      convert! ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x using 1
      simp only [one_smul]
    have H := ((ht (x+(0 : ℝ) • w)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      hl).tendsto_slope_zero
    simpa only [Q,Function.comp_def,zero_add,zero_smul,add_zero,smul_eq_mul,
      div_eq_mul_inv,mul_comm] using H
  exact hasDerivAt_of_tendstoUniformlyOnFilter hconv hqd hqconv

theorem spatial_parameter_twoJet {F F₁ F₂ : ℝ → E → ℝ} {A H k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hd₀ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F q x) (F₁ t x) t)
    (hd₁ : ∀ᶠ t in 𝓝 k, ∀ x, HasDerivAt (fun q => F₁ q x) (F₂ t x) t)
    (hF₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 A (F₁ t))
    (hF₂ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 H (F₂ t)) (x w : E) :
    deriv (fun t => fderiv ℝ (F t) x w) k = fderiv ℝ (F₁ k) x w ∧
      deriv (deriv (fun t => fderiv ℝ (F t) x w)) k = fderiv ℝ (F₂ k) x w := by
  have hfirst := hasDerivAt_spatial_of_uniform_jets hF hd₀ hF₁ x w
  have he : deriv (fun t => fderiv ℝ (F t) x w) =ᶠ[𝓝 k]
      (fun t => fderiv ℝ (F₁ t) x w) := by
    filter_upwards [eventually_eventually_nhds.mpr hF,
      eventually_eventually_nhds.mpr hd₀,eventually_eventually_nhds.mpr hF₁] with
      t hFt hdt hF₁t
    exact (hasDerivAt_spatial_of_uniform_jets hFt hdt hF₁t x w).deriv
  have hF₁diff : ∀ᶠ t in 𝓝 k, ∀ y, DifferentiableAt ℝ (F₁ t) y := by
    filter_upwards [hF₁] with t ht y
    exact ht.smooth.differentiable (by norm_num) y
  refine ⟨hfirst.deriv,?_⟩
  rw [he.deriv_eq]
  exact (hasDerivAt_spatial_of_uniform_jets hF₁diff hd₁ hF₂ x w).deriv

theorem spatial_parameter_twoJet_of_contDiff {F : ℝ → E → ℝ} {A H k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ∀ x, DifferentiableAt ℝ (F t) x)
    (hp : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun q => F q x) t)
    (hF₁ : ∀ᶠ t in 𝓝 k,
      QBoundedJets 2 A (fun x => deriv (fun q => F q x) t))
    (hF₂ : ∀ᶠ t in 𝓝 k,
      QBoundedJets 2 H (fun x => deriv (deriv (fun q => F q x)) t)) (x w : E) :
    deriv (fun t => fderiv ℝ (F t) x w) k =
        fderiv ℝ (fun y => deriv (fun t => F t y) k) x w ∧
      deriv (deriv (fun t => fderiv ℝ (F t) x w)) k =
        fderiv ℝ (fun y => deriv (deriv (fun t => F t y)) k) x w := by
  have hd₀ : ∀ᶠ t in 𝓝 k, ∀ x,
      HasDerivAt (fun q => F q x) (deriv (fun q => F q x) t) t := by
    filter_upwards [hp] with t ht x
    exact ((ht x).differentiableAt (by norm_num)).hasDerivAt
  have hd₁ : ∀ᶠ t in 𝓝 k, ∀ x,
      HasDerivAt (fun q => deriv (fun a => F a x) q)
        (deriv (deriv (fun q => F q x)) t) t := by
    filter_upwards [hp] with t ht x
    exact (((ht x).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  exact spatial_parameter_twoJet hF hd₀ hd₁ hF₁ hF₂ x w

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem gradient_sub_c2BoundAt {F : ℝ → E → ℝ} {f : E → ℝ} {C k : ℝ}
    (hF : ∀ᶠ t in 𝓝 k, ∀ y, DifferentiableAt ℝ (F t) y)
    (hp : ∀ᶠ t in 𝓝 k, ∀ y, ContDiffAt ℝ 2 (fun q => F q y) t)
    (hF₁ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 C (fun y => deriv (fun q => F q y) t))
    (hF₂ : ∀ᶠ t in 𝓝 k, QBoundedJets 2 C (fun y => deriv (deriv (fun q => F q y)) t))
    (hdiff : QBoundedJets 3 C (fun y => F k y-f y))
    (hf : Differentiable ℝ f) (x w : E)
    (hs : ContDiffAt ℝ 2 (fun t => fderiv ℝ (F t) x w) k) :
    C2BoundAt (C*‖w‖) (fun t => fderiv ℝ (F t) x w-fderiv ℝ f x w) k := by
  have hC := hdiff.nonneg
  have htwo := spatial_parameter_twoJet_of_contDiff hF hp hF₁ hF₂ x w
  have hfirst := (qBoundedJets_iff_qBddSmooth.mp hF₁.self_of_nhds).potential
  have hsecond := (qBoundedJets_iff_qBddSmooth.mp hF₂.self_of_nhds).potential
  refine ⟨by positivity,hs.sub contDiffAt_const,?_⟩
  intro c hc
  interval_cases c
  · have H := (hdiff.derivativeJets.apply_const w).norm_le x
    rw [fderiv_fun_sub (hF.self_of_nhds x) (hf x)] at H
    simpa only [iteratedDeriv_zero,Real.norm_eq_abs,sub_apply] using H
  · rw [iteratedDeriv_one,deriv_sub_const,htwo.1]
    exact hfirst.directional_le (by norm_num) x w
  · simp only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_sub_const_fun]
    rw [htwo.2]
    exact hsecond.directional_le (by norm_num) x w

private theorem inner_apply_eq_sum (L : E →L[ℝ] ℝ) (v : E) :
    L v = ∑ i : Fin 3, v i*L (Pi.single i 1) := by
  have hv : v = ∑ i : Fin 3, v i • Pi.single i 1 := by
    ext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]

theorem moving_gradient_sub_c2BoundAt {F : ℝ → E → ℝ} {f : E → ℝ}
    {v : ℝ → E} {C d k : ℝ} (x : E) (hd : 0 ≤ d)
    (hv : ContDiffAt ℝ 2 v k)
    (hb : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c v k‖ ≤ d)
    (hgrad : ∀ w : E, C2BoundAt (C*‖w‖)
      (fun t => fderiv ℝ (F t) x w-fderiv ℝ f x w) k) :
    C2BoundAt (12*d*C) (fun t => fderiv ℝ (F t) x (v t)-fderiv ℝ f x (v t)) k := by
  have hC : 0 ≤ C := by
    have H := (hgrad (Pi.single (0 : Fin 3) 1)).nonneg
    simpa only [Pi.norm_single,norm_one,mul_one] using H
  have hg (i : Fin 3) : C2BoundAt C
      (fun t => fderiv ℝ (F t) x (Pi.single i 1)-fderiv ℝ f x (Pi.single i 1)) k := by
    simpa only [Pi.norm_single,norm_one,mul_one] using hgrad (Pi.single i 1)
  have H := C2BoundAt.sum Finset.univ (by positivity : 0 ≤ 4*d*C)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      (c2BoundAt_coordinate hd hv hb i).mul (hg i))
  have he : (fun t => ∑ i : Fin 3, v t i*
      (fderiv ℝ (F t) x (Pi.single i 1)-fderiv ℝ f x (Pi.single i 1))) =
      (fun t => fderiv ℝ (F t) x (v t)-fderiv ℝ f x (v t)) := by
    funext t
    rw [inner_apply_eq_sum (fderiv ℝ (F t) x),inner_apply_eq_sum (fderiv ℝ f x),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  convert H using 1
  · change 12*d*C = (3 : ℝ)*(4*d*C)
    ring
  · exact he.symm

end SKBarriers2.Corner

namespace SKBarriers2.QBoundedJets

local notation "E" => (Fin 3 → ℝ)

theorem firstOrder_spatial_interpolate {A B eps h : ℝ} {f : E → ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (heps : 0 ≤ eps) (hh : 0 < h) (hh1 : h ≤ 1)
    (hhigh : QBoundedJets 2 (B*h) f)
    (hvalue : ∀ x, ‖f x‖ ≤ A*h^2+eps*Real.sqrt h/3) :
    QBoundedJets 1 ((3*A+B)*Real.sqrt h*h+eps) f := by
  have hr : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hr1 : Real.sqrt h ≤ 1 := Real.sqrt_le_one.mpr hh1
  have hlow : QBoundedJets 0 (A*h^2+eps*Real.sqrt h/3) f := by
    refine ⟨by positivity,hhigh.smooth.of_le (by norm_num),?_⟩
    intro c hc x
    have hc0 : c=0 := by omega
    subst c
    simpa only [norm_iteratedFDeriv_zero] using hvalue x
  have H := hhigh.interpolate_succ hlow hr hr1
  have hquot : h^2/Real.sqrt h = Real.sqrt h*h := by
    apply (div_eq_iff hr.ne').mpr
    calc
      h^2 = h*h := by ring
      _ = h*(Real.sqrt h)^2 := by rw [Real.sq_sqrt hh.le]
      _ = _ := by ring
  apply H.mono
  calc
    _ = 3*A*(h^2/Real.sqrt h)+eps+(B*h)*Real.sqrt h := by field_simp
    _ = (3*A+B)*Real.sqrt h*h+eps := by rw [hquot]; ring
    _ ≤ (3*A+B)*Real.sqrt h*h+eps := le_rfl

end SKBarriers2.QBoundedJets

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

open SKBarriers2.Corner

private theorem inner_chainEnergy_le_variation (ps : List (ℝ → ℝ × E)) (k : ℝ) :
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

theorem strictSuffix_spatialChainJets {r : ℕ} {B : ℝ} {l : List (ℝ × E)}
    {f : E → ℝ} (hlen : 0 < l.length)
    (hinner : ∀ j : ℕ, j < l.length → QPotential r B (vectorIncrementChain (l.drop (j+1)) f))
    (j : ℕ) : SpatialChainJets r B (l.drop (j+1)) f := by
  have hf : QPotential r B f := by
    have H := hinner (l.length-1) (by omega)
    simpa only [Nat.sub_add_cancel hlen,List.drop_length,vectorIncrementChain] using H
  intro n
  rw [List.drop_drop]
  by_cases h : j+n < l.length
  · have H := hinner (j+n) h
    convert H using 1
    congr 2
    omega
  · rw [List.drop_eq_nil_iff.mpr (by omega)]
    exact hf

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem scalarData_orderedInner_sub_c3 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
      let α := cdf (D.μ : Measure ℝ)
      QBoundedJets 3 (C*h) (fun x =>
        orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k x-
          massVariationTerminal β α (r-h) h x) := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,a0,hV,hA,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D hl hu
    let K := spatialStepDifferenceCoefficient 2 B
    have hK : 0 ≤ K := spatialStepDifferenceCoefficient_nonneg 2 hB
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
      exact (inner_chainEnergy_le_variation ps k).trans he
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
      refine ⟨by nlinarith [norm_nonneg p.2],?_⟩
      exact (mul_le_of_le_one_left (by positivity) (hm p hp).2).trans hsmall
    obtain ⟨_,hEN⟩ := hentropy r hr h hh
      (hh0.trans ((min_le_right _ _).trans (min_le_left _ _)))
      k (hk.trans (min_le_left _ _)) N hN
    have hinner := (hEN lam hlam).1
    have hlen : 0 < L.length := by
      dsimp only [L]
      rw [massPath,List.length_map,windowMassPath_length]
      omega
    have hjets : SpatialChainJets 5 B (L.drop (j.val+1)) f := by
      apply strictSuffix_spatialChainJets hlen
      intro n hn
      exact (hinner n (by simpa only [L,massPath,List.length_map] using hn)).of_le (by norm_num)
    have hsub : ∀ p ∈ L.drop (j.val+1), p ∈ L :=
      fun p hp => List.mem_of_mem_drop hp
    have htail : chainEnergy (L.drop (j.val+1)) ≤ chainEnergy L := by
      have H := congrArg chainEnergy (List.take_append_drop (j.val+1) L)
      rw [chainEnergy_append] at H
      linarith only [chainEnergy_nonneg (L.take (j.val+1)),H]
    apply (qBoundedJets_chain_sub (L.drop (j.val+1)) hjets
      (fun p hp => hm p (hsub p hp)) (fun p hp => hv p (hsub p hp))).mono
    calc
      _ ≤ K*(A*h) := mul_le_mul_of_nonneg_left (htail.trans henergy) hK
      _ = _ := by ring
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

private theorem inner2_window_direction_bound (β : ℝ) :
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

theorem scalarData_orderedInner_gradient_sub_c2BoundAt {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap → ∀ x : E,
      let α := cdf (D.μ : Measure ℝ)
      let w := fun t => (orderedWindowCurve β α (α (r-h)) (r-h) h N lam j t).2
      C2BoundAt (C*h*Real.sqrt (h/(N : ℝ))) (fun t =>
        fderiv ℝ (orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t) x (w t)-
          fderiv ℝ (massVariationTerminal β α (r-h) h) x (w t)) k := by
  by_cases hlu : l ≤ u
  · obtain ⟨C₀,hS,kapS,hC₀,hhS,hkapS,hsub⟩ := scalarData_orderedInner_sub_c3 D hl hu
    obtain ⟨C₁,hJ,hC₁,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
    obtain ⟨A,a0,hV,_,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨L,hL,hdir⟩ := inner2_window_direction_bound β
    let C := C₀+C₁
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨12*L*C,min hS (min hJ (min hV (kStabilityInteriorRadius D.q l u))),
      min kapS (1/4),by positivity,lt_min hhS (lt_min hhJ (lt_min hhV
        (kStabilityInteriorRadius_pos hl hu))),lt_min hkapS (by norm_num),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk x
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let qs := ps.drop (j.val+1)
    let f := massVariationTerminal β α (r-h) h
    let F := fun t => vectorIncrementChain (qs.map (fun p => p t)) f
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let w := fun t => (p t).2
    have hhS' := hh0.trans (min_le_left _ _)
    have hhJ' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhV' := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hhI := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hkhalf : |k| ≤ 1/2 := (hk.trans (min_le_right _ _)).trans (by norm_num)
    have hkstrict : |k| < 1/2 := lt_of_le_of_lt (hk.trans (min_le_right _ _)) (by norm_num)
    have hnear : ∀ᶠ t in 𝓝 k, |t| ≤ 1/2 := by
      filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hkstrict)] with t ht
      exact ht.le
    have ht : (r-h)+4*h ∈ Icc (0 : ℝ) 1 := by
      have H := kStability_time_mem hr hh.le hhI
        (show (4 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
      constructor <;> linarith [H.1,H.2,D.q_mem.2]
    have hf := scalarData_massVariationTerminal_qPotential D 3 ht
    have hmem : ∀ p ∈ qs, p ∈ ps := fun p hp => List.mem_of_mem_drop hp
    have hreg (t : ℝ) (ht' : |t| ≤ 1/2) : ∀ p ∈ qs, ContDiffAt ℝ 2 p t := by
      intro p hp
      exact ((hvar r hr h hh hhV' N hN lam hlam t ht').2 p (hmem p hp)).1
    have hpos (t : ℝ) (ht' : |t| ≤ 1/2) : ∀ p ∈ qs, 0 < (p t).1 := by
      intro p hp
      exact ha0.trans_le
        ((hvar r hr h hh hhV' N hN lam hlam t ht').2 p (hmem p hp)).2.1.1
    have heF (t : ℝ) : F t = orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t := by
      dsimp only [F,qs,ps,orderedInnerChain]
      rw [List.map_drop,windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
    have hjoint (t : ℝ) (ht' : |t| ≤ 1/2) (y : E) :
        ContDiffAt ℝ 2 (fun z : ℝ × E => F z.1 z.2) (t,y) :=
      ParamChain.contDiffAt_curveChain qs hf (by norm_num) (hreg t ht') (hpos t ht') y
    have hFspace : ∀ᶠ t in 𝓝 k, ∀ y, DifferentiableAt ℝ (F t) y := by
      filter_upwards [hnear] with t ht' y
      exact ((hjoint t ht' y).comp y
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)
    have hparam : ∀ᶠ t in 𝓝 k, ∀ y, ContDiffAt ℝ 2 (fun q => F q y) t := by
      filter_upwards [hnear] with t ht' y
      exact (hjoint t ht' y).comp t (contDiffAt_id.prodMk contDiffAt_const)
    have hdiff : QBoundedJets 3 (C*h) (fun y => F k y-f y) := by
      rw [heF]
      exact (hsub r hr h hh hhS' N hN lam hlam j k (hk.trans (min_le_left _ _))).mono
        (by dsimp only [C]; nlinarith only [mul_nonneg hC₁.le hh.le])
    have hfirst : ∀ᶠ t in 𝓝 k, QBoundedJets 2 (C*h) (fun y => deriv (fun q => F q y) t) := by
      filter_upwards [hnear] with t ht'
      have H := (hjets r hr h hh hhJ' N hN lam hlam j t ht').1.of_le (by norm_num : 2 ≤ 6)
      change QBoundedJets 2 (C₁*h) (fun y => iteratedDeriv 1
        (fun q => orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j q y) t) at H
      simp only [iteratedDeriv_one] at H
      rw [show F = (fun q => orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j q)
        from funext heF]
      exact H.mono (by dsimp only [C]; nlinarith only [mul_nonneg hC₀ hh.le])
    have hsecond : ∀ᶠ t in 𝓝 k,
        QBoundedJets 2 (C*h) (fun y => deriv (deriv (fun q => F q y)) t) := by
      filter_upwards [hnear] with t ht'
      have H := (hjets r hr h hh hhJ' N hN lam hlam j t ht').2.of_le (by norm_num : 2 ≤ 4)
      change QBoundedJets 2 (C₁*h) (fun y => iteratedDeriv 2
        (fun q => orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j q y) t) at H
      simp only [iteratedDeriv_succ,iteratedDeriv_zero] at H
      rw [show F = (fun q => orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j q)
        from funext heF]
      exact H.mono (by dsimp only [C]; nlinarith only [mul_nonneg hC₀ hh.le])
    have hg (w₀ : E) : C2BoundAt ((C*h)*‖w₀‖)
        (fun t => fderiv ℝ (F t) x w₀-fderiv ℝ f x w₀) k := by
      apply gradient_sub_c2BoundAt hFspace hparam hfirst hsecond hdiff
        (hf.smooth.differentiable (by norm_num))
      exact (ParamChain.contDiffAt_curveChain_spatial qs hf (by norm_num)
        (hreg k hkhalf) (hpos k hkhalf) x w₀).comp k
          (contDiffAt_id.prodMk contDiffAt_const)
    have hp : p ∈ ps := orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    have hw : ContDiffAt ℝ 2 w k :=
      ((hvar r hr h hh hhV' N hN lam hlam k hkhalf).2 p hp).1.snd
    have hds := hdir _ _ _ hh.le N p hp k hkhalf
    have hb : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c w k‖ ≤ L*Real.sqrt (h/(N : ℝ)) := by
      intro c hc
      interval_cases c
      · exact hds.1
      · simpa only [iteratedDeriv_one] using hds.2.1
      · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hds.2.2
    have H := moving_gradient_sub_c2BoundAt x (by positivity : 0 ≤ L*Real.sqrt (h/(N : ℝ)))
      hw hb hg
    simp_rw [heF] at H
    convert H using 1
    ring
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

def orderedInnerGradientRemainder (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (x : E) (k : ℝ) : ℝ :=
  let f := massVariationTerminal β α s h
  let w := (orderedWindowCurve β α a s h N lam j k).2
  let L := massPath (windowMassPath β α a (1/2) s h k N) lam
  fderiv ℝ (orderedInnerChain β α a (1/2) s h N lam j k) x w-
    fderiv ℝ f x w-pathGeneratorSum f (fun y => fderiv ℝ f y w) (L.drop (j.val+1)) x

theorem scalarData_windowInnerEnergyC2_of_gradient_remainder {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hR : ∃ R hR kapR : ℝ, 0 ≤ R ∧ 0 < hR ∧ 0 < kapR ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ hR → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N),
      ∀ k : ℝ, |k| ≤ kapR → ∀ x : E,
      let α := cdf (D.μ : Measure ℝ)
      C2BoundAt ((R*Real.sqrt h*h+eps)*Real.sqrt (h/(N : ℝ)))
        (orderedInnerGradientRemainder β α (α (r-h)) (r-h) h N lam j x) k) :
    WindowInnerEnergyC2 D (Icc l u) := by
  obtain ⟨R,hR,kapR,hR0,hhR,hkapR,hrem⟩ := hR
  obtain ⟨U,hT,hU,hhT,hterminal⟩ := scalarData_window_terminalGradient_c2BoundAt D hl hu
  obtain ⟨V,hG,kapG,hV,hhG,hkapG,hgradient⟩ :=
    scalarData_orderedInner_gradient_sub_c2BoundAt D hl hu
  refine ⟨4*V^2+8*U*R,min hR (min hT (min hG 1)),min kapR (min kapG (1/2)),
    by positivity,lt_min hhR (lt_min hhT (lt_min hhG (by norm_num))),
    lt_min hkapR (lt_min hkapG (by norm_num)),?_⟩
  intro r hr h hh hh0 eps heps
  have hhR' := hh0.trans (min_le_left _ _)
  have hhT' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhG' := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let δ := eps/(8*U*h+1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδeps : 8*U*δ*h ≤ eps := by
    have H : (8*U*h)/(8*U*h+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    convert mul_le_of_le_one_right heps.le H using 1
    dsimp only [δ]
    ring
  have hroot : h ≤ Real.sqrt h := by
    have hs := Real.sq_sqrt hh.le
    have hr := Real.sqrt_nonneg h
    have hr1 : Real.sqrt h ≤ 1 := (Real.sqrt_le_one).mpr hh1
    nlinarith only [hs,hr,mul_le_of_le_one_right hr hr1]
  filter_upwards [hrem r hr h hh hhR' δ hδ,eventually_ge_atTop (1 : ℕ)] with N hn hN
  intro lam hlam j k hk x
  let α := cdf (D.μ : Measure ℝ)
  have ha := hterminal r hr h hh hhT' N hN lam hlam j k
    (hk.trans ((min_le_right _ _).trans (min_le_right _ _))) x
  have hd := hgradient r hr h hh hhG' N hN lam hlam j k
    (hk.trans ((min_le_right _ _).trans (min_le_left _ _))) x
  have hrest := hn lam hlam j k (hk.trans (min_le_left _ _)) x
  have H := orderedEnergyAssemblyTerm_inner_c2BoundAt β α (α (r-h)) (r-h) h N
    lam j hh.le x ha hd hrest
  apply H.mono
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : (Real.sqrt (h/(N : ℝ)))^2 = h/(N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hVterm : 4*V^2*h^3 ≤ 4*V^2*(Real.sqrt h*h^2) := by
    have H := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 4*V^2*h^2 by positivity)
    convert H using 1 <;> ring
  calc
    _ = (4*V^2*h^3+8*U*R*Real.sqrt h*h^2+8*U*δ*h)/(N : ℝ) := by
      calc
        _ = (4*V^2*h^2+8*U*(R*Real.sqrt h*h+δ))*(Real.sqrt (h/(N : ℝ)))^2 := by ring
        _ = _ := by rw [hs]; ring
    _ ≤ (4*V^2*(Real.sqrt h*h^2)+8*U*R*Real.sqrt h*h^2+eps)/(N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hNpos.le
      linarith only [hVterm,hδeps]
    _ = _ := by ring

end SKBarriers2.Corner
