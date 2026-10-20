module

public import SKBarriers2.Corner.PathEnergyInner2

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem generator_apply_coordinate_sum (L : E →L[ℝ] ℝ) (v : E) :
    L v = ∑ i : Fin 3, v i*L (Pi.single i 1) := by
  have hv : v = ∑ i : Fin 3, v i • Pi.single i 1 := by
    ext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]

theorem c2BoundAt_linear_direction {v : ℝ → E} {d B k : ℝ}
    (hd : 0 ≤ d) (hB : 0 ≤ B) (hv : ContDiffAt ℝ 2 v k)
    (hb : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c v k‖ ≤ d)
    (L : E →L[ℝ] ℝ) (hL : ∀ w : E, |L w| ≤ B*‖w‖) :
    C2BoundAt (3*d*B) (fun t => L (v t)) k := by
  have hc (i : Fin 3) : |L (Pi.single i 1)| ≤ B := by
    simpa only [Pi.norm_single,norm_one,mul_one] using hL (Pi.single i 1)
  have H := C2BoundAt.sum Finset.univ (by positivity : 0 ≤ d*B)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      ((c2BoundAt_coordinate hd hv hb i).const_mul (L (Pi.single i 1))).mono (by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hc i) hd))
  convert H using 1
  · change 3*d*B = (3:ℝ)*(d*B)
    ring
  · funext t
    rw [generator_apply_coordinate_sum L (v t)]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem c2BoundAt_bilinear_directions {v w : ℝ → E} {d B k : ℝ}
    (hd : 0 ≤ d) (hB : 0 ≤ B)
    (hv : ContDiffAt ℝ 2 v k) (hw : ContDiffAt ℝ 2 w k)
    (hbv : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c v k‖ ≤ d)
    (hbw : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c w k‖ ≤ d)
    (L : E →L[ℝ] E →L[ℝ] ℝ) (hL : ∀ a b : E, |L a b| ≤ B*‖a‖*‖b‖) :
    C2BoundAt (36*d^2*B) (fun t => L (v t) (w t)) k := by
  have hinner (i : Fin 3) : C2BoundAt (3*d*B)
      (fun t => L (Pi.single i 1) (w t)) k := by
    apply c2BoundAt_linear_direction hd hB hw hbw
    intro a
    simpa only [Pi.norm_single,norm_one,mul_one] using hL (Pi.single i 1) a
  have H := C2BoundAt.sum Finset.univ (by positivity : 0 ≤ 4*d*(3*d*B))
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      (c2BoundAt_coordinate hd hv hbv i).mul (hinner i))
  convert H using 1
  · change 36*d^2*B = (3:ℝ)*(4*d*(3*d*B))
    ring
  · funext t
    exact generator_apply_coordinate_sum
      ((ContinuousLinearMap.apply ℝ ℝ (w t)).comp L) (v t)

theorem generatorComparison_c2BoundAt {F : ℝ → E → ℝ} {f : E → ℝ}
    {m : ℝ → ℝ} {v w : ℝ → E} {C B M d k : ℝ}
    (x : E) (hf : QPotential 3 B f) (hd : 0 ≤ d)
    (hm : C2BoundAt M m k)
    (hv : ContDiffAt ℝ 2 v k) (hw : ContDiffAt ℝ 2 w k)
    (hbv : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c v k‖ ≤ d)
    (hbw : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c w k‖ ≤ d)
    (hg : ∀ u : E, C2BoundAt (C*‖u‖)
      (fun t => fderiv ℝ (F t) x u-fderiv ℝ f x u) k) :
    C2BoundAt (165888*M*C*B^2*d^4)
      (fun t => pathGenerator (m t) (v t) (F t)
          (fun y => (fderiv ℝ f y (w t))^2) x-
        pathGenerator (m t) (v t) f
          (fun y => (fderiv ℝ f y (w t))^2) x) k := by
  have hD := moving_gradient_sub_c2BoundAt x hd hv hbv hg
  have hA := c2BoundAt_linear_direction hd hf.nonneg hw hbw (fderiv ℝ f x)
    (fun a => hf.directional_le (by norm_num) x a)
  have hH := c2BoundAt_bilinear_directions hd hf.nonneg hv hw hbv hbw
    (fderiv ℝ (fderiv ℝ f) x) (fun a b => by
      simpa only [Real.norm_eq_abs] using
        ((hf.derivativeJets.derivativeJets.apply_const a).apply_const b).norm_le x)
  have H := ((hm.mul hD).mul hA).mul hH
  have H' := H.const_mul 2
  convert H' using 1
  · norm_num
    ring
  · funext t
    have hs : HasFDerivAt (fun y => fderiv ℝ f y (w t))
        ((ContinuousLinearMap.apply ℝ ℝ (w t)).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ (w t)).hasFDerivAt.comp x
        ((hf.smooth.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
    have hs2 := (hs.mul hs).fderiv
    have he : fderiv ℝ (fun y => (fderiv ℝ f y (w t))^2) x (v t) =
        2*fderiv ℝ f x (w t)*fderiv ℝ (fderiv ℝ f) x (v t) (w t) := by
      have Hs := congrArg (fun L : E →L[ℝ] ℝ => L (v t)) hs2
      change fderiv ℝ (fun y => fderiv ℝ f y (w t)*fderiv ℝ f y (w t)) x (v t) = _ at Hs
      simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply,smul_eq_mul] at Hs
      calc
        _ = fderiv ℝ f x (w t)*fderiv ℝ (fderiv ℝ f) x (v t) (w t)+
            fderiv ℝ f x (w t)*fderiv ℝ (fderiv ℝ f) x (v t) (w t) := by
          simpa only [pow_two] using Hs
        _ = _ := by ring
    dsimp only [pathGenerator]
    rw [he]
    ring

theorem scalarData_orderedInner_fixed_gradient_sub_c2BoundAt {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap → ∀ x w : E,
      let α := cdf (D.μ : Measure ℝ)
      C2BoundAt (C*h*‖w‖) (fun t =>
        fderiv ℝ (orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t) x w-
          fderiv ℝ (massVariationTerminal β α (r-h) h) x w) k := by
  by_cases hlu : l ≤ u
  · obtain ⟨C₀,hS,kapS,hC₀,hhS,hkapS,hsub⟩ := scalarData_orderedInner_sub_c3 D hl hu
    obtain ⟨C₁,hJ,hC₁,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
    obtain ⟨A,a0,hV,_,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    let C := C₀+C₁
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨C,min hS (min hJ (min hV (kStabilityInteriorRadius D.q l u))),
      min kapS (1/4),by positivity,lt_min hhS (lt_min hhJ (lt_min hhV
        (kStabilityInteriorRadius_pos hl hu))),lt_min hkapS (by norm_num),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk x w
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let qs := ps.drop (j.val+1)
    let f := massVariationTerminal β α (r-h) h
    let F := fun t => vectorIncrementChain (qs.map (fun p => p t)) f
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
    have H := hg w
    simp_rw [heF] at H
    exact H
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

theorem generatorSumComparison_c2BoundAt {F : ℝ → E → ℝ} {f : E → ℝ}
    (ps : List (ℝ → ℝ × E)) {w : ℝ → E} {C B M d k : ℝ}
    (x : E) (hf : QPotential 3 B f) (hd : 0 ≤ d)
    (hm : ∀ p ∈ ps, C2BoundAt M (fun t => (p t).1) k)
    (hv : ∀ p ∈ ps, ContDiffAt ℝ 2 (fun t => (p t).2) k)
    (hbv : ∀ p ∈ ps, ∀ c : ℕ, c ≤ 2 →
      ‖iteratedDeriv c (fun t => (p t).2) k‖ ≤ d)
    (hw : ContDiffAt ℝ 2 w k)
    (hbw : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c w k‖ ≤ d)
    (hg : ∀ u : E, C2BoundAt (C*‖u‖)
      (fun t => fderiv ℝ (F t) x u-fderiv ℝ f x u) k) :
    C2BoundAt ((ps.length:ℝ)*(165888*M*C*B^2*d^4))
      (fun t => pathGeneratorSum (F t) (fun y => (fderiv ℝ f y (w t))^2)
          (ps.map (fun p => p t)) x-
        pathGeneratorSum f (fun y => (fderiv ℝ f y (w t))^2)
          (ps.map (fun p => p t)) x) k := by
  induction ps with
  | nil =>
    simpa only [List.map_nil,pathGeneratorSum,sub_self,List.length_nil,
      Nat.cast_zero,zero_mul,abs_zero] using C2BoundAt.const 0 k
  | cons p ps ih =>
    have hh := generatorComparison_c2BoundAt x hf hd (hm p (by simp))
      (hv p (by simp)) hw (hbv p (by simp)) hbw hg
    have ht := ih (fun q hq => hm q (by simp [hq]))
      (fun q hq => hv q (by simp [hq])) (fun q hq => hbv q (by simp [hq]))
    convert hh.add ht using 1
    · simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      ring
    · funext t
      simp only [List.map_cons,pathGeneratorSum]
      ring

private theorem generator_window_direction_bound (β : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (α : ℝ → ℝ) (s h : ℝ), 0 ≤ h → ∀ N : ℕ,
      ∀ p ∈ windowKCurves β α s h N, ∀ k : ℝ, |k| ≤ 1/2 →
      ∀ c : ℕ, c ≤ 2 →
        ‖iteratedDeriv c (fun t => (p t).2) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := window_direction_budget
  refine ⟨A*|β|,by positivity,?_⟩
  intro α s h hh N p hp k hk c hc
  obtain ⟨σ,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  have H := (hbound β h hh N i k hk).2
  interval_cases c
  · exact H.1
  · simpa only [iteratedDeriv_one] using H.2.1
  · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H.2.2

theorem scalarData_windowGeneratorComparisonC2 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    WindowGeneratorComparisonC2 D (Icc l u) := by
  by_cases hlu : l ≤ u
  · obtain ⟨G,hG,kap,hG0,hhG,hkap,hgrad⟩ :=
      scalarData_orderedInner_fixed_gradient_sub_c2BoundAt D hl hu
    obtain ⟨A,a0,hV,_,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨L,hL,hdir⟩ := generator_window_direction_bound β
    let B := terminalJetBound D 3
    have hB : 0 ≤ B := terminalJetBound_nonneg D 3
    let K := 1990656*G*B^2*L^4
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    refine ⟨K,min hG (min hV (min (kStabilityInteriorRadius D.q l u) 1)),
      min kap (1/2),hK,lt_min hhG (lt_min hhV
        (lt_min (kStabilityInteriorRadius_pos hl hu) (by norm_num))),
      lt_min hkap (by norm_num),?_⟩
    intro r hr h hh hh0 eps heps
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    intro lam hlam j k hk x
    have hhG' := hh0.trans (min_le_left _ _)
    have hhV' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhI := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hh1 := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hkG := hk.trans (min_le_left _ _)
    have hkhalf := hk.trans (min_le_right _ _)
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let qs := ps.take j.val
    let f := massVariationTerminal β α (r-h) h
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let w := fun t => (p t).2
    let F := fun t => vectorIncrementChain
      ((massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam).drop j.val) f
    have hp : p ∈ ps := orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    have hmem : ∀ p ∈ qs, p ∈ ps := fun p hp => List.mem_of_mem_take hp
    have hinputs := (hvar r hr h hh hhV' N hN lam hlam k hkhalf).2
    have hw : ContDiffAt ℝ 2 w k := (hinputs p hp).1.snd
    have hwd := hdir _ _ _ hh.le N p hp k hkhalf
    have ht : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
      have H := kStability_time_mem hr hh.le hhI
        (show (4:ℝ) ∈ Icc (0:ℝ) 4 by norm_num)
      constructor <;> linarith [H.1,H.2,D.q_mem.2]
    have hf : QPotential 3 B f := scalarData_massVariationTerminal_qPotential D 3 ht
    have hmass : ∀ p ∈ qs, C2BoundAt 1 (fun t => (p t).1) k := by
      intro p hp
      obtain ⟨hr,hm,hd1,hd2⟩ := hinputs p (hmem p hp)
      refine ⟨by norm_num,hr.fst,?_⟩
      intro c hc
      interval_cases c
      · simpa only [iteratedDeriv_zero,abs_of_nonneg (ha0.le.trans hm.1)] using hm.2
      · simpa only [iteratedDeriv_one] using hd1
      · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hd2
    have heq : (fun t => pathGeneratorSum (F t) (fun y => (fderiv ℝ f y (w t))^2)
        (qs.map (fun p => p t)) x-
      pathGeneratorSum f (fun y => (fderiv ℝ f y (w t))^2)
        (qs.map (fun p => p t)) x) =
        orderedEnergyAssemblyTerm β α (α (r-h)) (r-h) h N lam j x 2 := by
      funext t
      dsimp only [qs,ps,w,p,F,f]
      rw [List.map_take,windowKCurves_apply β _ (r-h) h t N hh.le,
        ← massPath_window_eq β α (α (r-h)) lam (1/2) (r-h) h t N,
        orderedWindowCurve_apply β α (α (r-h)) (r-h) h N lam j hh.le t]
      rfl
    by_cases hj : j.val = 0
    · rw [← heq]
      have hqs : qs = [] := by simp only [qs,hj,List.take_zero]
      simpa only [hqs,List.map_nil,pathGeneratorSum,sub_self,abs_zero] using
        (C2BoundAt.const 0 k).mono (by simp only [abs_zero]; positivity)
    · have hj1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr hj
      let jp : Fin (12*N) := ⟨j.val-1,by omega⟩
      have hF : F = fun t => orderedInnerChain β α (α (r-h)) (1/2)
          (r-h) h N lam jp t := by
        funext t y
        dsimp only [F,orderedInnerChain,jp]
        rw [Nat.sub_add_cancel hj1]
      have hg (z : E) : C2BoundAt ((G*h)*‖z‖)
          (fun t => fderiv ℝ (F t) x z-fderiv ℝ f x z) k := by
        rw [hF]
        exact hgrad r hr h hh hhG' N hN lam hlam jp k hkG x z
      have H := generatorSumComparison_c2BoundAt qs x hf
        (by positivity : 0 ≤ L*Real.sqrt (h/(N:ℝ))) hmass
        (fun p hp => (hinputs p (hmem p hp)).1.snd)
        (fun p hp => hdir _ _ _ hh.le N p (hmem p hp) k hkhalf)
        hw hwd hg
      rw [heq] at H
      apply H.mono
      have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
      have hlen : (qs.length:ℝ) ≤ 12*(N:ℝ) := by
        have H : qs.length ≤ 12*N := by
          exact (List.length_take_le j.val ps).trans j.isLt.le
        exact_mod_cast H
      have hsq : (L*Real.sqrt (h/(N:ℝ)))^4 = L^4*h^2/(N:ℝ)^2 := by
        rw [mul_pow,show (Real.sqrt (h/(N:ℝ)))^4 =
          ((Real.sqrt (h/(N:ℝ)))^2)^2 by ring,
          Real.sq_sqrt (div_nonneg hh.le hn.le)]
        ring
      have hsmall : h^3 ≤ Real.sqrt h*h^2 := by
        have hs : h ≤ Real.sqrt h := Real.le_sqrt_of_sq_le (by
          nlinarith only [mul_nonneg hh.le (sub_nonneg.mpr hh1)])
        nlinarith only [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hs)]
      calc
        _ ≤ (12*(N:ℝ))*(165888*1*(G*h)*B^2*(L*Real.sqrt (h/(N:ℝ)))^4) := by
          gcongr
        _ = K*h^3/(N:ℝ) := by rw [hsq]; dsimp only [K]; field_simp; ring
        _ ≤ K*(Real.sqrt h*h^2)/(N:ℝ) := by gcongr
        _ ≤ K*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ) :=
          le_add_of_nonneg_right (by positivity)
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner
