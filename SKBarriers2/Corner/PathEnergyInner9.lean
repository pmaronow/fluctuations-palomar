module

public import SKBarriers2.Corner.PathEnergyInner8
public import SKBarriers2.Corner.PathEnergyQuadraticJets

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem inner9_window_direction_bound (β : ℝ) :
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

theorem scalarData_orderedInner_valueRemainder_spatial_twoJets {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
      ∀ c : ℕ, c ≤ 2 →
      let α := cdf (D.μ : Measure ℝ)
      QBoundedJets 2 (C*h) (fun x => iteratedDeriv c (fun t =>
        orderedInnerValueRemainder β α (α (r-h)) (r-h) h N lam j t x) k) := by
  by_cases hlu : l ≤ u
  · obtain ⟨C₀,hS,kapS,hC₀,hhS,hkapS,hsub⟩ := scalarData_orderedInner_sub_c3 D hl hu
    obtain ⟨C₁,hJ,hC₁,hhJ,hvariations⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
    obtain ⟨A,a0,hV,_,ha0,hhV,hinputs⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨L,hL,hdir⟩ := inner9_window_direction_bound β
    let B := terminalJetBound D 4
    have hB : 0 ≤ B := terminalJetBound_nonneg D 4
    let P := (2*B+20*B^2)*12*L^2
    have hP : 0 ≤ P := by dsimp only [P]; positivity
    refine ⟨C₀+C₁+P,min hS (min hJ (min hV (kStabilityInteriorRadius D.q l u))),
      min kapS (1/2),by positivity,lt_min hhS (lt_min hhJ
        (lt_min hhV (kStabilityInteriorRadius_pos hl hu))),lt_min hkapS (by norm_num),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk c hc
    dsimp only
    have hhS' := hh0.trans (min_le_left _ _)
    have hhJ' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhV' := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hhI := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hkhalf := hk.trans (min_le_right _ _)
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let qs := ps.drop (j.val+1)
    let f := massVariationTerminal β α (r-h) h
    have ht : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
      have H := kStability_time_mem hr hh.le hhI (show (4:ℝ) ∈ Icc (0:ℝ) 4 by norm_num)
      constructor <;> linarith [H.1,H.2,D.q_mem.2]
    have hf := scalarData_massVariationTerminal_qPotential D 4 ht
    have hi := (hinputs r hr h hh hhV' N hN lam hlam k hkhalf).2
    have hmem : ∀ p ∈ qs, p ∈ ps := fun p hp => List.mem_of_mem_drop hp
    have hreg : ∀ p ∈ qs, ContDiffAt ℝ 2 p k := fun p hp => (hi p (hmem p hp)).1
    have hpos : ∀ p ∈ qs, 0 < (p k).1 := fun p hp => ha0.trans_le (hi p (hmem p hp)).2.1.1
    let d := L*Real.sqrt (h/(N:ℝ))
    have hd : 0 ≤ d := by dsimp only [d]; positivity
    have hjets : ∀ p ∈ qs,
        (p k).1 ∈ Icc (0:ℝ) 1 ∧ |deriv (fun t => (p t).1) k| ≤ 1 ∧
        |deriv (deriv (fun t => (p t).1)) k| ≤ 1 ∧
        ‖(p k).2‖ ≤ d ∧ ‖deriv (fun t => (p t).2) k‖ ≤ d ∧
        ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ d := by
      intro p hp
      have H := hi p (hmem p hp)
      have Hd := hdir _ _ _ hh.le N p (hmem p hp) k hkhalf
      exact ⟨⟨ha0.le.trans H.2.1.1,H.2.1.2⟩,H.2.2.1,H.2.2.2,Hd⟩
    have hPjets := qBoundedJets_pathQuadraticSum_parameter hf qs hreg hjets c hc
    have hlen : (qs.length:ℝ) ≤ 12*(N:ℝ) := by
      exact_mod_cast (show qs.length ≤ 12*N from by
        dsimp only [qs,ps]
        rw [List.length_drop,windowKCurves_length]
        omega)
    have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
    have hd2 : d^2 = L^2*h/(N:ℝ) := by
      dsimp only [d]
      rw [mul_pow,Real.sq_sqrt (div_nonneg hh.le (Nat.cast_nonneg N))]
      ring
    have hPjets' : QBoundedJets 2 (P*h) (fun x => iteratedDeriv c
        (fun t => pathQuadraticSum f (qs.map (fun p => p t)) x) k) := by
      apply hPjets.mono
      calc
        _ ≤ (2*B+20*B^2)*(12*(N:ℝ))*d^2 := by gcongr
        _ = _ := by rw [hd2]; dsimp only [P]; field_simp [ne_of_gt hNpos]
    have heF (t : ℝ) : vectorIncrementChain (qs.map (fun p => p t)) f =
        orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t := by
      dsimp only [qs,ps,orderedInnerChain]
      rw [List.map_drop,windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
    have hbase : QBoundedJets 2 ((C₀+C₁)*h) (fun x => iteratedDeriv c
        (fun t => vectorIncrementChain (qs.map (fun p => p t)) f x-f x) k) := by
      simp_rw [heF]
      interval_cases c
      · simp only [iteratedDeriv_zero]
        exact ((hsub r hr h hh hhS' N hN lam hlam j k (hk.trans (min_le_left _ _))).of_le
          (by norm_num : 2 ≤ 3)).mono (by nlinarith only [mul_nonneg hC₁.le hh.le])
      · simp only [iteratedDeriv_one,deriv_sub_const]
        have hcoeff : C₁*h ≤ (C₀+C₁)*h := by
          nlinarith only [mul_nonneg hC₀ hh.le]
        have H := ((hvariations r hr h hh hhJ' N hN lam hlam j k hkhalf).1.of_le
          (by norm_num : 2 ≤ 6)).mono hcoeff
        change QBoundedJets 2 ((C₀+C₁)*h) (fun x => iteratedDeriv 1 (fun t =>
          orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t x) k) at H
        simpa only [iteratedDeriv_one] using H
      · simp only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_sub_const_fun]
        have hcoeff : C₁*h ≤ (C₀+C₁)*h := by
          nlinarith only [mul_nonneg hC₀ hh.le]
        have H := ((hvariations r hr h hh hhJ' N hN lam hlam j k hkhalf).2.of_le
          (by norm_num : 2 ≤ 4)).mono hcoeff
        change QBoundedJets 2 ((C₀+C₁)*h) (fun x => iteratedDeriv 2 (fun t =>
          orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t x) k) at H
        simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H
    have he : (fun x => iteratedDeriv c (fun t =>
        orderedInnerValueRemainder β α (α (r-h)) (r-h) h N lam j t x) k) =
        fun x => iteratedDeriv c (fun t => vectorIncrementChain (qs.map (fun p => p t)) f x-f x) k-
          iteratedDeriv c (fun t => pathQuadraticSum f (qs.map (fun p => p t)) x) k := by
      funext x
      have heq (t : ℝ) : orderedInnerValueRemainder β α (α (r-h)) (r-h) h N lam j t x =
          chainFirstOrderRemainder f (qs.map (fun p => p t)) x := by
        dsimp only [orderedInnerValueRemainder,qs,ps]
        rw [List.map_drop,windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
      simp_rw [heq]
      have hchain := (ParamChain.contDiffAt_curveChain qs hf (by norm_num) hreg hpos x).comp k
        (contDiffAt_id.prodMk contDiffAt_const)
      exact iteratedDeriv_fun_sub ((hchain.sub contDiffAt_const).of_le (by exact_mod_cast hc))
        ((contDiffAt_pathQuadraticSum (hf.of_le (by norm_num)) qs hreg x).of_le (by exact_mod_cast hc))
    rw [he]
    convert hbase.sub hPjets' using 1
    ring
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

theorem scalarData_orderedInner_gradientRemainder_c2BoundAt {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ R h0 kap : ℝ, 0 ≤ R ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap → ∀ x : E,
      let α := cdf (D.μ : Measure ℝ)
      C2BoundAt (R*Real.sqrt h*h*Real.sqrt (h/(N:ℝ)))
        (orderedInnerGradientRemainder β α (α (r-h)) (r-h) h N lam j x) k := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,hA0,kapA,hA,hhA,hkapA,hvalues⟩ :=
      scalarData_orderedInner_valueRemainder_jets_bound D hl hu
    obtain ⟨B,hB0,kapB,hB,hhB,hkapB,hspatial⟩ :=
      scalarData_orderedInner_valueRemainder_spatial_twoJets D hl hu
    obtain ⟨W,a0,hV,_,ha0,hhV,hinputs⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨L,hL,hdir⟩ := inner9_window_direction_bound β
    refine ⟨12*L*(3*A+B),min hA0 (min hB0 (min hV
      (min (kStabilityInteriorRadius D.q l u) 1))),min kapA (min (kapB/2) (1/4)),
      by positivity,lt_min hhA (lt_min hhB (lt_min hhV
        (lt_min (kStabilityInteriorRadius_pos hl hu) (by norm_num)))),
      lt_min hkapA (lt_min (by positivity) (by norm_num)),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk x
    dsimp only
    have hhA' := hh0.trans (min_le_left _ _)
    have hhB' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhV' := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hhI := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
    have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
    have hkhalf : |k| ≤ 1/2 := (hk.trans ((min_le_right _ _).trans (min_le_right _ _))).trans (by norm_num)
    have hkB : |k| < kapB := (hk.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt
      (by linarith)
    have hkh : |k| < 1/2 := (hk.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt
      (by norm_num)
    have hnear : ∀ᶠ t in 𝓝 k, |t| ≤ kapB ∧ |t| ≤ 1/2 := by
      filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds (lt_min hkB hkh))] with t ht
      exact ⟨(ht.trans_le (min_le_left _ _)).le,(ht.trans_le (min_le_right _ _)).le⟩
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let qs := ps.drop (j.val+1)
    let f := massVariationTerminal β α (r-h) h
    let F := fun t => chainFirstOrderRemainder f (qs.map (fun p => p t))
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let w := fun t => (p t).2
    have heF (t : ℝ) : F t = orderedInnerValueRemainder β α (α (r-h)) (r-h) h N lam j t := by
      dsimp only [F,orderedInnerValueRemainder,qs,ps]
      rw [List.map_drop,windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
    have ht : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
      have H := kStability_time_mem hr hh.le hhI (show (4:ℝ) ∈ Icc (0:ℝ) 4 by norm_num)
      constructor <;> linarith [H.1,H.2,D.q_mem.2]
    have hf := scalarData_massVariationTerminal_qPotential D 4 ht
    have hmem : ∀ q ∈ qs, q ∈ ps := fun q hq => List.mem_of_mem_drop hq
    have hreg (t : ℝ) (ht : |t| ≤ 1/2) : ∀ q ∈ qs, ContDiffAt ℝ 2 q t :=
      fun q hq => ((hinputs r hr h hh hhV' N hN lam hlam t ht).2 q (hmem q hq)).1
    have hpos (t : ℝ) (ht : |t| ≤ 1/2) : ∀ q ∈ qs, 0 < (q t).1 :=
      fun q hq => ha0.trans_le ((hinputs r hr h hh hhV' N hN lam hlam t ht).2 q (hmem q hq)).2.1.1
    have hjets : ∀ᶠ t in 𝓝 k, ∀ c : ℕ, c ≤ 2 →
        QBoundedJets 2 (B*h) (fun y => iteratedDeriv c (fun q => F q y) t) := by
      filter_upwards [hnear] with t ht c hc
      simp_rw [heF]
      exact hspatial r hr h hh hhB' N hN lam hlam j t ht.1 c hc
    have hFspace : ∀ᶠ t in 𝓝 k, ∀ y, DifferentiableAt ℝ (F t) y := by
      filter_upwards [hjets] with t ht y
      simpa only [iteratedDeriv_zero] using (ht 0 (by norm_num)).smooth.differentiable (by norm_num) y
    have hp : ∀ᶠ t in 𝓝 k, ∀ y, ContDiffAt ℝ 2 (fun q => F q y) t := by
      filter_upwards [hnear] with t ht y
      exact contDiffAt_chainFirstOrderRemainder hf qs (hreg t ht.2) (hpos t ht.2) y
    have hvalue (c : ℕ) (hc : c ≤ 2) (y : E) :
        ‖iteratedDeriv c (fun q => F q y) k‖ ≤ A*h^2+(0:ℝ)*Real.sqrt h/3 := by
      simp_rw [heF]
      simpa only [Real.norm_eq_abs,zero_mul,zero_div,add_zero] using
        hvalues r hr h hh hhA' N hN lam hlam j k (hk.trans (min_le_left _ _)) y c hc
    have hs (v : E) : ContDiffAt ℝ 2 (fun t => fderiv ℝ (F t) x v) k := by
      have hchain := (ParamChain.contDiffAt_curveChain_spatial qs hf (by norm_num)
        (hreg k hkhalf) (hpos k hkhalf) x v).comp k
          (contDiffAt_id.prodMk contDiffAt_const)
      have hgen := contDiffAt_pathGeneratorSum_curve (f := f)
        ((hf.directional v).smooth.of_le (by norm_num)) qs (hreg k hkhalf) x
      have H := (hchain.sub (contDiffAt_const (c := fderiv ℝ f x v))).sub hgen
      convert H using 1
      funext t
      exact fderiv_chainFirstOrderRemainder hf _ x v
    have hpMem : p ∈ ps := orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    have hw : ContDiffAt ℝ 2 w k :=
      ((hinputs r hr h hh hhV' N hN lam hlam k hkhalf).2 p hpMem).1.snd
    have hds := hdir _ _ _ hh.le N p hpMem k hkhalf
    have hb (c : ℕ) (hc : c ≤ 2) :
        ‖iteratedDeriv c w k‖ ≤ L*Real.sqrt (h/(N:ℝ)) := by
      interval_cases c
      · exact hds.1
      · simpa only [iteratedDeriv_one] using hds.2.1
      · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hds.2.2
    have H := moving_gradient_c2BoundAt_of_value_jets hA hB (by norm_num : (0:ℝ) ≤ 0)
      hh hh1 hFspace hp hjets hvalue x hs (by positivity) hw hb
    have he : (fun t => fderiv ℝ (F t) x (w t)) =
        orderedInnerGradientRemainder β α (α (r-h)) (r-h) h N lam j x := by
      funext t
      rw [heF]
      exact (orderedInnerGradientRemainder_eq_fderiv lam j x t hf).symm
    rw [he] at H
    convert H using 1
    ring
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

theorem scalarData_windowInnerEnergyC2 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    WindowInnerEnergyC2 D (Icc l u) := by
  obtain ⟨R,h0,kap,hR,hh0,hkap,hbound⟩ :=
    scalarData_orderedInner_gradientRemainder_c2BoundAt D hl hu
  apply scalarData_windowInnerEnergyC2_of_gradient_remainder D hl hu
  refine ⟨R,h0,kap,hR,hh0,hkap,?_⟩
  intro r hr h hh hhh0 eps heps
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  intro lam hlam j k hk x
  apply (hbound r hr h hh hhh0 N hN lam hlam j k hk x).mono
  nlinarith only [mul_nonneg heps.le (Real.sqrt_nonneg (h/(N:ℝ)))]

end SKBarriers2.Corner
