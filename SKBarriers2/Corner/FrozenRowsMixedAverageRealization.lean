module

public import SKBarriers2.Corner.FrozenRowsMixed26
public import SKBarriers2.Corner.FrozenRowsMixedRecursion
public import SKBarriers2.Corner.FrozenRowsPotential22

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

theorem FrozenRowsNaturalRealization.bell_value_eq {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (q : Fin 12) (i : Fin 3) (y : Vec3) :
    frozenRowsNaturalBellTest β α s h z ε q i
      (frozenRowsNaturalParameterCurve β α a s h z ε k,y) =
    normalizedMovingBellTest (Real.sqrt h) (frozenRowsHead β a h q.val k).1
      (fun κ e => epsilonChain ((frozenSchedule β a (1/2) h κ).drop (q.val+1))
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) e)
      i k ε (Real.sqrt h • y+(fun _ => z)) := by
  have hm := (frozenRowsNaturalHead_values β α a s h z ε k H.mass_pos H.scale_pos.le q).1
  fin_cases i <;>
    simp only [frozenRowsNaturalBellTest,epsilonBellFamilies,
      Matrix.cons_val_zero',Matrix.cons_val_succ',frozenRowsNaturalNormalizedEpsilonJet,
      H.epsilon_eq k hk,hm,normalizedMovingBellTest,epsilonBellTestsKJet,
      MomentKJet.const,MomentKJet.add,MomentKJet.scale,MomentKJet.mul] <;> ring

theorem FrozenRowsNaturalRealization.translated_density_eq
    {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (q : Fin 12) (u : ℝ → Vec3) (t : ℝ) (y : Vec3) :
    affineCoordinateDensityPotential (frozenRowsNaturalHead h z q)
      (frozenRowsNaturalPotential β α s h z ε (q.val+1))
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k,(y,t)) =
    frozenCompletedHeadLogInput β α a s h z ε q k t
      (y+(Real.sqrt h)⁻¹ • u k) := by
  have hp := frozenRowsTranslated_head_values β α a s h z ε k
    H.mass_pos H.scale_pos.le q u
  have hn := frozenRowsNaturalHead_values β α a s h z ε k
    H.mass_pos H.scale_pos.le q
  have ht := (frozenRowsTranslated_tail_families β α a s h z ε q u k).1
  rw [← H.head_density_eq hk q t (y+(Real.sqrt h)⁻¹ • u k)]
  unfold affineCoordinateDensityPotential affineCoordinateEndpoint
  rw [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,ht,
    hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]
  congr 2
  rw [map_add,map_smul]
  abel

theorem FrozenRowsNaturalRealization.translated_density_eq_fine
    {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (parent q : Fin 12) (g t : ℝ) (y : Vec3) :
    affineCoordinateDensityPotential (frozenRowsNaturalHead h z q)
      (frozenRowsNaturalPotential β α s h z ε (q.val+1))
      (frozenRowsTranslatedParameterCurve β α a s h z ε q
        (fun κ => g • (frozenRowsHead β a h parent.val κ).2) k,(y,t)) =
    frozenCompletedFineLogInput β α a s h z ε q parent k g t y :=
  H.translated_density_eq hk q _ t y

theorem FrozenRowsNaturalRealization.translated_average_eq
    {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (q : Fin 12) (i : Fin 3) (u : ℝ → Vec3) (y : Vec3)
    (hD : 0 < (riccatiRecursion ((frozenSchedule β a (1/2) h k).drop (q.val+1))
      ((terminalTaylorQuadratic β α s h z).scale (1-ε))).precision
        (frozenRowsHead β a h q.val k).1 (frozenRowsHead β a h q.val k).2)
    {L : ℝ} (hR : Continuous (epsilonFrameResidual
      ((frozenSchedule β a (1/2) h k).drop (q.val+1))
      (terminalTaylorQuadratic β α s h z) (frozenTerminal β α s h) ε))
    (hLip : ∀ x w, |epsilonFrameResidual
      ((frozenSchedule β a (1/2) h k).drop (q.val+1))
      (terminalTaylorQuadratic β α s h z) (frozenTerminal β α s h) ε x-
      epsilonFrameResidual ((frozenSchedule β a (1/2) h k).drop (q.val+1))
      (terminalTaylorQuadratic β α s h z) (frozenTerminal β α s h) ε w| ≤ L*‖x-w‖) :
    normalizedMovingBellAverage (Real.sqrt h) (frozenRowsHead β a h q.val k).1
      (fun κ => (frozenRowsHead β a h q.val κ).2)
      (fun κ => Real.sqrt h • y+(fun _ => z)+u κ)
      (fun κ e => epsilonChain ((frozenSchedule β a (1/2) h κ).drop (q.val+1))
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) e) ε i k =
    affineCoordinateAverage (frozenRowsNaturalHead h z q)
      (frozenRowsNaturalPotential β α s h z ε (q.val+1))
      (frozenRowsNaturalBellTest β α s h z ε q i)
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k,y) := by
  let ρ := Real.sqrt h
  let c : Vec3 := fun _ => z
  let p := frozenRowsNaturalParameterCurve β α a s h z ε k
  let tail := (frozenSchedule β a (1/2) h k).drop (q.val+1)
  let Q := terminalTaylorQuadratic β α s h z
  let R := epsilonFrameResidual tail Q (frozenTerminal β α s h) ε
  let P := riccatiRecursion tail (Q.scale (1-ε))
  let m := (frozenRowsHead β a h q.val k).1
  let v := (frozenRowsHead β a h q.val k).2
  let A := quadraticMeanLinear P m v
  let b := quadraticNoiseConstant P m v
  let w := (Real.sqrt (P.precision m v)⁻¹) • v
  let ψ := normalizedMovingBellTest ρ m
    (fun κ e => epsilonChain ((frozenSchedule β a (1/2) h κ).drop (q.val+1))
      Q (terminalResidual β α s h z) e) i k ε
  have hρ : ρ ≠ 0 := (Real.sqrt_pos.mpr H.scale_pos).ne'
  have hψ (x : Vec3) : ψ x = frozenRowsNaturalBellTest β α s h z ε q i
      (p,ρ⁻¹ • (x-c)) := by
    rw [H.bell_value_eq hk]
    have he : ρ • (ρ⁻¹ • (x-c))+c = x := by
      rw [smul_smul,mul_inv_cancel₀ hρ,one_smul]
      abel
    exact congrArg ψ he.symm
  have hψc : Continuous ψ := by
    have he : ψ = fun x => frozenRowsNaturalBellTest β α s h z ε q i
        (p,ρ⁻¹ • (x-c)) := funext hψ
    rw [he]
    exact (H.bell_smooth q i).1.continuous.comp (by fun_prop)
  have hF (x : Vec3) : epsilonChain tail Q (terminalResidual β α s h z) ε x =
      P.value x+R x := by
    have HE := epsilonFrameResidual_eq_actual tail Q (frozenTerminal β α s h) ε x
    change R x = epsilonChain tail Q (terminalResidual β α s h z) ε x-P.value x at HE
    exact ((eq_sub_iff_add_eq.mp HE).symm).trans (add_comm _ _)
  have Hsquare := completedSquare_moment_eq_tiltedAverage P m v
    (ρ • y+c+u k) hD hR hψc hLip
  have Hrescale := congrFun (StepCalculus.spatialRescale_affine_tiltedAverage hρ
    m (quadraticMeanLinear P m v) (quadraticNoiseConstant P m v) c
    ((Real.sqrt (P.precision m v)⁻¹) • v) R ψ) (y+ρ⁻¹ • u k)
  have hx : ρ • (y+ρ⁻¹ • u k)+c = ρ • y+c+u k := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ hρ,one_smul]
    abel
  dsimp only [spatialRescale] at Hrescale
  rw [hx] at Hrescale
  unfold normalizedMovingBellAverage
  change epsilonMoment m v (fun e => epsilonChain tail Q (terminalResidual β α s h z) e)
    (fun _ => ψ) ε (ρ • y+c+u k) = _
  have he : epsilonMoment m v (fun e => epsilonChain tail Q (terminalResidual β α s h z) e)
      (fun _ => ψ) ε (ρ • y+c+u k) =
      epsilonMoment m v (fun _ x => P.value x+R x) (fun _ => ψ) 0 (ρ • y+c+u k) := by
    unfold epsilonMoment
    simp only [hF]
  rw [he,Hsquare,Hrescale]
  have hp := frozenRowsTranslated_head_values β α a s h z ε k
    H.mass_pos H.scale_pos.le q u
  have ht := frozenRowsTranslated_tail_families β α a s h z ε q u k
  have hmass : Real.exp ((frozenRowsNaturalHead h z q).logMass
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k)) = m := hp.1
  have hmean : (frozenRowsNaturalHead h z q).mean
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k) = A := hp.2.1
  have hnoise : (frozenRowsNaturalHead h z q).noise
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k) = ρ⁻¹ • w := hp.2.2.1
  have hshift : (frozenRowsNaturalHead h z q).shift
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k) =
      ρ⁻¹ • (A c+b-c)+ρ⁻¹ • A (u k) := hp.2.2.2
  unfold affineCoordinateAverage
  rw [hmass,hmean,hnoise,hshift]
  have hB : (fun x => frozenRowsNaturalPotential β α s h z ε (q.val+1)
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k,x)) =
      fun x => R (ρ • x+c) := by
    funext x
    rw [ht.1,H.potential_eq k hk]
  have hG : (fun x => frozenRowsNaturalBellTest β α s h z ε q i
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k,x)) =
      fun x => ψ (ρ • x+c) := by
    funext x
    rw [frozenRowsTranslated_bellTest_eq,H.bell_value_eq hk]
  rw [hB,hG]
  change StepCalculus.tiltedAverage m (ρ⁻¹ • w) (fun x => R (ρ • x+c))
    (fun x => ψ (ρ • x+c)) (A (y+ρ⁻¹ • u k)+ρ⁻¹ • (A c+b-c)) =
      StepCalculus.tiltedAverage m (ρ⁻¹ • w) (fun x => R (ρ • x+c))
        (fun x => ψ (ρ • x+c)) (A y+(ρ⁻¹ • (A c+b-c)+ρ⁻¹ • A (u k)))
  congr 1
  rw [map_add,map_smul]
  abel

theorem normalizedMovingBellKJet_eq_of_average_eq {m ε k : ℝ}
    {v x : ℝ → Vec3} {F : ℝ → ℝ → Vec3 → ℝ} {ρ : ℝ} {i : Fin 3}
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P × Vec3 → ℝ) (p : ℝ → P) (y : Vec3)
    (hk : k ∈ frozenRowsKDomain)
    (he : ∀ κ ∈ frozenRowsKDomain,
      normalizedMovingBellAverage ρ m v x F ε i κ = A (p κ,y)) :
    normalizedMovingBellKJet ρ m v x F ε i k = parameterCurveKJet A p k y := by
  apply MomentKJet.totalJets_congr
    (f := normalizedMovingBellAverage ρ m v x F ε i)
    (g := fun κ => A (p κ,y))
  filter_upwards [(show IsOpen frozenRowsKDomain from isOpen_Ioo).mem_nhds hk] with κ hκ
  exact he κ hκ

theorem normalizedMovingBellKJet_differentiates_of_paramSmooth_average
    {m ε k ρ : ℝ} {v x : ℝ → Vec3} {F : ℝ → ℝ → Vec3 → ℝ} {i : Fin 3}
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : P × Vec3 → ℝ} (hA : ParamSmooth A) {p : ℝ → P}
    (hp : ContDiffAt ℝ 2 p k) (y : Vec3) (hk : k ∈ frozenRowsKDomain)
    (he : ∀ κ ∈ frozenRowsKDomain,
      normalizedMovingBellAverage ρ m v x F ε i κ = A (p κ,y)) :
    MomentKJet.Differentiates (normalizedMovingBellKJet ρ m v x F ε i) k := by
  have he' : normalizedMovingBellAverage ρ m v x F ε i =ᶠ[𝓝 k]
      fun κ => A (p κ,y) := by
    filter_upwards [(show IsOpen frozenRowsKDomain from isOpen_Ioo).mem_nhds hk] with κ hκ
    exact he κ hκ
  have hS : ContDiffAt ℝ 2 (normalizedMovingBellAverage ρ m v x F ε i) k :=
    (hA.1.contDiffAt.comp k (hp.prodMk contDiffAt_const)).congr_of_eventuallyEq he'
  exact ⟨(hS.differentiableAt (by norm_num)).hasDerivAt,
    ((hS.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt⟩

theorem scalarData_frozenRows_average_inputs {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r-h)
      FrozenRowsNaturalRealization β α a (r-h) h z ε ∧
      ∀ k ∈ frozenRowsKDomain, ∀ q : Fin 12,
        let tail := (frozenSchedule β a (1/2) h k).drop (q.val+1)
        let Q := terminalTaylorQuadratic β α (r-h) h z
        let R := epsilonFrameResidual tail Q (frozenTerminal β α (r-h) h) ε
        0 < (riccatiRecursion tail (Q.scale (1-ε))).precision
          (frozenRowsHead β a h q.val k).1 (frozenRowsHead β a h q.val k).2 ∧
        ∃ L : ℝ, Continuous R ∧ ∀ x w, |R x-R w| ≤ L*‖x-w‖ := by
  obtain ⟨hR,hhR,HR⟩ := scalarData_frozenRows_natural_realization D hl hu
  obtain ⟨hA,_,hhA,_,HA⟩ := scalarData_frozen_suffix_lipschitz_frames D hl hu
  obtain ⟨C,hQ,_,hhQ,HQ⟩ := scalarData_epsilonFrameResidual_spatial_qPotential D hl hu 2 le_rfl
  refine ⟨min hR (min hA hQ),lt_min hhR (lt_min hhA hhQ),?_⟩
  intro r hr h hh hhsmall z ε hε
  have hcaps : h ≤ hR ∧ h ≤ hA ∧ h ≤ hQ := by simpa only [le_min_iff] using hhsmall
  refine ⟨HR r hr h hh hcaps.1 z ε hε,?_⟩
  intro k hk q
  have hk' : |k| ≤ 1/2 := abs_le.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩
  have hε' : ε ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hε.1],by linarith [hε.2]⟩
  have HAdm := (HA r hr h hh hcaps.2.1 k hk' z ε hε' _ (List.drop_suffix q.val _)).1
  rw [frozenSchedule_drop_cons] at HAdm
  have Hq := HQ r hr h hh hcaps.2.2 k hk' z ε hε' _ (List.drop_suffix (q.val+1) _)
  exact ⟨HAdm.2.2,C,Hq.smooth.continuous,fun x w =>
    (Hq.lipschitzWith (by norm_num)).norm_sub_le x w⟩

theorem scalarData_frozenRows_translated_potential_qPotential {β l u : ℝ}
    (D : ScalarData β) (hl : 0 < l) (hu : u < D.q) (R : ℕ) (hR : 2 ≤ R) :
    ∃ h₀ B : ℝ, 0 < h₀ ∧ 0 < B ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ q : Fin 12, ∀ u : ℝ → Vec3, ∀ k ∈ frozenRowsKDomain,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r-h)
      QPotential R B (fun y => frozenRowsNaturalPotential β α (r-h) h z ε (q.val+1)
        (frozenRowsTranslatedParameterCurve β α a (r-h) h z ε q u k,y)) := by
  obtain ⟨hN,hhN,HN⟩ := scalarData_frozenRows_natural_realization D hl hu
  obtain ⟨B,hQ,hB,hhQ,HQ⟩ := scalarData_epsilonFrameResidual_spatial_qPotential D hl hu R hR
  refine ⟨min hN (min hQ 1),B,lt_min hhN (lt_min hhQ (by norm_num)),hB,?_⟩
  intro r hr h hh hhsmall z ε hε q u k hk
  dsimp only
  have hcaps : h ≤ hN ∧ h ≤ hQ ∧ h ≤ 1 := by simpa only [le_min_iff] using hhsmall
  have H := HN r hr h hh hcaps.1 z ε hε
  have hk' : |k| ≤ 1/2 := abs_le.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩
  have hε' : ε ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hε.1],by linarith [hε.2]⟩
  have Hq := HQ r hr h hh hcaps.2.1 k hk' z ε hε' _ (List.drop_suffix (q.val+1) _)
  have hρ : |Real.sqrt h| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr hcaps.2.2
  have Hscaled := Hq.spatialRescale hρ (fun _ => z)
  have he : (fun y => frozenRowsNaturalPotential β (cdf (D.μ : Measure ℝ))
      (r-h) h z ε (q.val+1)
      (frozenRowsTranslatedParameterCurve β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h z ε q u k,y)) =
      spatialRescale (Real.sqrt h) (fun _ => z)
        (epsilonFrameResidual ((frozenSchedule β (cdf (D.μ : Measure ℝ) (r-h))
          (1/2) h k).drop (q.val+1))
          (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r-h) h z)
          (frozenTerminal β (cdf (D.μ : Measure ℝ)) (r-h) h) ε) := by
    funext y
    rw [(frozenRowsTranslated_tail_families β (cdf (D.μ : Measure ℝ))
      (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h z ε q u k).1,H.potential_eq k hk]
    rfl
  rw [he]
  exact Hscaled

end SKBarriers2.Corner
