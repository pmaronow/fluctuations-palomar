module

public import SKBarriers2.Corner.FrozenRowsMixed25
public import SKBarriers2.Corner.FrozenRowsMixedValue5
public import SKBarriers2.Corner.FrozenRowsMixed18

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

def frozenRowsNaturalNormalizedEpsilonJet (β : ℝ) (α : ℝ → ℝ) (s h z ε : ℝ)
    (n : ℕ) (i : Fin 3) : (ℝ × AffineRowParameters) × Vec3 → ℝ :=
  fun p => (((Real.sqrt h)^3)^(i.val+1))⁻¹*frozenRowsNaturalEpsilonJet β α s h z ε n i p

def frozenRowsNaturalBellTest (β : ℝ) (α : ℝ → ℝ) (s h z ε : ℝ)
    (q : Fin 12) (i : Fin 3) : (ℝ × AffineRowParameters) × Vec3 → ℝ :=
  epsilonBellFamilies (fun p => Real.exp ((frozenRowsNaturalHead h z q).logMass p.1))
    (frozenRowsNaturalNormalizedEpsilonJet β α s h z ε (q.val+1)) i

theorem parameterCurveKJet_const_mul_real {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : P × Vec3 → ℝ) (p : ℝ → P) (k : ℝ) (x : Vec3) (c : ℝ) :
    parameterCurveKJet (fun z => c*F z) p k x = (parameterCurveKJet F p k x).scale c := by
  simp only [parameterCurveKJet,MomentKJet.scale,deriv_const_mul_field']

theorem FrozenRowsNaturalRealization.normalized_epsilon_smooth {β a s h z ε : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (n : ℕ) (i : Fin 3) :
    ParamSmooth (frozenRowsNaturalNormalizedEpsilonJet β α s h z ε n i) :=
  (H.epsilon_smooth n i).const_mul _

theorem FrozenRowsNaturalRealization.bell_smooth {β a s h z ε : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (q : Fin 12) (i : Fin 3) :
    ParamSmooth (frozenRowsNaturalBellTest β α s h z ε q i) :=
  smooth_epsilonBellFamilies
    (ParamChain.regular_exp_parameter (frozenRowsNaturalHead h z q).logMass).toSmooth
    (fun j => H.normalized_epsilon_smooth (q.val+1) j) i

theorem FrozenRowsNaturalRealization.normalized_jet_eq {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (n : ℕ) (i : Fin 3) (y : Vec3) :
    MomentKJet.rescale (Real.sqrt h) (parameterCurveKJet
      (frozenRowsNaturalNormalizedEpsilonJet β α s h z ε n i)
      (frozenRowsNaturalParameterCurve β α a s h z ε) k y) =
      MomentKJet.rescale (Real.sqrt h) (normalizedEpsilonKJet
        (fun κ => (frozenSchedule β a (1/2) h κ).drop n)
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
        (Real.sqrt h) (fun _ => z) (fun _ => y) (i.val+1) ε k) := by
  have hρ : Real.sqrt h ≠ 0 := (Real.sqrt_pos.mpr H.scale_pos).ne'
  rw [normalizedEpsilonKJet_eq_inverse_scale hρ,MomentKJet.rescale_scale]
  unfold frozenRowsNaturalNormalizedEpsilonJet
  rw [parameterCurveKJet_const_mul_real,MomentKJet.rescale_scale,H.rawJet_eq hk n i y]
  rfl

theorem FrozenRowsNaturalRealization.normalized_bellJet_eq {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (q : Fin 12) (i : Fin 3) (y : Vec3) :
    MomentKJet.rescale (Real.sqrt h) (parameterCurveKJet
      (frozenRowsNaturalBellTest β α s h z ε q i)
      (frozenRowsNaturalParameterCurve β α a s h z ε) k y) =
      epsilonBellTestsKJet (a*frozenUnitMass q) (fun j =>
        MomentKJet.rescale (Real.sqrt h) (normalizedEpsilonKJet
          (fun κ => (frozenSchedule β a (1/2) h κ).drop (q.val+1))
          (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
          (Real.sqrt h) (fun _ => z) (fun _ => y) (j.val+1) ε k)) i := by
  have hm (κ : ℝ) (_hκ : κ ∈ frozenRowsKDomain) :
      Real.exp ((frozenRowsNaturalHead h z q).logMass
        (frozenRowsNaturalParameterCurve β α a s h z ε κ)) = a*frozenUnitMass q := by
    rw [(frozenRowsNaturalHead_values β α a s h z ε κ H.mass_pos H.scale_pos.le q).1,
      frozenRowsHead_mass_eq β a h κ H.scale_pos.le q]
  have HB := parameterCurveKJet_Bell (show IsOpen frozenRowsKDomain from isOpen_Ioo)
    (fun κ hκ => (H.curve_smooth κ hκ).of_le (by simp))
    (fun j => H.normalized_epsilon_smooth (q.val+1) j)
    (frozenRowsNaturalHead h z q) (a*frozenUnitMass q) hm hk y (Real.sqrt h) i
  dsimp only [frozenRowsNaturalBellTest]
  rw [HB]
  congr 1
  funext j
  exact H.normalized_jet_eq hk (q.val+1) j y

def frozenRowsTranslatedParameterCurve (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (q : Fin 12) (u : ℝ → Vec3) (k : ℝ) : ℝ × AffineRowParameters :=
  let p := frozenRowsNaturalParameterCurve β α a s h z ε k
  let i : Fin 12 := ⟨11-q.val,by omega⟩
  (p.1,p.2.addHeadShift i ((affineRowCoordinate i).mean p.2 (u k)))

theorem frozenRowsTranslatedParameterCurve_contDiffAt (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (q : Fin 12) {u : ℝ → Vec3} {k : ℝ}
    (hp : ContDiffAt ℝ ∞ (frozenRowsNaturalParameterCurve β α a s h z ε) k)
    (hu : ContDiffAt ℝ ∞ u k) :
    ContDiffAt ℝ ∞ (frozenRowsTranslatedParameterCurve β α a s h z ε q u) k := by
  let i : Fin 12 := ⟨11-q.val,by omega⟩
  have hv := ((affineRowCoordinate i).mean.contDiff.contDiffAt.comp k hp.snd).clm_apply hu
  exact hp.fst.prodMk (AffineRowParameters.addHeadShift_contDiffAt hp.snd hv i)

private theorem frozenRowsNaturalCoordinates_tail_lower (h z : ℝ) (q : Fin 12) :
    (frozenRowsNaturalCoordinates h z).drop (q.val+1) =
      (affineRowCoordinates (11-q.val) (by omega)).map
        (fun c => c.centeredRescale (Real.sqrt h) (fun _ => z)) := by
  have he : 12-(q.val+1) = 11-q.val := by omega
  unfold frozenRowsNaturalCoordinates
  rw [← List.map_drop,affineRowCoordinates_drop_eq_lower]
  simp only [he]

theorem frozenRowsTranslated_tail_agree (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (q : Fin 12) (u : ℝ → Vec3) (k : ℝ) :
    ∀ c ∈ (frozenRowsNaturalCoordinates h z).drop (q.val+1),
      c.AgreeAt (frozenRowsTranslatedParameterCurve β α a s h z ε q u k)
        (frozenRowsNaturalParameterCurve β α a s h z ε k) := by
  rw [frozenRowsNaturalCoordinates_tail_lower]
  dsimp only [frozenRowsTranslatedParameterCurve]
  exact affineRowCoordinates_centered_addHeadShift_agree _ _ _ _ _ _ _ le_rfl

theorem frozenRowsTranslated_tail_families (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (q : Fin 12) (u : ℝ → Vec3) (k : ℝ) :
    (∀ y, frozenRowsNaturalPotential β α s h z ε (q.val+1)
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k,y) =
      frozenRowsNaturalPotential β α s h z ε (q.val+1)
        (frozenRowsNaturalParameterCurve β α a s h z ε k,y)) ∧
    (∀ i y, frozenRowsNaturalEpsilonJet β α s h z ε (q.val+1) i
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k,y) =
      frozenRowsNaturalEpsilonJet β α s h z ε (q.val+1) i
        (frozenRowsNaturalParameterCurve β α a s h z ε k,y)) := by
  have H := frozenRowsTranslated_tail_agree β α a s h z ε q u k
  exact ⟨affinePotentialChain_parameter_congr _ _ _ _ H (fun _ => rfl),
    affineEpsilonJetChain_parameter_congr _ _ _ _ _ H (fun _ => rfl) (fun _ => rfl)⟩

theorem frozenRowsTranslated_bellTest_eq (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (q : Fin 12) (u : ℝ → Vec3) (k : ℝ) (i : Fin 3) (y : Vec3) :
    frozenRowsNaturalBellTest β α s h z ε q i
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k,y) =
    frozenRowsNaturalBellTest β α s h z ε q i
      (frozenRowsNaturalParameterCurve β α a s h z ε k,y) := by
  let p := frozenRowsNaturalParameterCurve β α a s h z ε k
  let j : Fin 12 := ⟨11-q.val,by omega⟩
  have hm : (frozenRowsNaturalHead h z q).logMass
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u k) =
      (frozenRowsNaturalHead h z q).logMass p :=
    (affineRowCoordinate_centered_addHeadShift p.2 j
      ((affineRowCoordinate j).mean p.2 (u k)) (fun _ => z) (Real.sqrt h) p.1).1
  have htail := (frozenRowsTranslated_tail_families β α a s h z ε q u k).2
  fin_cases i <;> simp only [frozenRowsNaturalBellTest,epsilonBellFamilies,
    Matrix.cons_val_zero',Matrix.cons_val_succ',frozenRowsNaturalNormalizedEpsilonJet,
    hm,htail,p]

theorem frozenRowsTranslated_bellJet_eq (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) (q : Fin 12) (u : ℝ → Vec3) (k : ℝ) (i : Fin 3) (y : Vec3) :
    parameterCurveKJet (frozenRowsNaturalBellTest β α s h z ε q i)
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u) k y =
    parameterCurveKJet (frozenRowsNaturalBellTest β α s h z ε q i)
      (frozenRowsNaturalParameterCurve β α a s h z ε) k y := by
  unfold parameterCurveKJet
  exact MomentKJet.totalJets_congr
    (f := fun κ => frozenRowsNaturalBellTest β α s h z ε q i
      (frozenRowsTranslatedParameterCurve β α a s h z ε q u κ,y))
    (g := fun κ => frozenRowsNaturalBellTest β α s h z ε q i
      (frozenRowsNaturalParameterCurve β α a s h z ε κ,y))
    (Filter.Eventually.of_forall (fun κ => frozenRowsTranslated_bellTest_eq β α a s h z ε q u κ i y))

theorem FrozenRowsNaturalRealization.head_contDiffAt {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε)
    (hk : k ∈ frozenRowsKDomain) (q : Fin 12) :
    ContDiffAt ℝ ∞ (frozenRowsCompletedMeanLinear β α a s h z ε q.val) k ∧
      ContDiffAt ℝ ∞ (frozenRowsCompletedMeanShift β α a s h z ε q.val) k ∧
      ContDiffAt ℝ ∞ (frozenRowsCompletedHeadDirection β α a s h z ε q.val) k := by
  let p := frozenRowsNaturalParameterCurve β α a s h z ε
  let c := frozenRowsNaturalHead h z q
  have hp := H.curve_smooth k hk
  have hA : (fun κ => c.mean (p κ)) = frozenRowsCompletedMeanLinear β α a s h z ε q.val :=
    funext (fun κ => (frozenRowsNaturalHead_values β α a s h z ε κ H.mass_pos H.scale_pos.le q).2.1)
  have hb : (fun κ => c.shift (p κ)) = frozenRowsCompletedMeanShift β α a s h z ε q.val :=
    funext (fun κ => (frozenRowsNaturalHead_values β α a s h z ε κ H.mass_pos H.scale_pos.le q).2.2.1)
  have hv : (fun κ => c.noise (p κ)) = frozenRowsCompletedHeadDirection β α a s h z ε q.val :=
    funext (fun κ => (frozenRowsNaturalHead_values β α a s h z ε κ H.mass_pos H.scale_pos.le q).2.2.2)
  rw [← hA,← hb,← hv]
  exact ⟨c.mean.contDiff.contDiffAt.comp k hp,c.shift.contDiff.contDiffAt.comp k hp,
    c.noise.contDiff.contDiffAt.comp k hp⟩

theorem frozenRowsTranslated_head_values (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε k : ℝ) (ha : 0 < a) (hh : 0 ≤ h) (q : Fin 12) (u : ℝ → Vec3) :
    let p := frozenRowsTranslatedParameterCurve β α a s h z ε q u k
    let c := frozenRowsNaturalHead h z q
    Real.exp (c.logMass p) = (frozenRowsHead β a h q.val k).1 ∧
      c.mean p = frozenRowsCompletedMeanLinear β α a s h z ε q.val k ∧
      c.noise p = frozenRowsCompletedHeadDirection β α a s h z ε q.val k ∧
      c.shift p = frozenRowsCompletedMeanShift β α a s h z ε q.val k+
        (Real.sqrt h)⁻¹ • (frozenRowsCompletedMeanLinear β α a s h z ε q.val k (u k)) := by
  let p := frozenRowsNaturalParameterCurve β α a s h z ε k
  let i : Fin 12 := ⟨11-q.val,by omega⟩
  have H := affineRowCoordinate_centered_addHeadShift p.2 i
    ((affineRowCoordinate i).mean p.2 (u k)) (fun _ => z) (Real.sqrt h) p.1
  have HV := frozenRowsNaturalHead_values β α a s h z ε k ha hh q
  dsimp only at HV ⊢
  change Real.exp ((frozenRowsNaturalHead h z q).logMass _) = _ ∧ _
  have hmean : (affineRowCoordinate i).mean p.2 =
      frozenRowsCompletedMeanLinear β α a s h z ε q.val k := HV.2.1
  exact ⟨(congrArg Real.exp H.1).trans HV.1,H.2.1.trans HV.2.1,H.2.2.1.trans HV.2.2.2,
    by
      have hs : (frozenRowsNaturalHead h z q).shift
          (frozenRowsTranslatedParameterCurve β α a s h z ε q u k) =
          (frozenRowsNaturalHead h z q).shift p+
            (Real.sqrt h)⁻¹ • ((affineRowCoordinate i).mean p.2 (u k)) := by
        simpa only [frozenRowsNaturalHead,frozenRowsTranslatedParameterCurve,p,i] using H.2.2.2
      rw [hs,HV.2.2.1,hmean]⟩

end SKBarriers2.Corner
