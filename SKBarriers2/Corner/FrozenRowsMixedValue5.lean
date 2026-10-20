module

public import SKBarriers2.Corner.FrozenRowsMixedValue4
public import SKBarriers2.Corner.FrozenRowsMixedValueBudget
public import SKBarriers2.Corner.FrozenRowsNoise7
public import SKBarriers2.Corner.FrozenRowsAffineGeometry
public import SKBarriers2.Corner.FrozenRowsPotential18

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

section Coordinates
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem CompletedSquareCoordinates.drop {p : P} {Q : QuadraticTerminal}
    {cs : List (AffineGaussianCoordinate P Vec3)} {us : List (ℝ × Vec3)}
    (H : CompletedSquareCoordinates p Q cs us) (n : ℕ) :
    CompletedSquareCoordinates p Q (cs.drop n) (us.drop n) := by
  induction n generalizing cs us with
  | zero => exact H
  | succ n ih =>
    cases cs with
    | nil =>
      cases us with
      | nil => trivial
      | cons u us => exact False.elim H
    | cons c cs =>
      cases us with
      | nil => exact False.elim H
      | cons u us => exact ih H.1

end Coordinates

def frozenRowsNaturalParameterCurve (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε k : ℝ) : ℝ × AffineRowParameters :=
  (1, completedRowParameters (List.finRange 12)
    (fun j => a * frozenUnitMass j)
    (fun j => Real.sqrt h • frozenUnitDirection β k j)
    ((terminalTaylorQuadratic β α s h z).scale (1 - ε)))

def frozenRowsNaturalCoordinates (h z : ℝ) :
    List (AffineGaussianCoordinate (ℝ × AffineRowParameters) Vec3) :=
  (affineRowCoordinates 12 le_rfl).map
    (fun c => c.centeredRescale (Real.sqrt h) (fun _ => z))

def frozenRowsNaturalHead (h z : ℝ) (q : Fin 12) :
    AffineGaussianCoordinate (ℝ × AffineRowParameters) Vec3 :=
  (affineRowCoordinate ⟨11 - q.val,by omega⟩).centeredRescale (Real.sqrt h) (fun _ => z)

theorem frozenRowsNaturalCoordinates_drop (h z : ℝ) (q : Fin 12) :
    (frozenRowsNaturalCoordinates h z).drop q.val = frozenRowsNaturalHead h z q ::
      (frozenRowsNaturalCoordinates h z).drop (q.val + 1) := by
  fin_cases q <;> rfl

def frozenRowsNaturalTerminal (β : ℝ) (α : ℝ → ℝ) (s h z ε : ℝ) :
    (ℝ × AffineRowParameters) × Vec3 → ℝ :=
  fun p => ε * frozenTerminal β α s h
    (Real.sqrt h • p.2 + p.1.1 • (fun _ => z))

def frozenRowsNaturalResidual (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) :
    (ℝ × AffineRowParameters) × Vec3 → ℝ :=
  fun p => terminalResidual β α s h z
    (Real.sqrt h • p.2 + p.1.1 • (fun _ => z))

def frozenRowsNaturalPotential (β : ℝ) (α : ℝ → ℝ) (s h z ε : ℝ) (n : ℕ) :
    (ℝ × AffineRowParameters) × Vec3 → ℝ :=
  affinePotentialChain ((frozenRowsNaturalCoordinates h z).drop n)
    (frozenRowsNaturalTerminal β α s h z ε)

def frozenRowsNaturalEpsilonJet (β : ℝ) (α : ℝ → ℝ) (s h z ε : ℝ) (n : ℕ)
    (i : Fin 3) : (ℝ × AffineRowParameters) × Vec3 → ℝ :=
  affineEpsilonJetChain ((frozenRowsNaturalCoordinates h z).drop n)
    (frozenRowsNaturalTerminal β α s h z ε) (frozenRowsNaturalResidual β α s h z) i

theorem frozenRowsNaturalParameterCurve_coordinates (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε k : ℝ) (ha : 0 < a) (hh : 0 ≤ h) (n : ℕ) :
    CompletedSquareCoordinates (frozenRowsNaturalParameterCurve β α a s h z ε k).2
      ((terminalTaylorQuadratic β α s h z).scale (1 - ε))
      ((affineRowCoordinates 12 le_rfl).drop n)
      ((frozenSchedule β a (1 / 2) h k).drop n) := by
  have hm : ∀ j ∈ List.finRange 12, 0 < a * frozenUnitMass j := by
    intro j _
    apply mul_pos ha
    fin_cases j <;> norm_num [frozenUnitMass]
  have H := completedRowParameters_coordinates (List.finRange 12) (by simp)
    (fun j => a * frozenUnitMass j) (fun j => Real.sqrt h • frozenUnitDirection β k j)
    ((terminalTaylorQuadratic β α s h z).scale (1 - ε)) hm
    (frozenRowsNaturalParameterCurve β α a s h z ε k).2 (fun _ _ => rfl)
  simp only [List.length_finRange] at H
  have HE := frozenSchedule_eq_labelled β a h k hh
  rw [← HE] at H
  exact H.drop n

theorem frozenRowsNaturalHead_values (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε k : ℝ) (ha : 0 < a) (hh : 0 ≤ h) (q : Fin 12) :
    let p := frozenRowsNaturalParameterCurve β α a s h z ε k
    let c := frozenRowsNaturalHead h z q
    Real.exp (c.logMass p) = (frozenRowsHead β a h q.val k).1 ∧
      c.mean p = frozenRowsCompletedMeanLinear β α a s h z ε q.val k ∧
      c.shift p = frozenRowsCompletedMeanShift β α a s h z ε q.val k ∧
      c.noise p = frozenRowsCompletedHeadDirection β α a s h z ε q.val k := by
  let p := (frozenRowsNaturalParameterCurve β α a s h z ε k).2
  let c := affineRowCoordinate ⟨11 - q.val,by omega⟩
  have H := frozenRowsNaturalParameterCurve_coordinates β α a s h z ε k ha hh q.val
  have hc : (affineRowCoordinates 12 le_rfl).drop q.val = c ::
      (affineRowCoordinates 12 le_rfl).drop (q.val + 1) := by
    dsimp only [c]
    fin_cases q <;> rfl
  rw [hc,frozenSchedule_drop_cons] at H
  dsimp only [CompletedSquareCoordinates] at H
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · change Real.exp (c.logMass p) = _
    exact H.2.1
  · change c.mean p = _
    exact H.2.2.1
  · change (Real.sqrt h)⁻¹ •
      (c.mean p (fun _ => z) + c.shift p - (1 : ℝ) • (fun _ => z)) = _
    rw [one_smul,H.2.2.1,H.2.2.2.1]
    rfl
  · change (Real.sqrt h)⁻¹ • c.noise p = _
    rw [H.2.2.2.2]
    rfl

theorem frozenRowsNaturalParameterCurve_contDiffAt (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε : ℝ) {k : ℝ} (hk : |k| < 3 / 5)
    (hA : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k)
      ((terminalTaylorQuadratic β α s h z).scale (1 - ε))) (hh : 0 ≤ h) :
    ContDiffAt ℝ ∞ (frozenRowsNaturalParameterCurve β α a s h z ε) k := by
  have hv (j : Fin 12) : ContDiffAt ℝ ∞
      (fun t => Real.sqrt h • frozenUnitDirection β t j) k :=
    (frozenUnitDirection_contDiffAt_k β hk j).const_smul (Real.sqrt h)
  have H := completedRowParameters_contDiffAt (List.finRange 12)
    (fun j (_ : ℝ) => a * frozenUnitMass j)
    (fun j t => Real.sqrt h • frozenUnitDirection β t j)
    (fun _ : ℝ => (terminalTaylorQuadratic β α s h z).scale (1 - ε))
    (fun _ _ => contDiffAt_const)
    (fun j _ i => contDiffAt_pi.mp (hv j) i)
    (QuadraticFamilyContDiffAt.const _ k)
    (by simpa only [← frozenSchedule_eq_labelled β a h k hh] using hA)
  exact contDiffAt_const.prodMk H

theorem frozenRowsNatural_representation (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε k : ℝ) (ha : 0 < a) (hh : 0 < h) (n : ℕ)
    (hε : ε ∈ Ioo (-1 : ℝ) 2)
    (hA : RiccatiAdmissible ((frozenSchedule β a (1 / 2) h k).drop n)
      ((terminalTaylorQuadratic β α s h z).scale (1 - ε)))
    (hFrames : ∀ t, t <:+ (frozenSchedule β a (1 / 2) h k).drop n → ∃ L : ℝ,
      Continuous (epsilonFrameResidual t (terminalTaylorQuadratic β α s h z)
        (frozenTerminal β α s h) ε) ∧
      ∀ x y, |epsilonFrameResidual t (terminalTaylorQuadratic β α s h z)
        (frozenTerminal β α s h) ε x - epsilonFrameResidual t
          (terminalTaylorQuadratic β α s h z) (frozenTerminal β α s h) ε y| ≤ L * ‖x - y‖)
    (hJets : ∀ t, t <:+ (frozenSchedule β a (1 / 2) h k).drop n → EpsilonJetControl
      (fun e => epsilonChain t (terminalTaylorQuadratic β α s h z)
        (terminalResidual β α s h z) e) (Ioo (-1 : ℝ) 2))
    (hMajor : ∀ u t, u :: t <:+ (frozenSchedule β a (1 / 2) h k).drop n →
      ∃ P : QuadraticTerminal, 1 / 2 ≤ P.precision u.1 u.2 ∧
        ∀ e ∈ Ioo (-1 : ℝ) 2, ∀ x, epsilonChain t (terminalTaylorQuadratic β α s h z)
          (terminalResidual β α s h z) e x ≤ P.value x)
    (hF : ParamRegular (fun p : AffineRowParameters × Vec3 => ε * frozenTerminal β α s h p.2))
    (hK : ParamSmooth (fun p : AffineRowParameters × Vec3 => terminalResidual β α s h z p.2)) :
    (∀ y, frozenRowsNaturalPotential β α s h z ε n
      (frozenRowsNaturalParameterCurve β α a s h z ε k,y) =
        epsilonFrameResidual ((frozenSchedule β a (1 / 2) h k).drop n)
          (terminalTaylorQuadratic β α s h z) (frozenTerminal β α s h) ε
          (Real.sqrt h • y + (fun _ => z))) ∧
    (∀ i y, frozenRowsNaturalEpsilonJet β α s h z ε n i
      (frozenRowsNaturalParameterCurve β α a s h z ε k,y) =
        epsilonSpatialJet (fun e => epsilonChain
          ((frozenSchedule β a (1 / 2) h k).drop n) (terminalTaylorQuadratic β α s h z)
          (terminalResidual β α s h z) e) (i.val + 1) ε
            (Real.sqrt h • y + (fun _ => z))) := by
  let cs := (affineRowCoordinates 12 le_rfl).drop n
  let us := (frozenSchedule β a (1 / 2) h k).drop n
  let Q := terminalTaylorQuadratic β α s h z
  let G := frozenTerminal β α s h
  let F := fun p : AffineRowParameters × Vec3 => ε * G p.2
  let K := fun p : AffineRowParameters × Vec3 => terminalResidual β α s h z p.2
  let p := (frozenRowsNaturalParameterCurve β α a s h z ε k).2
  have hpcurve : frozenRowsNaturalParameterCurve β α a s h z ε k = (1,p) := rfl
  have hC := frozenRowsNaturalParameterCurve_coordinates β α a s h z ε k ha hh.le n
  have hFn (p : AffineRowParameters) (y : Vec3) :
      frozenRowsNaturalTerminal β α s h z ε ((1,p),y) = F (p,Real.sqrt h • y+(fun _ => z)) := by
    simp only [frozenRowsNaturalTerminal,F,one_smul,G]
  have hKn (p : AffineRowParameters) (y : Vec3) :
      frozenRowsNaturalResidual β α s h z ((1,p),y) = K (p,Real.sqrt h • y+(fun _ => z)) := by
    simp only [frozenRowsNaturalResidual,K,one_smul]
  constructor
  · intro y
    have H := affinePotentialChain_centeredRescale (Real.sqrt_pos.mpr hh).ne' (fun _ => z)
      cs F (frozenRowsNaturalTerminal β α s h z ε) hFn p y
    change frozenRowsNaturalPotential β α s h z ε n
      (frozenRowsNaturalParameterCurve β α a s h z ε k,y) = _
    rw [show frozenRowsNaturalPotential β α s h z ε n =
      affinePotentialChain (cs.map (fun c => c.centeredRescale (Real.sqrt h) (fun _ => z)))
        (frozenRowsNaturalTerminal β α s h z ε) from by
          simp only [frozenRowsNaturalPotential,frozenRowsNaturalCoordinates,← List.map_drop,cs]]
    rw [hpcurve,H]
    exact affinePotentialChain_eq_frame cs us F p Q G ε hC hA hFrames (fun _ => rfl) _
  · intro i y
    have H := affineEpsilonJetChain_centeredRescale (Real.sqrt_pos.mpr hh).ne' (fun _ => z)
      cs F K (frozenRowsNaturalTerminal β α s h z ε) (frozenRowsNaturalResidual β α s h z)
      hFn hKn i p y
    change frozenRowsNaturalEpsilonJet β α s h z ε n i
      (frozenRowsNaturalParameterCurve β α a s h z ε k,y) = _
    rw [show frozenRowsNaturalEpsilonJet β α s h z ε n i =
      affineEpsilonJetChain (cs.map (fun c => c.centeredRescale (Real.sqrt h) (fun _ => z)))
        (frozenRowsNaturalTerminal β α s h z ε) (frozenRowsNaturalResidual β α s h z) i from by
          simp only [frozenRowsNaturalEpsilonJet,frozenRowsNaturalCoordinates,← List.map_drop,cs]]
    rw [hpcurve,H]
    exact affineEpsilonJetChain_eq_original cs us F K p Q G isOpen_Ioo hε hC hA
      hFrames hJets hMajor hF hK (fun _ => rfl) (fun _ => rfl) i _

structure FrozenRowsNaturalRealization (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ) : Prop where
  mass_pos : 0 < a
  scale_pos : 0 < h
  curve_smooth : ∀ k ∈ frozenRowsKDomain,
    ContDiffAt ℝ ∞ (frozenRowsNaturalParameterCurve β α a s h z ε) k
  potential_regular : ∀ n, ParamRegular (frozenRowsNaturalPotential β α s h z ε n)
  epsilon_smooth : ∀ n i, ParamSmooth (frozenRowsNaturalEpsilonJet β α s h z ε n i)
  potential_eq : ∀ k ∈ frozenRowsKDomain, ∀ n y,
    frozenRowsNaturalPotential β α s h z ε n
      (frozenRowsNaturalParameterCurve β α a s h z ε k,y) =
      epsilonFrameResidual ((frozenSchedule β a (1 / 2) h k).drop n)
        (terminalTaylorQuadratic β α s h z) (frozenTerminal β α s h) ε
        (Real.sqrt h • y+(fun _ => z))
  epsilon_eq : ∀ k ∈ frozenRowsKDomain, ∀ n i y,
    frozenRowsNaturalEpsilonJet β α s h z ε n i
      (frozenRowsNaturalParameterCurve β α a s h z ε k,y) =
      epsilonSpatialJet (fun e => epsilonChain ((frozenSchedule β a (1 / 2) h k).drop n)
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) e)
        (i.val+1) ε (Real.sqrt h • y+(fun _ => z))

theorem FrozenRowsNaturalRealization.head_derivatives {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (q : Fin 12) :
    let p := frozenRowsNaturalParameterCurve β α a s h z ε
    let c := frozenRowsNaturalHead h z q
    c.mean (deriv p k) = deriv (frozenRowsCompletedMeanLinear β α a s h z ε q.val) k ∧
      c.shift (deriv p k) = deriv (frozenRowsCompletedMeanShift β α a s h z ε q.val) k ∧
      c.noise (deriv p k) = deriv (frozenRowsCompletedHeadDirection β α a s h z ε q.val) k := by
  let p := frozenRowsNaturalParameterCurve β α a s h z ε
  let c := frozenRowsNaturalHead h z q
  have hp := ((H.curve_smooth k hk).differentiableAt (by norm_num)).hasDerivAt
  have hA : (fun t => c.mean (p t)) = frozenRowsCompletedMeanLinear β α a s h z ε q.val :=
    funext (fun t => (frozenRowsNaturalHead_values β α a s h z ε t H.mass_pos H.scale_pos.le q).2.1)
  have hb : (fun t => c.shift (p t)) = frozenRowsCompletedMeanShift β α a s h z ε q.val :=
    funext (fun t => (frozenRowsNaturalHead_values β α a s h z ε t H.mass_pos H.scale_pos.le q).2.2.1)
  have hv : (fun t => c.noise (p t)) = frozenRowsCompletedHeadDirection β α a s h z ε q.val :=
    funext (fun t => (frozenRowsNaturalHead_values β α a s h z ε t H.mass_pos H.scale_pos.le q).2.2.2)
  have HA := (c.mean.hasFDerivAt.comp_hasDerivAt k hp).deriv
  have Hb := (c.shift.hasFDerivAt.comp_hasDerivAt k hp).deriv
  have Hv := (c.noise.hasFDerivAt.comp_hasDerivAt k hp).deriv
  dsimp only [Function.comp_def] at HA Hb Hv
  rw [hA] at HA
  rw [hb] at Hb
  rw [hv] at Hv
  exact ⟨HA.symm,Hb.symm,Hv.symm⟩

theorem FrozenRowsNaturalRealization.head_density_eq {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (q : Fin 12) (t : ℝ) (y : Vec3) :
    affineCoordinateDensityPotential (frozenRowsNaturalHead h z q)
      (frozenRowsNaturalPotential β α s h z ε (q.val+1))
      (frozenRowsNaturalParameterCurve β α a s h z ε k,(y,t)) =
        frozenCompletedHeadLogInput β α a s h z ε q k t y := by
  let ρ := Real.sqrt h
  let c : Vec3 := fun _ => z
  let u := frozenRowsHead β a h q.val k
  let P := riccatiRecursion ((frozenSchedule β a (1/2) h k).drop (q.val+1))
    ((terminalTaylorQuadratic β α s h z).scale (1-ε))
  let A := quadraticMeanLinear P u.1 u.2
  let b := quadraticNoiseConstant P u.1 u.2
  let w := (Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2
  have hp := frozenRowsNaturalHead_values β α a s h z ε k H.mass_pos H.scale_pos.le q
  dsimp only at hp
  unfold affineCoordinateDensityPotential affineCoordinateEndpoint
  rw [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,H.potential_eq k hk]
  change u.1 * epsilonFrameResidual _ _ _ ε
    (ρ • (A y + ρ⁻¹ • (A c+b-c) + t • (ρ⁻¹ • w))+c) =
      u.1 * epsilonFrameResidual _ _ _ ε (A (ρ • y+c)+b+t • w)
  have hρ : ρ ≠ 0 := (Real.sqrt_pos.mpr H.scale_pos).ne'
  have hn : ρ • (t • (ρ⁻¹ • w)) = t • w := by
    rw [smul_comm ρ t,smul_smul ρ ρ⁻¹,mul_inv_cancel₀ hρ,one_smul]
  congr 2
  calc
    ρ • (A y + ρ⁻¹ • (A c+b-c) + t • (ρ⁻¹ • w))+c =
        (ρ • (A y+ρ⁻¹ • (A c+b-c))+c)+t • w := by rw [smul_add,hn]; abel
    _ = A (ρ • y+c)+b+t • w := by rw [← StepCalculus.affine_rescale hρ]

theorem FrozenRowsNaturalRealization.head_score_eq {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (q : Fin 12) (t : ℝ) (y : Vec3) :
    deriv (fun u => affineCoordinateDensityPotential (frozenRowsNaturalHead h z q)
      (frozenRowsNaturalPotential β α s h z ε (q.val+1))
      (frozenRowsNaturalParameterCurve β α a s h z ε u,(y,t))) k =
        deriv (fun u => frozenCompletedHeadLogInput β α a s h z ε q u t y) k := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [(show IsOpen frozenRowsKDomain from isOpen_Ioo).mem_nhds hk] with u hu
  exact H.head_density_eq hu q t y

theorem FrozenRowsNaturalRealization.rawJet_eq {β a s h z ε k : ℝ} {α : ℝ → ℝ}
    (H : FrozenRowsNaturalRealization β α a s h z ε) (hk : k ∈ frozenRowsKDomain)
    (n : ℕ) (i : Fin 3) (y : Vec3) :
    MomentKJet.rescale (Real.sqrt h) (parameterCurveKJet
      (frozenRowsNaturalEpsilonJet β α s h z ε n i)
      (frozenRowsNaturalParameterCurve β α a s h z ε) k y) =
        frozenRowsCoarseRawJet β α a s h z ε n i y k := by
  have he : (fun t => frozenRowsNaturalEpsilonJet β α s h z ε n i
      (frozenRowsNaturalParameterCurve β α a s h z ε t,y)) =ᶠ[𝓝 k]
      fun t => epsilonSpatialJet (fun e => epsilonChain
        ((frozenSchedule β a (1 / 2) h t).drop n) (terminalTaylorQuadratic β α s h z)
        (terminalResidual β α s h z) e) (i.val+1) ε (Real.sqrt h • y+(fun _ => z)) := by
    filter_upwards [(show IsOpen frozenRowsKDomain from isOpen_Ioo).mem_nhds hk] with t ht
    exact H.epsilon_eq t ht n i y
  simp only [parameterCurveKJet,frozenRowsCoarseRawJet,originalEpsilonKJet,
    iteratedDeriv_succ,iteratedDeriv_zero,he.self_of_nhds,he.deriv_eq,he.deriv.deriv_eq]

theorem scalarData_frozenRows_natural_realization {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1,
      FrozenRowsNaturalRealization β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h z ε := by
  obtain ⟨hA,_,hhA,_,HA⟩ := scalarData_frozen_suffix_lipschitz_frames D hl hu
  obtain ⟨C,hQ,_,hhQ,HQ⟩ := scalarData_epsilonFrameResidual_spatial_qPotential D hl hu 2 le_rfl
  obtain ⟨hJ,hhJ,_,HJ⟩ := scalarData_frozen_suffix_joint_epsilon_jets D hl hu
  let h₀ := min hA (min hQ (min hJ (min (l/2) ((D.q-u)/6))))
  have hh₀ : 0 < h₀ := lt_min hhA (lt_min hhQ (lt_min hhJ (lt_min (by positivity) (by positivity))))
  refine ⟨h₀,hh₀,?_⟩
  intro r hr h hh hhsmall z ε hε
  have hcaps : h ≤ hA ∧ h ≤ hQ ∧ h ≤ hJ ∧ h ≤ l/2 ∧ h ≤ (D.q-u)/6 := by
    simpa only [h₀,le_min_iff] using hhsmall
  obtain ⟨hhA',hhQ',hhJ',hhl,hhclear⟩ := hcaps
  have hs : 0 < r-h := by linarith [hr.1]
  have ht : (r-h)+4*h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2,D.q_mem.2]
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r-h)
  have ha : 0 < a := scalarData_cdf_pos_of_pos D hs
  have hεU : ε ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hε.1],by linarith [hε.2]⟩
  have hεS : ε ∈ Icc (-1 : ℝ) 2 := ⟨hεU.1.le,hεU.2.le⟩
  have hhalf (k : ℝ) (hk : k ∈ frozenRowsKDomain) : |k| ≤ 1/2 :=
    abs_le.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩
  obtain ⟨hF,hK⟩ := scalarData_frozenTerminal_centered_affine_inputs
    (P := AffineRowParameters) D ht (Real.sqrt h) z ε
  obtain ⟨hF₀,hK₀⟩ := scalarData_frozenTerminal_affine_inputs
    (P := AffineRowParameters) (z := z) (ε := ε) D ht
  have Hrep (k : ℝ) (hk : k ∈ frozenRowsKDomain) (n : ℕ) :=
    frozenRowsNatural_representation β α a (r-h) h z ε k ha hh n hεU
      (HA r hr h hh hhA' k (hhalf k hk) z ε hεS _ (List.drop_suffix _ _)).1
      (fun t ht => by
        have H := HQ r hr h hh hhQ' k (hhalf k hk) z ε hεS t
          (ht.trans (List.drop_suffix _ _))
        exact ⟨C,H.smooth.continuous,fun x y =>
          (H.lipschitzWith (by norm_num)).norm_sub_le x y⟩)
      (fun t ht => (HJ r hr h hh hhJ' k (hhalf k hk) z).1 t
        (ht.trans (List.drop_suffix _ _)))
      (fun u t ht => (HJ r hr h hh hhJ' k (hhalf k hk) z).2 u t
        (ht.trans (List.drop_suffix _ _))) hF₀ hK₀
  refine ⟨ha,hh,?_,?_,?_,?_,?_⟩
  · intro k hk
    exact frozenRowsNaturalParameterCurve_contDiffAt β α a (r-h) h z ε
      (abs_lt.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩)
      (HA r hr h hh hhA' k (hhalf k hk) z ε hεS _ (List.suffix_refl _)).1 hh.le
  · intro n
    exact regular_affinePotentialChain _ hF
  · intro n i
    exact smooth_affineEpsilonJetChain _ hF hK i
  · intro k hk n
    exact (Hrep k hk n).1
  · intro k hk n
    exact (Hrep k hk n).2

theorem scalarData_frozen_coarse_first_step {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (dmax : ℕ) :
    ∃ h₀ T : ℝ, 0 < h₀ ∧ 1 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ k ∈ frozenRowsKDomain, ∀ q : Fin 12,
      ∀ rsp : ℕ, rsp ≤ dmax → ∀ V : ℝ, 0 ≤ V →
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r-h)
      (∀ i : Fin 3, MomentKJet.FirstDegreeBound (rsp+1) (V^(i.val+1))
        (2*(i.val+1)-1) (fun y => frozenRowsCoarseRawJet β α a (r-h) h z ε (q.val+1) i y k)) →
      ∀ i : Fin 3, MomentKJet.FirstDegreeBound rsp
        ((epsilonSpatialStepBudget (rsp+2) T*V)^(i.val+1)) (2*(i.val+1)-1)
        (fun y => frozenRowsCoarseRawJet β α a (r-h) h z ε q.val i y k) := by
  obtain ⟨hR,hhR,HR⟩ := scalarData_frozenRows_natural_realization D hl hu
  obtain ⟨B,hQ,hB,hhQ,HQ⟩ := scalarData_epsilonFrameResidual_spatial_qPotential
    D hl hu (dmax+2) (by omega)
  obtain ⟨hG,K,hhG,hK,HG⟩ := scalarData_frozenRows_affine_geometry D hl hu
  obtain ⟨hS,L,hhS,hL,HS⟩ := scalarData_frozenCompletedHeadLogInput_first_score D hl hu dmax
  obtain ⟨T,hT,HT⟩ := movingAffineFirstCoefficient_uniform_orders dmax B K L
  let h₀ := min hR (min hQ (min hG (min hS 1)))
  refine ⟨h₀,T,lt_min hhR (lt_min hhQ (lt_min hhG (lt_min hhS (by norm_num)))),hT,?_⟩
  intro r hr h hh hhsmall z ε hε k hk q rsp hrsp V hV
  dsimp only
  intro Hinput i
  have hcaps : h ≤ hR ∧ h ≤ hQ ∧ h ≤ hG ∧ h ≤ hS ∧ h ≤ 1 := by
    simpa only [h₀,le_min_iff] using hhsmall
  obtain ⟨hhR',hhQ',hhG',hhS',hh₁⟩ := hcaps
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r-h)
  let ρ := Real.sqrt h
  let p := frozenRowsNaturalParameterCurve β α a (r-h) h z ε
  let c := frozenRowsNaturalHead h z q
  let F := frozenRowsNaturalPotential β α (r-h) h z ε (q.val+1)
  let R := frozenRowsNaturalEpsilonJet β α (r-h) h z ε (q.val+1)
  let m := a * frozenUnitMass q
  have Hmodel := HR r hr h hh hhR' z ε hε
  have hRaw (n : ℕ) (j : Fin 3) :
      (fun y => MomentKJet.rescale ρ (parameterCurveKJet
        (frozenRowsNaturalEpsilonJet β α (r-h) h z ε n j) p k y)) =
        fun y => frozenRowsCoarseRawJet β α a (r-h) h z ε n j y k :=
    funext (fun y => Hmodel.rawJet_eq hk n j y)
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hρ₁ : ρ ≤ 1 := Real.sqrt_le_one.mpr hh₁
  have hK₀ : 0 ≤ K := by linarith
  have hL₀ : 0 ≤ L := by linarith
  have hkhalf : |k| ≤ 1/2 := abs_le.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩
  have hgeo := HG r hr h hh hhG' z ε hε q k hkhalf
  dsimp only at hgeo
  have hvalues := frozenRowsNaturalHead_values β α a (r-h) h z ε k Hmodel.mass_pos hh.le q
  have hderivs := Hmodel.head_derivatives hk q
  dsimp only at hvalues hderivs
  have hA : ‖c.mean (p k)‖ ≤ K := by rw [hvalues.2.1]; exact hgeo.1
  have hU : ‖ρ • c.mean (deriv p k)‖ ≤ K := by
    rw [hderivs.1,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    apply (mul_le_of_le_one_left (norm_nonneg _) hρ₁).trans
    have H := hgeo.2.1 (0 : Fin 2)
    simp only [Fin.val_zero,zero_add,iteratedDeriv_one] at H
    exact H.trans (mul_le_of_le_one_right hK₀ hh₁)
  have hb : ‖c.shift (p k)‖ ≤ K := by
    rw [hvalues.2.2.1]
    have H := (hgeo.2.2 (0 : Fin 3)).1
    simp only [Fin.val_zero,iteratedDeriv_zero] at H
    exact H.trans (mul_le_of_le_one_right hK₀ hρ₁)
  have hd : ‖ρ • c.shift (deriv p k)‖ ≤ K := by
    rw [hderivs.2.1,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    apply (mul_le_of_le_one_left (norm_nonneg _) hρ₁).trans
    have H := (hgeo.2.2 (1 : Fin 3)).1
    simp only [Fin.val_one,iteratedDeriv_one] at H
    exact H.trans (mul_le_of_le_one_right hK₀ hρ₁)
  have hv : ‖c.noise (p k)‖ ≤ K := by
    rw [hvalues.2.2.2]
    simpa only [Fin.val_zero,iteratedDeriv_zero] using (hgeo.2.2 (0 : Fin 3)).2
  have hw : ‖ρ • c.noise (deriv p k)‖ ≤ K := by
    rw [hderivs.2.2,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    apply (mul_le_of_le_one_left (norm_nonneg _) hρ₁).trans
    simpa only [Fin.val_one,iteratedDeriv_one] using (hgeo.2.2 (1 : Fin 3)).2
  have hm : m ∈ Ioc (0 : ℝ) 1 := by
    have hu : 0 < frozenUnitMass q ∧ frozenUnitMass q ≤ 1 := by
      fin_cases q <;> norm_num [frozenUnitMass]
    refine ⟨mul_pos Hmodel.mass_pos hu.1,?_⟩
    exact (mul_le_mul (cdf_le_one (D.μ : Measure ℝ) (r-h)) hu.2 hu.1.le
      (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
  have hmass (t : ℝ) (_ht : t ∈ frozenRowsKDomain) : Real.exp (c.logMass (p t)) = m :=
    (frozenRowsNaturalHead_values β α a (r-h) h z ε t Hmodel.mass_pos hh.le q).1.trans
      (frozenRowsHead_mass_eq β a h t hh.le q)
  have hFn : (fun y => F (p k,y)) = fun y =>
      epsilonFrameResidual ((frozenSchedule β a (1/2) h k).drop (q.val+1))
        (terminalTaylorQuadratic β α (r-h) h z) (frozenTerminal β α (r-h) h) ε
        (ρ • y+(fun _ => z)) := funext (Hmodel.potential_eq k hk (q.val+1))
  have hQf : QPotential (rsp+1) B (fun y => F (p k,y)) := by
    rw [hFn]
    have H := (HQ r hr h hh hhQ' k hkhalf z ε
      ⟨by linarith [hε.1],by linarith [hε.2]⟩
      ((frozenSchedule β a (1/2) h k).drop (q.val+1)) (List.drop_suffix _ _)).of_le
        (show rsp+1 ≤ dmax+2 from by omega)
    have hnorm : ‖ρ • ContinuousLinearMap.id ℝ Vec3‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ,ContinuousLinearMap.norm_id,mul_one]
      exact hρ₁
    have H' := H.comp_affine (ρ • ContinuousLinearMap.id ℝ Vec3) (fun _ => z)
    simpa only [max_eq_left hnorm,one_pow,mul_one,smul_apply,
      ContinuousLinearMap.id_apply] using H'
  have hscore := HS r hr h hh hhS' z ε hε q k hk
  have heScore : (fun Z : ℝ × Vec3 => ρ * deriv
      (fun t => affineCoordinateDensityPotential c F (p t,(Z.2,Z.1))) k) =
      fun Z : ℝ × Vec3 => ρ * deriv
        (fun t => frozenCompletedHeadLogInput β α a (r-h) h z ε q t Z.1 Z.2) k :=
    funext (fun Z => congrArg (fun t : ℝ => ρ*t) (Hmodel.head_score_eq hk q Z.1 Z.2))
  have hs : ContDiff ℝ rsp (fun Z : ℝ × Vec3 => ρ * deriv
      (fun t => affineCoordinateDensityPotential c F (p t,(Z.2,Z.1))) k) := by
    rw [heScore]
    exact hscore.1.of_le (by exact_mod_cast hrsp)
  have hsj (dp : ℕ) (_hdp : dp ≤ 5) (t : ℝ) :
      WJets rsp (L*(1+|t|)^(dp+1)) 1
        (fun y => ρ * deriv (fun u => affineCoordinateDensityPotential c F (p u,(y,t))) k) := by
    have H := (hscore.2 t).of_le hrsp
    have hc : L*(1+|t|) ≤ L*(1+|t|)^(dp+1) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [pow_one] using pow_le_pow_right₀
          (by linarith [abs_nonneg t] : 1 ≤ 1+|t|) (by omega : 1 ≤ dp+1)) hL₀
    have H' := H.mono hc le_rfl
    convert H' using 1
    funext y
    exact congrFun heScore (t,y)
  have hInput : ∀ j : Fin 3, MomentKJet.FirstDegreeBound (rsp+1) ((V*1)^(j.val+1))
      (2*(j.val+1)-1) (fun y => MomentKJet.rescale ρ (parameterCurveKJet (R j) p k y)) := by
    intro j
    have he : (fun y => MomentKJet.rescale ρ (parameterCurveKJet (R j) p k y)) =
        fun y => frozenRowsCoarseRawJet β α a (r-h) h z ε (q.val+1) j y k := hRaw _ j
    rw [he]
    simpa only [mul_one] using Hinput j
  have Hstep := epsilonAffineStep_first_degree (p := p) (k := k) (r := rsp)
    (B := B) (M := V) (δ := 1) (T := T) (L := L) (K := K) (ρ := ρ) (m := m)
    (F := F) (R := R) (show IsOpen frozenRowsKDomain from isOpen_Ioo)
    (fun t ht => (Hmodel.curve_smooth t ht).of_le (by simp)) hk c
    (Hmodel.potential_regular (q.val+1)) (Hmodel.epsilon_smooth (q.val+1)) hmass hm
    hV (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ T) hL₀ hK hv hQf hs hsj
    (fun dp hdp => HT rsp hrsp dp hdp _ _ _ _ _ _ hA hU hb hd hv hw) hInput
  dsimp only at Hstep
  have hout : epsilonCumulantFamilies
      (fun v => Real.exp (c.logMass v.1))
      (fun j => affineCoordinateAverage c F
        (epsilonBellFamilies (fun v => Real.exp (c.logMass v.1)) R j)) i =
      frozenRowsNaturalEpsilonJet β α (r-h) h z ε q.val i := by
    unfold frozenRowsNaturalEpsilonJet
    rw [frozenRowsNaturalCoordinates_drop]
    rfl
  have Hout := Hstep i
  simp only [hout,mul_one] at Hout
  rw [hRaw] at Hout
  exact Hout

end SKBarriers2.Corner
