module

public import SKBarriers2.Corner.FrozenRowsNoise2
public import SKBarriers2.Corner.FrozenRowsScaled

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

section Realization

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def CompletedSquareCoordinates (p : P) (Q : QuadraticTerminal) :
    List (AffineGaussianCoordinate P Vec3) → List (ℝ × Vec3) → Prop
  | [], [] => True
  | c :: cs, u :: us =>
      CompletedSquareCoordinates p Q cs us ∧
        Real.exp (c.logMass p) = u.1 ∧
        c.mean p = quadraticMeanLinear (riccatiRecursion us Q) u.1 u.2 ∧
        c.shift p = quadraticNoiseConstant (riccatiRecursion us Q) u.1 u.2 ∧
        c.noise p = (Real.sqrt ((riccatiRecursion us Q).precision u.1 u.2)⁻¹) • u.2
  | _, _ => False

theorem affinePotentialChain_eq_frame
    (cs : List (AffineGaussianCoordinate P Vec3)) (us : List (ℝ × Vec3))
    (F : P × Vec3 → ℝ) (p : P) (Q : QuadraticTerminal) (G : Vec3 → ℝ) (ε : ℝ)
    (hC : CompletedSquareCoordinates p (Q.scale (1 - ε)) cs us)
    (hA : RiccatiAdmissible us (Q.scale (1 - ε)))
    (hFrames : ∀ t, t <:+ us → ∃ L : ℝ,
      Continuous (epsilonFrameResidual t Q G ε) ∧
        ∀ x y, |epsilonFrameResidual t Q G ε x - epsilonFrameResidual t Q G ε y| ≤
          L * ‖x - y‖)
    (hF : ∀ y, F (p, y) = ε * G y) :
    ∀ x, affinePotentialChain cs F (p, x) = epsilonFrameResidual us Q G ε x := by
  induction cs generalizing us with
  | nil =>
    cases us with
    | nil => intro x; exact (hF x).trans (epsilonFrameResidual_nil Q G ε x).symm
    | cons u us => exact False.elim hC
  | cons c cs ih =>
    cases us with
    | nil => exact False.elim hC
    | cons u us =>
      rcases hC with ⟨hCt, hmass, hmean, hshift, hnoise⟩
      have htail := List.suffix_cons u us
      have hEq := ih us hCt hA.1 (fun t ht => hFrames t (ht.trans htail))
      obtain ⟨L, hR, hLip⟩ := hFrames us htail
      let A := riccatiRecursion us (Q.scale (1 - ε))
      let R := epsilonFrameResidual us Q G ε
      have hpos (x : Vec3) : 0 < quadraticAverage A u.1 u.2
          (fun y => Real.exp (u.1 * R y)) x := by
        rw [quadraticAverage_eq_standard A u.1 u.2 x hA.2.2
          (g := fun y => Real.exp (u.1 * R y)) (by fun_prop)]
        exact integral_exp_pos (integrable_exp_lipschitz_line hR hLip u.1
          (quadraticMeanTransition A u.1 u.2 x)
          ((Real.sqrt (A.precision u.1 u.2)⁻¹) • u.2))
      intro x
      rw [epsilonFrameResidual_cons us Q G ε u x hR hA.2.1 hA.2.2 (hpos x)]
      simp only [affinePotentialChain, hmass, hmean, hshift, hnoise, hEq,
        StepCalculus.tiltedAffineStep]

theorem affineCoordinateAverage_eq_completedSquare
    (c : AffineGaussianCoordinate P Vec3) (B Ψ : P × Vec3 → ℝ) (p : P)
    (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) (R : Vec3 → ℝ)
    {L : ℝ} (hD : 0 < Q.precision m v)
    (hR : Continuous R) (hΨ : Continuous (fun y => Ψ (p, y)))
    (hLip : ∀ x y, |R x - R y| ≤ L * ‖x - y‖)
    (hB : ∀ y, B (p, y) = R y)
    (hm : Real.exp (c.logMass p) = m)
    (hA : c.mean p = quadraticMeanLinear Q m v)
    (hb : c.shift p = quadraticNoiseConstant Q m v)
    (hv : c.noise p = (Real.sqrt (Q.precision m v)⁻¹) • v) (x : Vec3) :
    affineCoordinateAverage c B Ψ (p, x) =
      epsilonMoment m v (fun _ y => Q.value y + R y) (fun _ y => Ψ (p, y)) 0 x := by
  simpa [affineCoordinateAverage, hm, hA, hb, hv, hB,
    vectorStepAverage, OAI.SK.Analytic.gaussianAverage, StepCalculus.tiltedAverage,
    StepCalculus.stepLaw, vectorTranslation, Function.comp_def]
    using (completedSquare_moment_eq_tiltedAverage Q m v x hD hR hΨ hLip).symm

theorem epsilonStep_jet_eq_affineCumulants
    {F : ℝ → Vec3 → ℝ} {U : Set ℝ} (H : EpsilonJetControl F U)
    (hU : IsOpen U) (Pmajor : QuadraticTerminal) {m ε : ℝ} (hm : 0 < m)
    (v : Vec3) (hmajorP : 1 / 2 ≤ Pmajor.precision m v)
    (hmajor : ∀ e ∈ U, ∀ y, F e y ≤ Pmajor.value y) (hε : ε ∈ U)
    (c : AffineGaussianCoordinate P Vec3) (B : P × Vec3 → ℝ)
    (T : Fin 3 → P × Vec3 → ℝ) (p : P)
    (Q : QuadraticTerminal) (R : Vec3 → ℝ) {L : ℝ}
    (hD : 0 < Q.precision m v) (hR : Continuous R)
    (hLip : ∀ x y, |R x - R y| ≤ L * ‖x - y‖)
    (hF : ∀ y, F ε y = Q.value y + R y) (hB : ∀ y, B (p, y) = R y)
    (hT : ∀ i, ParamSmooth (T i))
    (hTests : ∀ i : Fin 3, ∀ y, T i (p, y) = epsilonSpatialJet F (i.val + 1) ε y)
    (hmass : Real.exp (c.logMass p) = m)
    (hA : c.mean p = quadraticMeanLinear Q m v)
    (hb : c.shift p = quadraticNoiseConstant Q m v)
    (hv : c.noise p = (Real.sqrt (Q.precision m v)⁻¹) • v) :
    let mass := fun z : P × Vec3 => Real.exp (c.logMass z.1)
    let A := fun i => affineCoordinateAverage c B (epsilonBellFamilies mass T i)
    ∀ i : Fin 3, ∀ x,
      epsilonSpatialJet (fun e => vectorStep m v (F e)) (i.val + 1) ε x =
        epsilonCumulantFamilies mass A i (p, x) := by
  dsimp only
  let mass := fun z : P × Vec3 => Real.exp (c.logMass z.1)
  let A := fun i => affineCoordinateAverage c B (epsilonBellFamilies mass T i)
  have hmassSmooth : ParamSmooth mass :=
    (ParamChain.regular_exp_parameter c.logMass).toSmooth
  have hBell := smooth_epsilonBellFamilies hmassSmooth hT
  have hcont (i : Fin 3) : Continuous (fun y => epsilonBellFamilies mass T i (p, y)) :=
    (hBell i).1.continuous.comp (continuous_const.prodMk continuous_id)
  have hAvg (i : Fin 3) (x : Vec3) : A i (p, x) =
      epsilonMoment m v F
        (fun _ y => epsilonBellFamilies mass T i (p, y)) ε x := by
    have HE := affineCoordinateAverage_eq_completedSquare c B
      (epsilonBellFamilies mass T i) p Q m v R hD hR (hcont i) hLip hB hmass hA hb hv x
    change A i (p, x) = _ at HE
    rw [HE]
    unfold epsilonMoment
    simp only [hF]
  have hJets := epsilonStep_jet_values H hU Pmajor hm v hmajorP hmajor ε hε
  have hA₀ (x : Vec3) : A 0 (p,x) = epsilonMoment m v F (epsilonSpatialJet F 1) ε x := by
    rw [hAvg]
    simp [epsilonMoment,epsilonBellFamilies,mass,hmass,hTests]
  have hA₁ (x : Vec3) : A 1 (p,x) = epsilonMoment m v F
      (fun e y => epsilonSpatialJet F 2 e y+m*epsilonSpatialJet F 1 e y^2) ε x := by
    rw [hAvg]
    simp [epsilonMoment,epsilonBellFamilies,mass,hmass,hTests]
  have hA₂ (x : Vec3) : A 2 (p,x) = epsilonMoment m v F
      (fun e y => epsilonSpatialJet F 3 e y+3*m*epsilonSpatialJet F 1 e y*epsilonSpatialJet F 2 e y+
        m^2*epsilonSpatialJet F 1 e y^3) ε x := by
    rw [hAvg]
    simp [epsilonMoment,epsilonBellFamilies,mass,hmass,hTests]
  intro i x
  fin_cases i <;> simp only [epsilonCumulantFamilies,Matrix.cons_val_zero',
    Matrix.cons_val_succ',hmass,Nat.reduceAdd]
  · change epsilonSpatialJet (fun e => vectorStep m v (F e)) 1 ε x = A 0 (p,x)
    rw [hA₀]
    exact (hJets x).1
  · change epsilonSpatialJet (fun e => vectorStep m v (F e)) 2 ε x =
        A 1 (p,x)-m*(A 0 (p,x))^2
    rw [hA₁,hA₀]
    exact (hJets x).2.1
  · change epsilonSpatialJet (fun e => vectorStep m v (F e)) 3 ε x =
        A 2 (p,x)-3*m*A 0 (p,x)*A 1 (p,x)+2*m^2*(A 0 (p,x))^3
    rw [hA₂,hA₀,hA₁]
    exact (hJets x).2.2

private theorem epsilon_nil_first (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    deriv (fun e => epsilonChain [] Q K e x) = fun _ => K x := by
  funext e
  simpa only [epsilonChain, vectorIncrementChain, id_eq, one_mul] using
    (((hasDerivAt_id e).mul_const (K x)).const_add (Q.value x)).deriv

private theorem epsilon_nil_second (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 2 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext e
  rw [iteratedDeriv_succ, iteratedDeriv_one, epsilon_nil_first]
  exact deriv_const e (K x)

private theorem epsilon_nil_third (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 3 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext e
  rw [iteratedDeriv_succ, epsilon_nil_second]
  exact deriv_const e 0

theorem affineEpsilonJetChain_eq_original
    (cs : List (AffineGaussianCoordinate P Vec3)) (us : List (ℝ × Vec3))
    (F K : P × Vec3 → ℝ) (p : P) (Q : QuadraticTerminal) (G : Vec3 → ℝ)
    {U : Set ℝ} (hU : IsOpen U) {ε : ℝ} (hε : ε ∈ U)
    (hC : CompletedSquareCoordinates p (Q.scale (1 - ε)) cs us)
    (hA : RiccatiAdmissible us (Q.scale (1 - ε)))
    (hFrames : ∀ t, t <:+ us → ∃ L : ℝ,
      Continuous (epsilonFrameResidual t Q G ε) ∧
        ∀ x y, |epsilonFrameResidual t Q G ε x - epsilonFrameResidual t Q G ε y| ≤
          L * ‖x - y‖)
    (hJets : ∀ t, t <:+ us → EpsilonJetControl
      (fun e => epsilonChain t Q (fun y => G y - Q.value y) e) U)
    (hMajor : ∀ u t, u :: t <:+ us → ∃ A : QuadraticTerminal,
      1 / 2 ≤ A.precision u.1 u.2 ∧ ∀ e ∈ U, ∀ x,
        epsilonChain t Q (fun y => G y - Q.value y) e x ≤ A.value x)
    (hF : ParamRegular F) (hK : ParamSmooth K)
    (hFbase : ∀ y, F (p, y) = ε * G y)
    (hKbase : ∀ y, K (p, y) = G y - Q.value y) :
    ∀ i : Fin 3, ∀ x,
      affineEpsilonJetChain cs F K i (p, x) =
        epsilonSpatialJet (fun e => epsilonChain us Q (fun y => G y - Q.value y) e)
          (i.val + 1) ε x := by
  induction cs generalizing us with
  | nil =>
    cases us with
    | cons u us => exact False.elim hC
    | nil =>
      intro i x
      fin_cases i
      · simpa only [affineEpsilonJetChain, Matrix.cons_val_zero', Nat.reduceAdd, epsilonSpatialJet,
          iteratedDeriv_one] using (hKbase x).trans
            (congrFun (epsilon_nil_first Q (fun y => G y - Q.value y) x) ε).symm
      · simp only [affineEpsilonJetChain, Matrix.cons_val_succ', Matrix.cons_val_zero', Nat.reduceAdd,
          epsilonSpatialJet, epsilon_nil_second]
      · simp only [affineEpsilonJetChain, Matrix.cons_val_succ', Matrix.cons_val_zero', Nat.reduceAdd,
          epsilonSpatialJet, epsilon_nil_third]
  | cons c cs ih =>
    cases us with
    | nil => exact False.elim hC
    | cons u us =>
      rcases hC with ⟨hCt, hmass, hmean, hshift, hnoise⟩
      have htail := List.suffix_cons u us
      have hIt := ih us hCt hA.1 (fun t ht => hFrames t (ht.trans htail))
        (fun t ht => hJets t (ht.trans htail))
        (fun w t ht => hMajor w t (ht.trans htail))
      let B := affinePotentialChain cs F
      let T := affineEpsilonJetChain cs F K
      let Ft := fun e => epsilonChain us Q (fun y => G y - Q.value y) e
      let A := riccatiRecursion us (Q.scale (1 - ε))
      let R := epsilonFrameResidual us Q G ε
      obtain ⟨L, hR, hLip⟩ := hFrames us htail
      have hB : ∀ y, B (p, y) = R y :=
        affinePotentialChain_eq_frame cs us F p Q G ε hCt hA.1
          (fun t ht => hFrames t (ht.trans htail)) hFbase
      have hFt : ∀ y, Ft ε y = A.value y + R y := by
        intro y
        have HE := epsilonFrameResidual_eq_actual us Q G ε y
        change R y = Ft ε y - A.value y at HE
        linarith
      have hT : ∀ i, ParamSmooth (T i) := smooth_affineEpsilonJetChain cs hF hK
      have hmasspos : 0 < u.1 := hmass ▸ Real.exp_pos _
      obtain ⟨PM, hPM, hM⟩ := hMajor u us (List.suffix_refl _)
      have HE := epsilonStep_jet_eq_affineCumulants (hJets us htail) hU PM hmasspos
        u.2 hPM hM hε c B T p A R hA.2.2 hR hLip hFt hB hT hIt
        hmass hmean hshift hnoise
      intro i x
      exact (HE i x).symm

end Realization

end SKBarriers2.Corner
