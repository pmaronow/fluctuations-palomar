module

public import SKBarriers2.Corner.FrozenRowsNoise5

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem epsilonChain_moving_joint_contDiffOn {ι : Type*}
    (l : List ι) (hl : l.length ≤ 12) (m : ι → ℝ) (v : ι → ℝ → Vec3)
    (Q : QuadraticTerminal) (G : Vec3 → ℝ) {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) {ε : ℝ} (hε : ε ∈ U)
    (hm : ∀ j ∈ l, 0 < m j)
    (hv : ∀ k ∈ V, ∀ j ∈ l, ContDiffAt ℝ ∞ (v j) k)
    (hA : ∀ k ∈ V, RiccatiAdmissible (l.map (fun j => (m j, v j k))) (Q.scale (1 - ε)))
    (hFrames : ∀ k ∈ V, ∀ t, t <:+ l.map (fun j => (m j, v j k)) → ∃ L : ℝ,
      Continuous (epsilonFrameResidual t Q G ε) ∧
        ∀ x y, |epsilonFrameResidual t Q G ε x - epsilonFrameResidual t Q G ε y| ≤ L * ‖x - y‖)
    (hJets : ∀ k ∈ V, ∀ t, t <:+ l.map (fun j => (m j, v j k)) →
      EpsilonJetControl (fun e => epsilonChain t Q (fun y => G y - Q.value y) e) U)
    (hMajor : ∀ k ∈ V, ∀ u t, u :: t <:+ l.map (fun j => (m j, v j k)) →
      ∃ A : QuadraticTerminal, 1 / 2 ≤ A.precision u.1 u.2 ∧ ∀ e ∈ U, ∀ x,
        epsilonChain t Q (fun y => G y - Q.value y) e x ≤ A.value x)
    (hF : ParamRegular (fun p : AffineRowParameters × Vec3 => ε * G p.2))
    (hK : ParamSmooth (fun p : AffineRowParameters × Vec3 => G p.2 - Q.value p.2)) :
    ∀ i : Fin 4, ContDiffOn ℝ 2
      (fun p : ℝ × Vec3 => epsilonSpatialJet
        (fun e => epsilonChain (l.map (fun j => (m j, v j p.1))) Q
          (fun y => G y - Q.value y) e) i.val ε p.2)
      (V ×ˢ univ) := by
  let cs := affineRowCoordinates l.length hl
  let F := fun p : AffineRowParameters × Vec3 => ε * G p.2
  let K := fun p : AffineRowParameters × Vec3 => G p.2 - Q.value p.2
  let C := fun k => completedRowParameters l m (fun j => v j k) (Q.scale (1 - ε))
  have hCoords (k : ℝ) : CompletedSquareCoordinates (C k) (Q.scale (1 - ε)) cs
      (l.map (fun j => (m j, v j k))) :=
    completedRowParameters_coordinates l hl m (fun j => v j k) _ hm (C k) (fun _ _ => rfl)
  have hC (k : ℝ) (hk : k ∈ V) : ContDiffAt ℝ ∞ C k :=
    completedRowParameters_contDiffAt l (fun j _ => m j) v (fun _ => Q.scale (1 - ε))
      (fun _ _ => contDiffAt_const)
      (fun j hj i => (contDiffAt_apply ℝ ℝ i _).comp k (hv k hk j hj))
      (QuadraticFamilyContDiffAt.const _ k) (hA k hk)
  have hT := smooth_affineEpsilonJetChain cs hF hK
  have hB := regular_affinePotentialChain cs hF
  have hPos (i : Fin 3) : ContDiffOn ℝ 2
      (fun p : ℝ × Vec3 => epsilonSpatialJet
        (fun e => epsilonChain (l.map (fun j => (m j, v j p.1))) Q
          (fun y => G y - Q.value y) e) (i.val + 1) ε p.2) (V ×ˢ univ) := by
    intro p hp
    have hCurve : ContDiffAt ℝ 2 (fun z : ℝ × Vec3 => (C z.1, z.2)) p :=
      (((hC p.1 hp.1).of_le (by simp)).comp p contDiffAt_fst).prodMk contDiffAt_snd
    have H := (hT i).1.contDiffAt.comp p hCurve
    apply (H.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [(hV.prod isOpen_univ).mem_nhds hp] with z hz
    exact (affineEpsilonJetChain_eq_original cs (l.map (fun j => (m j, v j z.1)))
      F K (C z.1) Q G hU hε (hCoords z.1) (hA z.1 hz.1)
      (hFrames z.1 hz.1) (hJets z.1 hz.1) (hMajor z.1 hz.1)
      hF hK (fun _ => rfl) (fun _ => rfl) i z.2).symm
  have hZero : ContDiffOn ℝ 2
      (fun p : ℝ × Vec3 => epsilonChain (l.map (fun j => (m j, v j p.1))) Q
        (fun y => G y - Q.value y) ε p.2) (V ×ˢ univ) := by
    intro p hp
    have hCurve : ContDiffAt ℝ 2 (fun z : ℝ × Vec3 => (C z.1, z.2)) p :=
      (((hC p.1 hp.1).of_le (by simp)).comp p contDiffAt_fst).prodMk contDiffAt_snd
    have HR := hB.1.contDiffAt.comp p hCurve
    have HQ := riccatiRecursion_coefficients_contDiffAt l (fun j _ => m j) v
      (fun _ => Q.scale (1 - ε)) (fun _ _ => contDiffAt_const)
      (fun j hj i => (contDiffAt_apply ℝ ℝ i _).comp p.1 (hv p.1 hp.1 j hj))
      (QuadraticFamilyContDiffAt.const _ p.1) (hA p.1 hp.1)
    have HQ' : QuadraticFamilyContDiffAt
        (fun z : ℝ × Vec3 => riccatiRecursion
          (l.map (fun j => (m j, v j z.1))) (Q.scale (1 - ε))) p :=
      ⟨HQ.constant.comp p contDiffAt_fst,
        fun i => (HQ.linear i).comp p contDiffAt_fst,
        fun i j => (HQ.hessian i j).comp p contDiffAt_fst⟩
    have HQvalue := HQ'.value (x := fun z : ℝ × Vec3 => z.2) (fun i => by fun_prop)
    have H := (HQvalue.of_le (by simp)).add HR
    apply (H.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [(hV.prod isOpen_univ).mem_nhds hp] with z hz
    have HE := affinePotentialChain_eq_frame cs (l.map (fun j => (m j, v j z.1)))
      F (C z.1) Q G ε (hCoords z.1) (hA z.1 hz.1) (hFrames z.1 hz.1)
      (fun _ => rfl) z.2
    simp only [Function.comp_apply]
    rw [HE, epsilonFrameResidual_eq_actual]
    ring
  intro i
  fin_cases i
  · simpa only [epsilonSpatialJet, iteratedDeriv_zero] using hZero
  · simpa using hPos 0
  · simpa using hPos 1
  · simpa using hPos 2

end SKBarriers2.Corner
