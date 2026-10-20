module

public import SKBarriers2.Corner.FrozenRowsNoise
public import SKBarriers2.Corner.FrozenRowsNoise6
public import SKBarriers2.Corner.FrozenRowsNoise3

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem frozenRowsHead_eq_labelled (β a h k : ℝ) (hh : 0 ≤ h)
    (j : ℕ) (hj : j < 12) :
    frozenRowsHead β a h j k =
      (a * frozenUnitMass ⟨j, hj⟩, Real.sqrt h • frozenUnitDirection β k ⟨j, hj⟩) := by
  unfold frozenRowsHead
  rw [frozenSchedule_eq_labelled β a h k hh]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_finRange] using hj)]
  simp

theorem scalarData_frozenRowsNoiseRegularity {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) : FrozenRowsNoiseRegularity D (Icc l u) := by
  obtain ⟨hA, C₀, hhA, _, HA⟩ := scalarData_frozen_suffix_lipschitz_frames D hl hu
  obtain ⟨C, hQ, _, hhQ, HQ⟩ := scalarData_epsilonFrameResidual_spatial_qPotential D hl hu 2 le_rfl
  obtain ⟨hJ, hhJ, _, HJ⟩ := scalarData_frozen_suffix_joint_epsilon_jets D hl hu
  let h₀ := min hA (min hQ (min hJ (min (l / 2) ((D.q - u) / 6))))
  have hh₀ : 0 < h₀ := by
    simp only [h₀, lt_min_iff]
    exact ⟨hhA, hhQ, hhJ, by positivity, by positivity⟩
  apply frozenRowsNoiseRegularity_of_joint D (Icc l u)
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hsmall z ε hε j hj i
  have hcaps : h ≤ hA ∧ h ≤ hQ ∧ h ≤ hJ ∧ h ≤ l / 2 ∧ h ≤ (D.q - u) / 6 := by
    simpa only [h₀, le_min_iff] using hsmall
  obtain ⟨hhA', hhQ', hhJ', hhl, hhclear⟩ := hcaps
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  have hεU : ε ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hεS : ε ∈ Icc (-1 : ℝ) 2 := ⟨hεU.1.le, hεU.2.le⟩
  have hkhalf (k : ℝ) (hk : k ∈ frozenRowsKDomain) : |k| ≤ 1 / 2 := by
    exact abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hklarge (k : ℝ) (hk : k ∈ frozenRowsKDomain) : |k| < 3 / 5 := by
    exact abs_lt.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let G := frozenTerminal β α (r - h) h
  let labels := (List.finRange 12).drop (j + 1)
  let mass := fun b : Fin 12 => a * frozenUnitMass b
  let direction := fun b : Fin 12 => fun k : ℝ => Real.sqrt h • frozenUnitDirection β k b
  have hlabels : labels.length ≤ 12 := by simp only [labels, List.length_drop, List.length_finRange]; omega
  have hfull (k : ℝ) : frozenSchedule β a (1 / 2) h k =
      (List.finRange 12).map (fun b => (mass b, direction b k)) :=
    frozenSchedule_eq_labelled β a h k hh.le
  have hdrop (k : ℝ) : labels.map (fun b => (mass b, direction b k)) =
      (frozenSchedule β a (1 / 2) h k).drop (j + 1) := by
    rw [hfull, ← List.map_drop]
  have htail (k : ℝ) : labels.map (fun b => (mass b, direction b k)) <:+
      frozenSchedule β a (1 / 2) h k := by
    rw [hdrop]
    exact List.drop_suffix _ _
  have hmass : ∀ b ∈ labels, 0 < mass b := by
    intro b _
    apply mul_pos (scalarData_cdf_pos_of_pos D hs)
    fin_cases b <;> norm_num [frozenUnitMass]
  have hdir : ∀ k ∈ frozenRowsKDomain, ∀ b ∈ labels,
      ContDiffAt ℝ ∞ (direction b) k := by
    intro k hk b _
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => Real.sqrt h) k).smul
      (frozenUnitDirection_contDiffAt_k β (hklarge k hk) b)
  obtain ⟨hF, hK⟩ := scalarData_frozenTerminal_affine_inputs (P := AffineRowParameters)
    (z := z) (ε := ε) D htime
  have hinner := epsilonChain_moving_joint_contDiffOn labels hlabels mass direction Q G
    isOpen_Ioo (show IsOpen frozenRowsKDomain from isOpen_Ioo) hεU hmass hdir
    (fun k hk => (HA r hr h hh hhA' k (hkhalf k hk) z ε hεS _ (htail k)).1)
    (fun k hk t ht => by
      have H := HQ r hr h hh hhQ' k (hkhalf k hk) z ε hεS t ((ht.trans (htail k)))
      exact ⟨C, H.smooth.continuous, fun x y => (H.lipschitzWith (by norm_num)).norm_sub_le x y⟩)
    (fun k hk t ht => (HJ r hr h hh hhJ' k (hkhalf k hk) z).1 t (ht.trans (htail k)))
    (fun k hk w t ht => (HJ r hr h hh hhJ' k (hkhalf k hk) z).2 w t (ht.trans (htail k)))
    hF hK
  have hhead (k : ℝ) (hk : k ∈ frozenRowsKDomain) :
      ContDiffAt ℝ ∞ (fun t => (frozenRowsHead β a h j t).2) k := by
    have he : (fun t => (frozenRowsHead β a h j t).2) =
        fun t => Real.sqrt h • frozenUnitDirection β t ⟨j, by omega⟩ := by
      funext t
      rw [frozenRowsHead_eq_labelled β a h t hh.le j (by omega)]
    rw [he]
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => Real.sqrt h) k).smul
      (frozenUnitDirection_contDiffAt_k β (hklarge k hk) ⟨j, by omega⟩)
  intro p hp
  have hmap : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => (q.1, (fun _ : Fin 3 => z) + q.2 • (frozenRowsHead β a h j q.1).2)) p :=
    (contDiffAt_fst.prodMk
      (contDiffAt_const.add (contDiffAt_snd.smul ((hhead p.1 hp.1).comp p contDiffAt_fst)))).of_le
        (by simp)
  have hResidual : (fun y : Vec3 => G y-Q.value y) = terminalResidual β α (r-h) h z := rfl
  have H := ((hinner i).contDiffAt
    (x := (p.1,(fun _ : Fin 3 => z)+p.2 • (frozenRowsHead β a h j p.1).2))
    ((show IsOpen (frozenRowsKDomain ×ˢ (univ : Set Vec3)) from
      isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp.1,mem_univ _⟩)).comp p hmap
  simp only [Function.comp_def,hResidual,hdrop] at H
  simpa only [frozenRowsNoise,epsilonSuffixNoiseJet,epsilonSpatialJet,α,a,Q]
    using H.contDiffWithinAt

end SKBarriers2.Corner
