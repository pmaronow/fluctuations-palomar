module

public import SKBarriers2.Corner.FrozenRowsPotential16
public import SKBarriers2.Corner.FrozenRowsPotential17

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

open SKOptimized.Overshoot

namespace SKBarriers2.Corner
open StepCalculus

theorem frozenRowsHead_mass_eq (β a h k : ℝ) (hh : 0 ≤ h) (q : Fin 12) :
    (frozenRowsHead β a h q.val k).1 = a * frozenUnitMass q := by
  rw [frozenRowsHead, frozenSchedule_eq_labelled β a h k hh, ← List.ofFn_eq_map]
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left q.isLt,Option.getD_some]

theorem centeredFrozenRows_path_linear_eq (β : ℝ) (α : ℝ → ℝ) (a s h z ε k : ℝ) (n : ℕ) :
    gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h k).drop n)
      (centeredFrozenRowsQuadratic β α s h z ε) =
    gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h k).drop n)
      ((terminalTaylorQuadratic β α s h z).scale (1 - ε)) := by
  ext x i
  simp only [gaussianPathLinearCLM_apply]
  have H := separableTaylorQuadratic_scale_translate (Phi β α (s + 4 * h) z)
    (jet β α 1 (s + 4 * h) z) (jet β α 2 (s + 4 * h) z) z (1 - ε)
  change ((terminalTaylorQuadratic β α s h z).scale (1 - ε)).translate (fun _ => z) =
    (centeredFrozenRowsQuadratic β α s h z ε).addConstant
      (3 * (1 - ε) * Phi β α (s + 4 * h) z) at H
  have HE := gaussianPathLinear_translate ((frozenSchedule β a (1 / 2) h k).drop n)
    ((terminalTaylorQuadratic β α s h z).scale (1 - ε)) (fun _ => z) x
  rw [H,gaussianPathLinear_addConstant] at HE
  exact congrFun HE i

theorem frozenScore_path_mean_linear (l : List (ℝ × Vec3)) (R : QuadraticTerminal)
    (ρ : ℝ) (y : Vec3) : gaussianPathMean l R (ρ • y) =
      (ρ • gaussianPathLinearCLM l R) y + gaussianPathMean l R 0 := by
  have H := gaussianPathMean_shift l R 0 y ρ
  simpa only [zero_add,add_zero,smul_apply,gaussianPathLinearCLM_apply,add_comm] using H

set_option maxHeartbeats 0 in
theorem scalarData_frozenCompletedHeadLogInput_first_score {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ L : ℝ, 0 < h₀ ∧ 1 ≤ L ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ q : Fin 12, ∀ k ∈ frozenRowsKDomain,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r - h)
      ContDiff ℝ d (fun Z : ℝ × Vec3 => Real.sqrt h *
        deriv (fun κ => frozenCompletedHeadLogInput β α a (r - h) h z ε q κ Z.1 Z.2) k) ∧
      ∀ t : ℝ, WJets d (L * (1 + |t|)) 1 (fun y => Real.sqrt h *
        deriv (fun κ => frozenCompletedHeadLogInput β α a (r - h) h z ε q κ t y) k) := by
  obtain ⟨hF, LF, hhF, hLF, HF⟩ :=
    scalarData_frozenCompletedSuffixChain_regular_kJets_order D hl hu (d + 1) (by omega)
  obtain ⟨hR, hhR, HR⟩ := scalarData_frozenCompletedHeadLogInput_eq_pureChain D hl hu
  obtain ⟨hA, CA, hhA, hCA, HA⟩ := scalarData_frozenRows_path_linear_geometry D hl hu
  obtain ⟨hb, Cb, hhb, hCb, Hb⟩ := scalarData_frozenRows_path_mean_regular_geometry D hl hu
  obtain ⟨M, δ, hM, hδ, HV⟩ := frozenCompletedDirection_uniform_control β
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  let C := 1 + CA + Cb + M
  let L := 1 + LF * max 1 C ^ d * (1 + (2 : ℝ) ^ d * (3 * C))
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hC₀ : 0 ≤ C := by linarith
  have hLF₀ : 0 ≤ LF := by linarith
  have hL : 1 ≤ L := by
    have H : 0 ≤ LF * max 1 C ^ d * (1 + (2 : ℝ) ^ d * (3 * C)) := by positivity
    dsimp only [L]
    linarith
  let h₀ := min hF (min hR (min hA (min hb (min 1
    (min (δ / (B + 1)) (min (l / 2) ((D.q - u) / 6)))))))
  have hh₀ : 0 < h₀ := lt_min hhF (lt_min hhR (lt_min hhA (lt_min hhb
    (lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))))
  refine ⟨h₀,L,hh₀,hL,?_⟩
  intro r hr h hh hhsmall z ε hε q k hk
  have hhF' : h ≤ hF := hhsmall.trans (min_le_left _ _)
  have hhR' : h ≤ hR := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhA' : h ≤ hA := ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhb' : h ≤ hb := (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hhrest : h ≤ min 1 (min (δ / (B + 1)) (min (l / 2) ((D.q - u) / 6))) :=
    (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)
  have hh₁ : h ≤ 1 := hhrest.trans (min_le_left _ _)
  have hhδ : h ≤ δ / (B + 1) := (hhrest.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := ((hhrest.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 := ((hhrest.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let ρ := Real.sqrt h
  let χ := (1 - ε) * jet β α 2 ((r - h) + 4 * h) z
  let R := centeredFrozenRowsQuadratic β α (r - h) h z ε
  let f := centeredFrozenRowsTerminal β α (r - h) h z ε
  let A := fun κ => gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h κ).drop q.val) R
  let b := fun κ => gaussianPathMean ((frozenSchedule β a (1 / 2) h κ).drop q.val) R 0
  let v := frozenCompletedDirection β a χ h q
  let F := frozenCompletedSuffixChain β a χ h f q
  let G := fun y => deriv (fun κ => F κ y) k
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hρ₁ : ρ ≤ 1 := (Real.sqrt_le_one).mpr hh₁
  have hk' : |k| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hk.1],by linarith [hk.2]⟩
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hr.1],by linarith [hr.2,D.q_mem.2]⟩
  have ha : 0 < a ∧ a ≤ 1 :=
    ⟨scalarData_cdf_pos_of_pos D (by linarith [hr.1]),cdf_le_one _ _⟩
  have hχ : |χ| ≤ B := by
    dsimp only [χ]
    rw [abs_mul]
    have hε' : |1 - ε| ≤ 1 := abs_le.mpr ⟨by linarith [hε.2],by linarith [hε.1]⟩
    apply ((mul_le_mul hε' (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) htime z)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)).trans
    dsimp only [B]
    linarith
  have hscale : |a * χ * h| ≤ δ := by
    rw [abs_mul,abs_mul,abs_of_pos ha.1,abs_of_pos hh]
    have H := (le_div_iff₀ (by linarith : 0 < B + 1)).mp hhδ
    calc
      _ ≤ 1 * B * h := by gcongr; exact ha.2
      _ ≤ δ := by nlinarith
  have HVk (j : Fin 12) := HV a χ h k hscale hk' j
  have hvc : ContDiffAt ℝ 2 v k := (HVk q).2.2.2.2.2
  have hvD : ‖deriv v k‖ ≤ M := by
    rw [(HVk q).2.2.2.1.deriv]
    exact (HVk q).2.1.trans (mul_le_of_le_one_right hM.le hρ₁)
  let nq : Fin 13 := ⟨q.val,by omega⟩
  have Hmean := Hb r hr h hh hhb' z ε hε nq k hk'
  have hbc : ContDiffAt ℝ 2 b k := Hmean.1.of_le (by simp)
  have hAc : ContDiffAt ℝ 2 A k := Hmean.2.1.of_le (by simp)
  have hbD : ‖deriv b k‖ ≤ Cb := by
    have H₁ : ‖iteratedDeriv 1 b k‖ ≤ Cb := Hmean.2.2 (1 : Fin 3)
    simpa only [iteratedDeriv_one] using H₁
  have hAe : A = fun κ => gaussianPathLinearCLM ((frozenSchedule β a (1 / 2) h κ).drop q.val)
      ((terminalTaylorQuadratic β α (r - h) h z).scale (1 - ε)) := by
    funext κ
    exact centeredFrozenRows_path_linear_eq β α a (r - h) h z ε κ q.val
  have HAq := HA r hr h hh hhA' z ε hε nq k hk'
  have hAB : ‖A k‖ ≤ CA := by rw [hAe]; exact HAq.1
  have hAD : ‖deriv A k‖ ≤ CA := by
    rw [hAe]
    have H := HAq.2 (0 : Fin 2)
    simp only [Fin.val_zero,zero_add,iteratedDeriv_one] at H
    exact H.trans (mul_le_of_le_one_right (by linarith : 0 ≤ CA) hh₁)
  have HFq := HF r hr h hh hhF' z ε hε q k hk
  have hG : QBoundedJets d LF G := HFq.2.1.of_le (by omega)
  have hDF : QBoundedJets d LF (fderiv ℝ (F k)) := (HFq.1.of_le (by omega : d + 1 ≤ d + 1 + 4)).derivativeJets
  have hterminal : QPotential 2 (|ε| * terminalJetBound D 2) f :=
    ((scalarData_frozenTerminal_qPotential D 2 htime).const_mul ε).translate (fun _ => z)
  let n := 12 - (q.val + 1)
  let labels : Fin n → Fin 12 := fun i => ⟨q.val + 1 + i.val,by dsimp only [n] at i; omega⟩
  let m := fun i : Fin n => a * frozenUnitMass (labels i)
  let V := fun κ => fun i : Fin n => frozenCompletedDirection β a χ h (labels i) κ
  have hVc : ContDiffAt ℝ 2 V k := contDiffAt_pi.mpr (fun i => (HVk (labels i)).2.2.2.2.2)
  have hunit (i : Fin 12) : 0 < frozenUnitMass i := by
    fin_cases i <;> norm_num [frozenUnitMass]
  have hm (i : Fin n) : 0 < m i := mul_pos ha.1 (hunit (labels i))
  let μ := a * frozenUnitMass q
  have hμ : 0 < μ ∧ μ ≤ 1 := by
    have hu : 0 < frozenUnitMass q ∧ frozenUnitMass q ≤ 1 := by
      fin_cases q <;> norm_num [frozenUnitMass]
    exact ⟨mul_pos ha.1 hu.1,(mul_le_mul ha.2 hu.2 hu.1.le (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)⟩
  have hscore (t : ℝ) (y : Vec3) :
      deriv (fun κ => frozenCompletedHeadLogInput β α a (r - h) h z ε q κ t y) k =
        μ * (G ((ρ • A k) y + b k + t • v k) +
          fderiv ℝ (F k) ((ρ • A k) y + b k + t • v k)
            ((ρ • deriv A k) y + deriv b k + t • deriv v k)) := by
    let X := fun κ => (ρ • A κ) y + b κ + t • v κ
    have hXc : ContDiffAt ℝ 2 X k :=
      ((hAc.const_smul ρ).clm_apply contDiffAt_const).add hbc |>.add (hvc.const_smul t)
    have hXd : deriv X k = (ρ • deriv A k) y + deriv b k + t • deriv v k := by
      simpa only [ContinuousLinearMap.map_zero,add_zero] using
        (((((hAc.differentiableAt (by norm_num)).hasDerivAt.fun_const_smul ρ).clm_apply
        (hasDerivAt_const k y)).fun_add (hbc.differentiableAt (by norm_num)).hasDerivAt).fun_add
        ((hvc.differentiableAt (by norm_num)).hasDerivAt.fun_const_smul t)).deriv
    have Hjet := (fixedMassChain_moving_endpoint_jets_identity m hterminal hVc hXc hm).1
    have Hjet' : deriv (fun κ => F κ (X κ)) k = G (X k) +
        fderiv ℝ (F k) (X k) (deriv X k) := by
      have hF : F = fun κ y => vectorIncrementChain
          (List.ofFn (fun i : Fin n => (m i, V κ i))) f y := by
        funext κ y
        rfl
      simpa only [G,hF] using Hjet
    have hnear : (fun κ => frozenCompletedHeadLogInput β α a (r - h) h z ε q κ t y) =ᶠ[𝓝 k]
        fun κ => μ * F κ (X κ) := by
      have hkU : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [hk.1],by linarith [hk.2]⟩
      filter_upwards [isOpen_Ioo.mem_nhds hkU] with κ hκ
      have H := HR r hr h hh hhR' z ε hε q κ (abs_le.mpr ⟨hκ.1.le,hκ.2.le⟩) t y
      dsimp only at H
      rw [frozenRowsHead_mass_eq β a h κ hh.le q] at H
      simpa only [F,X,frozenScore_path_mean_linear] using H
    rw [hnear.deriv_eq,deriv_const_mul_field,Hjet',hXd]
  let K := LF * max 1 C ^ d * (1 + (2 : ℝ) ^ d * (3 * C))
  have hcoef : LF * max 1 ‖ρ • A k‖ ^ d *
      (1 + (2 : ℝ) ^ d * (‖ρ • deriv A k‖ + ‖deriv b k‖ + ‖deriv v k‖)) ≤ K := by
    have hAA : ‖ρ • A k‖ ≤ C := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
      exact (mul_le_of_le_one_left (norm_nonneg _) hρ₁).trans (hAB.trans (by dsimp only [C]; linarith))
    have hUU : ‖ρ • deriv A k‖ ≤ C := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
      exact (mul_le_of_le_one_left (norm_nonneg _) hρ₁).trans (hAD.trans (by dsimp only [C]; linarith))
    have hbb : ‖deriv b k‖ ≤ C := hbD.trans (by dsimp only [C]; linarith)
    have hvv : ‖deriv v k‖ ≤ C := hvD.trans (by dsimp only [C]; linarith)
    dsimp only [K]
    gcongr
    linarith
  have hρμ : |ρ * μ| ≤ 1 := by
    rw [abs_of_pos (mul_pos hρ hμ.1)]
    exact (mul_le_mul_of_nonneg_right hρ₁ hμ.1.le).trans (by simpa only [one_mul] using hμ.2)
  have hfun : (fun Z : ℝ × Vec3 => ρ * deriv
      (fun κ => frozenCompletedHeadLogInput β α a (r - h) h z ε q κ Z.1 Z.2) k) =
      fun Z : ℝ × Vec3 => (ρ * μ) * (G ((ρ • A k) Z.2 + b k + Z.1 • v k) +
        fderiv ℝ (F k) ((ρ • A k) Z.2 + b k + Z.1 • v k)
          ((ρ • deriv A k) Z.2 + deriv b k + Z.1 • deriv v k)) := by
    funext Z
    rw [hscore]
    ring
  constructor
  · change ContDiff ℝ d (fun Z : ℝ × Vec3 => ρ * _)
    rw [hfun]
    exact contDiff_const.mul (affine_first_score_contDiff hG hDF (ρ • A k)
      (ρ • deriv A k) (b k) (v k) (deriv b k) (deriv v k))
  · intro t
    have H := (affine_first_score_weighted hG hDF (ρ • A k) (ρ • deriv A k)
      (b k) (v k) (deriv b k) (deriv v k) t).const_smul (ρ * μ)
    have HC : |ρ * μ| * (LF * max 1 ‖ρ • A k‖ ^ d *
        (1 + (2 : ℝ) ^ d * (‖ρ • deriv A k‖ + ‖deriv b k‖ + ‖deriv v k‖)) *
          (1 + |t|)) ≤ L * (1 + |t|) := by
      apply (mul_le_of_le_one_left (by positivity [hLF]) hρμ).trans
      apply mul_le_mul_of_nonneg_right (hcoef.trans (by dsimp only [L,K]; linarith)) (by positivity)
    have HH := H.mono HC le_rfl
    convert HH using 1
    funext y
    simpa only [smul_eq_mul] using congrFun hfun (t,y)

end SKBarriers2.Corner
