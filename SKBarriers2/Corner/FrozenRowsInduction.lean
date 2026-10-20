module

public import SKBarriers2.Corner.FrozenRowsScaled

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

private theorem wJets_const_mul {r p : ℕ} {B a : ℝ} {f : Vec3 → ℝ}
    (hf : WJets r B p f) : WJets r (|a| * B) p (fun x => a * f x) := by
  simpa only [smul_eq_mul] using hf.const_smul a

private theorem wJets_small_mul {r p : ℕ} {B a : ℝ} {f : Vec3 → ℝ}
    (hf : WJets r B p f) (ha : |a| ≤ 1) : WJets r B p (fun x => a * f x) := by
  exact (wJets_const_mul hf).mono
    (mul_le_of_le_one_left hf.nonneg ha) le_rfl

private theorem wJets_square {r p : ℕ} {B : ℝ} {f : Vec3 → ℝ}
    (hf : WJets r B p f) :
    WJets r ((2 : ℝ) ^ r * B ^ 2) (p + p) (fun x => f x ^ 2) := by
  convert hf.mul hf using 1 <;> first | rfl | (funext x; ring) | ring

private theorem wJets_cube {r p : ℕ} {B : ℝ} {f : Vec3 → ℝ}
    (hf : WJets r B p f) :
    WJets r (((2 : ℝ) ^ r) ^ 2 * B ^ 3) (p + p + p) (fun x => f x ^ 3) := by
  convert (hf.mul hf).mul hf using 1 <;> first | rfl | (funext x; ring) | ring

def epsilonSpatialStepBudget (r : ℕ) (T : ℝ) : ℝ :=
  let S := (2 : ℝ) ^ r
  1 + T + (T * (1 + S) + S * T ^ 2) +
    (T * (1 + 3 * S + S ^ 2) + 3 * S * T ^ 2 * (1 + S) + 2 * S ^ 2 * T ^ 3)

theorem epsilonSpatialStepBudget_ge_one (r : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ epsilonSpatialStepBudget r T := by
  dsimp only [epsilonSpatialStepBudget]
  have h₂ : 0 ≤ T * (1 + (2 : ℝ) ^ r) + (2 : ℝ) ^ r * T ^ 2 := by positivity
  have h₃ : 0 ≤ T * (1 + 3 * (2 : ℝ) ^ r + ((2 : ℝ) ^ r) ^ 2) +
      3 * (2 : ℝ) ^ r * T ^ 2 * (1 + (2 : ℝ) ^ r) +
      2 * ((2 : ℝ) ^ r) ^ 2 * T ^ 3 := by positivity
  linarith

theorem epsilonStep_scaled_spatial_jets
    {F : ℝ → Vec3 → ℝ} {U : Set ℝ} {m ρ M δ T ε : ℝ} {c v : Vec3} {r : ℕ}
    (H : EpsilonJetControl F U) (hU : IsOpen U) (hε : ε ∈ U)
    (P : QuadraticTerminal) (hm : m ∈ Ioc (0 : ℝ) 1)
    (hP : 1 / 2 ≤ P.precision m v) (hmajor : ∀ e ∈ U, ∀ x, F e x ≤ P.value x)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (HJ : ∀ i : Fin 3, WJets r ((M * δ) ^ (i.val + 1)) (3 * (i.val + 1))
      (spatialRescale ρ c (epsilonSpatialJet F (i.val + 1) ε)))
    (HA : ∀ B : ℝ, ∀ p : ℕ, p ≤ 9 → ∀ ψ : Vec3 → ℝ,
      WJets r B p (spatialRescale ρ c ψ) →
        WJets r (T * B) p (spatialRescale ρ c (epsilonMoment m v F (fun _ => ψ) ε))) :
    ∀ i : Fin 3,
      WJets r ((epsilonSpatialStepBudget r T * M * δ) ^ (i.val + 1)) (3 * (i.val + 1))
        (spatialRescale ρ c
          (epsilonSpatialJet (fun e => vectorStep m v (F e)) (i.val + 1) ε)) := by
  let R := M * δ
  let S := (2 : ℝ) ^ r
  let C := epsilonSpatialStepBudget r T
  let f₁ := epsilonSpatialJet F 1 ε
  let f₂ := epsilonSpatialJet F 2 ε
  let f₃ := epsilonSpatialJet F 3 ε
  let ψ₂ : Vec3 → ℝ := fun x => f₂ x + m * f₁ x ^ 2
  let ψ₃ : Vec3 → ℝ := fun x => f₃ x + 3 * m * f₁ x * f₂ x + m ^ 2 * f₁ x ^ 3
  let A₁ := epsilonMoment m v F (fun _ => f₁) ε
  let A₂ := epsilonMoment m v F (fun _ => ψ₂) ε
  let A₃ := epsilonMoment m v F (fun _ => ψ₃) ε
  have hR : 0 ≤ R := mul_nonneg hM hδ
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hmabs : |m| ≤ 1 := by rw [abs_of_pos hm.1]; exact hm.2
  have hm₂abs : |m ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hmabs
  have H₁ : WJets r R 3 (spatialRescale ρ c f₁) := by
    simpa only [Fin.val_zero, zero_add, pow_one] using HJ 0
  have H₂ : WJets r (R ^ 2) 6 (spatialRescale ρ c f₂) := HJ 1
  have H₃ : WJets r (R ^ 3) 9 (spatialRescale ρ c f₃) := HJ 2
  have Hψ₂ : WJets r ((1 + S) * R ^ 2) 6 (spatialRescale ρ c ψ₂) := by
    convert H₂.add (wJets_small_mul (wJets_square H₁) hmabs) using 1 <;>
      first | rfl | (dsimp only [S]; ring)
  have Hψ₃ : WJets r ((1 + 3 * S + S ^ 2) * R ^ 3) 9 (spatialRescale ρ c ψ₃) := by
    have Hprod : WJets r (S * R ^ 3) 9
        (fun x => spatialRescale ρ c f₁ x * spatialRescale ρ c f₂ x) := by
      convert H₁.mul H₂ using 1
      ring
    have Hmid := wJets_const_mul (a := (3 : ℝ)) (wJets_small_mul Hprod hmabs)
    have Hlast := wJets_small_mul (wJets_cube H₁) hm₂abs
    convert (H₃.add Hmid).add Hlast using 1 <;>
      first | rfl | (funext x; dsimp only [spatialRescale, ψ₃]; ring) |
        (norm_num; ring)
  have HA₁ : WJets r (T * R) 3 (spatialRescale ρ c A₁) := HA _ _ (by norm_num) f₁ H₁
  have HA₂ : WJets r (T * ((1 + S) * R ^ 2)) 6 (spatialRescale ρ c A₂) :=
    HA _ _ (by norm_num) ψ₂ Hψ₂
  have HA₃ : WJets r (T * ((1 + 3 * S + S ^ 2) * R ^ 3)) 9 (spatialRescale ρ c A₃) :=
    HA _ _ (by norm_num) ψ₃ Hψ₃
  have hC : 1 ≤ C := epsilonSpatialStepBudget_ge_one r hT
  have hTC : T ≤ C := by
    dsimp only [C, epsilonSpatialStepBudget]
    nlinarith [show 0 ≤ T * (1 + S) + S * T ^ 2 by positivity,
      show 0 ≤ T * (1 + 3 * S + S ^ 2) + 3 * S * T ^ 2 * (1 + S) +
        2 * S ^ 2 * T ^ 3 by positivity]
  have hb₂ : T * (1 + S) + S * T ^ 2 ≤ C ^ 2 := by
    have hle : T * (1 + S) + S * T ^ 2 ≤ C := by
      dsimp only [C, epsilonSpatialStepBudget]
      nlinarith [show 0 ≤ T * (1 + 3 * S + S ^ 2) + 3 * S * T ^ 2 * (1 + S) +
        2 * S ^ 2 * T ^ 3 by positivity]
    exact hle.trans (by nlinarith)
  have hb₃ : T * (1 + 3 * S + S ^ 2) + 3 * S * T ^ 2 * (1 + S) +
      2 * S ^ 2 * T ^ 3 ≤ C ^ 3 := by
    have hle : T * (1 + 3 * S + S ^ 2) + 3 * S * T ^ 2 * (1 + S) +
        2 * S ^ 2 * T ^ 3 ≤ C := by
      dsimp only [C, epsilonSpatialStepBudget]
      nlinarith [show 0 ≤ T * (1 + S) + S * T ^ 2 by positivity]
    exact hle.trans (by nlinarith [mul_nonneg (show 0 ≤ C - 1 by linarith) (sq_nonneg C)])
  have he := epsilonStep_jet_values H hU P hm.1 v hP hmajor ε hε
  have he₁ : epsilonSpatialJet (fun e => vectorStep m v (F e)) 1 ε = A₁ :=
    funext (fun x => (he x).1)
  have he₂ : epsilonSpatialJet (fun e => vectorStep m v (F e)) 2 ε =
      fun x => A₂ x - m * A₁ x ^ 2 := funext (fun x => (he x).2.1)
  have he₃ : epsilonSpatialJet (fun e => vectorStep m v (F e)) 3 ε =
      fun x => A₃ x - 3 * m * A₁ x * A₂ x + 2 * m ^ 2 * A₁ x ^ 3 :=
    funext (fun x => (he x).2.2)
  intro i
  fin_cases i
  · rw [he₁]
    apply HA₁.mono _ le_rfl
    simpa only [zero_add, pow_one, C, R, mul_assoc] using mul_le_mul_of_nonneg_right hTC hR
  · rw [he₂]
    have HB := HA₂.sub (wJets_small_mul (wJets_square HA₁) hmabs)
    apply HB.mono _ le_rfl
    convert mul_le_mul_of_nonneg_right hb₂ (sq_nonneg R) using 1 <;>
      dsimp only [C, R, S] <;> ring
  · rw [he₃]
    have Hprod : WJets r (S * T ^ 2 * (1 + S) * R ^ 3) 9
        (fun x => spatialRescale ρ c A₁ x * spatialRescale ρ c A₂ x) := by
      convert HA₁.mul HA₂ using 1
      ring
    have Hmid := wJets_const_mul (a := (3 : ℝ)) (wJets_small_mul Hprod hmabs)
    have Hlast := wJets_const_mul (a := (2 : ℝ)) (wJets_small_mul (wJets_cube HA₁) hm₂abs)
    have HB := (HA₃.sub Hmid).add Hlast
    have HB' : WJets r
        ((T * (1 + 3 * S + S ^ 2) + 3 * S * T ^ 2 * (1 + S) +
          2 * S ^ 2 * T ^ 3) * R ^ 3) 9
        (spatialRescale ρ c (fun x => A₃ x - 3 * m * A₁ x * A₂ x +
          2 * m ^ 2 * A₁ x ^ 3)) := by
      convert HB using 1 <;> first | rfl |
        (funext x; dsimp only [spatialRescale]; ring) |
        (norm_num; ring)
    apply HB'.mono _ le_rfl
    convert mul_le_mul_of_nonneg_right hb₃ (pow_nonneg hR 3) using 1
    dsimp only [C, R]
    ring

theorem scalarData_frozen_scaled_moment_wJets {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ T : ℝ, 0 < h₀ ∧ 1 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∀ M : ℝ, ∀ p : ℕ, p ≤ 9 → ∀ ψ : Vec3 → ℝ,
        WJets d M p (spatialRescale (Real.sqrt h) (fun _ => z) ψ) →
        WJets d (T * M) p (spatialRescale (Real.sqrt h) (fun _ => z)
          (epsilonMoment w.1 w.2 (fun e => epsilonChain t
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e) (fun _ => ψ) ε)) := by
  rcases scalarData_epsilonFrameResidual_spatial_qPotential D hl hu (max 2 (d + 1))
      (le_max_left _ _) with ⟨C, hF, hC, hhF, HF⟩
  let B := scalarTerminalJetBound D 3 + 1
  let G := (2 : ℝ) ^ 12 * (2 * B)
  let K := 6 * (|β| + 1)
  let S := 72 * (2 ^ 12 * (20 * B)) * (β ^ 2 + 1)
  let L := 2 * K + 1
  let A := 3 + 2 * G * K ^ 2
  let coeff : Fin 10 → ℝ := fun p =>
    StepCalculus.noiseAverageCoefficient d p.val (C * L ^ (d + 1)) *
      L ^ (p.val + d) * A ^ p.val * (2 : ℝ) ^ d
  let T := 1 + ∑ p : Fin 10, |coeff p|
  have hB : 0 < B := by dsimp only [B]; positivity [scalarTerminalJetBound_nonneg D 3]
  have hG : 0 < G := by dsimp only [G]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hS : 0 < S := by dsimp only [S]; positivity
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hT : 1 ≤ T := by
    have H := Finset.sum_nonneg (fun p (_ : p ∈ (Finset.univ : Finset (Fin 10))) => abs_nonneg (coeff p))
    dsimp only [T]; linarith
  have hcoeff (p : ℕ) (hp : p ≤ 9) :
      StepCalculus.noiseAverageCoefficient d p (C * L ^ (d + 1)) *
        L ^ (p + d) * A ^ p * (2 : ℝ) ^ d ≤ T := by
    let i : Fin 10 := ⟨p, by omega⟩
    have H := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 10))) => abs_nonneg (coeff j)) (Finset.mem_univ i)
    exact (le_abs_self (coeff i)).trans (H.trans (by dsimp only [T]; linarith))
  let h₀ := min hF (min 1 (min (l / 2) (min ((D.q - u) / 6) S⁻¹)))
  refine ⟨h₀, T, lt_min hhF (lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (inv_pos.mpr hS)))), hT, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε w t ht M p hp ψ hψ
  have hhF' : h ≤ hF := hhsmall.trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhS : h ≤ S⁻¹ :=
    (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  let α := cdf (D.μ : Measure ℝ)
  let full := frozenSchedule β (α (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let Qε := Q.scale (1 - ε)
  let P := riccatiRecursion t Qε
  let R := epsilonFrameResidual t Q (frozenTerminal β α (r - h) h) ε
  let c : Vec3 := fun _ => z
  let ρ := Real.sqrt h
  have hρ : ρ ∈ Ioc (0 : ℝ) 1 := ⟨Real.sqrt_pos.mpr hh, Real.sqrt_le_one.mpr hh₁⟩
  have htt : t <:+ full := (List.suffix_cons w t).trans ht
  have hmem : w ∈ full := ht.subset List.mem_cons_self
  have hlen : t.length ≤ 12 := by simpa only [full, frozenSchedule_length] using htt.length_le
  have hmass := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hm : w.1 ∈ Icc (0 : ℝ) 1 := ⟨(hmass w hmem).1.le, (hmass w hmem).2⟩
  have he' : |1 - ε| ≤ 2 := abs_le.mpr ⟨by linarith [hε.2], by linarith [hε.1]⟩
  have hQ : ∀ i j, |Qε.hessian i j| ≤ 2 * B := by
    intro i j
    change |(1 - ε) * Q.hessian i j| ≤ _
    rw [abs_mul]
    apply mul_le_mul he' _ (abs_nonneg _) (by norm_num)
    exact terminalTaylorQuadratic_hessian_bound β α (r - h) h z B hB.le
      ((scalarData_jet_le D (r := 3) (by norm_num) (by norm_num) htime z).trans
        (by dsimp only [B]; linarith)) i j
  have hgrad : ∀ i, |Qε.slopeVector c i| ≤ 2 * B := by
    intro i
    rw [terminalTaylorQuadratic_scaled_centerGradient, abs_mul]
    apply mul_le_mul he' _ (abs_nonneg _) (by norm_num)
    exact (scalarData_jet_le D (r := 3) (by norm_num : 1 ≤ 1) (by norm_num) htime z).trans
      (by dsimp only [B]; linarith)
  have hsmall : 72 * (2 ^ 12 * (20 * B)) * β ^ 2 * h ≤ 1 := by
    calc
      _ ≤ S * h := by dsimp only [S]; nlinarith
      _ ≤ S * S⁻¹ := mul_le_mul_of_nonneg_left hhS hS.le
      _ = 1 := mul_inv_cancel₀ hS.ne'
  have hnoise (v : ℝ × Vec3) (hv : v ∈ full) :
      2 * (2 ^ 12 * (20 * B)) * directionEnergy v.2 ≤ 1 := by
    simpa only [frozenSchedule_length] using frozenSchedule_small_directions β _ h k
      (B := 20 * B) (by positivity) hh.le hk hsmall v hv
  have hvt (v : ℝ × Vec3) (hv : v ∈ t) : 2 * (2 ^ t.length * (2 * B)) * directionEnergy v.2 ≤ 1 := by
    apply le_trans _ (hnoise v (htt.subset hv))
    apply mul_le_mul_of_nonneg_right _ (directionEnergy_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : 0 ≤ (2 : ℝ))
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen)
      (by linarith : 2 * B ≤ 20 * B) (by positivity) (by positivity)
  have hPt := riccatiAdmissible_of_small_directions t Qε (by positivity) hQ
    (fun v hv => hmass v (htt.subset hv)) hvt
  have hess : ∀ i j, |P.hessian i j| ≤ G := fun i j => (hPt.2 i j).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen) (by positivity))
  have grad : ∀ i, |P.slopeVector c i| ≤ G := fun i =>
    (riccati_centerGradient_bound t Qε (by positivity) (by positivity) hQ hgrad
      (fun v hv => hmass v (htt.subset hv)) hvt i).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen) (by positivity))
  have hsmallw : 6 * G * directionEnergy w.2 ≤ 1 := by
    apply le_trans _ (hnoise w hmem)
    apply mul_le_mul_of_nonneg_right _ (directionEnergy_nonneg _)
    dsimp only [G]
    norm_num
    linarith
  have h2 : 2 * G * directionEnergy w.2 ≤ 1 := by
    nlinarith [mul_nonneg hG.le (directionEnergy_nonneg w.2)]
  have hD : 1 / 2 ≤ P.precision w.1 w.2 := (P.update_small hG hess hm w.2 h2).1
  have hAlin : ‖quadraticMeanLinear P w.1 w.2‖ ≤ 2 :=
    quadraticMeanLinear_norm_le_two hG.le hess hm w.2 hD hsmallw
  have hdir := frozenSchedule_centered_direction_scale hh.le hk hmem
  have hscale := quadraticTransition_centered_scale hG.le hG.le hK.le ⟨hρ.1.le, hρ.2⟩
    hess grad hm hD hsmallw hdir.1 hdir.2
  have hw : ‖ρ⁻¹ • ((Real.sqrt (P.precision w.1 w.2)⁻¹) • w.2)‖ ≤ L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ.1)]
    calc
      _ ≤ ρ⁻¹ * (2 * K * ρ) := mul_le_mul_of_nonneg_left hscale.1 (inv_nonneg.mpr hρ.1.le)
      _ = 2 * K := by field_simp [hρ.1.ne']
      _ ≤ L := by dsimp only [L]; linarith
  have hb : ‖ρ⁻¹ • (quadraticMeanLinear P w.1 w.2 c + quadraticNoiseConstant P w.1 w.2 - c)‖ ≤
      2 * G * K ^ 2 := by
    rw [← quadraticMeanTransition_eq_affine, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hρ.1)]
    have HE := quadraticMeanTransition_center_bound hG.le grad hm hD
    have Hρ : directionEnergy w.2 ≤ K ^ 2 * ρ := hdir.2.trans
      (by nlinarith [mul_nonneg (by positivity : 0 ≤ K ^ 2 * ρ) (sub_nonneg.mpr hρ.2)])
    calc
      _ ≤ ρ⁻¹ * (2 * G * (K ^ 2 * ρ)) := by gcongr; exact HE.trans (by gcongr)
      _ = _ := by field_simp [hρ.1.ne']
  have hε' : ε ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hRfull : QPotential (max 2 (d + 1)) C R := HF r hr h hh hhF' k hk z ε hε' t htt
  have hR := hRfull.of_le (le_max_right _ _)
  have hRscaled := hR.spatialRescale (by rw [abs_of_pos hρ.1]; exact hρ.2) c
  have hLip : ∀ x y, |R x - R y| ≤ C * ‖x - y‖ := fun x y =>
    (hRfull.lipschitzWith (by omega)).norm_sub_le x y
  have hψc : Continuous ψ := (contDiff_of_spatialRescale hρ.1.ne' hψ.smooth).continuous
  let f := fun e => epsilonChain t Q (terminalResidual β α (r - h) h z) e
  have heq : f ε = fun x => P.value x + R x := by
    funext x
    have HE := epsilonFrameResidual_eq_actual t Q (frozenTerminal β α (r - h) h) ε x
    change R x = f ε x - P.value x at HE
    linarith
  have havg := StepCalculus.wJets_tiltedAverage_boundedNoise hRscaled hψ hm hL _ hw
  have Hraw := havg.comp_affine (quadraticMeanLinear P w.1 w.2)
    (ρ⁻¹ • (quadraticMeanLinear P w.1 w.2 c + quadraticNoiseConstant P w.1 w.2 - c))
  have hactual : spatialRescale ρ c (epsilonMoment w.1 w.2 f (fun _ => ψ) ε) =
      fun y => StepCalculus.tiltedAverage w.1
        (ρ⁻¹ • ((Real.sqrt (P.precision w.1 w.2)⁻¹) • w.2))
        (spatialRescale ρ c R) (spatialRescale ρ c ψ)
        (quadraticMeanLinear P w.1 w.2 y +
          ρ⁻¹ • (quadraticMeanLinear P w.1 w.2 c + quadraticNoiseConstant P w.1 w.2 - c)) := by
    have HE : epsilonMoment w.1 w.2 f (fun _ => ψ) ε =
        epsilonMoment w.1 w.2 (fun _ x => P.value x + R x) (fun _ => ψ) 0 := by
      unfold epsilonMoment
      simp only [heq]
    rw [HE]
    have HC : epsilonMoment w.1 w.2 (fun _ x => P.value x + R x) (fun _ => ψ) 0 =
        fun x => StepCalculus.tiltedAverage w.1 ((Real.sqrt (P.precision w.1 w.2)⁻¹) • w.2)
          R ψ (quadraticMeanLinear P w.1 w.2 x + quadraticNoiseConstant P w.1 w.2) := by
      funext x
      exact completedSquare_moment_eq_tiltedAverage P w.1 w.2 x
        (by linarith : 0 < P.precision w.1 w.2) hR.smooth.continuous hψc hLip
    rw [HC, StepCalculus.spatialRescale_affine_tiltedAverage hρ.1.ne']
  rw [hactual]
  apply Hraw.mono _ le_rfl
  calc
    _ ≤ (StepCalculus.noiseAverageCoefficient d p (C * L ^ (d + 1)) * (M * L ^ (p + d))) *
        A ^ p * (2 : ℝ) ^ d := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ havg.nonneg
        apply pow_le_pow_left₀ (by positivity)
        dsimp only [A]
        linarith
      · exact pow_le_pow_left₀ (by positivity) (max_le (by norm_num) hAlin) d
      · positivity
      · positivity [havg.nonneg]
    _ = (StepCalculus.noiseAverageCoefficient d p (C * L ^ (d + 1)) *
        L ^ (p + d) * A ^ p * (2 : ℝ) ^ d) * M := by ring
    _ ≤ T * M := mul_le_mul_of_nonneg_right (hcoeff p hp) hψ.nonneg

private theorem nil_epsilon_first (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    deriv (fun e => epsilonChain [] Q K e x) = fun _ => K x := by
  funext e
  simpa only [epsilonChain, vectorIncrementChain, id_eq, one_mul] using
    (((hasDerivAt_id e).mul_const (K x)).const_add (Q.value x)).deriv

private theorem nil_epsilon_second (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 2 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext e
  rw [iteratedDeriv_succ, iteratedDeriv_one, nil_epsilon_first]
  exact deriv_const e (K x)

private theorem nil_epsilon_third (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 3 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext e
  rw [iteratedDeriv_succ, nil_epsilon_second]
  exact deriv_const e 0

private theorem wJets_zero (d p : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    WJets d B p (fun _ : Vec3 => (0 : ℝ)) := by
  refine ⟨hB, contDiff_const, ?_⟩
  intro j _ x
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero, norm_zero] using
      mul_nonneg hB (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) p)
  | succ j =>
    rw [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
    positivity

theorem scalarData_frozen_scaled_epsilon_spatial_jets {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ t, t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WJets d ((M * (Real.sqrt h * h)) ^ (i.val + 1)) (3 * (i.val + 1))
          (spatialRescale (Real.sqrt h) (fun _ => z) (epsilonSpatialJet
            (fun e => epsilonChain t
              (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
              (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e)
            (i.val + 1) ε)) := by
  rcases scalarData_frozen_suffix_joint_epsilon_jets D hl hu with ⟨hJ, hhJ, _, HJ⟩
  rcases scalarData_frozen_scaled_moment_wJets D hl hu d with ⟨hA, T, hhA, hT, HA⟩
  let M₀ := terminalJetBound D (max 3 d) + 1
  let C := epsilonSpatialStepBudget d T
  let M := C ^ 12 * M₀
  have hM₀ : 1 ≤ M₀ := by dsimp only [M₀]; linarith [terminalJetBound_nonneg D (max 3 d)]
  have hC : 1 ≤ C := epsilonSpatialStepBudget_ge_one d (by linarith)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) hM₀
  let h₀ := min hJ (min hA (min 1 (min (l / 2) ((D.q - u) / 6))))
  refine ⟨h₀, M, lt_min hhJ (lt_min hhA (lt_min (by norm_num)
    (lt_min (by positivity) (by positivity)))), hM, ?_⟩
  intro r hr h hh hhsmall k hk z t ht ε hε i
  have hhJ' : h ≤ hJ := hhsmall.trans (min_le_left _ _)
  have hhA' : h ≤ hA := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hh₁ : h ≤ 1 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 :=
    (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  let α := cdf (D.μ : Measure ℝ)
  let full := frozenSchedule β (α (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let K := terminalResidual β α (r - h) h z
  let c : Vec3 := fun _ => z
  let ρ := Real.sqrt h
  let δ := ρ ^ 3
  have hρ : ρ ∈ Ioc (0 : ℝ) 1 := ⟨Real.sqrt_pos.mpr hh, Real.sqrt_le_one.mpr hh₁⟩
  have hδ : 0 ≤ δ := pow_nonneg hρ.1.le _
  have heδ : δ = Real.sqrt h * h := by
    dsimp only [δ, ρ]
    rw [pow_succ, Real.sq_sqrt hh.le, mul_comm]
  have HK : WJets d (M₀ * δ) 3 (spatialRescale ρ c K) := by
    have H := scalarData_scaledTerminalResidual_wJets D htime hρ d z
    have heq : spatialRescale ρ c K = fun y => δ * scaledTerminalResidual β α (r - h) h z ρ y := by
      funext y
      dsimp only [spatialRescale, scaledTerminalResidual, δ, c, K]
      field_simp [hρ.1.ne']
    rw [heq]
    apply (wJets_const_mul H).mono _ le_rfl
    rw [abs_of_nonneg hδ]
    have HM : terminalJetBound D (max 3 d) ≤ M₀ := by dsimp only [M₀]; linarith
    exact (mul_le_mul_of_nonneg_left HM hδ).trans_eq (by ring)
  have HJ' := HJ r hr h hh hhJ' k hk z
  have hm := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hε' : ε ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hnil₁ : epsilonSpatialJet (fun e => epsilonChain [] Q K e) 1 ε = K := by
    funext x
    simpa only [epsilonSpatialJet, iteratedDeriv_one] using congrFun (nil_epsilon_first Q K x) ε
  have hnil₂ : epsilonSpatialJet (fun e => epsilonChain [] Q K e) 2 ε = fun _ => 0 := by
    funext x
    exact congrFun (nil_epsilon_second Q K x) ε
  have hnil₃ : epsilonSpatialJet (fun e => epsilonChain [] Q K e) 3 ε = fun _ => 0 := by
    funext x
    exact congrFun (nil_epsilon_third Q K x) ε
  have Hbound : ∀ j, j <:+ full → ∀ i : Fin 3,
      WJets d ((C ^ j.length * M₀ * δ) ^ (i.val + 1)) (3 * (i.val + 1))
        (spatialRescale ρ c (epsilonSpatialJet (fun e => epsilonChain j Q K e) (i.val + 1) ε)) := by
    intro j
    induction j with
    | nil =>
      intro _ i
      fin_cases i
      · simpa only [List.length_nil, pow_zero, one_mul, Fin.val_zero, zero_add, pow_one,
          hnil₁] using HK
      · change WJets d ((C ^ [].length * M₀ * δ) ^ 2) 6
          (spatialRescale ρ c (epsilonSpatialJet (fun e => epsilonChain [] Q K e) 2 ε))
        rw [hnil₂]
        exact wJets_zero d 6 (by positivity : 0 ≤ (C ^ [].length * M₀ * δ) ^ 2)
      · change WJets d ((C ^ [].length * M₀ * δ) ^ 3) 9
          (spatialRescale ρ c (epsilonSpatialJet (fun e => epsilonChain [] Q K e) 3 ε))
        rw [hnil₃]
        exact wJets_zero d 9 (by positivity : 0 ≤ (C ^ [].length * M₀ * δ) ^ 3)
    | cons w j ih =>
      intro hj i
      have hj' : j <:+ full := (List.suffix_cons w j).trans hj
      rcases HJ'.2 w j hj with ⟨P, hP, hmajor⟩
      have Hstep := epsilonStep_scaled_spatial_jets (HJ'.1 j hj') isOpen_Ioo hε' P
        (hm w (hj.subset List.mem_cons_self)) hP hmajor
        (by positivity : 0 ≤ C ^ j.length * M₀) hδ (by linarith : 0 ≤ T) (ih hj')
        (fun B p hp ψ hψ => HA r hr h hh hhA' k hk z ε hε w j hj B p hp ψ hψ) i
      have heq : C ^ (w :: j).length * M₀ = C * (C ^ j.length * M₀) := by
        rw [List.length_cons, pow_succ]
        ring
      rw [heq]
      exact Hstep
  have hlen : t.length ≤ 12 := by simpa only [full, frozenSchedule_length] using ht.length_le
  rw [← heδ]
  apply (Hbound t ht i).mono _ le_rfl
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hlen) (by linarith)) hδ

theorem scalarData_frozen_normalized_epsilon_spatial_jets {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ t, t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WJets d (M ^ (i.val + 1)) (3 * (i.val + 1))
          (fun y => iteratedDeriv (i.val + 1) (fun e => normalizedVariationChain t
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z).value
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (Real.sqrt h) (fun _ => z) e y) ((Real.sqrt h) ^ 3 * ε)) := by
  rcases scalarData_frozen_scaled_epsilon_spatial_jets D hl hu d with ⟨h₀, M, hh₀, hM, H⟩
  refine ⟨h₀, M, hh₀, hM, ?_⟩
  intro r hr h hh hhsmall k hk z t ht ε hε i
  have HB := H r hr h hh hhsmall k hk z t ht ε hε i
  let ρ := Real.sqrt h
  let δ := ρ ^ 3
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hδ : 0 < δ := pow_pos hρ _
  have heδ : δ = Real.sqrt h * h := by
    dsimp only [δ, ρ]
    rw [pow_succ, Real.sq_sqrt hh.le, mul_comm]
  have heq : spatialRescale ρ (fun _ => z) (epsilonSpatialJet (fun e => epsilonChain t
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e) (i.val + 1) ε) =
      fun y => δ ^ (i.val + 1) * iteratedDeriv (i.val + 1) (fun e => normalizedVariationChain t
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z).value
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        ρ (fun _ => z) e y) (δ * ε) := by
    funext y
    exact iteratedDeriv_spatialRescale_variationChain hρ.ne' t _ _ _ _ _ _
  rw [← heδ, heq] at HB
  have Hscaled := wJets_const_mul (a := (δ ^ (i.val + 1))⁻¹) HB
  have heinv : (fun y => (δ ^ (i.val + 1))⁻¹ *
      (δ ^ (i.val + 1) * iteratedDeriv (i.val + 1) (fun e => normalizedVariationChain t
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z).value
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        ρ (fun _ => z) e y) (δ * ε))) =
      fun y => iteratedDeriv (i.val + 1) (fun e => normalizedVariationChain t
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z).value
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        ρ (fun _ => z) e y) (δ * ε) := by
    funext y
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hδ.ne'), one_mul]
  rw [heinv] at Hscaled
  convert Hscaled using 1
  rw [abs_of_pos (inv_pos.mpr (pow_pos hδ _)), mul_pow]
  field_simp [hδ.ne']

end SKBarriers2.Corner
