module

public import SKBarriers2.Corner.FrozenRowsMixed

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

namespace MomentKJet

def SpatialBound (r : ℕ) (B : ℝ) (p : ℕ) (J : Vec3 → MomentKJet) : Prop :=
  WJets r B p (fun y => (J y).value) ∧
    WJets r B p (fun y => (J y).first) ∧ WJets r B p (fun y => (J y).second)

theorem SpatialBound.mono {r p q : ℕ} {B C : ℝ} {J : Vec3 → MomentKJet}
    (H : SpatialBound r B p J) (hBC : B ≤ C) (hpq : p ≤ q) : SpatialBound r C q J :=
  ⟨H.1.mono hBC hpq, H.2.1.mono hBC hpq, H.2.2.mono hBC hpq⟩

theorem SpatialBound.of_le {r s p : ℕ} {B : ℝ} {J : Vec3 → MomentKJet}
    (H : SpatialBound r B p J) (hs : s ≤ r) : SpatialBound s B p J :=
  ⟨H.1.of_le hs, H.2.1.of_le hs, H.2.2.of_le hs⟩

theorem SpatialBound.add {r p : ℕ} {B C : ℝ} {J K : Vec3 → MomentKJet}
    (HJ : SpatialBound r B p J) (HK : SpatialBound r C p K) :
    SpatialBound r (B + C) p (fun y => (J y).add (K y)) :=
  ⟨HJ.1.add HK.1, HJ.2.1.add HK.2.1, HJ.2.2.add HK.2.2⟩

theorem SpatialBound.scale {r p : ℕ} {B : ℝ} {J : Vec3 → MomentKJet}
    (HJ : SpatialBound r B p J) (c : ℝ) :
    SpatialBound r (|c| * B) p (fun y => (J y).scale c) :=
  ⟨HJ.1.const_smul c, HJ.2.1.const_smul c, HJ.2.2.const_smul c⟩

theorem scale_scale (J : MomentKJet) (c d : ℝ) :
    (J.scale c).scale d = J.scale (d * c) := by
  unfold scale
  congr 1 <;> ring

theorem SpatialBound.mul {r p q : ℕ} {B C : ℝ} {J K : Vec3 → MomentKJet}
    (HJ : SpatialBound r B p J) (HK : SpatialBound r C q K) :
    SpatialBound r ((2 : ℝ) ^ (r + 2) * B * C) (p + q)
      (fun y => (J y).mul (K y)) := by
  have hB := HJ.1.nonneg
  have hC := HK.1.nonneg
  have hS : 0 ≤ (2 : ℝ) ^ r := by positivity
  have he : (2 : ℝ) ^ (r + 2) = 4 * (2 : ℝ) ^ r := by rw [pow_add]; ring
  refine ⟨(HJ.1.mul HK.1).mono ?_ le_rfl, ?_, ?_⟩
  · rw [he]
    nlinarith [mul_nonneg (mul_nonneg hS hB) hC]
  · apply ((HJ.2.1.mul HK.1).add (HJ.1.mul HK.2.1)).mono _ le_rfl
    rw [he]
    nlinarith [mul_nonneg (mul_nonneg hS hB) hC]
  · have H := ((HJ.2.2.mul HK.1).add ((HJ.2.1.mul HK.2.1).const_smul 2)).add
      (HJ.1.mul HK.2.2)
    change WJets r _ (p + q) (fun y => (J y).second * (K y).value +
      2 * (J y).first * (K y).first + (J y).value * (K y).second)
    convert H using 1
    · norm_num
      rw [he]
      ring
    · funext y
      simp only [smul_eq_mul]
      ring

end MomentKJet

theorem FrozenRowsMixedEnvelope.intrinsic_spatialBound
    {β a s h z ε M k : ℝ} {α : ℝ → ℝ} {j : ℕ}
    (H : FrozenRowsMixedEnvelope β α a s h z ε j M k) (i : Fin 3) :
    MomentKJet.SpatialBound (2 * j) (M ^ (i.val + 1)) (3 * (i.val + 1))
      (fun y => MomentKJet.rescale (Real.sqrt h)
        (frozenRowsNormalizedJet β α a s h z ε j i y k 0)) := by
  simpa only [MomentKJet.SpatialBound, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    add_zero, one_pow, mul_one] using H 0 i

def epsilonBellTestsKJet (m : ℝ) (R : Fin 3 → MomentKJet) (i : Fin 3) : MomentKJet :=
  ![R 0,
    (R 1).add (((R 0).mul (R 0)).scale m),
    ((R 2).add (((R 0).mul (R 1)).scale (3 * m))).add
      ((((R 0).mul (R 0)).mul (R 0)).scale (m ^ 2))] i

def epsilonLogCumulantsKJet (m : ℝ) (A : Fin 3 → MomentKJet) (i : Fin 3) : MomentKJet :=
  ![A 0,
    (A 1).add (((A 0).mul (A 0)).scale (-m)),
    ((A 2).add (((A 0).mul (A 1)).scale (-3 * m))).add
      ((((A 0).mul (A 0)).mul (A 0)).scale (2 * m ^ 2))] i

theorem epsilonBellTestsKJet_differentiates {R : Fin 3 → ℝ → MomentKJet} {k : ℝ}
    (H : ∀ i, MomentKJet.Differentiates (R i) k) (m : ℝ) (i : Fin 3) :
    MomentKJet.Differentiates (fun x => epsilonBellTestsKJet m (fun i => R i x) i) k := by
  fin_cases i
  · exact H 0
  · exact (H 1).add (((H 0).mul (H 0)).scale m)
  · exact ((H 2).add (((H 0).mul (H 1)).scale (3 * m))).add
      ((((H 0).mul (H 0)).mul (H 0)).scale (m ^ 2))

theorem epsilonLogCumulantsKJet_differentiates {A : Fin 3 → ℝ → MomentKJet} {k : ℝ}
    (H : ∀ i, MomentKJet.Differentiates (A i) k) (m : ℝ) (i : Fin 3) :
    MomentKJet.Differentiates (fun x => epsilonLogCumulantsKJet m (fun i => A i x) i) k := by
  fin_cases i
  · exact H 0
  · exact (H 1).add (((H 0).mul (H 0)).scale (-m))
  · exact ((H 2).add (((H 0).mul (H 1)).scale (-3 * m))).add
      ((((H 0).mul (H 0)).mul (H 0)).scale (2 * m ^ 2))

theorem epsilonBellTestsKJet_rescale (ρ m : ℝ) (R : Fin 3 → MomentKJet) (i : Fin 3) :
    MomentKJet.rescale ρ (epsilonBellTestsKJet m R i) =
      epsilonBellTestsKJet m (fun i => MomentKJet.rescale ρ (R i)) i := by
  fin_cases i <;>
    simp only [epsilonBellTestsKJet, Matrix.cons_val_zero', Matrix.cons_val_succ',
      MomentKJet.rescale_add, MomentKJet.rescale_scale, MomentKJet.rescale_mul]

theorem epsilonLogCumulantsKJet_rescale (ρ m : ℝ) (A : Fin 3 → MomentKJet) (i : Fin 3) :
    MomentKJet.rescale ρ (epsilonLogCumulantsKJet m A i) =
      epsilonLogCumulantsKJet m (fun i => MomentKJet.rescale ρ (A i)) i := by
  fin_cases i <;>
    simp only [epsilonLogCumulantsKJet, Matrix.cons_val_zero', Matrix.cons_val_succ',
      MomentKJet.rescale_add, MomentKJet.rescale_scale, MomentKJet.rescale_mul]

private theorem spatialBound_small_scale {r p : ℕ} {B c : ℝ} {J : Vec3 → MomentKJet}
    (H : MomentKJet.SpatialBound r B p J) (hc : |c| ≤ 1) :
    MomentKJet.SpatialBound r B p (fun y => (J y).scale c) :=
  (H.scale c).mono (mul_le_of_le_one_left H.1.nonneg hc) le_rfl

theorem epsilonBellTestsKJet_spatial {r d : ℕ} {m M : ℝ}
    {R : Fin 3 → Vec3 → MomentKJet} (hm : m ∈ Icc (0 : ℝ) 1)
    (H : ∀ i : Fin 3, MomentKJet.SpatialBound r (M ^ (i.val + 1)) (d * (i.val + 1)) (R i)) :
    let S := (2 : ℝ) ^ (r + 2)
    MomentKJet.SpatialBound r M d (fun y => epsilonBellTestsKJet m (fun i => R i y) 0) ∧
      MomentKJet.SpatialBound r ((1 + S) * M ^ 2) (2 * d)
        (fun y => epsilonBellTestsKJet m (fun i => R i y) 1) ∧
      MomentKJet.SpatialBound r ((1 + 3 * S + S ^ 2) * M ^ 3) (3 * d)
        (fun y => epsilonBellTestsKJet m (fun i => R i y) 2) := by
  let S := (2 : ℝ) ^ (r + 2)
  have hmabs : |m| ≤ 1 := by rw [abs_of_nonneg hm.1]; exact hm.2
  have hm₂abs : |m ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hmabs
  have H₁ : MomentKJet.SpatialBound r M d (R 0) := by simpa only [Fin.val_zero, zero_add, pow_one, mul_one] using H 0
  have H₂ : MomentKJet.SpatialBound r (M ^ 2) (2 * d) (R 1) := by
    have H' := H 1
    change MomentKJet.SpatialBound r (M ^ 2) (d * 2) (R 1) at H'
    simpa only [Nat.mul_comm] using H'
  have H₃ : MomentKJet.SpatialBound r (M ^ 3) (3 * d) (R 2) := by
    have H' := H 2
    change MomentKJet.SpatialBound r (M ^ 3) (d * 3) (R 2) at H'
    simpa only [Nat.mul_comm] using H'
  have Hsq : MomentKJet.SpatialBound r (S * M ^ 2) (2 * d)
      (fun y => (R 0 y).mul (R 0 y)) := by convert H₁.mul H₁ using 1 <;> first | rfl | ring
  have Hprod : MomentKJet.SpatialBound r (S * M ^ 3) (3 * d)
      (fun y => (R 0 y).mul (R 1 y)) := by convert H₁.mul H₂ using 1 <;> first | rfl | ring
  have Hcube : MomentKJet.SpatialBound r (S ^ 2 * M ^ 3) (3 * d)
      (fun y => ((R 0 y).mul (R 0 y)).mul (R 0 y)) := by
    convert Hsq.mul H₁ using 1 <;> first | rfl | ring
  have Hmid := (spatialBound_small_scale Hprod hmabs).scale 3
  have Hlast := spatialBound_small_scale Hcube hm₂abs
  refine ⟨H₁, ?_, ?_⟩
  · convert H₂.add (spatialBound_small_scale Hsq hmabs) using 1
    · dsimp only [S]
      ring
    · funext y
      simp [epsilonBellTestsKJet]
  · convert (H₃.add Hmid).add Hlast using 1
    · norm_num
      dsimp only [S]
      ring
    · funext y
      simp [epsilonBellTestsKJet, MomentKJet.scale_scale]

def mixedCumulantBudget (r : ℕ) (D : ℝ) : ℝ :=
  let S := (2 : ℝ) ^ (r + 2)
  1 + D + 4 * S * D ^ 2 + 2 * S ^ 2 * D ^ 3

theorem mixedCumulantBudget_ge_one (r : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ mixedCumulantBudget r D := by
  dsimp only [mixedCumulantBudget]
  have h₂ : 0 ≤ 4 * (2 : ℝ) ^ (r + 2) * D ^ 2 := by positivity
  have h₃ : 0 ≤ 2 * ((2 : ℝ) ^ (r + 2)) ^ 2 * D ^ 3 := by positivity
  linarith

theorem epsilonLogCumulantsKJet_spatial {r d : ℕ} {m M D : ℝ}
    {A : Fin 3 → Vec3 → MomentKJet} (hm : m ∈ Icc (0 : ℝ) 1)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (H : ∀ i : Fin 3, MomentKJet.SpatialBound r (D * M ^ (i.val + 1))
      (d * (i.val + 1)) (A i)) :
    ∀ i : Fin 3, MomentKJet.SpatialBound r
      ((mixedCumulantBudget r D * M) ^ (i.val + 1)) (d * (i.val + 1))
        (fun y => epsilonLogCumulantsKJet m (fun i => A i y) i) := by
  let S := (2 : ℝ) ^ (r + 2)
  let C := mixedCumulantBudget r D
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hC : 1 ≤ C := mixedCumulantBudget_ge_one r hD
  have hmabs : |m| ≤ 1 := by rw [abs_of_nonneg hm.1]; exact hm.2
  have hmneg : |-m| ≤ 1 := by simpa only [abs_neg] using hmabs
  have hm₂abs : |m ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hmabs
  have H₁ : MomentKJet.SpatialBound r (D * M) d (A 0) := by
    simpa only [Fin.val_zero, zero_add, pow_one, mul_one] using H 0
  have H₂ : MomentKJet.SpatialBound r (D * M ^ 2) (2 * d) (A 1) := by
    have H' := H 1
    change MomentKJet.SpatialBound r (D * M ^ 2) (d * 2) (A 1) at H'
    simpa only [Nat.mul_comm] using H'
  have H₃ : MomentKJet.SpatialBound r (D * M ^ 3) (3 * d) (A 2) := by
    have H' := H 2
    change MomentKJet.SpatialBound r (D * M ^ 3) (d * 3) (A 2) at H'
    simpa only [Nat.mul_comm] using H'
  have Hsq : MomentKJet.SpatialBound r (S * D ^ 2 * M ^ 2) (2 * d)
      (fun y => (A 0 y).mul (A 0 y)) := by
    convert H₁.mul H₁ using 1 <;> first | rfl | ring
  have Hprod : MomentKJet.SpatialBound r (S * D ^ 2 * M ^ 3) (3 * d)
      (fun y => (A 0 y).mul (A 1 y)) := by
    convert H₁.mul H₂ using 1 <;> first | rfl | ring
  have Hcube : MomentKJet.SpatialBound r (S ^ 2 * D ^ 3 * M ^ 3) (3 * d)
      (fun y => ((A 0 y).mul (A 0 y)).mul (A 0 y)) := by
    convert Hsq.mul H₁ using 1 <;> first | rfl | ring
  have h₁ : D ≤ C := by
    dsimp only [C, mixedCumulantBudget]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hS) (sq_nonneg D),
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg S)) (pow_nonneg hD 3)]
  have h₂ : D + S * D ^ 2 ≤ C ^ 2 := by
    have Hle : D + S * D ^ 2 ≤ C := by
      dsimp only [C, mixedCumulantBudget]
      nlinarith [mul_nonneg hS (sq_nonneg D),
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg S)) (pow_nonneg hD 3)]
    exact Hle.trans (by nlinarith)
  have h₃ : D + 3 * S * D ^ 2 + 2 * S ^ 2 * D ^ 3 ≤ C ^ 3 := by
    have Hle : D + 3 * S * D ^ 2 + 2 * S ^ 2 * D ^ 3 ≤ C := by
      dsimp only [C, mixedCumulantBudget]
      nlinarith [mul_nonneg hS (sq_nonneg D)]
    exact Hle.trans (by nlinarith [mul_nonneg (by linarith : 0 ≤ C - 1) (sq_nonneg C)])
  intro i
  fin_cases i
  · simpa [epsilonLogCumulantsKJet, C] using
      H₁.mono (mul_le_mul_of_nonneg_right h₁ hM) le_rfl
  · change MomentKJet.SpatialBound r ((C * M) ^ 2) (d * 2)
      (fun y => (A 1 y).add (((A 0 y).mul (A 0 y)).scale (-m)))
    rw [Nat.mul_comm d 2]
    have HB := H₂.add (spatialBound_small_scale Hsq hmneg)
    apply HB.mono _ le_rfl
    convert mul_le_mul_of_nonneg_right h₂ (sq_nonneg M) using 1 <;> ring
  · change MomentKJet.SpatialBound r ((C * M) ^ 3) (d * 3)
      (fun y => epsilonLogCumulantsKJet m (fun i => A i y) 2)
    rw [Nat.mul_comm d 3]
    have Hmid := (spatialBound_small_scale Hprod hmneg).scale 3
    have Hlast := (spatialBound_small_scale Hcube hm₂abs).scale 2
    have HB := (H₃.add Hmid).add Hlast
    have HB' : MomentKJet.SpatialBound r
        ((D + 3 * S * D ^ 2 + 2 * S ^ 2 * D ^ 3) * M ^ 3) (3 * d)
        (fun y => epsilonLogCumulantsKJet m (fun i => A i y) 2) := by
      convert HB using 1
      · norm_num
        ring
      · funext y
        simp [epsilonLogCumulantsKJet, MomentKJet.scale_scale, mul_neg, neg_mul]
    apply HB'.mono _ le_rfl
    convert mul_le_mul_of_nonneg_right h₃ (pow_nonneg hM 3) using 1; ring

theorem epsilonMixedStep_of_movingBellBounds {r : ℕ} {m M T : ℝ}
    {R A : Fin 3 → Vec3 → MomentKJet} (hm : m ∈ Icc (0 : ℝ) 1)
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (HR : ∀ i : Fin 3, MomentKJet.SpatialBound (r + 2) (M ^ (i.val + 1))
      (3 * (i.val + 1)) (R i))
    (HA : ∀ i : Fin 3, ∀ B : ℝ,
      MomentKJet.SpatialBound (r + 2) B (3 * (i.val + 1))
        (fun y => epsilonBellTestsKJet m (fun i => R i y) i) →
      MomentKJet.SpatialBound r (T * B) (3 * (i.val + 1)) (A i)) :
    let S := (2 : ℝ) ^ (r + 4)
    let D := T * (1 + 3 * S + S ^ 2)
    ∀ i : Fin 3, MomentKJet.SpatialBound r
      ((mixedCumulantBudget r D * M) ^ (i.val + 1)) (3 * (i.val + 1))
        (fun y => epsilonLogCumulantsKJet m (fun i => A i y) i) := by
  let S := (2 : ℝ) ^ (r + 4)
  let B₀ := 1 + 3 * S + S ^ 2
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hB₀ : 1 ≤ B₀ := by dsimp only [B₀]; nlinarith [sq_nonneg S]
  have hB₂ : 1 + S ≤ B₀ := by dsimp only [B₀]; nlinarith [sq_nonneg S]
  have HB := epsilonBellTestsKJet_spatial hm HR
  have HB' : ∀ i : Fin 3, MomentKJet.SpatialBound (r + 2) (B₀ * M ^ (i.val + 1))
      (3 * (i.val + 1)) (fun y => epsilonBellTestsKJet m (fun i => R i y) i) := by
    intro i
    fin_cases i
    · simpa using HB.1.mono (le_mul_of_one_le_left hM hB₀) le_rfl
    · exact HB.2.1.mono (mul_le_mul_of_nonneg_right hB₂ (sq_nonneg M)) le_rfl
    · exact HB.2.2
  have HA' : ∀ i : Fin 3, MomentKJet.SpatialBound r
      ((T * B₀) * M ^ (i.val + 1)) (3 * (i.val + 1)) (A i) := by
    intro i
    simpa only [mul_assoc] using HA i _ (HB' i)
  exact epsilonLogCumulantsKJet_spatial hm hM (mul_nonneg hT (by linarith)) HA'

def frozenRowsCompletedPotential (β : ℝ) (α : ℝ → ℝ)
    (s h z ε : ℝ) (t : List (ℝ × Vec3)) : Vec3 → ℝ :=
  spatialRescale (Real.sqrt h) (fun _ => z)
    (epsilonFrameResidual t (terminalTaylorQuadratic β α s h z)
      (frozenTerminal β α s h) ε)

def frozenRowsCompletedDirection (β : ℝ) (α : ℝ → ℝ)
    (s h z ε : ℝ) (w : ℝ × Vec3) (t : List (ℝ × Vec3)) : Vec3 :=
  let P := riccatiRecursion t ((terminalTaylorQuadratic β α s h z).scale (1 - ε))
  (Real.sqrt h)⁻¹ • ((Real.sqrt (P.precision w.1 w.2)⁻¹) • w.2)

def frozenRowsCompletedLaw (β : ℝ) (α : ℝ → ℝ)
    (s h z ε : ℝ) (w : ℝ × Vec3) (t : List (ℝ × Vec3)) (x : Vec3) : Measure ℝ :=
  StepCalculus.stepLaw w.1 (frozenRowsCompletedDirection β α s h z ε w t)
    (frozenRowsCompletedPotential β α s h z ε t) x

private theorem frozenRowsHead_mem (β a h k : ℝ) {j : ℕ} (hj : j < 12) :
    frozenRowsHead β a h j k ∈ frozenSchedule β a (1 / 2) h k := by
  have hj' : j < (frozenSchedule β a (1 / 2) h k).length := by
    simpa only [frozenSchedule_length] using hj
  rw [frozenRowsHead, List.getD_eq_getElem _ _ hj']
  exact List.getElem_mem hj'

theorem scalarData_frozenRowsMixed_value {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, j < 12 → ∀ k ∈ frozenRowsKDomain, ∀ g : ℝ, ∀ i : Fin 3,
        WJets 22 ((M * (1 + g ^ 2) ^ 3) ^ (i.val + 1)) (3 * (i.val + 1))
          (fun y => (frozenRowsNormalizedJet β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j i y k g).value) := by
  obtain ⟨h₀, M₀, hh₀, hM₀, H⟩ := scalarData_frozen_normalized_epsilon_spatial_jets D hl hu 22
  let K := 6 * (|β| + 1)
  let M := M₀ * (2 * (K + 1) ^ 2) ^ 3
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hM₀
    (one_le_pow₀ (by nlinarith : 1 ≤ 2 * (K + 1) ^ 2))
  refine ⟨h₀, M, hh₀, hM, ?_⟩
  intro r hr h hh hhsmall z ε hε j hj k hk g i
  let α := cdf (D.μ : Measure ℝ)
  let ρ := Real.sqrt h
  let v := ρ⁻¹ • (frozenRowsHead β (α (r - h)) h j k).2
  have hk' : |k| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hv : ‖v‖ ≤ K := frozenSchedule_scaled_direction_bound hh hk'
    (List.mem_map.mpr ⟨frozenRowsHead β (α (r - h)) h j k,
      frozenRowsHead_mem β _ h k hj, rfl⟩)
  have HE := H r hr h hh hhsmall k hk' z
    ((frozenSchedule β (α (r - h)) (1 / 2) h k).drop (j + 1)) (List.drop_suffix _ _) ε hε i
  have Hshift := HE.translate (g • v)
  have hweight : (1 + ‖g • v‖) ^ 3 ≤
      (2 * (K + 1) ^ 2) ^ 3 * (1 + g ^ 2) ^ 3 := by
    let R := (K + 1) * (1 + |g|)
    have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by linarith)
      (by linarith [abs_nonneg g])
    have hnorm : 1 + ‖g • v‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ 1 + |g| * K := add_le_add_right (mul_le_mul_of_nonneg_left hv (abs_nonneg g)) 1
        _ ≤ R := by dsimp only [R]; nlinarith [abs_nonneg g]
    have hsquare : R ^ 2 ≤ (2 * (K + 1) ^ 2) * (1 + g ^ 2) := by
      have Hsq : (1 + |g|) ^ 2 ≤ 2 * (1 + g ^ 2) := by
        nlinarith [sq_nonneg (|g| - 1), sq_abs g]
      dsimp only [R]
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left Hsq (sq_nonneg (K + 1))]
    calc
      _ ≤ R ^ 3 := pow_le_pow_left₀ (by positivity) hnorm 3
      _ ≤ R ^ 6 := pow_le_pow_right₀ hR (by omega)
      _ = (R ^ 2) ^ 3 := by ring
      _ ≤ ((2 * (K + 1) ^ 2) * (1 + g ^ 2)) ^ 3 :=
        pow_le_pow_left₀ (sq_nonneg R) hsquare 3
      _ = _ := by ring
  have Hbound : M₀ ^ (i.val + 1) * (1 + ‖g • v‖) ^ (3 * (i.val + 1)) ≤
      (M * (1 + g ^ 2) ^ 3) ^ (i.val + 1) := by
    calc
      _ = (M₀ * (1 + ‖g • v‖) ^ 3) ^ (i.val + 1) := by rw [mul_pow, pow_mul]
      _ ≤ (M₀ * ((2 * (K + 1) ^ 2) ^ 3 * (1 + g ^ 2) ^ 3)) ^ (i.val + 1) :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hweight (by linarith)) _
      _ = _ := by dsimp only [M]; ring
  have heq : (fun y => (frozenRowsNormalizedJet β α (α (r - h)) (r - h) h z ε j i y k g).value) =
      fun y => iteratedDeriv (i.val + 1) (fun e => normalizedVariationChain
        ((frozenSchedule β (α (r - h)) (1 / 2) h k).drop (j + 1))
        (terminalTaylorQuadratic β α (r - h) h z).value
        (terminalResidual β α (r - h) h z) ρ (fun _ => z) e (y + g • v)) (ρ ^ 3 * ε) := by
    funext y
    simp only [frozenRowsNormalizedJet, normalizedEpsilonKJet, v, ρ, smul_smul, mul_comm]
  rw [heq]
  exact Hshift.mono Hbound le_rfl

theorem scalarData_frozenRowsCompletedLaw_moments {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (N : ℕ) :
    ∃ h₀ T : ℝ, 0 < h₀ ∧ 1 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (-1 : ℝ) 2, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∀ x : Vec3,
          let μ := frozenRowsCompletedLaw β (cdf (D.μ : Measure ℝ)) (r - h) h z ε w t x
          IsProbabilityMeasure μ ∧ ∀ q ≤ N,
            Integrable (fun g : ℝ => (1 + |g|) ^ q) μ ∧
              (∫ g : ℝ, (1 + |g|) ^ q ∂μ) ≤ T := by
  obtain ⟨hM, T, hhM, hT, HM⟩ := scalarData_frozen_normalized_noise_moments D hl hu N
  obtain ⟨C, hF, _, hhF, HF⟩ := scalarData_frozen_scaled_frame_qPotential D hl hu 3 (by norm_num)
  refine ⟨min hM hF, T, lt_min hhM hhF, hT, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε w t ht x
  have H := HF r hr h hh (hhsmall.trans (min_le_right _ _)) k hk z ε hε t
    ((List.suffix_cons w t).trans ht)
  refine ⟨StepCalculus.stepLaw_probability H (by norm_num) w.1
    (frozenRowsCompletedDirection β _ _ h z ε w t) x, ?_⟩
  exact HM r hr h hh (hhsmall.trans (min_le_left _ _)) k hk z ε hε w t ht x

private theorem memLp_two_of_noise_envelope {μ : Measure ℝ} {f : ℝ → ℝ}
    {C : ℝ} {p : ℕ} (hf : Continuous f)
    (hbound : ∀ g, |f g| ≤ C * (1 + |g|) ^ p)
    (hi : Integrable (fun g : ℝ => (1 + |g|) ^ (2 * p)) μ) :
    MemLp f 2 μ := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply (hi.const_mul (C ^ 2)).mono' (hf.pow 2).aestronglyMeasurable
  filter_upwards [] with g
  change ‖f g ^ 2‖ ≤ C ^ 2 * (1 + |g|) ^ (2 * p)
  rw [Real.norm_eq_abs, abs_pow]
  have H := pow_le_pow_left₀ (abs_nonneg (f g)) (hbound g) 2
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using H

theorem wJets_affine_noise_memLp {μ : Measure ℝ} {r p : ℕ} {B : ℝ} {f : Vec3 → ℝ}
    (hf : WJets r B p f) (a v : Vec3)
    (hi : Integrable (fun g : ℝ => (1 + |g|) ^ (2 * p)) μ) :
    MemLp (fun g => f (a + g • v)) 2 μ := by
  apply memLp_two_of_noise_envelope (f := fun g => f (a + g • v))
    (hf.smooth.continuous.comp (by fun_prop)) (C :=
    B * (1 + ‖a‖ + ‖v‖) ^ p) _ hi
  intro g
  have hb : 1 + ‖a + g • v‖ ≤ (1 + ‖a‖ + ‖v‖) * (1 + |g|) := by
    have H := norm_add_le a (g • v)
    rw [norm_smul, Real.norm_eq_abs] at H
    nlinarith [mul_nonneg (norm_nonneg a) (abs_nonneg g), abs_nonneg g, norm_nonneg v]
  calc
    _ ≤ B * (1 + ‖a + g • v‖) ^ p := by
      simpa only [Real.norm_eq_abs] using hf.norm_le (a + g • v)
    _ ≤ B * ((1 + ‖a‖ + ‖v‖) * (1 + |g|)) ^ p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb p) hf.nonneg
    _ = _ := by rw [mul_pow]; ring

private theorem memLp_two_of_centered_noise_envelope {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} {C f₀ : ℝ} {p : ℕ} (hf : Continuous f)
    (hb : ∀ g, |f g - f₀| ≤ C * (1 + |g|) ^ p)
    (hi : Integrable (fun g : ℝ => (1 + |g|) ^ (2 * p)) μ) : MemLp f 2 μ := by
  have H := memLp_two_of_noise_envelope (hf.sub continuous_const) hb hi
  convert H.add (memLp_const f₀) using 1
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel]

theorem scalarData_frozenRowsCompletedLaw_centered_bounds {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (p q : ℕ) :
    ∃ h₀ T : ℝ, 0 < h₀ ∧ 1 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (-1 : ℝ) 2, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∀ x : Vec3, ∀ f s : ℝ → ℝ, Continuous f → Continuous s →
        ∀ C L f₀ s₀ : ℝ, 0 ≤ C → 0 ≤ L →
          (∀ g, |f g - f₀| ≤ C * (1 + |g|) ^ p) →
          (∀ g, |s g - s₀| ≤ L * (1 + |g|) ^ q) →
          let μ := frozenRowsCompletedLaw β (cdf (D.μ : Measure ℝ)) (r - h) h z ε w t x
          |covariance f s μ| ≤ C * L * (T + T ^ 2) ∧
            |covariance f (fun g => s g ^ 2) μ -
                2 * (∫ g, s g ∂μ) * covariance f s μ| ≤
              C * L ^ 2 * ((T + T ^ 2) + 2 * T * (T + T ^ 2)) := by
  obtain ⟨h₀, T, hh₀, hT, H⟩ :=
    scalarData_frozenRowsCompletedLaw_moments D hl hu (2 * (p + 2 * q))
  refine ⟨h₀, T, hh₀, hT, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε w t ht x f s hf hs C L f₀ s₀ hC hL hfB hsB
  let μ := frozenRowsCompletedLaw β (cdf (D.μ : Measure ℝ)) (r - h) h z ε w t x
  have Hlaw := H r hr h hh hhsmall k hk z ε hε w t ht x
  let _ : IsProbabilityMeasure μ := Hlaw.1
  have hfLp : MemLp f 2 μ := memLp_two_of_centered_noise_envelope hf hfB
    (Hlaw.2 (2 * p) (by omega)).1
  have hsLp : MemLp s 2 μ := memLp_two_of_centered_noise_envelope hs hsB
    (Hlaw.2 (2 * q) (by omega)).1
  have hsC : MemLp (fun g => s g - s₀) 2 μ := hsLp.sub (memLp_const s₀)
  have hsqB (g : ℝ) : |(s g - s₀) ^ 2| ≤ L ^ 2 * (1 + |g|) ^ (2 * q) := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (hsB g) 2).trans_eq
      (by rw [mul_pow, ← pow_mul]; ring)
  have hsqC : MemLp (fun g => (s g - s₀) ^ 2) 2 μ :=
    memLp_two_of_noise_envelope ((hs.sub continuous_const).pow 2) hsqB
      (Hlaw.2 (2 * (2 * q)) (by omega)).1
  have hsq : MemLp (fun g => s g ^ 2) 2 μ := by
    convert (hsqC.add (hsC.const_mul (2 * s₀))).add (memLp_const (s₀ ^ 2)) using 1
    funext g
    simp only [Pi.add_apply]
    ring
  have hi (n : ℕ) (hn : n ≤ p + 2 * q) : Integrable (fun g : ℝ => (1 + |g|) ^ n) μ :=
    (Hlaw.2 n (by omega)).1
  have hMom (n : ℕ) (hn : n ≤ p + 2 * q) : (∫ g : ℝ, (1 + |g|) ^ n ∂μ) ≤ T :=
    (Hlaw.2 n (by omega)).2
  exact ⟨covariance_centered_weight_bound hfLp hsLp hC hL hfB hsB
    (hi p (by omega)) (hi q (by omega)) (hi (p + q) (by omega))
    (hMom p (by omega)) (hMom q (by omega)) (hMom (p + q) (by omega)) (by linarith),
    scoreCumulant_centered_weight_bound hfLp hsLp hsq hC hL (by linarith) hfB hsB hi hMom⟩

theorem scalarData_frozenRowsMixedTail_memLp {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k ∈ frozenRowsKDomain, ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∀ x a v : Vec3, ∀ j : ℕ, ∀ M : ℝ,
          FrozenRowsMixedEnvelope β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j M k → ∀ i : Fin 3,
          let μ := frozenRowsCompletedLaw β (cdf (D.μ : Measure ℝ)) (r - h) h z ε w t x
          let J := fun g => MomentKJet.rescale (Real.sqrt h)
            (frozenRowsNormalizedJet β (cdf (D.μ : Measure ℝ))
              (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j i (a + g • v) k 0)
          MemLp (fun g => (J g).value) 2 μ ∧
            MemLp (fun g => (J g).first) 2 μ ∧ MemLp (fun g => (J g).second) 2 μ := by
  obtain ⟨h₀, T, hh₀, _, H⟩ := scalarData_frozenRowsCompletedLaw_moments D hl hu 18
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε w t ht x a v j M HJ i
  have hk' : |k| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hε' : ε ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have Hlaw := H r hr h hh hhsmall k hk' z ε hε' w t ht x
  have hmom := (Hlaw.2 (2 * (3 * (i.val + 1))) (by omega)).1
  exact ⟨wJets_affine_noise_memLp (HJ 0 i).1 a v hmom,
    wJets_affine_noise_memLp (HJ 0 i).2.1 a v hmom,
    wJets_affine_noise_memLp (HJ 0 i).2.2 a v hmom⟩

def movingLinearGaussianStep (A k ε : ℝ) : ℝ :=
  quadraticPerturbation 1 0 (Real.sin (A * k)) 0 (fun g => g) ε

theorem movingLinearGaussianStep_input_spatial (r : ℕ) :
    WJets r 1 3 (fun g : ℝ => g) := by
  refine ⟨by norm_num, contDiff_id, ?_⟩
  intro j _hj g
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  by_cases hj0 : j = 0
  · subst j
    simp only [iteratedDeriv_zero, one_mul, Real.norm_eq_abs]
    nlinarith [abs_nonneg g, mul_nonneg (abs_nonneg g) (sq_nonneg (|g| + 1))]
  · by_cases hj1 : j = 1
    · subst j
      simp only [iteratedDeriv_one, deriv_id'', abs_one, one_mul, Real.norm_eq_abs]
      nlinarith [abs_nonneg g, mul_nonneg (abs_nonneg g) (sq_nonneg (|g| + 1))]
    · rw [iteratedDeriv_fun_id, ite_eq_right hj0, ite_eq_right hj1, abs_zero, one_mul]
      positivity

theorem movingLinearGaussianStep_input_jets (A k g ε : ℝ) :
    let f := fun e => Real.sin (A * k) * g + e * g
    iteratedDeriv 1 f ε = g ∧ iteratedDeriv 2 f ε = 0 ∧ iteratedDeriv 3 f ε = 0 := by
  have hd : deriv (fun e => Real.sin (A * k) * g + e * g) = fun _ => g := by
    funext e
    convert ((hasDerivAt_const e (Real.sin (A * k) * g)).add
      ((hasDerivAt_id e).mul_const g)).deriv using 1 <;> simp
  dsimp only
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, hd, deriv_const']
  trivial

theorem movingLinearGaussianStep_value (A k ε : ℝ) :
    movingLinearGaussianStep A k ε = (Real.sin (A * k) + ε) ^ 2 / 2 := by
  have he : (fun p : Unit × ℝ =>
      0 + Real.sin (A * k) * p.2 + (0 : ℝ) / 2 * p.2 ^ 2 + ε * p.2) =
      fun p => 0 + (Real.sin (A * k) + ε) * p.2 + (0 : ℝ) / 2 * p.2 ^ 2 := by
    funext p
    ring
  unfold movingLinearGaussianStep quadraticPerturbation
  rw [he, gaussianStep_quadratic (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : 0 < 1 - (1 : ℝ) * 0)]
  norm_num

theorem movingLinearGaussianStep_epsilon_first (A k ε : ℝ) :
    deriv (movingLinearGaussianStep A k) ε = Real.sin (A * k) + ε := by
  have he : movingLinearGaussianStep A k = fun e => (Real.sin (A * k) + e) ^ 2 / 2 :=
    funext (movingLinearGaussianStep_value A k)
  rw [he]
  have H := (((hasDerivAt_const ε (Real.sin (A * k))).add (hasDerivAt_id ε)).pow 2).div_const 2
  convert H.deriv using 1 <;> simp [Pi.pow_apply, Pi.add_apply]

theorem movingLinearGaussianStep_mixed_first (A ε : ℝ) :
    deriv (fun k => deriv (movingLinearGaussianStep A k) ε) 0 = A := by
  have he : (fun k => deriv (movingLinearGaussianStep A k) ε) =
      fun k => Real.sin (A * k) + ε := funext (fun k => movingLinearGaussianStep_epsilon_first A k ε)
  rw [he]
  simpa only [id_eq, mul_zero, Real.cos_zero, one_mul, mul_one] using
    ((((hasDerivAt_id (0 : ℝ)).const_mul A).sin).add_const ε).deriv

theorem movingLinearGaussianStep_uniform_moments (N : ℕ) :
    ∃ T : ℝ, 0 < T ∧ ∀ A k ε : ℝ, ε ∈ Icc (-1 : ℝ) 2 →
      let μ := (gaussianReal 0 1).tilted (fun g => (Real.sin (A * k) + ε) * g)
      Integrable (fun g : ℝ => (1 + |g|) ^ N) μ ∧
        (∫ g : ℝ, (1 + |g|) ^ N ∂μ) ≤ T := by
  refine ⟨gaussianTiltPolynomialConstant 3 N, gaussianTiltPolynomialConstant_pos 3 N, ?_⟩
  intro A k ε hε
  have hεabs : |ε| ≤ 2 := abs_le.mpr ⟨by linarith [hε.1], hε.2⟩
  have hs : |Real.sin (A * k) + ε| ≤ 3 :=
    (abs_add_le _ _).trans ((add_le_add (Real.abs_sin_le_one _) hεabs).trans_eq (by norm_num))
  apply gaussian_tilt_polynomial_bound (by fun_prop) (by norm_num : (0 : ℝ) ≤ 3)
  intro g
  simp only [mul_zero, sub_zero, abs_mul]
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg g)

theorem movingLinearGaussianStep_mixed_first_unbounded (C : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧
      C < |deriv (fun k => deriv (movingLinearGaussianStep A k) 0) 0| := by
  refine ⟨|C| + 1, by linarith [abs_nonneg C], ?_⟩
  rw [movingLinearGaussianStep_mixed_first, abs_of_pos (by positivity : 0 < |C| + 1)]
  linarith [le_abs_self C]

end SKBarriers2.Corner
