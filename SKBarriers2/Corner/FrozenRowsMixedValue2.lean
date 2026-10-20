module

public import SKBarriers2.Corner.FrozenRowsMixedValue
public import SKBarriers2.Corner.FrozenRowsMixed2

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner.MomentKJet

structure FirstDegreeBound (r : ℕ) (B : ℝ) (p : ℕ) (J : Vec3 → MomentKJet) : Prop where
  value : DegreeJets r B p (fun y => (J y).value)
  first : WJets r B (p + 1) (fun y => (J y).first)

namespace FirstDegreeBound
variable {r s p q : ℕ} {B C : ℝ} {J K : Vec3 → MomentKJet}

theorem mono (hJ : FirstDegreeBound r B p J) (hBC : B ≤ C) (hpq : p ≤ q) :
    FirstDegreeBound r C q J :=
  ⟨hJ.value.mono hBC hpq, hJ.first.mono hBC (by omega)⟩

theorem congr (hJ : FirstDegreeBound r B p J)
    (hvalue : ∀ y, (K y).value = (J y).value)
    (hfirst : ∀ y, (K y).first = (J y).first) : FirstDegreeBound r B p K := by
  refine ⟨?_, ?_⟩
  · have h : (fun y => (K y).value) = fun y => (J y).value := funext hvalue
    rw [h]
    exact hJ.value
  · have h : (fun y => (K y).first) = fun y => (J y).first := funext hfirst
    rw [h]
    exact hJ.first

theorem of_le (hJ : FirstDegreeBound r B p J) (hs : s ≤ r) :
    FirstDegreeBound s B p J := ⟨hJ.value.of_le hs, hJ.first.of_le hs⟩

theorem add (hJ : FirstDegreeBound r B p J) (hK : FirstDegreeBound r C p K) :
    FirstDegreeBound r (B + C) p (fun y => (J y).add (K y)) :=
  ⟨hJ.value.add hK.value, hJ.first.add hK.first⟩

theorem scale (hJ : FirstDegreeBound r B p J) (a : ℝ) :
    FirstDegreeBound r (|a| * B) p (fun y => (J y).scale a) :=
  ⟨hJ.value.const_mul a, by simpa only [MomentKJet.scale, smul_eq_mul] using hJ.first.const_smul a⟩

theorem small_scale (hJ : FirstDegreeBound r B p J) {a : ℝ} (ha : |a| ≤ 1) :
    FirstDegreeBound r B p (fun y => (J y).scale a) :=
  (hJ.scale a).mono (mul_le_of_le_one_left hJ.value.value.nonneg ha) le_rfl

theorem mul (hJ : FirstDegreeBound r B p J) (hK : FirstDegreeBound r C q K) :
    FirstDegreeBound r ((2 : ℝ) ^ (r + 1) * B * C) (p + q + 1)
      (fun y => (J y).mul (K y)) := by
  have hB := hJ.value.value.nonneg
  have hC := hK.value.value.nonneg
  have hS : (2 : ℝ) ^ r ≤ 2 ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ r)
  refine ⟨(hJ.value.mul hK.value).mono
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hB) hC) le_rfl, ?_⟩
  have H := (hJ.first.mul hK.value.value).add (hJ.value.value.mul hK.first)
  change WJets r _ _ (fun y => (J y).first * (K y).value + (J y).value * (K y).first)
  convert H using 1
  · rw [pow_succ]
    ring
  · omega

theorem mul_budget (hJ : FirstDegreeBound r B p J) (hK : FirstDegreeBound r C q K)
    {S : ℝ} (hS : (2 : ℝ) ^ (r + 1) ≤ S) :
    FirstDegreeBound r (S * B * C) (p + q + 1) (fun y => (J y).mul (K y)) :=
  (hJ.mul hK).mono (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hS hJ.value.value.nonneg) hK.value.value.nonneg) le_rfl

theorem square (hJ : FirstDegreeBound r B p J) :
    FirstDegreeBound r ((2 : ℝ) ^ (r + 1) * B ^ 2) (p + p + 1)
      (fun y => (J y).mul (J y)) := by
  convert hJ.mul hJ using 1
  ring

theorem cube (hJ : FirstDegreeBound r B p J) :
    FirstDegreeBound r (((2 : ℝ) ^ (r + 1)) ^ 2 * B ^ 3) (p + p + 1 + p + 1)
      (fun y => ((J y).mul (J y)).mul (J y)) := by
  convert (hJ.mul hJ).mul hJ using 1
  ring

theorem square_budget (hJ : FirstDegreeBound r B p J) {S : ℝ}
    (hS : (2 : ℝ) ^ (r + 1) ≤ S) :
    FirstDegreeBound r (S * B ^ 2) (p + p + 1) (fun y => (J y).mul (J y)) := by
  convert hJ.mul_budget hJ hS using 1
  ring

theorem cube_budget (hJ : FirstDegreeBound r B p J) {S : ℝ}
    (hS : (2 : ℝ) ^ (r + 1) ≤ S) :
    FirstDegreeBound r (S ^ 2 * B ^ 3) (p + p + 1 + p + 1)
      (fun y => ((J y).mul (J y)).mul (J y)) := by
  convert (hJ.mul_budget hJ hS).mul_budget hJ hS using 1
  ring

end FirstDegreeBound
end SKBarriers2.Corner.MomentKJet

namespace SKBarriers2.Corner

theorem epsilonBellTestsKJet_first_degree {r : ℕ} {V m : ℝ}
    (hV : 0 ≤ V) (hm : m ∈ Icc (0 : ℝ) 1) {R : Fin 3 → Vec3 → MomentKJet}
    (HJ : ∀ i : Fin 3, MomentKJet.FirstDegreeBound r
      (V ^ (i.val + 1)) (2 * (i.val + 1) - 1) (R i)) :
    ∀ i : Fin 3, MomentKJet.FirstDegreeBound r
      ((1 + 3 * (2 : ℝ) ^ (r + 1) + ((2 : ℝ) ^ (r + 1)) ^ 2) * V ^ (i.val + 1))
      (2 * (i.val + 1) - 1)
      (fun y => epsilonBellTestsKJet m (fun j => R j y) i) := by
  let S := (2 : ℝ) ^ (r + 1)
  let D := 1 + 3 * S + S ^ 2
  let f₁ := R 0
  let f₂ := R 1
  let f₃ := R 2
  let ψ₂ : Vec3 → MomentKJet := fun x => (f₂ x).add (((f₁ x).mul (f₁ x)).scale m)
  let ψ₃ : Vec3 → MomentKJet := fun x =>
    ((f₃ x).add (((f₁ x).mul (f₂ x)).scale (3 * m))).add
      ((((f₁ x).mul (f₁ x)).mul (f₁ x)).scale (m ^ 2))
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hmabs : |m| ≤ 1 := by rw [abs_of_nonneg hm.1]; exact hm.2
  have hm₂abs : |m ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hmabs
  have H₁ : MomentKJet.FirstDegreeBound r V 1 f₁ := by
    simpa only [Fin.val_zero, zero_add, pow_one] using HJ 0
  have H₂ : MomentKJet.FirstDegreeBound r (V ^ 2) 3 f₂ := HJ 1
  have H₃ : MomentKJet.FirstDegreeBound r (V ^ 3) 5 f₃ := HJ 2
  have Hψ₂ : MomentKJet.FirstDegreeBound r ((1 + S) * V ^ 2) 3 ψ₂ := by
    convert H₂.add (H₁.square.small_scale hmabs) using 1
    dsimp only [S]
    ring
  have Hψ₃ : MomentKJet.FirstDegreeBound r ((1 + 3 * S + S ^ 2) * V ^ 3) 5 ψ₃ := by
    have Hprod : MomentKJet.FirstDegreeBound r (S * V ^ 3) 5
        (fun x => (f₁ x).mul (f₂ x)) := by
      convert H₁.mul H₂ using 1
      ring
    have Hmid := (Hprod.small_scale hmabs).scale 3
    have Hlast := H₁.cube.small_scale hm₂abs
    convert (H₃.add Hmid).add Hlast using 1
    · norm_num
      ring
    · funext x
      simp only [ψ₃, MomentKJet.add, MomentKJet.scale, MomentKJet.mul]
      congr 1 <;> ring
  intro i
  fin_cases i
  · change MomentKJet.FirstDegreeBound r (D * V ^ 1) 1 f₁
    rw [pow_one]
    apply H₁.mono _ le_rfl
    have hD : 1 ≤ D := by dsimp only [D]; nlinarith [sq_nonneg S]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD hV
  · change MomentKJet.FirstDegreeBound r (D * V ^ 2) 3 ψ₂
    exact Hψ₂.mono (mul_le_mul_of_nonneg_right
      (by dsimp only [D]; nlinarith [sq_nonneg S]) (sq_nonneg V)) le_rfl
  · exact Hψ₃

theorem epsilonBellCumulants_first_degree
    {r : ℕ} {m M δ T : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (R : Fin 3 → Vec3 → MomentKJet)
    (avg : (Vec3 → MomentKJet) → Vec3 → MomentKJet)
    (HJ : ∀ i : Fin 3, MomentKJet.FirstDegreeBound (r + 1)
      ((M * δ) ^ (i.val + 1)) (2 * (i.val + 1) - 1) (R i))
    (HA : ∀ B : ℝ, ∀ p : ℕ, p ≤ 5 → ∀ J : Vec3 → MomentKJet,
      MomentKJet.FirstDegreeBound (r + 1) B p J →
        MomentKJet.FirstDegreeBound r (T * B) p (avg J)) :
    ∀ i : Fin 3, MomentKJet.FirstDegreeBound r
      ((epsilonSpatialStepBudget (r + 2) T * M * δ) ^ (i.val + 1))
      (2 * (i.val + 1) - 1)
      (fun y => epsilonLogCumulantsKJet m
        (fun i => avg (fun x => epsilonBellTestsKJet m (fun i => R i x) i) y) i) := by
  let V := M * δ
  let S := (2 : ℝ) ^ (r + 2)
  let C := epsilonSpatialStepBudget (r + 2) T
  let f₁ := R 0
  let f₂ := R 1
  let f₃ := R 2
  let ψ₂ : Vec3 → MomentKJet := fun x => (f₂ x).add (((f₁ x).mul (f₁ x)).scale m)
  let ψ₃ : Vec3 → MomentKJet := fun x =>
    ((f₃ x).add (((f₁ x).mul (f₂ x)).scale (3 * m))).add
      ((((f₁ x).mul (f₁ x)).mul (f₁ x)).scale (m ^ 2))
  let A₁ := avg f₁
  let A₂ := avg ψ₂
  let A₃ := avg ψ₃
  have hR : 0 ≤ V := mul_nonneg hM hδ
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hSout : (2 : ℝ) ^ (r + 1) ≤ S := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmabs : |m| ≤ 1 := by rw [abs_of_pos hm.1]; exact hm.2
  have hmneg : |-m| ≤ 1 := by simpa only [abs_neg] using hmabs
  have hm₂abs : |m ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hmabs
  have H₁ : MomentKJet.FirstDegreeBound (r + 1) V 1 f₁ := by
    simpa only [Fin.val_zero, zero_add, pow_one] using HJ 0
  have H₂ : MomentKJet.FirstDegreeBound (r + 1) (V ^ 2) 3 f₂ := HJ 1
  have H₃ : MomentKJet.FirstDegreeBound (r + 1) (V ^ 3) 5 f₃ := HJ 2
  have Hψ₂ : MomentKJet.FirstDegreeBound (r + 1) ((1 + S) * V ^ 2) 3 ψ₂ := by
    convert H₂.add (H₁.square.small_scale hmabs) using 1
    dsimp only [S]
    ring
  have Hψ₃ : MomentKJet.FirstDegreeBound (r + 1) ((1 + 3 * S + S ^ 2) * V ^ 3) 5 ψ₃ := by
    have Hprod : MomentKJet.FirstDegreeBound (r + 1) (S * V ^ 3) 5
        (fun x => (f₁ x).mul (f₂ x)) := by
      convert H₁.mul H₂ using 1
      ring
    have Hmid := (Hprod.small_scale hmabs).scale 3
    have Hlast := H₁.cube.small_scale hm₂abs
    convert (H₃.add Hmid).add Hlast using 1
    · norm_num
      ring
    · funext x
      simp only [ψ₃, MomentKJet.add, MomentKJet.scale, MomentKJet.mul]
      congr 1 <;> ring
  have HA₁ : MomentKJet.FirstDegreeBound r (T * V) 1 A₁ := HA _ _ (by norm_num) f₁ H₁
  have HA₂ : MomentKJet.FirstDegreeBound r (T * ((1 + S) * V ^ 2)) 3 A₂ :=
    HA _ _ (by norm_num) ψ₂ Hψ₂
  have HA₃ : MomentKJet.FirstDegreeBound r (T * ((1 + 3 * S + S ^ 2) * V ^ 3)) 5 A₃ :=
    HA _ _ (by norm_num) ψ₃ Hψ₃
  have hC : 1 ≤ C := epsilonSpatialStepBudget_ge_one (r + 2) hT
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
  intro i
  fin_cases i
  · change MomentKJet.FirstDegreeBound r _ 1 A₁
    apply HA₁.mono _ le_rfl
    simpa only [zero_add, pow_one, C, V, mul_assoc] using mul_le_mul_of_nonneg_right hTC hR
  · change MomentKJet.FirstDegreeBound r _ 3
      (fun x => (A₂ x).add (((A₁ x).mul (A₁ x)).scale (-m)))
    have HB := HA₂.add ((HA₁.square_budget hSout).small_scale hmneg)
    apply HB.mono _ le_rfl
    convert mul_le_mul_of_nonneg_right hb₂ (sq_nonneg V) using 1 <;>
      dsimp only [C, V, S] <;> ring
  · change MomentKJet.FirstDegreeBound r _ 5
      (fun x => ((A₃ x).add (((A₁ x).mul (A₂ x)).scale (-3 * m))).add
        ((((A₁ x).mul (A₁ x)).mul (A₁ x)).scale (2 * m ^ 2)))
    have Hprod : MomentKJet.FirstDegreeBound r (S * T ^ 2 * (1 + S) * V ^ 3) 5
        (fun x => (A₁ x).mul (A₂ x)) := by
      convert HA₁.mul_budget HA₂ hSout using 1
      ring
    have Hmid := (Hprod.small_scale hmneg).scale 3
    have Hlast := ((HA₁.cube_budget hSout).small_scale hm₂abs).scale 2
    have HB := (HA₃.add Hmid).add Hlast
    have HB' : MomentKJet.FirstDegreeBound r
        ((T * (1 + 3 * S + S ^ 2) + 3 * S * T ^ 2 * (1 + S) +
          2 * S ^ 2 * T ^ 3) * V ^ 3) 5
        (fun x => ((A₃ x).add (((A₁ x).mul (A₂ x)).scale (-3 * m))).add
          ((((A₁ x).mul (A₁ x)).mul (A₁ x)).scale (2 * m ^ 2))) := by
      convert HB using 1
      · norm_num
        ring
      · funext x
        simp only [MomentKJet.add, MomentKJet.scale, MomentKJet.mul]
        congr 1 <;> ring
    apply HB'.mono _ le_rfl
    convert mul_le_mul_of_nonneg_right hb₃ (pow_nonneg hR 3) using 1
    dsimp only [C, V]
    ring

end SKBarriers2.Corner
