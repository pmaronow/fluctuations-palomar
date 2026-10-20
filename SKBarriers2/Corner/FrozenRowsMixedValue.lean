module

public import SKBarriers2.Corner.FrozenRowsMixed4
public import SKBarriers2.Corner.FrozenRowsInduction

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2
namespace WQ
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {r s p q : ℕ} {B C : ℝ} {f g : E → F}

theorem mono (hf : WQ r B p f) (hBC : B ≤ C) (hpq : p ≤ q) : WQ r C q f := by
  refine ⟨hf.nonneg.trans hBC, hf.smooth, ?_⟩
  intro j hjpos hj x
  exact (hf.bound j hjpos hj x).trans (mul_le_mul hBC
    (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hpq) (by positivity)
    (hf.nonneg.trans hBC))

theorem add (hf : WQ r B p f) (hg : WQ r C p g) :
    WQ r (B + C) p (fun x => f x + g x) := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, hf.smooth.add hg.smooth, ?_⟩
  intro j hjpos hj x
  change ‖iteratedFDeriv ℝ j (f + g) x‖ ≤ _
  rw [iteratedFDeriv_add (hf.smooth.of_le (by exact_mod_cast hj))
    (hg.smooth.of_le (by exact_mod_cast hj))]
  exact (norm_add_le _ _).trans ((add_le_add (hf.bound j hjpos hj x) (hg.bound j hjpos hj x)).trans_eq
    (by ring))

theorem const_smul (hf : WQ r B p f) (c : ℝ) :
    WQ r (|c| * B) p (fun x => c • f x) := by
  refine ⟨mul_nonneg (abs_nonneg c) hf.nonneg, hf.smooth.const_smul c, ?_⟩
  intro j hjpos hj x
  rw [iteratedFDeriv_const_smul_apply' ((hf.smooth.of_le (by exact_mod_cast hj)).contDiffAt),
    norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf.bound j hjpos hj x) (abs_nonneg c)).trans_eq (by ring)

theorem sub (hf : WQ r B p f) (hg : WQ r C p g) :
    WQ r (B + C) p (fun x => f x - g x) := by
  simpa only [abs_neg, abs_one, one_mul, neg_one_smul, sub_eq_add_neg] using
    hf.add (hg.const_smul (-1))

theorem translate (hf : WQ r B p f) (b : E) :
    WQ r (B * (1 + ‖b‖) ^ p) p (fun x => f (x + b)) := by
  refine ⟨by positivity [hf.nonneg], hf.smooth.comp (contDiff_id.add contDiff_const), ?_⟩
  intro j hjpos hj x
  rw [iteratedFDeriv_comp_add_right]
  calc
    _ ≤ B * (1 + ‖x + b‖) ^ p := hf.bound j hjpos hj _
    _ ≤ B * ((1 + ‖b‖) * (1 + ‖x‖)) ^ p := by
      apply mul_le_mul_of_nonneg_left _ hf.nonneg
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [norm_add_le x b, mul_nonneg (norm_nonneg b) (norm_nonneg x)]
    _ = _ := by rw [mul_pow]; ring

theorem comp_affine (hf : WQ r B p f) (A : E →L[ℝ] E) (b : E) :
    WQ r (B * (1 + ‖A‖ + ‖b‖) ^ p * max 1 ‖A‖ ^ r) p
      (fun x => f (A x + b)) := by
  have hB := hf.nonneg
  refine ⟨by positivity, hf.smooth.comp (A.contDiff.add contDiff_const), ?_⟩
  intro j hjpos hj x
  change ‖iteratedFDeriv ℝ j ((fun y => f (y + b)) ∘ A) x‖ ≤ _
  rw [A.iteratedFDeriv_comp_right (hf.translate b).smooth x (by exact_mod_cast hj)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => f (y + b)) (A x)‖ * ∏ _ : Fin j, ‖A‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j f (A x + b)‖ * ‖A‖ ^ j := by
      rw [iteratedFDeriv_comp_add_right]; simp
    _ ≤ (B * (1 + ‖A x + b‖) ^ p) * max 1 ‖A‖ ^ r := by
      apply mul_le_mul (hf.bound j hjpos hj _) _ (by positivity) (by positivity)
      exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) hj)
    _ ≤ (B * ((1 + ‖A‖ + ‖b‖) * (1 + ‖x‖)) ^ p) * max 1 ‖A‖ ^ r := by
      gcongr
      exact one_add_norm_affine_le A b x
    _ = _ := by rw [mul_pow]; ring

end WQ

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem WQ.spatialContract {r p : ℕ} {B ρ : ℝ} {f : E → ℝ}
    (hf : WQ r B p f) (hρ : |ρ| ≤ 1) :
    WQ r B p (spatialRescale ρ 0 f) := by
  refine ⟨hf.nonneg, hf.smooth.comp ((contDiff_id.const_smul ρ).add contDiff_const), ?_⟩
  intro j hjpos hj y
  rw [norm_iteratedFDeriv_spatialRescale hf.smooth hj]
  have hw : (1 + ‖ρ • y + (0 : E)‖) ^ p ≤ (1 + ‖y‖) ^ p := by
    rw [add_zero, norm_smul, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg y) hρ
  exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) hρ)
    ((hf.bound j hjpos hj _).trans (mul_le_mul_of_nonneg_left hw hf.nonneg))
    (norm_nonneg _) (by positivity)).trans_eq (one_mul _)

theorem WQ.dilate {r p : ℕ} {B ρ : ℝ} {f : E → ℝ}
    (hf : WQ r B p f) (hρ : 1 ≤ ρ) :
    WQ r (B * ρ ^ (p + r)) p (spatialRescale ρ 0 f) := by
  have hρ₀ : 0 ≤ ρ := by linarith
  refine ⟨by positivity [hf.nonneg],
    hf.smooth.comp ((contDiff_id.const_smul ρ).add contDiff_const), ?_⟩
  intro j hjpos hj y
  rw [norm_iteratedFDeriv_spatialRescale hf.smooth hj, abs_of_nonneg hρ₀]
  have hw : (1 + ‖ρ • y + (0 : E)‖) ^ p ≤ ρ ^ p * (1 + ‖y‖) ^ p := by
    rw [add_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ₀, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  calc
    _ ≤ ρ ^ r * (B * (ρ ^ p * (1 + ‖y‖) ^ p)) :=
      mul_le_mul (pow_le_pow_right₀ hρ hj)
        ((hf.bound j hjpos hj _).trans (mul_le_mul_of_nonneg_left hw hf.nonneg))
        (norm_nonneg _) (pow_nonneg hρ₀ _)
    _ = _ := by rw [pow_add]; ring

namespace StepCalculus
local notation "X" => (Fin 3 → ℝ)
theorem wQ_tiltedAverage_boundedNoise {r p : ℕ} {B C m K : ℝ} {f g : X → ℝ}
    (hf : QPotential (r + 1) B f) (hg : WQ (r + 1) C p g)
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : X) (hv : ‖v‖ ≤ K) :
    WQ r ((1 + noiseAverageCoefficient r (p + 1) (B * K ^ (r + 1))) *
      (C * K ^ (p + (r + 1)))) p (tiltedAverage m v f g) := by
  have hK₀ : 0 < K := by linarith
  have hKi : |K⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hK₀)]
    exact (inv_le_one₀ hK₀).mpr hK
  have hv' : ‖K⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK₀)]
    exact (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hK₀.le)).trans_eq
      (inv_mul_cancel₀ hK₀.ne')
  have H := (wQ_tiltedAverage (hf.dilate hK) (hg.dilate hK) hm (K⁻¹ • v) hv').spatialContract hKi
  have he : spatialRescale K⁻¹ 0
      (tiltedAverage m (K⁻¹ • v) (spatialRescale K 0 f) (spatialRescale K 0 g)) =
      tiltedAverage m v f g := by
    rw [← spatialRescale_tiltedAverage]
    simp only [smul_smul, mul_inv_cancel₀ hK₀.ne', one_smul]
    funext x
    simp only [spatialRescale, add_zero, smul_smul, mul_inv_cancel₀ hK₀.ne', one_smul]
  rw [he] at H
  convert H using 1
  ring

theorem wQ_affineAverage_boundedNoise {r p : ℕ} {B C m K : ℝ} {f g : X → ℝ}
    (hf : QPotential (r + 1) B f) (hg : WQ (r + 1) C p g)
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : X) (hv : ‖v‖ ≤ K)
    (A : X →L[ℝ] X) (b : X) :
    WQ r (((1 + noiseAverageCoefficient r (p + 1) (B * K ^ (r + 1))) *
      (C * K ^ (p + (r + 1)))) * (1 + ‖A‖ + ‖b‖) ^ p * max 1 ‖A‖ ^ r) p
      (fun y => tiltedAverage m v f g (A y + b)) := by
  exact (wQ_tiltedAverage_boundedNoise hf hg hm hK v hv).comp_affine A b

end StepCalculus

structure DegreeJets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (B : ℝ) (p : ℕ) (f : E → ℝ) : Prop where
  value : WJets r B (p + 1) f
  positive : WQ r B p f

namespace DegreeJets
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {r s p q : ℕ} {B C : ℝ} {f g : E → ℝ}

theorem mono (hf : DegreeJets r B p f) (hBC : B ≤ C) (hpq : p ≤ q) :
    DegreeJets r C q f :=
  ⟨hf.value.mono hBC (by omega), hf.positive.mono hBC hpq⟩

theorem of_le (hf : DegreeJets r B p f) (hs : s ≤ r) : DegreeJets s B p f :=
  ⟨hf.value.of_le hs, hf.positive.of_le hs⟩

theorem add (hf : DegreeJets r B p f) (hg : DegreeJets r C p g) :
    DegreeJets r (B + C) p (fun x => f x + g x) :=
  ⟨hf.value.add hg.value, hf.positive.add hg.positive⟩

theorem sub (hf : DegreeJets r B p f) (hg : DegreeJets r C p g) :
    DegreeJets r (B + C) p (fun x => f x - g x) :=
  ⟨hf.value.sub hg.value, hf.positive.sub hg.positive⟩

theorem const_mul (hf : DegreeJets r B p f) (a : ℝ) :
    DegreeJets r (|a| * B) p (fun x => a * f x) := by
  exact ⟨by simpa only [smul_eq_mul] using hf.value.const_smul a,
    by simpa only [smul_eq_mul] using hf.positive.const_smul a⟩

theorem small_mul (hf : DegreeJets r B p f) {a : ℝ} (ha : |a| ≤ 1) :
    DegreeJets r B p (fun x => a * f x) :=
  (hf.const_mul a).mono (mul_le_of_le_one_left hf.value.nonneg ha) le_rfl

theorem mul (hf : DegreeJets r B p f) (hg : DegreeJets r C q g) :
    DegreeJets r ((2 : ℝ) ^ r * B * C) (p + q + 1) (fun x => f x * g x) := by
  refine ⟨?_, hf.positive.mul_weighted_value hg.positive
    (fun x => by simpa only [Real.norm_eq_abs] using hf.value.norm_le x)
    (fun x => by simpa only [Real.norm_eq_abs] using hg.value.norm_le x)⟩
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf.value.mul hg.value

theorem square (hf : DegreeJets r B p f) :
    DegreeJets r ((2 : ℝ) ^ r * B ^ 2) (p + p + 1) (fun x => f x ^ 2) := by
  convert hf.mul hf using 1 <;> first | rfl | (funext x; ring) | ring

theorem cube (hf : DegreeJets r B p f) :
    DegreeJets r (((2 : ℝ) ^ r) ^ 2 * B ^ 3) (p + p + 1 + p + 1)
      (fun x => f x ^ 3) := by
  convert (hf.mul hf).mul hf using 1 <;> first | rfl | (funext x; ring) | ring

theorem mul_budget (hf : DegreeJets r B p f) (hg : DegreeJets r C q g)
    {S : ℝ} (hS : (2 : ℝ) ^ r ≤ S) :
    DegreeJets r (S * B * C) (p + q + 1) (fun x => f x * g x) :=
  (hf.mul hg).mono (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hS hf.value.nonneg) hg.value.nonneg) le_rfl

theorem square_budget (hf : DegreeJets r B p f) {S : ℝ} (hS : (2 : ℝ) ^ r ≤ S) :
    DegreeJets r (S * B ^ 2) (p + p + 1) (fun x => f x ^ 2) := by
  convert hf.mul_budget hf hS using 1 <;> first | rfl | (funext x; ring) | ring

theorem cube_budget (hf : DegreeJets r B p f) {S : ℝ} (hS : (2 : ℝ) ^ r ≤ S) :
    DegreeJets r (S ^ 2 * B ^ 3) (p + p + 1 + p + 1) (fun x => f x ^ 3) := by
  convert (hf.mul_budget hf hS).mul_budget hf hS using 1 <;>
    first | rfl | (funext x; ring) | ring

end DegreeJets

end SKBarriers2

namespace SKBarriers2.Corner

theorem epsilonStep_scaled_degree_jets
    {F : ℝ → Vec3 → ℝ} {U : Set ℝ} {m ρ M δ T ε : ℝ} {c v : Vec3} {r : ℕ}
    (H : EpsilonJetControl F U) (hU : IsOpen U) (hε : ε ∈ U)
    (P : QuadraticTerminal) (hm : m ∈ Ioc (0 : ℝ) 1)
    (hP : 1 / 2 ≤ P.precision m v) (hmajor : ∀ e ∈ U, ∀ x, F e x ≤ P.value x)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (HJ : ∀ i : Fin 3, DegreeJets (r + 1) ((M * δ) ^ (i.val + 1)) (2 * (i.val + 1) - 1)
      (spatialRescale ρ c (epsilonSpatialJet F (i.val + 1) ε)))
    (HA : ∀ B : ℝ, ∀ p : ℕ, p ≤ 5 → ∀ ψ : Vec3 → ℝ,
      DegreeJets (r + 1) B p (spatialRescale ρ c ψ) →
        DegreeJets r (T * B) p (spatialRescale ρ c (epsilonMoment m v F (fun _ => ψ) ε))) :
    ∀ i : Fin 3,
      DegreeJets r ((epsilonSpatialStepBudget (r + 1) T * M * δ) ^ (i.val + 1)) (2 * (i.val + 1) - 1)
        (spatialRescale ρ c
          (epsilonSpatialJet (fun e => vectorStep m v (F e)) (i.val + 1) ε)) := by
  let R := M * δ
  let S := (2 : ℝ) ^ (r + 1)
  let C := epsilonSpatialStepBudget (r + 1) T
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
  have hSout : (2 : ℝ) ^ r ≤ S := pow_le_pow_right₀ (by norm_num) (Nat.le_succ r)
  have hmabs : |m| ≤ 1 := by rw [abs_of_pos hm.1]; exact hm.2
  have hm₂abs : |m ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hmabs
  have H₁ : DegreeJets (r + 1) R 1 (spatialRescale ρ c f₁) := by
    simpa only [Fin.val_zero, zero_add, pow_one] using HJ 0
  have H₂ : DegreeJets (r + 1) (R ^ 2) 3 (spatialRescale ρ c f₂) := HJ 1
  have H₃ : DegreeJets (r + 1) (R ^ 3) 5 (spatialRescale ρ c f₃) := HJ 2
  have Hψ₂ : DegreeJets (r + 1) ((1 + S) * R ^ 2) 3 (spatialRescale ρ c ψ₂) := by
    convert H₂.add (DegreeJets.small_mul (DegreeJets.square H₁) hmabs) using 1
    · dsimp only [S]
      ring
    · rfl
  have Hψ₃ : DegreeJets (r + 1) ((1 + 3 * S + S ^ 2) * R ^ 3) 5 (spatialRescale ρ c ψ₃) := by
    have Hprod : DegreeJets (r + 1) (S * R ^ 3) 5
        (fun x => spatialRescale ρ c f₁ x * spatialRescale ρ c f₂ x) := by
      convert H₁.mul H₂ using 1
      ring
    have Hmid := DegreeJets.const_mul (a := (3 : ℝ)) (DegreeJets.small_mul Hprod hmabs)
    have Hlast := DegreeJets.small_mul (DegreeJets.cube H₁) hm₂abs
    convert (H₃.add Hmid).add Hlast using 1 <;>
      first | rfl | (funext x; dsimp only [spatialRescale, ψ₃]; ring) |
        (norm_num; ring)
  have HA₁ : DegreeJets r (T * R) 1 (spatialRescale ρ c A₁) := HA _ _ (by norm_num) f₁ H₁
  have HA₂ : DegreeJets r (T * ((1 + S) * R ^ 2)) 3 (spatialRescale ρ c A₂) :=
    HA _ _ (by norm_num) ψ₂ Hψ₂
  have HA₃ : DegreeJets r (T * ((1 + 3 * S + S ^ 2) * R ^ 3)) 5 (spatialRescale ρ c A₃) :=
    HA _ _ (by norm_num) ψ₃ Hψ₃
  have hC : 1 ≤ C := epsilonSpatialStepBudget_ge_one (r + 1) hT
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
    have HB := HA₂.sub (DegreeJets.small_mul (DegreeJets.square_budget HA₁ hSout) hmabs)
    apply HB.mono _ le_rfl
    convert mul_le_mul_of_nonneg_right hb₂ (sq_nonneg R) using 1 <;>
      dsimp only [C, R, S] <;> ring
  · rw [he₃]
    have Hprod : DegreeJets r (S * T ^ 2 * (1 + S) * R ^ 3) 5
        (fun x => spatialRescale ρ c A₁ x * spatialRescale ρ c A₂ x) := by
      convert HA₁.mul_budget HA₂ hSout using 1
      ring
    have Hmid := DegreeJets.const_mul (a := (3 : ℝ)) (DegreeJets.small_mul Hprod hmabs)
    have Hlast := DegreeJets.const_mul (a := (2 : ℝ)) (DegreeJets.small_mul (DegreeJets.cube_budget HA₁ hSout) hm₂abs)
    have HB := (HA₃.sub Hmid).add Hlast
    have HB' : DegreeJets r
        ((T * (1 + 3 * S + S ^ 2) + 3 * S * T ^ 2 * (1 + S) +
          2 * S ^ 2 * T ^ 3) * R ^ 3) 5
        (spatialRescale ρ c (fun x => A₃ x - 3 * m * A₁ x * A₂ x +
          2 * m ^ 2 * A₁ x ^ 3)) := by
      convert HB using 1
      all_goals try norm_num
      all_goals try (apply funext; intro x)
      all_goals try dsimp only [spatialRescale]
      all_goals ring
    apply HB'.mono _ le_rfl
    convert mul_le_mul_of_nonneg_right hb₃ (pow_nonneg hR 3) using 1
    dsimp only [C, R]
    ring

theorem scalarData_frozen_scaled_moment_wQ {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ T : ℝ, 0 < h₀ ∧ 1 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∀ M : ℝ, ∀ p : ℕ, p ≤ 5 → ∀ ψ : Vec3 → ℝ,
        WQ (d + 1) M p (spatialRescale (Real.sqrt h) (fun _ => z) ψ) →
        WQ d (T * M) p (spatialRescale (Real.sqrt h) (fun _ => z)
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
  let coeff : Fin 6 → ℝ := fun p =>
    (1 + StepCalculus.noiseAverageCoefficient d (p.val + 1) (C * L ^ (d + 1))) *
      L ^ (p.val + (d + 1)) * A ^ p.val * (2 : ℝ) ^ d
  let T := 1 + ∑ p : Fin 6, |coeff p|
  have hB : 0 < B := by dsimp only [B]; positivity [scalarTerminalJetBound_nonneg D 3]
  have hG : 0 < G := by dsimp only [G]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hS : 0 < S := by dsimp only [S]; positivity
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hT : 1 ≤ T := by
    have H := Finset.sum_nonneg (fun p (_ : p ∈ (Finset.univ : Finset (Fin 6))) => abs_nonneg (coeff p))
    dsimp only [T]; linarith
  have hcoeff (p : ℕ) (hp : p ≤ 5) :
      (1 + StepCalculus.noiseAverageCoefficient d (p + 1) (C * L ^ (d + 1))) *
        L ^ (p + (d + 1)) * A ^ p * (2 : ℝ) ^ d ≤ T := by
    let i : Fin 6 := ⟨p, by omega⟩
    have H := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 6))) => abs_nonneg (coeff j)) (Finset.mem_univ i)
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
  have havg := StepCalculus.wQ_tiltedAverage_boundedNoise hRscaled hψ hm hL _ hw
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
    _ ≤ ((1 + StepCalculus.noiseAverageCoefficient d (p + 1) (C * L ^ (d + 1))) * (M * L ^ (p + (d + 1)))) *
        A ^ p * (2 : ℝ) ^ d := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ havg.nonneg
        apply pow_le_pow_left₀ (by positivity)
        dsimp only [A]
        linarith
      · exact pow_le_pow_left₀ (by positivity) (max_le (by norm_num) hAlin) d
      · positivity
      · positivity [havg.nonneg]
    _ = ((1 + StepCalculus.noiseAverageCoefficient d (p + 1) (C * L ^ (d + 1))) *
        L ^ (p + (d + 1)) * A ^ p * (2 : ℝ) ^ d) * M := by ring
    _ ≤ T * M := mul_le_mul_of_nonneg_right (hcoeff p hp) hψ.nonneg

theorem scalarData_frozen_scaled_moment_degreeJets {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ T : ℝ, 0 < h₀ ∧ 1 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∀ M : ℝ, ∀ p : ℕ, p ≤ 5 → ∀ ψ : Vec3 → ℝ,
        DegreeJets (d + 1) M p (spatialRescale (Real.sqrt h) (fun _ => z) ψ) →
        DegreeJets d (T * M) p (spatialRescale (Real.sqrt h) (fun _ => z)
          (epsilonMoment w.1 w.2 (fun e => epsilonChain t
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e) (fun _ => ψ) ε)) := by
  rcases scalarData_frozen_scaled_moment_wJets D hl hu (d + 1) with
    ⟨hV, TV, hhV, hTV, HV⟩
  rcases scalarData_frozen_scaled_moment_wQ D hl hu d with
    ⟨hQ, TQ, hhQ, hTQ, HQ⟩
  refine ⟨min hV hQ, TV + TQ, lt_min hhV hhQ, by linarith, ?_⟩
  intro r hr h hh hsmall k hk z ε hε w t ht M p hp ψ hψ
  have hMV : TV * M ≤ (TV + TQ) * M := by
    nlinarith [hψ.value.nonneg]
  have hMQ : TQ * M ≤ (TV + TQ) * M := by
    nlinarith [hψ.value.nonneg]
  refine ⟨?_, ?_⟩
  · exact ((HV r hr h hh (hsmall.trans (min_le_left _ _)) k hk z ε hε w t ht
      M (p + 1) (by omega) ψ hψ.value).of_le (Nat.le_succ d)).mono hMV le_rfl
  · exact (HQ r hr h hh (hsmall.trans (min_le_right _ _)) k hk z ε hε w t ht
      M p hp ψ hψ.positive).mono hMQ le_rfl

theorem scalarData_frozen_scaled_moment_degreeJets_uniform {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ T : ℝ, 0 < h₀ ∧ 1 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∀ j : ℕ, j ≤ d → ∀ M : ℝ, ∀ p : ℕ, p ≤ 5 → ∀ ψ : Vec3 → ℝ,
        DegreeJets (j + 1) M p (spatialRescale (Real.sqrt h) (fun _ => z) ψ) →
        DegreeJets j (T * M) p (spatialRescale (Real.sqrt h) (fun _ => z)
          (epsilonMoment w.1 w.2 (fun e => epsilonChain t
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e) (fun _ => ψ) ε)) := by
  classical
  have hall (j : Fin (d + 1)) := scalarData_frozen_scaled_moment_degreeJets D hl hu j.val
  choose hA TA hhA hTA HA using hall
  let h₀ := Finset.univ.inf' Finset.univ_nonempty hA
  let T := 1 + ∑ j : Fin (d + 1), |TA j|
  have hh₀ : 0 < h₀ := (Finset.lt_inf'_iff _).mpr (fun j _ => hhA j)
  have hT : 1 ≤ T := by
    dsimp only [T]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (d + 1)))) =>
      abs_nonneg (TA j))]
  refine ⟨h₀, T, hh₀, hT, ?_⟩
  intro r hr h hh hsmall k hk z ε hε w t ht j hj M p hp ψ hψ
  let i : Fin (d + 1) := ⟨j, by omega⟩
  have hhA' : h ≤ hA i := hsmall.trans (Finset.inf'_le hA (Finset.mem_univ i))
  have hTi : TA i ≤ T := by
    have H := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (d + 1)))) => abs_nonneg (TA j))
      (Finset.mem_univ i)
    exact (le_abs_self (TA i)).trans (H.trans (by dsimp only [T]; linarith))
  exact (HA i r hr h hh hhA' k hk z ε hε w t ht M p hp ψ hψ).mono
    (mul_le_mul_of_nonneg_right hTi hψ.value.nonneg) le_rfl

private theorem coarse_nil_epsilon_first (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    deriv (fun e => epsilonChain [] Q K e x) = fun _ => K x := by
  funext e
  simpa only [epsilonChain, vectorIncrementChain, id_eq, one_mul] using
    (((hasDerivAt_id e).mul_const (K x)).const_add (Q.value x)).deriv

private theorem coarse_nil_epsilon_second (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 2 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext e
  rw [iteratedDeriv_succ, iteratedDeriv_one, coarse_nil_epsilon_first]
  exact deriv_const e (K x)

private theorem coarse_nil_epsilon_third (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 3 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext e
  rw [iteratedDeriv_succ, coarse_nil_epsilon_second]
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

private theorem degreeJets_zero (d p : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    DegreeJets d B p (fun _ : Vec3 => (0 : ℝ)) :=
  ⟨wJets_zero d (p + 1) hB, (wJets_zero d p hB).potential⟩

private theorem epsilonSpatialStepBudget_mono_order {r s : ℕ} (hrs : r ≤ s)
    {T : ℝ} (hT : 0 ≤ T) : epsilonSpatialStepBudget r T ≤ epsilonSpatialStepBudget s T := by
  have hpow : (2 : ℝ) ^ r ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hrs
  dsimp only [epsilonSpatialStepBudget]
  gcongr

theorem scalarData_terminalResidual_coarse_degreeJets {β s h ρ : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (d : ℕ) (hd : 1 ≤ d) (z : ℝ) :
    DegreeJets d (6 * scalarTerminalJetBound D (max 2 d) * ρ ^ 2) 1
      (spatialRescale ρ (fun _ => z) (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z)) := by
  let α := cdf (D.μ : Measure ℝ)
  let f := spatialRescale ρ (fun _ => z) (terminalResidual β α s h z)
  have H := scalarData_scaledTerminalResidual_wQ_global D ht hρ d z
  have heq : f = fun y => ρ ^ 3 * scaledTerminalResidual β α s h z ρ y := by
    funext y
    dsimp only [f, spatialRescale, scaledTerminalResidual]
    field_simp [hρ.1.ne']
  have HQ : WQ d (6 * scalarTerminalJetBound D (max 2 d) * ρ ^ 2) 1 f := by
    rw [heq]
    have HS := H.const_smul (ρ ^ 3)
    simp only [smul_eq_mul] at HS
    convert HS using 1
    rw [abs_of_pos (pow_pos hρ.1 _)]
    field_simp [hρ.1.ne']
  refine ⟨?_, HQ⟩
  have Hcenter := HQ.centered_wJets hd
  have H0 : f 0 = 0 := by
    simp [f, spatialRescale, terminalResidual_eq_quadraticTaylorTails,
      quadraticTaylorTail, scalarTaylorPolynomial, Finset.sum_range_succ]
  simpa only [H0, sub_zero] using Hcenter

theorem scalarData_frozen_coarse_scaled_epsilon_jets {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ t, t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ i : Fin 3,
        DegreeJets d ((M * h) ^ (i.val + 1)) (2 * (i.val + 1) - 1)
          (spatialRescale (Real.sqrt h) (fun _ => z) (epsilonSpatialJet
            (fun e => epsilonChain t
              (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
              (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e)
            (i.val + 1) ε)) := by
  rcases scalarData_frozen_suffix_joint_epsilon_jets D hl hu with ⟨hJ, hhJ, _, HJ⟩
  let d₀ := d + 12
  rcases scalarData_frozen_scaled_moment_degreeJets_uniform D hl hu d₀ with ⟨hA, T, hhA, hT, HA⟩
  let M₀ := 6 * scalarTerminalJetBound D (max 2 d₀) + 1
  let C := epsilonSpatialStepBudget (d₀ + 1) T
  let M := C ^ 12 * M₀
  have hM₀ : 1 ≤ M₀ := by dsimp only [M₀]; linarith [scalarTerminalJetBound_nonneg D (max 2 d₀)]
  have hC : 1 ≤ C := epsilonSpatialStepBudget_ge_one (d₀ + 1) (by linarith)
  have hC₀ : 0 ≤ C := by linarith
  have hM₀₀ : 0 ≤ M₀ := by linarith
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
  let δ := ρ ^ 2
  have hρ : ρ ∈ Ioc (0 : ℝ) 1 := ⟨Real.sqrt_pos.mpr hh, Real.sqrt_le_one.mpr hh₁⟩
  have hδ : 0 ≤ δ := pow_nonneg hρ.1.le _
  have heδ : δ = h := Real.sq_sqrt hh.le
  have HK : DegreeJets d₀ (M₀ * δ) 1 (spatialRescale ρ c K) := by
    have H := scalarData_terminalResidual_coarse_degreeJets D htime hρ d₀ (by dsimp only [d₀]; omega) z
    apply H.mono _ le_rfl
    change (6 * scalarTerminalJetBound D (max 2 d₀)) * δ ≤ M₀ * δ
    apply mul_le_mul_of_nonneg_right _ hδ
    dsimp only [M₀]
    linarith
  have HJ' := HJ r hr h hh hhJ' k hk z
  have hm := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hε' : ε ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hnil₁ : epsilonSpatialJet (fun e => epsilonChain [] Q K e) 1 ε = K := by
    funext x
    simpa only [epsilonSpatialJet, iteratedDeriv_one] using congrFun (coarse_nil_epsilon_first Q K x) ε
  have hnil₂ : epsilonSpatialJet (fun e => epsilonChain [] Q K e) 2 ε = fun _ => 0 := by
    funext x
    exact congrFun (coarse_nil_epsilon_second Q K x) ε
  have hnil₃ : epsilonSpatialJet (fun e => epsilonChain [] Q K e) 3 ε = fun _ => 0 := by
    funext x
    exact congrFun (coarse_nil_epsilon_third Q K x) ε
  have Hbound : ∀ j, j <:+ full → ∀ i : Fin 3,
      DegreeJets (d₀ - j.length) ((C ^ j.length * M₀ * δ) ^ (i.val + 1)) (2 * (i.val + 1) - 1)
        (spatialRescale ρ c (epsilonSpatialJet (fun e => epsilonChain j Q K e) (i.val + 1) ε)) := by
    intro j
    induction j with
    | nil =>
      intro _ i
      fin_cases i
      · simpa only [List.length_nil, Nat.sub_zero, pow_zero, one_mul, Fin.val_zero, zero_add, pow_one,
          hnil₁] using HK
      · change DegreeJets d₀ ((C ^ [].length * M₀ * δ) ^ 2) 3
          (spatialRescale ρ c (epsilonSpatialJet (fun e => epsilonChain [] Q K e) 2 ε))
        rw [hnil₂]
        exact degreeJets_zero d₀ 3 (by positivity : 0 ≤ (C ^ [].length * M₀ * δ) ^ 2)
      · change DegreeJets d₀ ((C ^ [].length * M₀ * δ) ^ 3) 5
          (spatialRescale ρ c (epsilonSpatialJet (fun e => epsilonChain [] Q K e) 3 ε))
        rw [hnil₃]
        exact degreeJets_zero d₀ 5 (by positivity : 0 ≤ (C ^ [].length * M₀ * δ) ^ 3)
    | cons w j ih =>
      intro hj i
      have hj' : j <:+ full := (List.suffix_cons w j).trans hj
      rcases HJ'.2 w j hj with ⟨P, hP, hmajor⟩
      have hlenj : (w :: j).length ≤ 12 := by
        simpa only [full, frozenSchedule_length] using hj.length_le
      let q := d₀ - (w :: j).length
      have hq : q + 1 = d₀ - j.length := by dsimp only [q, d₀]; simp only [List.length_cons] at *; omega
      have Hinput : ∀ i : Fin 3, DegreeJets (q + 1)
          ((C ^ j.length * M₀ * δ) ^ (i.val + 1)) (2 * (i.val + 1) - 1)
          (spatialRescale ρ c (epsilonSpatialJet (fun e => epsilonChain j Q K e) (i.val + 1) ε)) := by
        rw [hq]
        exact ih hj'
      have Hstep := epsilonStep_scaled_degree_jets (HJ'.1 j hj') isOpen_Ioo hε' P
        (hm w (hj.subset List.mem_cons_self)) hP hmajor
        (by positivity : 0 ≤ C ^ j.length * M₀) hδ (by linarith : 0 ≤ T) Hinput
        (fun B p hp ψ hψ => HA r hr h hh hhA' k hk z ε hε w j hj
          q (by dsimp only [q]; omega) B p hp ψ hψ) i
      have hbudget : epsilonSpatialStepBudget (q + 1) T ≤ C :=
        epsilonSpatialStepBudget_mono_order (by dsimp only [q]; omega) (by linarith)
      have hbudget₀ : 0 ≤ epsilonSpatialStepBudget (q+1) T :=
        (by norm_num : (0 : ℝ) ≤ 1).trans (epsilonSpatialStepBudget_ge_one _ (by linarith))
      have Hstep' := Hstep.mono
        (pow_le_pow_left₀ (by positivity :
          0 ≤ epsilonSpatialStepBudget (q+1) T * (C ^ j.length * M₀) * δ)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hbudget (by positivity : 0 ≤ C ^ j.length * M₀)) hδ)
          (i.val+1)) le_rfl
      have heq : C ^ (w :: j).length * M₀ = C * (C ^ j.length * M₀) := by
        rw [List.length_cons, pow_succ]
        ring
      rw [heq]
      exact Hstep'
  have hlen : t.length ≤ 12 := by simpa only [full, frozenSchedule_length] using ht.length_le
  have hcoef : (M*h)^(i.val+1) = (M*δ)^(i.val+1) := by rw [heδ]
  rw [hcoef]
  apply ((Hbound t ht i).of_le (by dsimp only [d₀]; omega)).mono _ le_rfl
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hlen) (by linarith)) hδ

theorem scalarData_frozen_coarse_normalized_epsilon_jets {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (d : ℕ) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ t, t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ i : Fin 3,
        DegreeJets d ((M * (Real.sqrt h)⁻¹) ^ (i.val + 1)) (2 * (i.val + 1) - 1)
          (fun y => iteratedDeriv (i.val + 1) (fun e => normalizedVariationChain t
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z).value
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (Real.sqrt h) (fun _ => z) e y) ((Real.sqrt h) ^ 3 * ε)) := by
  rcases scalarData_frozen_coarse_scaled_epsilon_jets D hl hu d with ⟨h₀, M, hh₀, hM, H⟩
  refine ⟨h₀, M, hh₀, hM, ?_⟩
  intro r hr h hh hhsmall k hk z t ht ε hε i
  have HB := H r hr h hh hhsmall k hk z t ht ε hε i
  let ρ := Real.sqrt h
  let δ := ρ ^ 3
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hδ : 0 < δ := pow_pos hρ _
  have heq : spatialRescale ρ (fun _ => z) (epsilonSpatialJet (fun e => epsilonChain t
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e) (i.val + 1) ε) =
      fun y => δ ^ (i.val + 1) * iteratedDeriv (i.val + 1) (fun e => normalizedVariationChain t
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z).value
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        ρ (fun _ => z) e y) (δ * ε) := by
    funext y
    exact iteratedDeriv_spatialRescale_variationChain hρ.ne' t _ _ _ _ _ _
  have heh : h = ρ ^ 2 := (Real.sq_sqrt hh.le).symm
  have hcoef : (M * h) ^ (i.val + 1) = (M * ρ ^ 2) ^ (i.val + 1) := by rw [heh]
  rw [hcoef, heq] at HB
  have Hscaled := DegreeJets.const_mul (a := (δ ^ (i.val + 1))⁻¹) HB
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
  rw [abs_of_pos (inv_pos.mpr (pow_pos hδ _)), ← inv_pow, ← mul_pow]
  congr 1
  dsimp only [δ, ρ]
  field_simp [hρ.ne']

end SKBarriers2.Corner
