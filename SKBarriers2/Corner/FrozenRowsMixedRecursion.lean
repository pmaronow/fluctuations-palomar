module

public import SKBarriers2.Corner.FrozenRowsMixed18

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def normalizedMovingBellTest (ρ m : ℝ) (F : ℝ → ℝ → Vec3 → ℝ)
    (i : Fin 3) (k ε : ℝ) (y : Vec3) : ℝ :=
  (epsilonBellTestsKJet m (fun j => MomentKJet.const
    (((ρ ^ 3) ^ (j.val + 1))⁻¹ * epsilonSpatialJet (F k) (j.val + 1) ε y)) i).value

def normalizedMovingBellAverage (ρ m : ℝ) (v x : ℝ → Vec3)
    (F : ℝ → ℝ → Vec3 → ℝ) (ε : ℝ) (i : Fin 3) (k : ℝ) : ℝ :=
  epsilonMoment m (v k) (F k) (normalizedMovingBellTest ρ m F i k) ε (x k)

def normalizedMovingBellKJet (ρ m : ℝ) (v x : ℝ → Vec3)
    (F : ℝ → ℝ → Vec3 → ℝ) (ε : ℝ) (i : Fin 3) (k : ℝ) : MomentKJet :=
  let A := normalizedMovingBellAverage ρ m v x F ε i
  ⟨A k, deriv A k, deriv (deriv A) k⟩

theorem normalizedMovingBellTest_eq_scale (ρ m : ℝ)
    (F : ℝ → ℝ → Vec3 → ℝ) (i : Fin 3) (k ε : ℝ) (y : Vec3) :
    normalizedMovingBellTest ρ m F i k ε y =
      ((ρ ^ 3) ^ (i.val + 1))⁻¹ *
        (epsilonBellTestsKJet m
          (fun j => MomentKJet.const (epsilonSpatialJet (F k) (j.val + 1) ε y)) i).value := by
  have H := congrArg MomentKJet.value (epsilonBellTestsKJet_scale_grade
    ((ρ ^ 3)⁻¹) m
    (fun j => MomentKJet.const (epsilonSpatialJet (F k) (j.val + 1) ε y)) i)
  simpa only [normalizedMovingBellTest, inv_pow, MomentKJet.scale,
    MomentKJet.const, mul_zero] using H.symm

private theorem epsilonMoment_const_mul_test (c m : ℝ) (v : Vec3)
    (F ψ : ℝ → Vec3 → ℝ) (ε : ℝ) (x : Vec3) :
    epsilonMoment m v F (fun e y => c * ψ e y) ε x =
      c * epsilonMoment m v F ψ ε x := by
  unfold epsilonMoment
  have he (t : ℝ) : Real.exp (m * F ε (x + t • v)) * (c * ψ ε (x + t • v)) =
      c * (Real.exp (m * F ε (x + t • v)) * ψ ε (x + t • v)) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  ring

theorem normalizedMovingBellAverage_eq_scale (ρ m : ℝ) (v x : ℝ → Vec3)
    (F : ℝ → ℝ → Vec3 → ℝ) (ε : ℝ) (i : Fin 3) :
    normalizedMovingBellAverage ρ m v x F ε i =
      fun k => ((ρ ^ 3) ^ (i.val + 1))⁻¹ * epsilonMovingBellAverage m v x F ε i k := by
  funext k
  unfold normalizedMovingBellAverage epsilonMovingBellAverage
  have ht : normalizedMovingBellTest ρ m F i k =
      fun e y => ((ρ ^ 3) ^ (i.val + 1))⁻¹ *
        (epsilonBellTestsKJet m
          (fun j => MomentKJet.const (epsilonSpatialJet (F k) (j.val + 1) e y)) i).value :=
    funext (fun e => funext (fun y => normalizedMovingBellTest_eq_scale ρ m F i k e y))
  rw [ht]
  exact epsilonMoment_const_mul_test _ _ _ _ _ _ _

theorem normalizedMovingBellKJet_eq_scale (ρ m : ℝ) (v x : ℝ → Vec3)
    (F : ℝ → ℝ → Vec3 → ℝ) (ε : ℝ) (i : Fin 3) (k : ℝ) :
    normalizedMovingBellKJet ρ m v x F ε i k =
      (epsilonMovingBellKJet m v x F ε i k).scale (((ρ ^ 3) ^ (i.val + 1))⁻¹) := by
  simp only [normalizedMovingBellKJet, normalizedMovingBellAverage_eq_scale,
    epsilonMovingBellKJet, MomentKJet.scale, deriv_const_mul_field,
    deriv_const_mul_field']

theorem epsilonMovingBellKJet_eq_scale_normalized {ρ : ℝ} (hρ : ρ ≠ 0)
    (m : ℝ) (v x : ℝ → Vec3) (F : ℝ → ℝ → Vec3 → ℝ)
    (ε : ℝ) (i : Fin 3) (k : ℝ) :
    epsilonMovingBellKJet m v x F ε i k =
      (normalizedMovingBellKJet ρ m v x F ε i k).scale ((ρ ^ 3) ^ (i.val + 1)) := by
  rw [normalizedMovingBellKJet_eq_scale,MomentKJet.scale_scale,
    mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hρ))]
  cases epsilonMovingBellKJet m v x F ε i k
  simp only [MomentKJet.scale,one_mul]

theorem normalizedMovingBellKJet_completedSquare {U : Set ℝ} (hU : IsOpen U)
    (ρ m ε : ℝ) (v x : ℝ → Vec3) (P : ℝ → QuadraticTerminal)
    (F : ℝ → ℝ → Vec3 → ℝ) (R : ℝ → Vec3 → ℝ) (L : ℝ → ℝ)
    (i : Fin 3) (hframe : ∀ k ∈ U, ∀ y, F k ε y = (P k).value y + R k y)
    (hR : ∀ k ∈ U, Continuous (R k))
    (hψ : ∀ k ∈ U, Continuous (normalizedMovingBellTest ρ m F i k ε))
    (hLip : ∀ k ∈ U, ∀ y z, |R k y - R k z| ≤ L k * ‖y - z‖)
    (hD : ∀ k ∈ U, 0 < (P k).precision m (v k)) {k : ℝ} (hk : k ∈ U) :
    let B := fun t => StepCalculus.tiltedAverage m
      ((Real.sqrt ((P t).precision m (v t))⁻¹) • v t) (R t)
      (normalizedMovingBellTest ρ m F i t ε)
      (quadraticMeanLinear (P t) m (v t) (x t) + quadraticNoiseConstant (P t) m (v t))
    normalizedMovingBellKJet ρ m v x F ε i k =
      MomentKJet.mk (B k) (deriv B k) (deriv (deriv B) k) := by
  have H := completedSquare_movingMoment_totalKJet hU m ε v x P F R
    (fun t => normalizedMovingBellTest ρ m F i t ε) L hframe hR hψ hLip hD hk
  have he : normalizedMovingBellAverage ρ m v x F ε i =
      fun t => epsilonMoment m (v t) (F t)
        (fun _ => normalizedMovingBellTest ρ m F i t ε) ε (x t) := rfl
  simpa only [normalizedMovingBellKJet,he] using H

theorem normalizedEpsilonKJet_cons_eq_cumulants {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) {ε ρ m : ℝ} (hε : ε ∈ V) (hρ : ρ ≠ 0)
    (l : ℝ → List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (c : Vec3) (y v : ℝ → Vec3)
    (H : ∀ k ∈ U, EpsilonJetControl (fun e => epsilonChain (l k) Q K e) V)
    (P : ℝ → QuadraticTerminal) (hm : 0 < m)
    (hP : ∀ k ∈ U, 1 / 2 ≤ (P k).precision m (v k))
    (hmajor : ∀ k ∈ U, ∀ e ∈ V, ∀ z, epsilonChain (l k) Q K e z ≤ (P k).value z)
    (hA : ∀ k ∈ U, ∀ i,
      MomentKJet.Differentiates (epsilonMovingBellKJet m v
        (fun t => ρ • y t + c) (fun t e => epsilonChain (l t) Q K e) ε i) k)
    {k : ℝ} (hk : k ∈ U) (i : Fin 3) :
    normalizedEpsilonKJet (fun t => (m,v t) :: l t) Q K ρ c y (i.val + 1) ε k =
      epsilonLogCumulantsKJet m (fun j => normalizedMovingBellKJet ρ m v
        (fun t => ρ • y t + c) (fun t e => epsilonChain (l t) Q K e) ε j k) i := by
  rw [normalizedEpsilonKJet_eq_inverse_scale hρ]
  have HE := epsilonStep_moving_totalKJet hU hV hε H P hm hP hmajor hA hk i
  dsimp only at HE
  have ho : originalEpsilonKJet (fun t => (m,v t) :: l t) Q K ρ c y (i.val + 1) ε k =
      MomentKJet.mk
        (epsilonSpatialJet (fun e => vectorStep m (v k) (epsilonChain (l k) Q K e))
          (i.val + 1) ε (ρ • y k + c))
        (deriv (fun t => epsilonSpatialJet
          (fun e => vectorStep m (v t) (epsilonChain (l t) Q K e))
          (i.val + 1) ε (ρ • y t + c)) k)
        (deriv (deriv (fun t => epsilonSpatialJet
          (fun e => vectorStep m (v t) (epsilonChain (l t) Q K e))
          (i.val + 1) ε (ρ • y t + c))) k) := by
    simp only [originalEpsilonKJet,epsilonChain,vectorIncrementChain,
      iteratedDeriv_succ,iteratedDeriv_zero]
  rw [ho,HE]
  have HG := epsilonLogCumulantsKJet_scale_grade ((ρ ^ 3)⁻¹) m
    (fun j => epsilonMovingBellKJet m v (fun t => ρ • y t + c)
      (fun t e => epsilonChain (l t) Q K e) ε j k) i
  simpa only [inv_pow,normalizedMovingBellKJet_eq_scale] using HG

def frozenRowsMovingBellKJet (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (i : Fin 3) (y : Vec3) (k g : ℝ) : MomentKJet :=
  normalizedMovingBellKJet (Real.sqrt h) (frozenPartitionMass a (j + 1))
    (fun t => (frozenRowsHead β a h (j + 1) t).2)
    (fun t => Real.sqrt h • (y + (Real.sqrt h)⁻¹ •
      (g • (frozenRowsHead β a h j t).2)) + (fun _ => z))
    (fun t e => epsilonChain ((frozenSchedule β a (1 / 2) h t).drop (j + 2))
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) e) ε i k

theorem frozenRows_next_suffix (β a h k : ℝ) (j : ℕ) (hj : j < 11) :
    (frozenSchedule β a (1 / 2) h k).drop (j + 1) =
      (frozenPartitionMass a (j + 1),(frozenRowsHead β a h (j + 1) k).2) ::
        (frozenSchedule β a (1 / 2) h k).drop (j + 2) := by
  interval_cases j <;>
    rfl

theorem frozenRowsNormalizedJet_eq_cumulants {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) {β a s h z ε : ℝ} {α : ℝ → ℝ}
    (hh : 0 < h) (hε : ε ∈ V) (j : ℕ) (hj : j < 11) (y : Vec3) (g : ℝ)
    (H : ∀ k ∈ U, EpsilonJetControl
      (fun e => epsilonChain ((frozenSchedule β a (1 / 2) h k).drop (j + 2))
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) e) V)
    (P : ℝ → QuadraticTerminal) (hm : 0 < frozenPartitionMass a (j + 1))
    (hP : ∀ k ∈ U, 1 / 2 ≤ (P k).precision (frozenPartitionMass a (j + 1))
      (frozenRowsHead β a h (j + 1) k).2)
    (hmajor : ∀ k ∈ U, ∀ e ∈ V, ∀ w,
      epsilonChain ((frozenSchedule β a (1 / 2) h k).drop (j + 2))
        (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) e w ≤
          (P k).value w)
    (hA : ∀ k ∈ U, ∀ i, MomentKJet.Differentiates
      (epsilonMovingBellKJet (frozenPartitionMass a (j + 1))
        (fun t => (frozenRowsHead β a h (j + 1) t).2)
        (fun t => Real.sqrt h • (y + (Real.sqrt h)⁻¹ •
          (g • (frozenRowsHead β a h j t).2)) + (fun _ => z))
        (fun t e => epsilonChain ((frozenSchedule β a (1 / 2) h t).drop (j + 2))
          (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) e) ε i) k)
    {k : ℝ} (hk : k ∈ U) (i : Fin 3) :
    frozenRowsNormalizedJet β α a s h z ε j i y k g =
      epsilonLogCumulantsKJet (frozenPartitionMass a (j + 1))
        (fun t => frozenRowsMovingBellKJet β α a s h z ε j t y k g) i := by
  have hel : (fun t => (frozenSchedule β a (1 / 2) h t).drop (j + 1)) =
      fun t => (frozenPartitionMass a (j + 1),(frozenRowsHead β a h (j + 1) t).2) ::
        (frozenSchedule β a (1 / 2) h t).drop (j + 2) :=
    funext (fun t => frozenRows_next_suffix β a h t j hj)
  unfold frozenRowsNormalizedJet
  rw [hel]
  exact normalizedEpsilonKJet_cons_eq_cumulants hU hV hε (Real.sqrt_pos.mpr hh).ne'
    _ _ _ _ _ _ H P hm hP hmajor hA hk i

theorem frozenRowsMovingBell_rescale_cumulants (β : ℝ) (α : ℝ → ℝ)
    (a s h z ε σ : ℝ) (j : ℕ) (i : Fin 3) (y : Vec3) (k g : ℝ) :
    MomentKJet.rescale σ (epsilonLogCumulantsKJet (frozenPartitionMass a (j + 1))
      (fun t => frozenRowsMovingBellKJet β α a s h z ε j t y k g) i) =
      epsilonLogCumulantsKJet (frozenPartitionMass a (j + 1))
        (fun t => MomentKJet.rescale σ
          (frozenRowsMovingBellKJet β α a s h z ε j t y k g)) i :=
  epsilonLogCumulantsKJet_rescale _ _ _ _

end SKBarriers2.Corner
