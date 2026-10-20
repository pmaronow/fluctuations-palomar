module

public import SKBarriers2.Corner.FrozenRowsMixed2

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

namespace MomentKJet

theorem actual_of_eventuallyEq {J : ℝ → MomentKJet} {f : ℝ → ℝ} {k : ℝ}
    (hJ : ∀ᶠ t in 𝓝 k, Differentiates J t)
    (hf : f =ᶠ[𝓝 k] fun t => (J t).value) :
    MomentKJet.mk (f k) (deriv f k) (deriv (deriv f) k) = J k := by
  have hfirst : deriv (fun t => (J t).value) =ᶠ[𝓝 k] fun t => (J t).first :=
    hJ.mono (fun t ht => ht.1.deriv)
  have hk := hJ.self_of_nhds
  have h₀ := hf.self_of_nhds
  have h₁ : deriv f k = (J k).first := hf.deriv_eq.trans hk.1.deriv
  have h₂ : deriv (deriv f) k = (J k).second :=
    hf.deriv.deriv_eq.trans (hfirst.deriv_eq.trans hk.2.deriv)
  rw [h₀, h₁, h₂]

theorem totalJets_congr {f g : ℝ → ℝ} {k : ℝ} (h : f =ᶠ[𝓝 k] g) :
    MomentKJet.mk (f k) (deriv f k) (deriv (deriv f) k) =
      MomentKJet.mk (g k) (deriv g k) (deriv (deriv g) k) := by
  rw [h.self_of_nhds, h.deriv_eq, h.deriv.deriv_eq]

theorem actual_of_eqOn {J : ℝ → MomentKJet} {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hJ : ∀ t ∈ U, Differentiates J t)
    (hf : ∀ t ∈ U, f t = (J t).value) {k : ℝ} (hk : k ∈ U) :
    MomentKJet.mk (f k) (deriv f k) (deriv (deriv f) k) = J k := by
  apply actual_of_eventuallyEq
  · filter_upwards [hU.mem_nhds hk] with t ht
    exact hJ t ht
  · filter_upwards [hU.mem_nhds hk] with t ht
    exact hf t ht

end MomentKJet

theorem epsilonLogCumulantsKJet_actual {A : Fin 3 → ℝ → MomentKJet}
    {f : Fin 3 → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hA : ∀ t ∈ U, ∀ i, MomentKJet.Differentiates (A i) t)
    (m : ℝ)
    (hf : ∀ t ∈ U, ∀ i, f i t =
      (epsilonLogCumulantsKJet m (fun i => A i t) i).value)
    {k : ℝ} (hk : k ∈ U) (i : Fin 3) :
    MomentKJet.mk (f i k) (deriv (f i) k) (deriv (deriv (f i)) k) =
      epsilonLogCumulantsKJet m (fun i => A i k) i := by
  apply MomentKJet.actual_of_eqOn hU
  · intro t ht
    exact epsilonLogCumulantsKJet_differentiates (hA t ht) m i
  · intro t ht
    exact hf t ht i
  · exact hk

def epsilonMovingBellAverage (m : ℝ) (v x : ℝ → Vec3)
    (F : ℝ → ℝ → Vec3 → ℝ) (ε : ℝ) (i : Fin 3) (k : ℝ) : ℝ :=
  epsilonMoment m (v k) (F k)
    (fun e y => (epsilonBellTestsKJet m
      (fun j => MomentKJet.const (epsilonSpatialJet (F k) (j.val + 1) e y)) i).value)
    ε (x k)

def epsilonMovingBellKJet (m : ℝ) (v x : ℝ → Vec3)
    (F : ℝ → ℝ → Vec3 → ℝ) (ε : ℝ) (i : Fin 3) (k : ℝ) : MomentKJet :=
  let A := epsilonMovingBellAverage m v x F ε i
  ⟨A k, deriv A k, deriv (deriv A) k⟩

theorem epsilonStep_moving_totalKJet {U V : Set ℝ}
    {F : ℝ → ℝ → Vec3 → ℝ} {m ε : ℝ} {v x : ℝ → Vec3}
    (hU : IsOpen U) (hV : IsOpen V) (hε : ε ∈ V)
    (H : ∀ k ∈ U, EpsilonJetControl (F k) V)
    (P : ℝ → QuadraticTerminal) (hm : 0 < m)
    (hP : ∀ k ∈ U, 1 / 2 ≤ (P k).precision m (v k))
    (hmajor : ∀ k ∈ U, ∀ e ∈ V, ∀ y, F k e y ≤ (P k).value y)
    (hA : ∀ k ∈ U, ∀ i,
      MomentKJet.Differentiates (epsilonMovingBellKJet m v x F ε i) k)
    {k : ℝ} (hk : k ∈ U) (i : Fin 3) :
    let f := fun k => epsilonSpatialJet
      (fun e => vectorStep m (v k) (F k e)) (i.val + 1) ε (x k)
    MomentKJet.mk (f k) (deriv f k) (deriv (deriv f) k) =
      epsilonLogCumulantsKJet m (fun j => epsilonMovingBellKJet m v x F ε j k) i := by
  refine epsilonLogCumulantsKJet_actual
    (f := fun j κ => epsilonSpatialJet (fun e => vectorStep m (v κ) (F κ e))
      (j.val+1) ε (x κ)) hU hA m ?_ hk i
  intro t ht j
  have HE := epsilonStep_jet_values (H t ht) hV (P t) hm (v t)
    (hP t ht) (hmajor t ht) ε hε (x t)
  fin_cases j
  · simpa [epsilonMovingBellKJet, epsilonMovingBellAverage,
      epsilonBellTestsKJet, epsilonLogCumulantsKJet, MomentKJet.const] using HE.1
  · simpa [epsilonMovingBellKJet, epsilonMovingBellAverage,
      epsilonBellTestsKJet, epsilonLogCumulantsKJet,
      MomentKJet.const, MomentKJet.add, MomentKJet.scale, MomentKJet.mul,
      pow_two,sub_eq_add_neg] using HE.2.1
  · simpa [epsilonMovingBellKJet, epsilonMovingBellAverage,
      epsilonBellTestsKJet, epsilonLogCumulantsKJet,
      MomentKJet.const, MomentKJet.add, MomentKJet.scale, MomentKJet.mul,
      pow_two, pow_succ, sub_eq_add_neg, mul_add, add_mul, mul_assoc] using HE.2.2

theorem completedSquare_movingMoment_totalKJet {U : Set ℝ} (hU : IsOpen U)
    (m ε : ℝ) (v x : ℝ → Vec3) (P : ℝ → QuadraticTerminal)
    (F : ℝ → ℝ → Vec3 → ℝ) (R ψ : ℝ → Vec3 → ℝ) (L : ℝ → ℝ)
    (hframe : ∀ k ∈ U, ∀ y, F k ε y = (P k).value y + R k y)
    (hR : ∀ k ∈ U, Continuous (R k)) (hψ : ∀ k ∈ U, Continuous (ψ k))
    (hLip : ∀ k ∈ U, ∀ y z, |R k y - R k z| ≤ L k * ‖y - z‖)
    (hD : ∀ k ∈ U, 0 < (P k).precision m (v k))
    {k : ℝ} (hk : k ∈ U) :
    let A := fun t => epsilonMoment m (v t) (F t) (fun _ => ψ t) ε (x t)
    let B := fun t => StepCalculus.tiltedAverage m
      ((Real.sqrt ((P t).precision m (v t))⁻¹) • v t) (R t) (ψ t)
      (quadraticMeanLinear (P t) m (v t) (x t) + quadraticNoiseConstant (P t) m (v t))
    MomentKJet.mk (A k) (deriv A k) (deriv (deriv A) k) =
      MomentKJet.mk (B k) (deriv B k) (deriv (deriv B) k) := by
  dsimp only
  apply MomentKJet.totalJets_congr
    (f := fun t => epsilonMoment m (v t) (F t) (fun _ => ψ t) ε (x t))
    (g := fun t => StepCalculus.tiltedAverage m
      ((Real.sqrt ((P t).precision m (v t))⁻¹) • v t) (R t) (ψ t)
      (quadraticMeanLinear (P t) m (v t) (x t)+quadraticNoiseConstant (P t) m (v t)))
  filter_upwards [hU.mem_nhds hk] with t ht
  change epsilonMoment m (v t) (F t) (fun _ => ψ t) ε (x t) = _
  have heq : epsilonMoment m (v t) (F t) (fun _ => ψ t) ε (x t) =
      epsilonMoment m (v t) (fun _ y => (P t).value y + R t y) (fun _ => ψ t) 0 (x t) := by
    unfold epsilonMoment
    simp_rw [hframe t ht]
  rw [heq]
  exact completedSquare_moment_eq_tiltedAverage (P t) m (v t) (x t)
    (hD t ht) (hR t ht) (hψ t ht) (hLip t ht)

end SKBarriers2.Corner
