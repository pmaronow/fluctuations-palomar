module

public import SKBarriers2.Corner.PathEnergyGeneratorSum3
public import SKBarriers2.Corner.PathEnergyGenerator6

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

def curveFullGeneratorJet (f F Q g a q : ℝ → E → ℝ) (p : Curve)
    (c : Fin 3) (t : ℝ) (x : E) : ℝ :=
  fullGeneratorJet (p t).1 (deriv (fun z => (p z).1) t)
    (deriv (deriv (fun z => (p z).1)) t) (f t) (F t) (Q t) (g t) (a t) (q t)
    (p t).2 (deriv (fun z => (p z).2) t)
    (deriv (deriv (fun z => (p z).2)) t) c x

private theorem finite_sum_parameter_twoJet {T : Type} (J : T → Fin 3 → ℝ → ℝ)
    (ps : List T) {k : ℝ}
    (h₀ : ∀ p ∈ ps, ∀ᶠ t in 𝓝 k, HasDerivAt (J p 0) (J p 1 t) t)
    (h₁ : ∀ p ∈ ps, HasDerivAt (J p 1) (J p 2 k) k) :
    (∀ᶠ t in 𝓝 k, HasDerivAt (fun z => (ps.map (fun p => J p 0 z)).sum)
      (ps.map (fun p => J p 1 t)).sum t) ∧
    HasDerivAt (fun z => (ps.map (fun p => J p 1 z)).sum)
      (ps.map (fun p => J p 2 k)).sum k := by
  induction ps with
  | nil =>
    exact ⟨Eventually.of_forall (fun t => by simpa using hasDerivAt_const t (0 : ℝ)),
      by simpa using hasDerivAt_const k (0 : ℝ)⟩
  | cons p ps ih =>
    have hi := ih (fun z hz => h₀ z (List.mem_cons_of_mem _ hz))
      (fun z hz => h₁ z (List.mem_cons_of_mem _ hz))
    refine ⟨?_,?_⟩
    · filter_upwards [h₀ p List.mem_cons_self,hi.1] with t hpt hit
      simpa only [List.map_cons,List.sum_cons] using hpt.fun_add hit
    · simpa only [List.map_cons,List.sum_cons] using
        (h₁ p List.mem_cons_self).fun_add hi.2

private theorem curveFullGeneratorJet_sum (f F Q g a q : ℝ → E → ℝ)
    (ps : List Curve) (c : Fin 3) (t : ℝ) (x : E) :
    (ps.map (fun p => curveFullGeneratorJet f F Q g a q p c t x)).sum =
      fullGeneratorCurveSumJet (f t) (F t) (Q t) (g t) (a t) (q t) t ps c x := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons]
    change curveFullGeneratorJet f F Q g a q p c t x +
      (ps.map (fun p => curveFullGeneratorJet f F Q g a q p c t x)).sum =
      curveFullGeneratorJet f F Q g a q p c t x +
        fullGeneratorCurveSumJet (f t) (F t) (Q t) (g t) (a t) (q t) t ps c x
    rw [ih]

theorem fullGeneratorCurveSumJet_eq_iteratedDeriv
    {f F Q g a q : ℝ → E → ℝ} (ps : List Curve) {k : ℝ}
    (hg : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (g t))
    (h₀ : ∀ p ∈ ps, ∀ᶠ t in 𝓝 k, ∀ x,
      HasDerivAt (fun z => curveFullGeneratorJet f F Q g a q p 0 z x)
        (curveFullGeneratorJet f F Q g a q p 1 t x) t)
    (h₁ : ∀ p ∈ ps, ∀ x,
      HasDerivAt (fun z => curveFullGeneratorJet f F Q g a q p 1 z x)
        (curveFullGeneratorJet f F Q g a q p 2 k x) k)
    (c : Fin 3) (x : E) :
    fullGeneratorCurveSumJet (f k) (F k) (Q k) (g k) (a k) (q k) k ps c x =
      iteratedDeriv c.val (fun t => pathGeneratorSum (f t) (g t)
        (ps.map (fun p => p t)) x) k := by
  have H := finite_sum_parameter_twoJet
    (fun p i t => curveFullGeneratorJet f F Q g a q p i t x) ps
    (fun p hp => (h₀ p hp).mono (fun t ht => ht x))
    (fun p hp => h₁ p hp x)
  simp only [curveFullGeneratorJet_sum] at H
  have Htwo := (iteratedDeriv_eq_of_twoJet
    (J := fun i t => fullGeneratorCurveSumJet (f t) (F t) (Q t) (g t) (a t) (q t)
      t ps i x) H.1 H.2 c).symm
  have hvalue : ∀ (ts : List Curve) (t : ℝ), ContDiff ℝ 2 (g t) →
      fullGeneratorCurveSumJet (f t) (F t) (Q t) (g t) (a t) (q t) t ts 0 x =
      pathGeneratorSum (f t) (g t) (ts.map (fun p => p t)) x := by
    intro ts t hgt
    induction ts with
    | nil => rfl
    | cons p ps ih =>
      simp only [fullGeneratorCurveSumJet,List.map_cons,pathGeneratorSum]
      rw [← pathGenerator_eq_fullGeneratorJet_zero hgt,ih]
  have hevent : (fun t => fullGeneratorCurveSumJet (f t) (F t) (Q t) (g t) (a t) (q t)
      t ps 0 x) =ᶠ[𝓝 k] fun t => pathGeneratorSum (f t) (g t)
        (ps.map (fun p => p t)) x := hg.mono (fun t ht => hvalue ps t ht)
  exact Htwo.trans (hevent.iteratedDeriv_eq c.val)

end SKBarriers2.StepCalculus
