module

public import SKFluctuationsOAI.Probability.SKFluctuations.MarkedPairExpectation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open Filter Set
open scoped Topology
set_option maxHeartbeats 30000000

private theorem native_second_low_uncurry_hasFDerivAt
    (f g h : ℝ → ℝ → ℝ)
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hh : Continuous (fun p : ℝ × ℝ => h p.1 p.2))
    (dg : ∀ s t, HasDerivAt (fun z => f z t) (g s t) s)
    (dh : ∀ s t, HasDerivAt (fun z => f s z) (h s t) t)
    (p : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (g p.1 p.2)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (h p.1 p.2))) p := by
  exact (hasStrictFDerivAt_uncurry_coprod
    (u := p) (f := f)
    (f₁ := fun s t => ContinuousLinearMap.toSpanSingleton ℝ (g s t))
    (f₂ := fun s t => ContinuousLinearMap.toSpanSingleton ℝ (h s t))
    (Eventually.of_forall (fun q => (dg q.1 q.2).hasFDerivAt))
    (Eventually.of_forall (fun q => (dh q.1 q.2).hasFDerivAt))
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hg).continuousAt)
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hh).continuousAt)).hasFDerivAt

private theorem native_second_low_continuous_mixed_partials_commute
    (f g h gg gh hg hh : ℝ → ℝ → ℝ)
    (cg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (ch : Continuous (fun p : ℝ × ℝ => h p.1 p.2))
    (cgg : Continuous (fun p : ℝ × ℝ => gg p.1 p.2))
    (cgh : Continuous (fun p : ℝ × ℝ => gh p.1 p.2))
    (chg : Continuous (fun p : ℝ × ℝ => hg p.1 p.2))
    (chh : Continuous (fun p : ℝ × ℝ => hh p.1 p.2))
    (dfg : ∀ s t, HasDerivAt (fun z => f z t) (g s t) s)
    (dfh : ∀ s t, HasDerivAt (fun z => f s z) (h s t) t)
    (dgg : ∀ s t, HasDerivAt (fun z => g z t) (gg s t) s)
    (dgh : ∀ s t, HasDerivAt (fun z => g s z) (gh s t) t)
    (dhg : ∀ s t, HasDerivAt (fun z => h z t) (hg s t) s)
    (dhh : ∀ s t, HasDerivAt (fun z => h s z) (hh s t) t) :
    gh 0 0 = hg 0 0 := by
  let A : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let B : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let D : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun p => g p.1 p.2 • A + h p.1 p.2 • B
  let G := (ContinuousLinearMap.toSpanSingleton ℝ (gg 0 0)).coprod
    (ContinuousLinearMap.toSpanSingleton ℝ (gh 0 0))
  let H := (ContinuousLinearMap.toSpanSingleton ℝ (hg 0 0)).coprod
    (ContinuousLinearMap.toSpanSingleton ℝ (hh 0 0))
  have hd (p : ℝ × ℝ) : HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2) (D p) p := by
    have HE : D p = (ContinuousLinearMap.toSpanSingleton ℝ (g p.1 p.2)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (h p.1 p.2)) := by
      apply ContinuousLinearMap.ext
      intro q
      simp [D,A,B,ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply,mul_comm]
    rw [HE]
    exact native_second_low_uncurry_hasFDerivAt f g h cg ch dfg dfh p
  have hG : HasFDerivAt (fun p : ℝ × ℝ => g p.1 p.2) G (0,0) :=
    native_second_low_uncurry_hasFDerivAt g gg gh cgg cgh dgg dgh (0,0)
  have hH : HasFDerivAt (fun p : ℝ × ℝ => h p.1 p.2) H (0,0) :=
    native_second_low_uncurry_hasFDerivAt h hg hh chg chh dhg dhh (0,0)
  have hD := (hG.smul_const A).add (hH.smul_const B)
  have hs := second_derivative_symmetric hd hD ((1,0) : ℝ × ℝ) ((0,1) : ℝ × ℝ)
  simpa [D,G,H,A,B,ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply]
    using hs.symm

namespace ReplicaTree
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_second_low_powerJet_two_symm
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ)
    (u v x : ι → ℝ) :
    powerJet w φ a [u,v] T P x = powerJet w φ a [v,u] T P x := by
  let F : List (ι → ℝ) → ℝ → ℝ → ℝ := fun vs s t =>
    Real.exp (a * gaussianHierarchy w φ steps (x + s • u + t • v)) *
      powerJet w φ a vs T P (x + s • u + t • v)
  have hc (vs : List (ι → ℝ)) : Continuous (fun p : ℝ × ℝ => F vs p.1 p.2) := by
    have chier := (gaussianHierarchy_regular hw φ steps ha 0).1.choose_spec.continuous
    exact ((Real.continuous_exp.comp (continuous_const.mul chier)).mul
      (powerJet_smooth hw φ vs T ha P 0).continuous).comp (by fun_prop)
  have hdU (vs : List (ι → ℝ)) (s t : ℝ) :
      HasDerivAt (fun z => F vs z t) (F (vs++[u]) s t) s := by
    simpa only [F,add_right_comm x] using
      weighted_powerJet_hasDerivAt hw φ vs T ha P u (x+t • v) s
  have hdV (vs : List (ι → ℝ)) (s t : ℝ) :
      HasDerivAt (fun z => F vs s z) (F (vs++[v]) s t) t := by
    exact weighted_powerJet_hasDerivAt hw φ vs T ha P v (x+s • u) t
  have h := native_second_low_continuous_mixed_partials_commute
    (F []) (F [u]) (F [v]) (F [u,u]) (F [u,v]) (F [v,u]) (F [v,v])
    (hc _) (hc _) (hc _) (hc _) (hc _) (hc _)
    (hdU []) (hdV []) (hdU [u]) (hdV [u]) (hdU [v]) (hdV [v])
  simp only [F,zero_smul,add_zero] at h
  exact (mul_left_cancel₀ (ne_of_gt (Real.exp_pos _))) h

theorem native_second_low_marked_field_pair_symm
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ)
    (u v x : ι → ℝ) :
    T.markedPairExpectation w φ a P (fun σ τ => φ σ u * φ τ v) x =
      T.markedPairExpectation w φ a P (fun σ τ => φ σ v * φ τ u) x := by
  rw [← powerJet_two_marked,← powerJet_two_marked]
  exact native_second_low_powerJet_two_symm hw φ T ha P u v x

end ReplicaTree
end OAI.SKFluctuations.Hierarchy
