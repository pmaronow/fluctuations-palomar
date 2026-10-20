module

public import CavitySplitDensity

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
open GaussianCalculus
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem ClockPolynomial.finiteLowJet_zero_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (P : T.Assignment → ℝ)
    (b d : ℕ → ι → ℝ) (t : ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    (ClockPolynomial.finiteLowJet (T.testExpr P) φ b d 0).finiteEval w φ t v q x =
      T.disorderExpect w φ v q P x := by
  unfold ClockPolynomial.finiteLowJet ClockPolynomial.finiteEval
  simp only [ClockPolynomial.lowJet,ClockPolynomial.rootEval,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Polynomial.eval_one,one_mul,add_zero]
  rw [ClockTree.rootEval_testExpr hw (reindexFeature (finiteJetEquiv ι) φ) T ho
    (fun i => v (finiteJetEquiv ι i)) (fun j i => q j (finiteJetEquiv ι i)) P
    ((coordinateEquiv (finiteJetEquiv ι)).symm x)]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    T.disorderExpect_reindex (finiteJetEquiv ι) w φ v q P
      ((coordinateEquiv (finiteJetEquiv ι)).symm x)

 theorem ClockTree.iteratedDeriv_finiteLowJet_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (P : T.Assignment → ℝ)
    (b d : ℕ → ι → ℝ) (t : ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    {a z : ℝ}
    (hp : ∀ s ∈ Ioo a z, ∀ i, Monotone (fun j => q j i+s*(b j i+t*d j i)))
    (hr : ∀ s ∈ Ioo a z, ∀ i, v i ≤ q 0 i+s*(b 0 i+t*d 0 i))
    (k : ℕ) {u : ℝ} (hu : u ∈ Ioo a z) :
    iteratedDeriv k (fun s => T.disorderExpect w φ v
      (fun j i => q j i+s*(b j i+t*d j i)) P x) u =
      (ClockPolynomial.finiteLowJet (T.testExpr P) φ b d k).finiteEval w φ t v
        (fun j i => q j i+u*(b j i+t*d j i)) x := by
  induction k generalizing u with
  | zero => exact (ClockPolynomial.finiteLowJet_zero_actual hw φ T ho P b d t v _ x).symm
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun s => T.disorderExpect w φ v
        (fun j i => q j i+s*(b j i+t*d j i)) P x) =ᶠ[𝓝 u]
        (fun s => (ClockPolynomial.finiteLowJet (T.testExpr P) φ b d k).finiteEval w φ t v
          (fun j i => q j i+s*(b j i+t*d j i)) x) := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with s hs
      exact ih hs
    rw [he.deriv_eq]
    exact (ClockPolynomial.finiteLowJet_hasDerivAt_low hw φ (T.testExpr P) ho
      v q b d k t hp hr hu x).deriv

 theorem ClockPolynomial.finiteLowJet_eq_profileJets_affine {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (b d : ℕ → ι → ℝ) (t : ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) {a z : ℝ}
    (hp : ∀ s ∈ Ioo a z, ∀ i, Monotone (fun j => q j i+s*(b j i+t*d j i)))
    (hr : ∀ s ∈ Ioo a z, ∀ i, v i ≤ q 0 i+s*(b 0 i+t*d 0 i))
    (k : ℕ) {u : ℝ} (hu : u ∈ Ioo a z) :
    (ClockPolynomial.finiteLowJet (T.testExpr P) φ b d k).finiteEval w φ t v
        (fun j i => q j i+u*(b j i+t*d j i)) x =
      ClockTree.disorderProfileJets w φ v (fun j i => q j i+u*(b j i+t*d j i)) x
        (List.replicate k (ReplicaTree.coordinateProfile φ (fun j i => b j i+t*d j i))) T P := by
  rw [← T.iteratedDeriv_finiteLowJet_actual hw φ ho P b d t v q x hp hr k hu]
  exact T.iteratedDeriv_finiteProfileJets hw φ ho v q (fun j i => b j i+t*d j i)
    hp hr P x k hu

 theorem ClockPolynomial.finiteLowJet_eq_profileJets_zero {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (b d : ℕ → ι → ℝ) (t : ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) {z : ℝ} (hz : 0 < z)
    (hp : ∀ s ∈ Ioo 0 z, ∀ i, Monotone (fun j => q j i+s*(b j i+t*d j i)))
    (hr : ∀ s ∈ Ioo 0 z, ∀ i, v i ≤ q 0 i+s*(b 0 i+t*d 0 i)) (k : ℕ) :
    (ClockPolynomial.finiteLowJet (T.testExpr P) φ b d k).finiteEval w φ t v q x =
      ClockTree.disorderProfileJets w φ v q x
        (List.replicate k (ReplicaTree.coordinateProfile φ (fun j i => b j i+t*d j i))) T P := by
  have he : Set.EqOn
      (fun u => (ClockPolynomial.finiteLowJet (T.testExpr P) φ b d k).finiteEval w φ t v
        (fun j i => q j i+u*(b j i+t*d j i)) x)
      (fun u => ClockTree.disorderProfileJets w φ v (fun j i => q j i+u*(b j i+t*d j i)) x
        (List.replicate k (ReplicaTree.coordinateProfile φ (fun j i => b j i+t*d j i))) T P)
      (Ioo (0:ℝ) z) := by
    intro u hu
    exact ClockPolynomial.finiteLowJet_eq_profileJets_affine hw φ T ho P b d t v q x hp hr k hu
  have hq : Continuous (fun u : ℝ => fun j i => q j i+u*(b j i+t*d j i)) := by fun_prop
  have hE := ClockPolynomial.finiteEval_continuous hw φ
    (ClockPolynomial.finiteLowJet (T.testExpr P) φ b d k)
    (fun _ => t) continuous_const v (fun j u i => q j i+u*(b j i+t*d j i))
      (fun j => (continuous_apply j).comp hq) (fun _ => x) continuous_const
  have hJ := ClockTree.disorderProfileJets_continuous hw φ ho v
    (fun u j i => q j i+u*(b j i+t*d j i)) (fun j => (continuous_apply j).comp hq)
    (fun _ => x) continuous_const
      (List.replicate k (ReplicaTree.coordinateProfile φ (fun j i => b j i+t*d j i))) T P
  have h0 : (0:ℝ) ∈ closure (Ioo (0:ℝ) z) := by
    rw [closure_Ioo hz.ne]
    exact ⟨le_rfl,hz.le⟩
  have H := he.closure hE hJ h0
  simpa only [zero_mul,add_zero] using H

end OAI.SKFluctuations.Hierarchy
