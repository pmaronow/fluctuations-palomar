module

public import CavityProfileJointContinuity
public import CavityMixedPartialSymmetry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

def doubleClock (q D E : ℕ → ι → ℝ) (p : ℝ × ℝ) : ℕ → ι → ℝ :=
  fun j i => q j i+p.1*D j i+p.2*E j i

theorem doubleClock_strict {v : ι → ℝ} {q D E : ℕ → ι → ℝ}
    {epsilon B : ℝ} (he : 0 < epsilon) (hB : 0 ≤ B)
    (hq : strictCumulativeClock v q epsilon)
    (hD : ∀ j i, |D j i| ≤ B) (hE : ∀ j i, |E j i| ≤ B)
    (p : ℝ × ℝ) (hs : |p.1| < epsilon/(8*(2*B+1)))
    (ht : |p.2| < epsilon/(8*(2*B+1))) :
    strictCumulativeClock v (doubleClock q D E p) (epsilon/4) := by
  have hb : 0 < 2*B+1 := by linarith
  have hs' : |p.1| *(2*B+1) ≤ epsilon/2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 8*(2*B+1))).mp hs
    nlinarith [abs_nonneg p.1]
  have ht' : |p.2| *(2*B+1) ≤ (epsilon/2)/2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 8*(2*B+1))).mp ht
    nlinarith [abs_nonneg p.2]
  have hfirst := strictCumulativeClock_perturb he hB hq hD hs'
  change strictCumulativeClock v (fun j i => q j i+p.1*D j i+p.2*E j i) (epsilon/4)
  have h := strictCumulativeClock_perturb (by positivity) hB hfirst hE ht'
  norm_num only [div_div] at h
  exact h

theorem ClockTree.actual_profileJet_append_swap_strict {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q D E : ℕ → ι → ℝ) {epsilon B : ℝ}
    (he : 0 < epsilon) (hB : 0 ≤ B) (hq : strictCumulativeClock v q epsilon)
    (hD : ∀ j i, |D j i| ≤ B) (hE : ∀ j i, |E j i| ≤ B)
    (Ks : List (ℕ → S → S → ℝ)) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    disorderProfileJets w φ v q x
      (Ks++[ReplicaTree.coordinateProfile φ D,ReplicaTree.coordinateProfile φ E]) T P =
    disorderProfileJets w φ v q x
      (Ks++[ReplicaTree.coordinateProfile φ E,ReplicaTree.coordinateProfile φ D]) T P := by
  let R := epsilon/(8*(2*B+1))
  have hR : 0 < R := by dsimp [R]; positivity
  let U : Set (ℝ × ℝ) := Ioo (-R) R ×ˢ Ioo (-R) R
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have h0 : (0,0) ∈ U := by constructor <;> constructor <;> linarith
  have hadm (p : ℝ × ℝ) (hp : p ∈ U) :
      strictCumulativeClock v (doubleClock q D E p) (epsilon/4) := by
    exact doubleClock_strict he hB hq hD hE p
      ((abs_lt).2 hp.1) ((abs_lt).2 hp.2)
  let J := fun L : List (ℕ → S → S → ℝ) => fun p : ℝ × ℝ =>
    disorderProfileJets w φ v (doubleClock q D E p) x L T P
  have hc (L : List (ℕ → S → S → ℝ)) : Continuous (J L) := by
    exact actual_disorderProfileJets_joint_continuous hw φ ho v (doubleClock q D E)
      (by intro j; apply continuous_pi; intro i; unfold doubleClock; fun_prop)
      (fun _ => x) continuous_const L T P
  have dx (L : List (ℕ → S → S → ℝ)) (p : ℝ × ℝ) (hp : p ∈ U) :
      HasDerivAt (fun s => J L (s,p.2))
        (J (L++[ReplicaTree.coordinateProfile φ D]) p) p.1 := by
    have hh (s : ℝ) (hs : s ∈ Ioo (-R) R) :
        strictCumulativeClock v (fun j i => q j i+p.2*E j i+s*D j i) (epsilon/4) := by
      have h := hadm (s,p.2) ⟨hs,hp.2⟩
      convert h using 1
      funext j i
      unfold doubleClock
      ring
    have h := hasDerivAt_finiteProfileJets hw φ ho v
      (fun j i => q j i+p.2*E j i) D
      (fun s hs i => (hh s hs).monotone (by positivity) i)
      (fun s hs i => (le_add_of_nonneg_right (by positivity)).trans ((hh s hs).1 i))
      L T P x hp.1
    have heq (s : ℝ) : (fun j i => q j i+p.2*E j i+s*D j i) =
        doubleClock q D E (s,p.2) := by
      funext j i
      unfold doubleClock
      ring
    simpa only [heq] using h
  have dy (L : List (ℕ → S → S → ℝ)) (p : ℝ × ℝ) (hp : p ∈ U) :
      HasDerivAt (fun t => J L (p.1,t))
        (J (L++[ReplicaTree.coordinateProfile φ E]) p) p.2 := by
    have hh (t : ℝ) (ht : t ∈ Ioo (-R) R) := hadm (p.1,t) ⟨hp.1,ht⟩
    exact hasDerivAt_finiteProfileJets hw φ ho v
      (fun j i => q j i+p.1*D j i) E
      (fun t ht i => (hh t ht).monotone (by positivity) i)
      (fun t ht i => (le_add_of_nonneg_right (by positivity)).trans ((hh t ht).1 i))
      L T P x hp.2
  let Dp := ReplicaTree.coordinateProfile φ D
  let Ep := ReplicaTree.coordinateProfile φ E
  have h := Cavity.actual_mixed_partials_eq (J Ks) (J (Ks++[Dp])) (J (Ks++[Ep]))
    (J ((Ks++[Dp])++[Dp])) (J ((Ks++[Dp])++[Ep]))
    (J ((Ks++[Ep])++[Dp])) (J ((Ks++[Ep])++[Ep])) U hU h0
    (hc _) (hc _) (hc _) (hc _) (hc _) (hc _)
    (dx Ks) (dy Ks) (dx _) (dy _) (dx _) (dy _)
  have heq : doubleClock q D E (0,0) = q := by
    funext j i
    dsimp [doubleClock]
    ring
  change disorderProfileJets w φ v (doubleClock q D E (0,0)) x
    ((Ks++[Dp])++[Ep]) T P = disorderProfileJets w φ v (doubleClock q D E (0,0)) x
    ((Ks++[Ep])++[Dp]) T P at h
  rw [heq] at h
  simpa only [List.append_assoc,List.singleton_append,Dp,Ep] using h

end OAI.SKFluctuations.Hierarchy
