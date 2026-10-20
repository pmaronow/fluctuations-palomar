module

public import CavityProfileJetSwap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

private theorem ClockTree.actual_head_swap_strict {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q D E : ℕ → ι → ℝ) {epsilon B : ℝ}
    (he : 0 < epsilon) (hB : 0 ≤ B) (hq : strictCumulativeClock v q epsilon)
    (hD : ∀ j i, |D j i| ≤ B) (hE : ∀ j i, |E j i| ≤ B)
    (Ds : List (ℕ → ι → ℝ)) (hDs : ∀ F ∈ Ds, ∀ j i, |F j i| ≤ B)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    disorderProfileJets w φ v q x ((D::E::Ds).map (ReplicaTree.coordinateProfile φ)) T P =
    disorderProfileJets w φ v q x ((E::D::Ds).map (ReplicaTree.coordinateProfile φ)) T P := by
  induction Ds using List.reverseRecOn generalizing q epsilon with
  | nil =>
    exact T.actual_profileJet_append_swap_strict hw φ ho v q D E he hB hq hD hE [] P x
  | append_singleton Ds F ih =>
    have hF : ∀ j i, |F j i| ≤ B := hDs F (by simp)
    have hOld : ∀ G ∈ Ds, ∀ j i, |G j i| ≤ B := fun G hG => hDs G (by simp [hG])
    let R := epsilon/(2*(2*B+1))
    have hR : 0 < R := by dsimp [R]; positivity
    have hpert (s : ℝ) (hs : s ∈ Ioo (-R) R) :
        strictCumulativeClock v (fun j i => q j i+s*F j i) (epsilon/2) := by
      apply strictCumulativeClock_perturb he hB hq hF
      have ha : |s| < R := (abs_lt).2 hs
      have h := (lt_div_iff₀ (by positivity : 0 < 2*(2*B+1))).mp ha
      linarith
    have hmono : ∀ s ∈ Ioo (-R) R, ∀ i, Monotone (fun j => q j i+s*F j i) :=
      fun s hs i => (hpert s hs).monotone (by positivity) i
    have hroot : ∀ s ∈ Ioo (-R) R, ∀ i, v i ≤ q 0 i+s*F 0 i := by
      intro s hs i
      have H := (hpert s hs).1 i
      linarith
    have h0 : (0:ℝ) ∈ Ioo (-R) R := by constructor <;> linarith
    have hL := hasDerivAt_finiteProfileJets hw φ ho v q F hmono hroot
      ((D::E::Ds).map (ReplicaTree.coordinateProfile φ)) T P x h0
    have hR' := hasDerivAt_finiteProfileJets hw φ ho v q F hmono hroot
      ((E::D::Ds).map (ReplicaTree.coordinateProfile φ)) T P x h0
    have hf : (fun s => disorderProfileJets w φ v (fun j i => q j i+s*F j i) x
        ((D::E::Ds).map (ReplicaTree.coordinateProfile φ)) T P) =ᶠ[𝓝 (0:ℝ)]
        (fun s => disorderProfileJets w φ v (fun j i => q j i+s*F j i) x
          ((E::D::Ds).map (ReplicaTree.coordinateProfile φ)) T P) := by
      filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
      exact ih (fun j i => q j i+s*F j i) (by positivity) (hpert s hs) hOld
    have H := hf.deriv_eq
    rw [hL.deriv,hR'.deriv] at H
    simpa only [List.map_cons,List.map_append,List.map_singleton,zero_mul,add_zero,
      List.cons_append,List.map_nil] using H

theorem ClockTree.actual_profileJets_perm_strict {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) {epsilon B : ℝ}
    (he : 0 < epsilon) (hB : 0 ≤ B) (hq : strictCumulativeClock v q epsilon)
    {Ds Es : List (ℕ → ι → ℝ)} (hperm : Ds.Perm Es)
    (hDs : ∀ D ∈ Ds, ∀ j i, |D j i| ≤ B)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P =
    disorderProfileJets w φ v q x (Es.map (ReplicaTree.coordinateProfile φ)) T P := by
  induction hperm generalizing T with
  | nil => rfl
  | @cons F Ds Es hperm ih =>
    have hOld : ∀ D ∈ Ds, ∀ j i, |D j i| ≤ B :=
      fun D hD => hDs D (List.mem_cons_of_mem F hD)
    simp only [List.map_cons,disorderProfileJets]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    rw [ih r.tree hOld]
  | swap D E Ds =>
    exact T.actual_head_swap_strict hw φ ho v q E D he hB hq
      (hDs E (by simp)) (hDs D (by simp)) Ds
      (fun F hF => hDs F (by simp [hF])) P x
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ T hDs P).trans (ih₂ T
      (fun D hD => hDs D (h₁.mem_iff.mpr hD)) P)

theorem ClockTree.actual_profileJets_perm {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (hq : ∀ i, Monotone (fun j => q j i))
    (hq0 : ∀ i, v i ≤ q 0 i) {Ds Es : List (ℕ → ι → ℝ)}
    {B : ℝ} (hB : 0 ≤ B) (hperm : Ds.Perm Es)
    (hDs : ∀ D ∈ Ds, ∀ j i, |D j i| ≤ B)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P =
    disorderProfileJets w φ v q x (Es.map (ReplicaTree.coordinateProfile φ)) T P := by
  let qr := fun e : ℝ => fun j i => q j i+e*(j+1:ℕ)
  have hf : EqOn (fun e => disorderProfileJets w φ v (qr e) x
      (Ds.map (ReplicaTree.coordinateProfile φ)) T P)
      (fun e => disorderProfileJets w φ v (qr e) x
        (Es.map (ReplicaTree.coordinateProfile φ)) T P) (Ioi (0:ℝ)) := by
    intro e he
    exact T.actual_profileJets_perm_strict hw φ ho v (qr e) he hB
      (strictCumulativeClock_regularize hq hq0 he.le) hperm hDs P x
  have hc (j : ℕ) : Continuous (fun e => qr e j) := by dsimp [qr]; fun_prop
  have hL := disorderProfileJets_continuous hw φ ho v qr hc (fun _ => x) continuous_const
    (Ds.map (ReplicaTree.coordinateProfile φ)) T P
  have hR := disorderProfileJets_continuous hw φ ho v qr hc (fun _ => x) continuous_const
    (Es.map (ReplicaTree.coordinateProfile φ)) T P
  have h0 : (0:ℝ) ∈ closure (Ioi (0:ℝ)) := by
    simpa only [closure_Ioi,mem_Ici] using (le_rfl : (0:ℝ) ≤ 0)
  have H := hf.closure hL hR h0
  simpa only [qr,zero_mul,add_zero] using H

end OAI.SKFluctuations.Hierarchy
