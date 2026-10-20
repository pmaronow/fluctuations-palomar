module

public import CavityPhysicalForkLawBridge

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

abbrev BareCoordinate (n : ℕ) := Fin n ⊕ Edge n

def endpointCoordinateForward (n : ℕ) : BareCoordinate (n+1) ⊕ Fin 1 → FullCoordinate n
  | .inl (.inl i) => Fin.lastCases (.inr (.inr 0)) (fun j => .inl (.inl (.inr j))) i
  | .inl (.inr e) => match (edgeEquiv n).symm e with
    | .inl f => .inl (.inl (.inl f))
    | .inr i => .inr (.inl i)
  | .inr _ => .inl (.inr 0)

def endpointCoordinateBackward (n : ℕ) : FullCoordinate n → BareCoordinate (n+1) ⊕ Fin 1
  | .inl (.inl (.inl e)) => .inl (.inr (oldEdge e))
  | .inl (.inl (.inr i)) => .inl (.inl i.castSucc)
  | .inl (.inr _) => .inr 0
  | .inr (.inl i) => .inl (.inr (rowEdge i))
  | .inr (.inr _) => .inl (.inl (Fin.last n))

 theorem edgeEquiv_apply_old (n : ℕ) (e : Edge n) : (edgeEquiv n) (.inl e) = oldEdge e := rfl
 theorem edgeEquiv_apply_row (n : ℕ) (i : Fin n) : (edgeEquiv n) (.inr i) = rowEdge i := rfl

 def endpointCoordinateEquiv (n : ℕ) : BareCoordinate (n+1) ⊕ Fin 1 ≃ FullCoordinate n where
  toFun := endpointCoordinateForward n
  invFun := endpointCoordinateBackward n
  left_inv z := by
    rcases z with (i|e)|i
    · refine Fin.lastCases ?_ (fun j => ?_) i <;>
        simp [endpointCoordinateForward,endpointCoordinateBackward]
    · rcases he : (edgeEquiv n).symm e with f|i
      · have h := (edgeEquiv n).apply_symm_apply e
        rw [he,edgeEquiv_apply_old] at h
        simp [endpointCoordinateForward,endpointCoordinateBackward,he,h]
      · have h := (edgeEquiv n).apply_symm_apply e
        rw [he,edgeEquiv_apply_row] at h
        simp [endpointCoordinateForward,endpointCoordinateBackward,he,h]
    · have hi : i=0 := Subsingleton.elim _ _
      subst i
      rfl
  right_inv z := by
    rcases z with ((e|i)|i)|(i|i)
    · have h := (edgeEquiv n).symm_apply_apply (.inl e)
      rw [edgeEquiv_apply_old] at h
      simp [endpointCoordinateForward,endpointCoordinateBackward,h]
    · simp [endpointCoordinateForward,endpointCoordinateBackward]
    · have hi : i=0 := Subsingleton.elim _ _
      subst i
      rfl
    · have h := (edgeEquiv n).symm_apply_apply (.inr i)
      rw [edgeEquiv_apply_row] at h
      simp [endpointCoordinateForward,endpointCoordinateBackward,h]
    · have hi : i=0 := Subsingleton.elim _ _
      subst i
      simp [endpointCoordinateForward,endpointCoordinateBackward]

 def completedCoordinateEquiv (n : ℕ) : BareCoordinate n ⊕ Fin 1 ≃ FeatureIndex n where
  toFun := fun z => match z with
    | .inl (.inl i) => .inl i
    | .inl (.inr e) => .inr (some e)
    | .inr _ => .inr none
  invFun := fun z => match z with
    | .inl i => .inl (.inl i)
    | .inr none => .inr 0
    | .inr (some e) => .inl (.inr e)
  left_inv z := by
    rcases z with (i|e)|i
    · rfl
    · rfl
    · have hi : i=0 := Subsingleton.elim _ _
      subst i
      rfl
  right_inv z := by rcases z with i|(_|e) <;> rfl

 def bareFeature (n : ℕ) (σ : Spin n) : (BareCoordinate n → ℝ) →L[ℝ] ℝ :=
   ∑ i : Fin n, spinValue (σ i) • ContinuousLinearMap.proj (.inl i) +
   ∑ e : Edge n, (spinValue (σ e.val.1)*spinValue (σ e.val.2)/Real.sqrt (n:ℝ)) •
     ContinuousLinearMap.proj (.inr e)

 @[simp] theorem bareFeature_apply (n : ℕ) (σ : Spin n) (x : BareCoordinate n → ℝ) :
    bareFeature n σ x = (∑ i : Fin n, spinValue (σ i)*x (.inl i))+
      ∑ e : Edge n, (spinValue (σ e.val.1)*spinValue (σ e.val.2)/Real.sqrt (n:ℝ))*x (.inr e) := by
  simp [bareFeature]

 theorem completed_restrict_bare (n : ℕ) (σ : Spin n) :
    (reindexFeature (completedCoordinateEquiv n) (finiteFeature n) σ).comp cavityEmbed =
      bareFeature n σ := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,reindexFeature,finiteFeature_apply,
    ContinuousLinearEquiv.coe_coe,coordinateEquiv_apply,featureCoefficient,
    Fintype.sum_sum_type,Fintype.sum_option,liftedCoefficients,bareFeature_apply]
  simp only [completedCoordinateEquiv,Equiv.coe_fn_symm_mk,cavityEmbed_inl,cavityEmbed_inr,mul_zero,zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

 theorem continuous_pi_ext_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : (ι → ℝ) →L[ℝ] ℝ) (h : ∀ i, A (Pi.single i 1)=B (Pi.single i 1)) : A=B := by
  ext x
  have hx : x = ∑ i, x i • Pi.single i 1 := by ext j; simp [Pi.single_apply]
  rw [hx,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,map_smul,h]

 theorem endpoint_restrict_bare (n : ℕ) (σ : Spin n × Bool) :
    (reindexFeature (endpointCoordinateEquiv n) (fullFeature n) σ).comp cavityEmbed =
      bareFeature (n+1) (joinSpin σ) := by
  classical
  apply continuous_pi_ext_one
  intro i
  have hembed : cavityEmbed (Pi.single i (1:ℝ)) =
      Pi.single (.inl i : BareCoordinate (n+1) ⊕ Fin 1) 1 := by
    ext j
    rcases j with j|j <;> simp [cavityEmbed,Pi.single_apply]
  simp only [ContinuousLinearMap.comp_apply,reindexFeature,ContinuousLinearEquiv.coe_coe]
  rw [hembed,coordinateEquiv_single]
  rw [fullFeature_single_any_decidable]
  rcases i with i|e
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [endpointCoordinateEquiv,endpointCoordinateForward,fullCoefficient,dormantCoefficient,
        bareFeature_apply,Pi.single_apply,joinSpin_last,Fin.sum_univ_one]
    · simp [endpointCoordinateEquiv,endpointCoordinateForward,fullCoefficient,restCoefficient,
        bareFeature_apply,Pi.single_apply,joinSpin_old]
  · rcases he : (edgeEquiv n).symm e with f|i
    · have h := (edgeEquiv n).apply_symm_apply e
      rw [he,edgeEquiv_apply_old] at h
      subst e
      have hf := (edgeEquiv n).symm_apply_apply (.inl f)
      rw [edgeEquiv_apply_old] at hf
      simp only [endpointCoordinateEquiv,Equiv.coe_fn_mk,endpointCoordinateForward,hf]
      simp [fullCoefficient,restCoefficient,bareFeature_apply,Pi.single_apply,oldEdge,joinSpin_old]
    · have h := (edgeEquiv n).apply_symm_apply e
      rw [he,edgeEquiv_apply_row] at h
      subst e
      have hi := (edgeEquiv n).symm_apply_apply (.inr i)
      rw [edgeEquiv_apply_row] at hi
      simp only [endpointCoordinateEquiv,Equiv.coe_fn_mk,endpointCoordinateForward,hi]
      simp [fullCoefficient,dormantCoefficient,bareFeature_apply,Pi.single_apply,rowEdge,joinSpin_old,joinSpin_last]
      ring

 def bareClock (n : ℕ) (b h : ℕ → ℝ) (j : ℕ) : BareCoordinate n → ℝ :=
   Sum.elim (fun _ => h j) (fun _ => b j)

 def physicalCompletedClock (n : ℕ) (b h : ℕ → ℝ) (j : ℕ) : FeatureIndex n → ℝ :=
   Sum.elim (fun _ => h j) (fun _ => b j)

 def nullCompletedClock (n : ℕ) (b h : ℕ → ℝ) (j : ℕ) : FeatureIndex n → ℝ :=
   Sum.elim (fun _ => h j) (fun e => match e with | none => 0 | some _ => b j)

 theorem endpointClock_reindex (n U : ℕ) (b h K : ℕ → ℝ) :
    (fun j i => cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j))
      b h K j (endpointCoordinateEquiv n i)) =
    fun j => Sum.elim (bareClock (n+1) b h j) (fun _ : Fin 1 => 0) := by
  funext j i
  rcases i with (i|e)|i
  · refine Fin.lastCases ?_ (fun k => ?_) i <;>
      simp [endpointCoordinateEquiv,endpointCoordinateForward,cavityPath,fullVariance,bareClock]
  · rcases he : (edgeEquiv n).symm e with f|i <;>
      simp [endpointCoordinateEquiv,endpointCoordinateForward,cavityPath,fullVariance,bareClock,he]
  · simp [endpointCoordinateEquiv,endpointCoordinateForward,cavityPath,fullVariance]

 theorem nullCompletedClock_reindex (n : ℕ) (b h : ℕ → ℝ) :
    (fun j i => nullCompletedClock n b h j (completedCoordinateEquiv n i)) =
    fun j => Sum.elim (bareClock n b h j) (fun _ : Fin 1 => 0) := by
  funext j i
  rcases i with (i|e)|i <;> rfl

end OAI.SKFluctuations.Cavity
