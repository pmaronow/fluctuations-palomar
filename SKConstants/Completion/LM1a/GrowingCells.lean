module
public import SKConstants.Completion.LC0.PathConcatenation
public import SKConstants.Completion.LC0.SourceReplay

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal Topology
namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

def piLast {n : ℕ} (α : Fin (n+1) → Type*) [∀ i, MeasurableSpace (α i)] :
    ((i : Fin (n+1)) → α i) ≃ᵐ α (Fin.last n) × ((i : Fin n) → α i.castSucc) where
  toFun f := (f (Fin.last n), fun i => f i.castSucc)
  invFun p := Fin.snoc p.2 p.1
  left_inv f := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := (measurable_pi_apply _).prodMk
    (Measurable.of_eval (fun i => measurable_pi_apply i.castSucc))
  measurable_invFun := by
    simp only [Equiv.coe_fn_symm_mk]
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using (measurable_fst : Measurable (Prod.fst :
        α (Fin.last n) × ((i : Fin n) → α i.castSucc) → α (Fin.last n)))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using ((measurable_pi_apply j).comp measurable_snd :
        Measurable (fun p : α (Fin.last n) × ((i : Fin n) → α i.castSucc) => p.2 j))

theorem piLast_law {n : ℕ} {α : Fin (n+1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : (i : Fin (n+1)) → Measure (α i))
    [∀ i, SigmaFinite (μ i)] :
    (Measure.pi μ).map (piLast α) =
      (μ (Fin.last n)).prod (Measure.pi (fun i : Fin n => μ i.castSucc)) := by
  have h : MeasurePreserving (piLast α).symm
      ((μ (Fin.last n)).prod (Measure.pi (fun i : Fin n => μ i.castSucc)))
      (Measure.pi μ) := by
    refine ⟨(piLast α).symm.measurable, (Measure.pi_eq (fun s hs => ?_)).symm⟩
    rw [(piLast α).symm.map_apply]
    have he : (piLast α).symm ⁻¹' Set.univ.pi s =
        s (Fin.last n) ×ˢ Set.univ.pi (fun i : Fin n => s i.castSucc) := by
      ext p
      simp only [piLast, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
        Equiv.coe_fn_symm_mk, Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
      rw [Fin.forall_iff_castSucc]
      simp
    rw [he, Measure.prod_prod, Measure.pi_pi]
    rw [Fin.prod_univ_castSucc, mul_comm]
  exact h.symm.map_eq

theorem growingQueryTime_monotone (δ : ℝ≥0) : Monotone (growingQueryTime δ) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [growingQueryTime_succ]
  exact le_self_add

def GrowingCell (δ : ℝ≥0) (q : ℕ) (j : Fin (q+1))
    (b : ScalarContinuousPath (Horizon δ q)) :
    ScalarContinuousPath (growingQueryDuration δ j.val) :=
  ⟨fun u => b ⟨(growingQueryTime δ j.val : ℝ)+u,
      add_nonneg (growingQueryTime δ j.val).coe_nonneg u.property.1,
      by
        have hu := u.property.2
        have ht := growingQueryTime_monotone δ (Nat.succ_le_of_lt j.isLt)
        rw [growingQueryTime_succ] at ht
        change _ ≤ (growingQueryTime δ (q+1) : ℝ)
        have hu' : (growingQueryTime δ j.val : ℝ) + u ≤
            (growingQueryTime δ j.val : ℝ) + growingQueryDuration δ j.val :=
          by linarith
        exact hu'.trans (by exact_mod_cast ht)⟩ -
    b ⟨growingQueryTime δ j.val,(growingQueryTime δ j.val).coe_nonneg,
      by exact_mod_cast growingQueryTime_monotone δ (Nat.le_of_lt j.isLt)⟩,
    (b.continuous.comp (by fun_prop)).sub continuous_const⟩

theorem measurable_GrowingCell (δ : ℝ≥0) (q : ℕ) (j : Fin (q+1)) :
    Measurable (GrowingCell δ q j) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro u
  exact (ContinuousMap.measurable_eval _).sub (ContinuousMap.measurable_eval _)

theorem GrowingCell_zero (δ : ℝ≥0) (q : ℕ) (j : Fin (q+1))
    (b : ScalarContinuousPath (Horizon δ q)) :
    GrowingCell δ q j b ⟨0,le_rfl,(growingQueryDuration δ j.val).coe_nonneg⟩ = 0 := by
  simp [GrowingCell]

theorem GrowingCell_last (δ : ℝ≥0) (q : ℕ)
    (b : ScalarContinuousPath (Horizon δ (q+1))) :
    GrowingCell δ (q+1) (Fin.last (q+1)) b =
      (scalarSplitPath (Horizon δ q) (growingQueryDuration δ (q+1)) b).2 := by
  ext u
  rfl

theorem GrowingCell_prefix (δ : ℝ≥0) (q : ℕ) (j : Fin (q+1))
    (b : ScalarContinuousPath (Horizon δ (q+1))) :
    GrowingCell δ (q+1) j.castSucc b =
      GrowingCell δ q j
        (scalarSplitPath (Horizon δ q) (growingQueryDuration δ (q+1)) b).1 := by
  ext u
  rfl

theorem scalarPrimitiveBrownianRestriction_law (W : BrownianSystem Ω)
    (H h : ℝ≥0) (hh : h ≤ H) :
    (scalarPrimitiveBrownianPathLaw W H).map
      (scalarInitialAuxiliaryRestriction H h hh) = scalarPrimitiveBrownianPathLaw W h := by
  unfold scalarPrimitiveBrownianPathLaw
  rw [Measure.map_map (measurable_scalarInitialAuxiliaryRestriction H h hh)
    (measurable_scalarPrimitiveBrownianPathVersion W H)]
  apply Measure.map_congr
  filter_upwards [scalarPrimitiveBrownianPathVersion_ae W H,
    scalarPrimitiveBrownianPathVersion_ae W h] with ω hH hh'
  ext t
  exact (hH _).trans (hh' t).symm

theorem growingBrownianCells_law (W : BrownianSystem Ω) (δ : ℝ≥0) (q : ℕ) :
    (scalarPrimitiveBrownianPathLaw W (Horizon δ q)).map
      (fun b j => GrowingCell δ q j b) =
      Measure.pi (fun j : Fin (q+1) =>
        scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ j.val)) := by
  induction q with
  | zero =>
    have hH : Horizon δ 0 = growingQueryDuration δ 0 := by
      simp [Horizon, scalarGrowingSourceHorizon, growingQueryTime_succ,
        growingQueryTime_zero]
    let e0 := MeasurableEquiv.piUnique (fun j : Fin 1 =>
      ScalarContinuousPath (growingQueryDuration δ j.val))
    apply (MeasurableEquiv.map_measurableEquiv_injective e0).eq_iff.mp
    rw [Measure.map_map e0.measurable
      (Measurable.of_eval (fun j => measurable_GrowingCell δ 0 j)),
      (measurePreserving_piUnique (fun j : Fin 1 =>
        scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ j.val))).map_eq]
    have he : (fun b : ScalarContinuousPath (Horizon δ 0) => GrowingCell δ 0 0 b) =ᵐ[
        scalarPrimitiveBrownianPathLaw W (Horizon δ 0)]
        scalarInitialAuxiliaryRestriction (Horizon δ 0) (growingQueryDuration δ 0)
          hH.ge := by
      filter_upwards [scalarPrimitiveBrownianPathLaw_zero_ae W (Horizon δ 0)] with b hb
      ext t
      simp [GrowingCell, growingQueryTime_zero, scalarInitialAuxiliaryRestriction, hb]
    change (scalarPrimitiveBrownianPathLaw W (Horizon δ 0)).map
      (fun b => GrowingCell δ 0 0 b) = _
    rw [Measure.map_congr he]
    exact scalarPrimitiveBrownianRestriction_law W _ _ hH.ge
  | succ q ih =>
    let e := piLast (fun j : Fin (q+1+1) =>
      ScalarContinuousPath (growingQueryDuration δ j.val))
    apply (MeasurableEquiv.map_measurableEquiv_injective e).eq_iff.mp
    rw [Measure.map_map e.measurable
      (Measurable.of_eval (fun j => measurable_GrowingCell δ (q+1) j)),
      piLast_law]
    have he : e ∘ (fun b j => GrowingCell δ (q+1) j b) =
        (fun p => (p.2,fun j => GrowingCell δ q j p.1)) ∘
          scalarSplitPath (Horizon δ q) (growingQueryDuration δ (q+1)) := by
      funext b
      apply Prod.ext
      · exact GrowingCell_last δ q b
      · funext j
        exact GrowingCell_prefix δ q j b
    change (scalarPrimitiveBrownianPathLaw W
      (Horizon δ q + growingQueryDuration δ (q+1))).map _ = _
    rw [he]
    have hm : Measurable (fun p : ScalarContinuousPath (Horizon δ q) ×
        ScalarContinuousPath (growingQueryDuration δ (q+1)) =>
        (p.2,fun j => GrowingCell δ q j p.1)) :=
      measurable_snd.prodMk (Measurable.of_eval (fun j =>
        (measurable_GrowingCell δ q j).comp measurable_fst))
    rw [← Measure.map_map hm (measurable_scalarSplitPath _ _), scalarBrownianSplit_law W]
    have hs := (Measure.measurePreserving_swap
      (μ := scalarPrimitiveBrownianPathLaw W (Horizon δ q))
      (ν := scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ (q+1)))).map_eq
    have hp := Measure.map_prod_map
      (scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ (q+1)))
      (scalarPrimitiveBrownianPathLaw W (Horizon δ q)) measurable_id
      (Measurable.of_eval (fun j => measurable_GrowingCell δ q j))
    rw [Measure.map_id, ih] at hp
    rw [show (fun p => (p.2,fun j => GrowingCell δ q j p.1)) =
      Prod.map id (fun b j => GrowingCell δ q j b) ∘ Prod.swap from rfl,
      ← Measure.map_map (measurable_id.prodMap
        (Measurable.of_eval (fun j => measurable_GrowingCell δ q j))) measurable_swap, hs]
    exact hp.symm

end SKConstants.M1
