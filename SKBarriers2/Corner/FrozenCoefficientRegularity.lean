module

public import SKBarriers2.Corner.FrozenCoef9

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

def NoisePrecisionsPositive (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) : Prop :=
  ∀ D ∈ riccatiPrecisions l Q, 0 < D

private theorem noisePrecisionsPositive_cons (u : ℝ × Vec3) (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) :
    NoisePrecisionsPositive (u :: l) Q ↔
      NoisePrecisionsPositive l Q ∧ 0 < (riccatiRecursion l Q).precision u.1 u.2 := by
  simp only [NoisePrecisionsPositive, riccatiPrecisions, List.mem_cons, forall_eq_or_imp, and_comm]

theorem riccatiRecursion_hessian_contDiffAt {E ι : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List ι) (m : ι → E → ℝ) (v : ι → E → Vec3) (Q : E → QuadraticTerminal) {p : E}
    (hm : ∀ j ∈ l, ContDiffAt ℝ ∞ (m j) p)
    (hv : ∀ j ∈ l, ∀ i, ContDiffAt ℝ ∞ (fun x => v j x i) p)
    (hQ : ∀ i j, ContDiffAt ℝ ∞ (fun x => (Q x).hessian i j) p)
    (hP : NoisePrecisionsPositive (l.map (fun j => (m j p, v j p))) (Q p)) :
    ∀ i j, ContDiffAt ℝ ∞
      (fun x => (riccatiRecursion (l.map (fun j => (m j x, v j x))) (Q x)).hessian i j) p := by
  induction l with
  | nil => exact hQ
  | cons j l ih =>
    have HP := (noisePrecisionsPositive_cons _ _ _).mp hP
    have hH := ih (fun j hj => hm j (List.mem_cons_of_mem _ hj))
      (fun j hj => hv j (List.mem_cons_of_mem _ hj)) HP.1
    have hmj := hm j List.mem_cons_self
    have hvj := hv j List.mem_cons_self
    have hD (i : Fin 3) : ContDiffAt ℝ ∞
        (fun x => (riccatiRecursion (l.map (fun j => (m j x, v j x))) (Q x)).hessianDirection (v j x) i) p := by
      unfold QuadraticTerminal.hessianDirection
      exact ContDiffAt.sum (fun k _ => (hH i k).mul (hvj k))
    have hPrec : ContDiffAt ℝ ∞
        (fun x => (riccatiRecursion (l.map (fun j => (m j x, v j x))) (Q x)).precision (m j x) (v j x)) p := by
      exact contDiffAt_const.sub (hmj.mul (ContDiffAt.sum (fun i _ => (hvj i).mul (hD i))))
    intro i k
    exact (hH i k).add (((hmj.div hPrec (ne_of_gt HP.2)).mul (hD i)).mul (hD k))

private theorem parameter_precision_contDiffAt {E ι : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List ι) (m : ι → E → ℝ) (v : ι → E → Vec3) (Q : E → QuadraticTerminal) {p : E}
    (hm : ∀ j ∈ l, ContDiffAt ℝ ∞ (m j) p)
    (hv : ∀ j ∈ l, ∀ i, ContDiffAt ℝ ∞ (fun x => v j x i) p)
    (hQ : ∀ i j, ContDiffAt ℝ ∞ (fun x => (Q x).hessian i j) p)
    (hP : NoisePrecisionsPositive (l.map (fun j => (m j p, v j p))) (Q p))
    {b : E → ℝ} {w : E → Vec3} (hb : ContDiffAt ℝ ∞ b p)
    (hw : ∀ i, ContDiffAt ℝ ∞ (fun x => w x i) p) :
    ContDiffAt ℝ ∞ (fun x =>
      (riccatiRecursion (l.map (fun j => (m j x, v j x))) (Q x)).precision (b x) (w x)) p := by
  have hH := riccatiRecursion_hessian_contDiffAt l m v Q hm hv hQ hP
  exact contDiffAt_const.sub (hb.mul (ContDiffAt.sum (fun i _ => (hw i).mul
    (ContDiffAt.sum (fun j _ => (hH i j).mul (hw j))))))

theorem gaussianPathLinear_contDiffAt {E ι : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List ι) (m : ι → E → ℝ) (v : ι → E → Vec3) (Q : E → QuadraticTerminal) {p : E}
    (hm : ∀ j ∈ l, ContDiffAt ℝ ∞ (m j) p)
    (hv : ∀ j ∈ l, ∀ i, ContDiffAt ℝ ∞ (fun x => v j x i) p)
    (hQ : ∀ i j, ContDiffAt ℝ ∞ (fun x => (Q x).hessian i j) p)
    (hP : NoisePrecisionsPositive (l.map (fun j => (m j p, v j p))) (Q p))
    (w : E → Vec3) (hw : ∀ i, ContDiffAt ℝ ∞ (fun x => w x i) p) :
    ∀ i, ContDiffAt ℝ ∞
      (fun x => gaussianPathLinear (l.map (fun j => (m j x, v j x))) (Q x) (w x) i) p := by
  induction l generalizing w with
  | nil => exact hw
  | cons j l ih =>
    have HP := (noisePrecisionsPositive_cons _ _ _).mp hP
    have hmt := fun j hj => hm j (List.mem_cons_of_mem _ hj)
    have hvt := fun j hj => hv j (List.mem_cons_of_mem _ hj)
    have hH := riccatiRecursion_hessian_contDiffAt l m v Q hmt hvt hQ HP.1
    have hmj := hm j List.mem_cons_self
    have hvj := hv j List.mem_cons_self
    have hPrec := parameter_precision_contDiffAt l m v Q hmt hvt hQ HP.1 hmj hvj
    apply ih hmt hvt HP.1
    intro i
    exact (hw i).add (((hmj.div hPrec (ne_of_gt HP.2)).mul
      (ContDiffAt.sum (fun k _ => (hw k).mul (ContDiffAt.sum (fun n _ => (hH k n).mul (hvj n)))))).mul
        (hvj i))

theorem noisePrecisionsPositive_isOpen {E ι : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List ι) (m : ι → E → ℝ) (v : ι → E → Vec3) (Q : E → QuadraticTerminal)
    (U : Set E) (hU : IsOpen U)
    (hm : ∀ j ∈ l, ContDiffOn ℝ ∞ (m j) U)
    (hv : ∀ j ∈ l, ∀ i, ContDiffOn ℝ ∞ (fun x => v j x i) U)
    (hQ : ∀ i j, ContDiffOn ℝ ∞ (fun x => (Q x).hessian i j) U) :
    IsOpen {p | p ∈ U ∧ NoisePrecisionsPositive (l.map (fun j => (m j p, v j p))) (Q p)} := by
  induction l with
  | nil => simpa only [List.map_nil, NoisePrecisionsPositive, riccatiPrecisions,
      List.not_mem_nil, false_implies, implies_true, and_true, ofPred_mem_eq] using hU
  | cons j l ih =>
    have hmt := fun j hj => hm j (List.mem_cons_of_mem _ hj)
    have hvt := fun j hj => hv j (List.mem_cons_of_mem _ hj)
    have htail := ih hmt hvt
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have HP := (noisePrecisionsPositive_cons _ _ _).mp hp.2
    have hQat := fun i k => (hQ i k).contDiffAt (hU.mem_nhds hp.1)
    have hmAt := fun j hj => (hmt j hj).contDiffAt (hU.mem_nhds hp.1)
    have hvAt := fun j hj i => (hvt j hj i).contDiffAt (hU.mem_nhds hp.1)
    have hPrec := parameter_precision_contDiffAt l m v Q hmAt hvAt hQat HP.1
      ((hm j List.mem_cons_self).contDiffAt (hU.mem_nhds hp.1))
      (fun i => (hv j List.mem_cons_self i).contDiffAt (hU.mem_nhds hp.1))
    have hpos : ∀ᶠ x in 𝓝 p, 0 <
        (riccatiRecursion (l.map (fun j => (m j x, v j x))) (Q x)).precision (m j x) (v j x) :=
      hPrec.continuousAt.eventually (Ioi_mem_nhds HP.2)
    filter_upwards [htail.mem_nhds ⟨hp.1, HP.1⟩, hpos] with x hx hposx
    exact ⟨hx.1, (noisePrecisionsPositive_cons _ _ _).mpr ⟨hx.2, hposx⟩⟩

end SKBarriers2.Corner
