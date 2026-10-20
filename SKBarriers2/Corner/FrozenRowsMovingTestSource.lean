module

public import SKBarriers2.Corner.FrozenRowsMixedValue
public import SKBarriers2.Corner.FrozenRowsMixed7

@[expose] public section

noncomputable section
open scoped Topology

namespace SKBarriers2

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def movingTestFirstCoefficient (r p : ℕ) (A U : E →L[ℝ] E) (b d v w : E) : ℝ :=
  (1+(2:ℝ)^r)*(1+‖A‖+‖b‖+‖v‖)^(p+1)*
    (1+‖U‖+‖d‖+‖w‖)*max 1 ‖A‖^r

def movingTestCenteredCoefficient (r p : ℕ) (A : E →L[ℝ] E) (b v : E) : ℝ :=
  (1+‖A‖+‖b‖+‖v‖)^(2*p+1)*max 1 ‖A‖^r

theorem movingTestFirstCoefficient_nonneg (r p : ℕ) (A U : E →L[ℝ] E) (b d v w : E) :
    0 ≤ movingTestFirstCoefficient r p A U b d v w := by
  dsimp only [movingTestFirstCoefficient]
  positivity

theorem movingTestCenteredCoefficient_nonneg (r p : ℕ) (A : E →L[ℝ] E) (b v : E) :
    0 ≤ movingTestCenteredCoefficient r p A b v := by
  dsimp only [movingTestCenteredCoefficient]
  positivity

private theorem movingTest_affine_noise_weight (A : E →L[ℝ] E) (b v : E) (t : ℝ) :
    1+‖A‖+‖b+t • v‖ ≤ (1+‖A‖+‖b‖+‖v‖)*(1+|t|) := by
  have H := norm_add_le b (t • v)
  rw [norm_smul,Real.norm_eq_abs] at H
  nlinarith [norm_nonneg A,norm_nonneg b,norm_nonneg v,abs_nonneg t,
    mul_nonneg (norm_nonneg A) (abs_nonneg t),
    mul_nonneg (norm_nonneg b) (abs_nonneg t)]

private theorem movingTest_velocity_weight (U : E →L[ℝ] E) (d w : E) (t : ℝ) :
    ‖U‖+‖d+t • w‖ ≤ (1+‖U‖+‖d‖+‖w‖)*(1+|t|) := by
  have H := norm_add_le d (t • w)
  rw [norm_smul,Real.norm_eq_abs] at H
  nlinarith [norm_nonneg U,norm_nonneg d,norm_nonneg w,abs_nonneg t,
    mul_nonneg (norm_nonneg U) (abs_nonneg t),
    mul_nonneg (norm_nonneg d) (abs_nonneg t)]

theorem WQ.moving_firstSource_jets {r p : ℕ} {B : ℝ} {f a : E → F}
    (hf : WQ (r+1) B p f) (ha : WJets r B (p+1) a)
    (A U : E →L[ℝ] E) (b d v w : E) (t : ℝ) :
    WJets r (B*movingTestFirstCoefficient r p A U b d v w*(1+|t|)^(p+1)) (p+1)
      (fun x => a (A x+b+t • v)+
        fderiv ℝ f (A x+b+t • v) (U x+d+t • w)) := by
  let G := 1+‖A‖+‖b‖+‖v‖
  let H := 1+‖U‖+‖d‖+‖w‖
  let T := 1+|t|
  let M := max 1 ‖A‖^r
  have hB := hf.nonneg
  have hG : 1 ≤ G := by dsimp only [G]; linarith [norm_nonneg A,norm_nonneg b,norm_nonneg v]
  have hH : 1 ≤ H := by dsimp only [H]; linarith [norm_nonneg U,norm_nonneg d,norm_nonneg w]
  have hT : 1 ≤ T := by dsimp only [T]; linarith [abs_nonneg t]
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hgw : 1+‖A‖+‖b+t • v‖ ≤ G*T := movingTest_affine_noise_weight A b v t
  have hvw : ‖U‖+‖d+t • w‖ ≤ H*T := movingTest_velocity_weight U d w t
  have hA := ha.comp_affine A (b+t • v)
  have hD := (hf.derivativeJets.comp_affine A (b+t • v)).clm_apply
    (WJets.affine r U (d+t • w))
  have hbase : B*(1+‖A‖+‖b+t • v‖)^(p+1)*M ≤ B*G^(p+1)*H*M*T^(p+1) := by
    calc
      _ ≤ B*(G*T)^(p+1)*M := by gcongr
      _ ≤ B*(G*T)^(p+1)*M*H := le_mul_of_one_le_right (by positivity) hH
      _ = _ := by rw [mul_pow]; ring
  have hgrad : (2:ℝ)^r*(B*(1+‖A‖+‖b+t • v‖)^p*M)*
      (‖U‖+‖d+t • w‖) ≤ (2:ℝ)^r*(B*G^(p+1)*H*M*T^(p+1)) := by
    calc
      _ ≤ (2:ℝ)^r*(B*(G*T)^p*M)*(H*T) := by gcongr
      _ = (2:ℝ)^r*(B*G^p*H*M*T^(p+1)) := by rw [mul_pow,pow_succ]; ring
      _ ≤ _ := by gcongr; omega
  have HS := (hA.mono hbase le_rfl).add (hD.mono hgrad (by omega))
  convert HS using 1
  · dsimp only [movingTestFirstCoefficient,G,H,T,M]
    ring
  · funext x
    simp only [add_assoc]

theorem WQ.moving_firstSource_contDiff {r p : ℕ} {B : ℝ} {f a : E → F}
    (hf : WQ (r+1) B p f) (ha : WJets r B (p+1) a)
    (A U : E →L[ℝ] E) (b d v w : E) :
    ContDiff ℝ r (fun z : ℝ × E => a (A z.2+b+z.1 • v)+
      fderiv ℝ f (A z.2+b+z.1 • v) (U z.2+d+z.1 • w)) := by
  have he : ContDiff ℝ r (fun z : ℝ × E => A z.2+b+z.1 • v) := by fun_prop
  have hv : ContDiff ℝ r (fun z : ℝ × E => U z.2+d+z.1 • w) := by fun_prop
  exact (ha.smooth.comp he).add ((hf.derivativeJets.smooth.comp he).clm_apply hv)

theorem WQ.affine_noise_centered_jets {r p : ℕ} {B : ℝ} {f : E → F}
    (hf : WQ (r+1) B p f) (A : E →L[ℝ] E) (b v : E) (t : ℝ) :
    WJets r (B*movingTestCenteredCoefficient r p A b v*(1+|t|)^(p+1)) p
      (fun x => f (A x+b+t • v)-f (A x+b)) := by
  let G := 1+‖A‖+‖b‖+‖v‖
  let T := 1+|t|
  let M := max 1 ‖A‖^r
  have hB := hf.nonneg
  have hG : 1 ≤ G := by dsimp only [G]; linarith [norm_nonneg A,norm_nonneg b,norm_nonneg v]
  have hT : 1 ≤ T := by dsimp only [T]; linarith [abs_nonneg t]
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hv : ‖v‖ ≤ G := by dsimp only [G]; linarith [norm_nonneg A,norm_nonneg b]
  have hnorm : ‖t • v‖ ≤ T*G := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (by dsimp only [T]; linarith [abs_nonneg t]) hv (norm_nonneg v) (by positivity)
  have hnoise : 1+‖t • v‖ ≤ G*T := by
    rw [norm_smul,Real.norm_eq_abs]
    nlinarith only [hG,mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hv)]
  have hgeom : 1+‖A‖+‖b‖ ≤ G := by dsimp only [G]; linarith [norm_nonneg v]
  have H := (hf.increment (t • v)).comp_affine A b
  apply H.mono _ le_rfl
  calc
    _ ≤ B*(T*G)*(G*T)^p*G^p*M := by gcongr
    _ = _ := by
      dsimp only [movingTestCenteredCoefficient,G,T,M]
      rw [show 2*p+1 = p+p+1 by omega]
      simp only [mul_pow,pow_add,pow_one]
      ring

theorem WQ.affine_noise_centered_contDiff {r p : ℕ} {B : ℝ} {f : E → F}
    (hf : WQ (r+1) B p f) (A : E →L[ℝ] E) (b v : E) :
    ContDiff ℝ r (fun z : ℝ × E => f (A z.2+b+z.1 • v)-f (A z.2+b)) := by
  have hs : ContDiff ℝ r f := hf.smooth.of_le (by exact_mod_cast Nat.le_succ r)
  exact (hs.comp (by fun_prop)).sub (hs.comp (by fun_prop))

theorem DegreeJets.moving_firstSource {r p : ℕ} {B : ℝ} {f a : E → ℝ}
    (hf : DegreeJets (r+1) B p f) (ha : WJets (r+1) B (p+1) a)
    (A U : E →L[ℝ] E) (b d v w : E) :
    ContDiff ℝ r (fun z : ℝ × E => a (A z.2+b+z.1 • v)+
      fderiv ℝ f (A z.2+b+z.1 • v) (U z.2+d+z.1 • w)) ∧
      ∀ t : ℝ, WJets r
        (B*movingTestFirstCoefficient r p A U b d v w*(1+|t|)^(p+1)) (p+1)
        (fun x => a (A x+b+t • v)+fderiv ℝ f (A x+b+t • v) (U x+d+t • w)) :=
  ⟨hf.positive.moving_firstSource_contDiff (ha.of_le (Nat.le_succ r)) A U b d v w,
    fun t => hf.positive.moving_firstSource_jets (ha.of_le (Nat.le_succ r)) A U b d v w t⟩

end SKBarriers2
