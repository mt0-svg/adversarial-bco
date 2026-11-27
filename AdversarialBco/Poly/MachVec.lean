/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachVL

@[expose] public section

/-!
# The machine layer, part 3: vector and matrix macros

Programs of `MachVL.lean` on whole vectors and matrices, each with its rule: the result as a function of the
environment, the variables it changes (`Frame`) and its number of steps. Vectors and matrices are arrays read by
`Env.vec` and `Env.mat`; every loop runs over `i < d` with a natural variable `dv` holding `d` and `one` holding `1`.
-/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.RealRAM Matrix

variable {d : ℕ} {L : Layout} {w : World d}

theorem lt_asz {k : ℕ} (hk : k < d) : k < asz d := by unfold asz; omega

/-! ## Frames -/

theorem Env.Frame.refl (σ : Env d) (ns ss as : List ℕ) : σ.Frame σ ns ss as :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Env.Frame.mono {σ σ' : Env d} {ns ss as ns' ss' as' : List ℕ} (h : σ.Frame σ' ns ss as)
    (hn : ∀ i ∈ ns, i ∈ ns') (hs : ∀ x ∈ ss, x ∈ ss') (ha : ∀ a ∈ as, a ∈ as') : σ.Frame σ' ns' ss' as' :=
  ⟨fun i hi => h.1 i (fun h' => hi (hn i h')), fun x hx => h.2.1 x (fun h' => hx (hs x h')),
    fun a ha' => h.2.2.1 a (fun h' => ha' (ha a h')), h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem Env.Frame.trans {σ σ' σ'' : Env d} {ns ss as : List ℕ} (h : σ.Frame σ' ns ss as)
    (h' : σ'.Frame σ'' ns ss as) : σ.Frame σ'' ns ss as :=
  ⟨fun i hi => (h'.1 i hi).trans (h.1 i hi), fun x hx => (h'.2.1 x hx).trans (h.2.1 x hx),
    fun a ha => (h'.2.2.1 a ha).trans (h.2.2.1 a ha), h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

theorem Env.Frame.setSc {σ σ' : Env d} {ns ss as : List ℕ} (h : σ.Frame σ' ns ss as) {x : ℕ} (hx : x ∈ ss)
    (v : ℝ) : σ.Frame (σ'.setSc x v) ns ss as :=
  ⟨fun i hi => h.1 i hi, fun y hy => by
      have hyx : y ≠ x := fun e => hy (e ▸ hx)
      simp only [Env.setSc_sc, hyx, ite_false]; exact h.2.1 y hy,
    fun a ha => h.2.2.1 a ha, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem Env.Frame.setNat {σ σ' : Env d} {ns ss as : List ℕ} (h : σ.Frame σ' ns ss as) {i : ℕ} (hi : i ∈ ns)
    (v : ℕ) : σ.Frame (σ'.setNat i v) ns ss as :=
  ⟨fun j hj => by
      have hji : j ≠ i := fun e => hj (e ▸ hi)
      simp only [Env.setNat_nat, hji, ite_false]; exact h.1 j hj, fun y hy => h.2.1 y hy,
    fun a ha => h.2.2.1 a ha, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `‖x‖` in `E d` through the dot product. -/
theorem norm_toLp_eq (x : Fin d → ℝ) : ‖WithLp.toLp 2 x‖ = Real.sqrt (x ⬝ᵥ x) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq]

/-- `y := y + α x` on vectors (`x = y` allowed); loop variable `i`, temporaries `t1`, `t2`. -/
def vaxpy (L : Layout) (dv one i y x α t1 t2 : ℕ) : Cmd :=
  forN i dv one
    (.seq (aget L t1 x i) (.seq (sop2 L .mul t1 α t1) (.seq (aget L t2 y i) (.seq (sop2 L .add t2 t2 t1)
      (aset L y i t2)))))

theorem runs_vaxpy {dv one i y x α t1 t2 : ℕ} (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN)
    (hy : y < L.NA) (hx : x < L.NA) (hα : α < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hidv : i ≠ dv)
    (hione : i ≠ one) (h12 : t1 ≠ t2) (hα1 : α ≠ t1) (hα2 : α ≠ t2) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (vaxpy L dv one i y x α t1 t2) σ (d * 11 + 3)
      (fun σ' => σ'.vec y = σ.vec y + σ.sc α • σ.vec x ∧ Env.Frame σ σ' [i] [t1, t2] [y] ∧
        ∀ k, d ≤ k → σ'.arr y k = σ.arr y k) := by
  let J : ℕ → Env d → Prop := fun t σ' =>
    (∀ k, σ'.arr y k = if k < t then σ.arr y k + σ.sc α * σ.arr x k else σ.arr y k) ∧
      (∀ b, b ≠ y → σ'.arr b = σ.arr b) ∧ (∀ z, z ≠ t1 → z ≠ t2 → σ'.sc z = σ.sc z) ∧
      (∀ j, j ≠ i → σ'.nat j = σ.nat j) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := .seq (aget L t1 x i) (.seq (sop2 L .mul t1 α t1)
      (.seq (aget L t2 y i) (.seq (sop2 L .add t2 t2 t1) (aset L y i t2))))) hi hdv hone hidv hione d 8 J σ hd h1
    ⟨fun k => by simp, fun b _ => rfl, fun z _ _ => rfl, fun j hj => by simp [hj], rfl, rfl, rfl⟩
    (fun t ht σ' hJ hit hdt hot => by
      obtain ⟨Jy, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      have hk : σ'.nat i < asz d := by rw [hit]; exact lt_asz ht
      have hxt : σ'.arr x t = σ.arr x t := by
        by_cases hxy : x = y
        · subst hxy; rw [Jy]; simp
        · rw [Jb x hxy]
      have hyt : σ'.arr y t = σ.arr y t := by rw [Jy]; simp
      refine runs_mono (runs_seq_eq (runs_aget (w := w) (σ := σ') ht1 hx hi hk) <|
        runs_seq_eq (runs_sop2 ht1 hα ht1 .mul) <|
        runs_seq_eq (runs_aget ht2 hy hi (by simpa using hk)) <|
        runs_seq_eq (runs_sop2 ht2 ht2 ht1 .add) <|
        runs_aset hy hi ht2 (by simpa using hk)) (by norm_num) (fun σ5 e5 => ?_)
      subst e5
      simp only [Env.setArr_nat, Env.setSc_nat, hit, hdt, hot, true_and]
      refine ⟨fun k => ?_, fun b hb => ?_, fun z hz1 hz2 => ?_, fun j hj => ?_, Jd, Jr, Jp⟩
      · simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_sc, hxt, hyt]
        by_cases hkt : k = t
        · subst hkt; simp [Op2.eval, h12, hα1, Js α hα1 hα2]
        · rw [Jy]
          by_cases hk' : k < t
          · simp [hkt, hk', show k < t + 1 by omega]
          · simp [hkt, hk', show ¬ k < t + 1 by omega]
      · funext k; simp [hb, Jb b hb]
      · simp [Env.setNat_sc, hz1, hz2, Js z hz1 hz2]
      · simp [hj, Jn j hj])
  refine runs_mono hfor (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨Jy, Jb, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ⟨fun j hj => Jn j (by simpa using hj), fun z hz => Js z (by simp at hz; tauto) (by simp at hz; tauto),
    fun b hb => Jb b (by simpa using hb), Jd, Jr, Jp⟩, fun k hk => by rw [Jy]; simp; omega⟩
  funext k
  simp [Env.vec, Jy, k.2]

/-! ## The other macros -/

/-- `y[i] := z` for `i < d`. -/
def vfill (L : Layout) (dv one i y z : ℕ) : Cmd := forN i dv one (aset L y i z)

/-- `y := x`. -/
def vcopy (L : Layout) (dv one i y x t : ℕ) : Cmd := forN i dv one (.seq (aget L t x i) (aset L y i t))

/-- `y := α y`. -/
def vscale (L : Layout) (dv one i y α t : ℕ) : Cmd :=
  forN i dv one (.seq (aget L t y i) (.seq (sop2 L .mul t α t) (aset L y i t)))

/-- `r := ⟨x, y⟩`. -/
def vdot (L : Layout) (dv one i r x y t1 t2 : ℕ) : Cmd :=
  .seq (sconst L r 0) (forN i dv one
    (.seq (aget L t1 x i) (.seq (aget L t2 y i) (.seq (sop2 L .mul t1 t1 t2) (sop2 L .add r r t1)))))

/-- `y[i] :=` the next Gaussian draw, for `i < d`. -/
def vgauss (L : Layout) (dv one i y t : ℕ) : Cmd := forN i dv one (.seq (gauss L t) (aset L y i t))

/-- `r := tr A`, with the index `k = (d + 1) i`. -/
def mtrace (L : Layout) (dv one i k r A t : ℕ) : Cmd :=
  .seq (sconst L r 0) (.seq (nconst k 0) (forN i dv one
    (.seq (aget L t A k) (.seq (sop2 L .add r r t) (.seq (nadd k k dv) (nadd k k one))))))

/-- `y := A x` (`y ≠ x`), with the index `k = d i + j` and the accumulator `s`. -/
def matvec (L : Layout) (dv one i j k y A x s t1 t2 : ℕ) : Cmd :=
  .seq (nconst k 0) (forN i dv one
    (.seq (sconst L s 0) (.seq (forN j dv one
      (.seq (aget L t1 A k) (.seq (aget L t2 x j) (.seq (sop2 L .mul t1 t1 t2) (.seq (sop2 L .add s s t1)
        (nadd k k one))))))
      (aset L y i s))))

/-- `A := α A + β u vᵀ`, with the index `k = d i + j`. -/
def rankOne (L : Layout) (dv one i j k A α β u v t1 t2 t3 : ℕ) : Cmd :=
  .seq (nconst k 0) (forN i dv one (forN j dv one
    (.seq (aget L t1 A k) (.seq (sop2 L .mul t1 α t1) (.seq (aget L t2 u i) (.seq (sop2 L .mul t2 β t2)
      (.seq (aget L t3 v j) (.seq (sop2 L .mul t2 t2 t3) (.seq (sop2 L .add t1 t1 t2)
        (.seq (aset L A k t1) (nadd k k one)))))))))))

/-- `dd := d²`. -/
def nsq (dv one i dd : ℕ) : Cmd := .seq (nconst dd 0) (forN i dv one (nadd dd dd dv))

/-- `B[m] := A[m]` for `m < d²` (`dd` holds `d²`). -/
def mcopy (L : Layout) (dd one m B A t : ℕ) : Cmd := forN m dd one (.seq (aget L t A m) (aset L B m t))

/-- `A[m] := z` for `m < d²` (`dd` holds `d²`). -/
def mfill (L : Layout) (dd one m A z : ℕ) : Cmd := forN m dd one (aset L A m z)

/-- `A[(d + 1) i] := z` for `i < d`: the diagonal. -/
def mdiag (L : Layout) (dv one i k A z : ℕ) : Cmd :=
  .seq (nconst k 0) (forN i dv one (.seq (aset L A k z) (.seq (nadd k k dv) (nadd k k one))))

/-- `r := |x|`, the Euclidean norm. -/
def vnorm (L : Layout) (dv one i r x t1 t2 : ℕ) : Cmd := .seq (vdot L dv one i r x x t1 t2) (sop1 L .sqrt r r)

/-- `o := 1` if `μ + T y ∈ K`, else `0`: `tmp := T y` (`tmp` distinct from `y`, `T`, `μ`), `c := 1`, `tmp := tmp + c μ`,
then the membership query of `tmp`. -/
def memAff (L : Layout) (dv one i j k o mu T y tmp c s t1 t2 : ℕ) : Cmd :=
  .seq (matvec L dv one i j k tmp T y s t1 t2) (.seq (sconst L c 1) (.seq (vaxpy L dv one i tmp mu c t1 t2)
    (query L o tmp)))

/-- `C := A B` (`C ≠ A`, `C ≠ B`), with the indices `kA = d i + l`, `kB = d l + j`, `kC = d i + j`. -/
def mmul (L : Layout) (dv one i j l kA kB kC C A B s t1 t2 : ℕ) : Cmd :=
  .seq (nconst kC 0) (forN i dv one (forN j dv one
    (.seq (sconst L s 0) (.seq (nsub kA kC j) (.seq (nsub kB kC kA) (.seq (forN l dv one
      (.seq (aget L t1 A kA) (.seq (aget L t2 B kB) (.seq (sop2 L .mul t1 t1 t2) (.seq (sop2 L .add s s t1)
        (.seq (nadd kA kA one) (nadd kB kB dv)))))))
      (.seq (aset L C kC s) (nadd kC kC one))))))))

/-- `B := Aᵀ` (`B ≠ A`), with the indices `kA = d j + i`, `kB = d i + j`. -/
def mtransp (L : Layout) (dv one i j kA kB B A t : ℕ) : Cmd :=
  .seq (nconst kB 0) (forN i dv one (.seq (nconst kA 0) (.seq (nadd kA kA i) (forN j dv one
    (.seq (aget L t A kA) (.seq (aset L B kB t) (.seq (nadd kA kA dv) (nadd kB kB one))))))))

/-- `C := α A + β B` on the entries `m < d²` (`dd` holds `d²`; `C` may be `A` or `B`). -/
def mlin (L : Layout) (dd one m C A B α β t1 t2 : ℕ) : Cmd :=
  forN m dd one (.seq (aget L t1 A m) (.seq (sop2 L .mul t1 α t1) (.seq (aget L t2 B m) (.seq (sop2 L .mul t2 β t2)
    (.seq (sop2 L .add t1 t1 t2) (aset L C m t1))))))

/-! ## Scalar macros -/

/-- `x := y`, through the cell that holds `0`. -/
def smov (L : Layout) (x y : ℕ) : Cmd := .prim (.op2 .add (L.rS x) (L.rS y) L.rZ)

theorem runs_smov {σ : Env d} {x y : ℕ} (hx : x < L.NS) (hy : y < L.NS) :
    Runs L w (smov L x y) σ 1 (· = σ.setSc x (σ.sc y)) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _
      { s with
        mem := Function.update s.mem (s.nreg (L.rS x))
          (Op2.eval .add (s.mem (s.nreg (L.rS y))) (s.mem (s.nreg L.rZ))) }
    rw [hs.rS x hx, hs.rS y hy, hs.sc y hy, hs.rZ, hs.zero, Op2.eval, add_zero]; exact hs.setSc hx _, rfl⟩

/-- `z := max x y`. -/
def smax (L : Layout) (z x y : ℕ) : Cmd := ifS L x y (smov L z y) (smov L z x)

/-- `z := min x y`. -/
def smin (L : Layout) (z x y : ℕ) : Cmd := ifS L x y (smov L z x) (smov L z y)

theorem runs_smax {σ : Env d} {z x y : ℕ} (hz : z < L.NS) (hx : x < L.NS) (hy : y < L.NS) :
    Runs L w (smax L z x y) σ 3 (· = σ.setSc z (max (σ.sc x) (σ.sc y))) := by
  by_cases h : σ.sc x < σ.sc y
  · exact runs_mono (runs_ifS_t hx hy h (runs_smov hz hy)) (by norm_num)
      (fun σ' e => by rw [e, max_eq_right h.le])
  · exact runs_ifS_f hx hy h (runs_mono (runs_smov hz hx) le_rfl
      (fun σ' e => by rw [e, max_eq_left (not_lt.1 h)]))

theorem runs_smin {σ : Env d} {z x y : ℕ} (hz : z < L.NS) (hx : x < L.NS) (hy : y < L.NS) :
    Runs L w (smin L z x y) σ 3 (· = σ.setSc z (min (σ.sc x) (σ.sc y))) := by
  by_cases h : σ.sc x < σ.sc y
  · exact runs_mono (runs_ifS_t hx hy h (runs_smov hz hx)) (by norm_num)
      (fun σ' e => by rw [e, min_eq_left h.le])
  · exact runs_ifS_f hx hy h (runs_mono (runs_smov hz hy) le_rfl
      (fun σ' e => by rw [e, min_eq_right (not_lt.1 h)]))

/-- `i := ⌈x⌉₊`, counting up from `0` while the cast `t` of `i` is below `x`. -/
def nceil (L : Layout) (i one x t : ℕ) : Cmd :=
  .seq (nconst i 0) (.seq (ncast L t i) (whileS L t x (.seq (nadd i i one) (ncast L t i))))

/-- The gauge by bisection (`piTilde`): `r := |x|`; if `r > 0`, `j` halvings (`jv` holds `j`) of `[r/ρ, r]`, each asking
the code `memQ` whether the array `yv`, set to `s⁻¹ x`, is in a set (the answer `1` or `0` in the scalar `qo`), and
`pv :=` the upper end; else `pv := 0`. The scalars `z`, `h`, `o` hold `0`, `1/2`, `1`. -/
def gaugeBis (L : Layout) (memQ : Cmd) (dv one i jj jv x yv ρ qo pv nx sl su mid inv z h o t1 t2 : ℕ) : Cmd :=
  .seq (vnorm L dv one i nx x t1 t2) (.seq (sconst L z 0) (.seq (sconst L h (1 / 2)) (.seq (sconst L o 1)
    (ifS L z nx
      (.seq (sop2 L .div sl nx ρ) (.seq (smov L su nx) (.seq (forN jj jv one
        (.seq (sop2 L .add mid sl su) (.seq (sop2 L .mul mid mid h)
          (ifS L z mid
            (.seq (sop2 L .div inv o mid) (.seq (vcopy L dv one i yv x t1) (.seq (vscale L dv one i yv inv t1)
              (.seq memQ (ifS L z qo (smov L su mid) (smov L sl mid))))))
            (smov L sl mid)))))
        (smov L pv su))))
      (smov L pv z)))))

/-! ## The rules of the macros -/

/-- The rule of `vfill`. -/
theorem runs_vfill {dv one i y z : ℕ}
    (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hy : y < L.NA) (hz : z < L.NS)
    (hidv : i ≠ dv) (hione : i ≠ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (vfill L dv one i y z) σ (d * 5 + 3)
      (fun σ' => σ'.vec y = (fun _ => σ.sc z) ∧ Env.Frame σ σ' [i] [] [y] ∧
        ∀ k, d ≤ k → σ'.arr y k = σ.arr y k) := by
  let J : ℕ → Env d → Prop := fun t σ' =>
    (∀ k, σ'.arr y k = if k < t then σ.sc z else σ.arr y k) ∧
    (∀ b, b ≠ y → σ'.arr b = σ.arr b) ∧
    (∀ z', σ'.sc z' = σ.sc z') ∧
    (∀ j, j ≠ i → σ'.nat j = σ.nat j) ∧
    σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := aset L y i z) hi hdv hone hidv hione d 2 J σ hd h1
    ⟨fun k => by simp, fun b _ => rfl, fun z' => rfl, fun j hj => by simp [hj], rfl, rfl, rfl⟩
    (fun t ht σ' hJ hit hdt hot => by
      obtain ⟨Jy, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      have hk : σ'.nat i < asz d := by rw [hit]; exact lt_asz ht
      refine runs_mono (runs_aset (w := w) (σ := σ') hy hi hz hk) (by norm_num) (fun σ'' e'' => ?_)
      subst e''
      simp only [Env.setArr_nat, hit, hdt, hot, true_and]
      refine ⟨fun k => ?_, fun b hb => ?_, fun z' => ?_, fun j hj => ?_, Jd, Jr, Jp⟩
      · simp only [Env.setNat_arr, Env.setArr_arr]
        by_cases hkt : k = t
        · subst hkt; simp [Js z]
        · rw [Jy k]
          by_cases hlt : k < t
          · simp [hkt, hlt, show k < t + 1 by omega]
          · have hge : t < k := by omega
            simp [hkt, hlt, show ¬ k < t + 1 by omega]
      · funext k; simp [hb, Jb b hb]
      · simp [Env.setArr_sc, Js z']
      · simp [Env.setArr_nat, hj, Jn j hj])
  refine runs_mono hfor (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨Jy, Jb, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ⟨fun j hj => Jn j (by simpa using hj), fun z' _ => Js z',
    fun b hb => Jb b (by simpa using hb), Jd, Jr, Jp⟩, fun k hk => by rw [Jy]; simp; omega⟩
  · funext k
    simp [Env.vec, Jy, k.2]

/-- The rule of `vscale`. -/
theorem runs_vscale {dv one i y α t : ℕ}
    (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hy : y < L.NA) (hα : α < L.NS)
    (ht : t < L.NS) (hidv : i ≠ dv) (hione : i ≠ one) (hαt : α ≠ t) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (vscale L dv one i y α t) σ (d * 8 + 3)
      (fun σ' => σ'.vec y = σ.sc α • σ.vec y ∧ Env.Frame σ σ' [i] [t] [y] ∧
        ∀ k, d ≤ k → σ'.arr y k = σ.arr y k) := by
  let J : ℕ → Env d → Prop := fun k σ' =>
    (∀ k', σ'.arr y k' = if k' < k then σ.sc α * σ.arr y k' else σ.arr y k') ∧
    (∀ b, b ≠ y → σ'.arr b = σ.arr b) ∧ (∀ z, z ≠ t → σ'.sc z = σ.sc z) ∧
    (∀ j, j ≠ i → σ'.nat j = σ.nat j) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := .seq (aget L t y i) (.seq (sop2 L .mul t α t) (aset L y i t)))
    hi hdv hone hidv hione d 5 J σ hd h1
    ⟨fun k => by simp, fun b _ => rfl, fun z _ => rfl, fun j hj => by simp [hj], rfl, rfl, rfl⟩
    (fun k hk σ' hJ hik hdk hok => by
      obtain ⟨Jy, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      have hk_asz : σ'.nat i < asz d := by rw [hik]; exact lt_asz hk
      refine runs_mono (runs_seq_eq (runs_aget (w := w) (σ := σ') ht hy hi hk_asz) <|
        runs_seq_eq (runs_sop2 ht hα ht .mul) <|
        runs_aset hy hi ht (by simpa using hk_asz)) (by norm_num) (fun σ5 e5 => ?_)
      subst e5
      simp only [Env.setArr_nat, Env.setSc_nat, hik, hdk, hok, true_and]
      refine ⟨fun k' => ?_, fun b hb => ?_, fun z hzt => ?_, fun j hj => ?_, Jd, Jr, Jp⟩
      · -- array condition: σ5.arr y k' = if k' < k+1 then σ.sc α * σ.arr y k' else σ.arr y k'
        simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_sc]
        by_cases h_eq_k : k' = k
        · subst h_eq_k
          simp [hαt, Op2.eval, Jy, Js α hαt]
        · rw [Jy]
          by_cases hk'_lt_k : k' < k
          · simp [h_eq_k, hk'_lt_k, show k' < k + 1 by omega, Jy k']
          · simp [h_eq_k, hk'_lt_k, show ¬ k' < k + 1 by omega, Jy k']
      · -- other arrays unchanged
        funext k'; simp [hb, Jb b hb]
      · -- scalar condition: σ5.sc z = σ.sc z for z ≠ t
        simp [Env.setArr_sc, Env.setSc_sc, hzt, Js z hzt]
      · -- nat condition
        simp [hj, Jn j hj])
  refine runs_mono hfor (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨Jy, Jb, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ⟨fun j hj => Jn j (by simpa using hj), fun z hzt => Js z (by simpa using hzt),
    fun b hb => Jb b (by simpa using hb), Jd, Jr, Jp⟩, fun k hk => by rw [Jy]; simp; omega⟩
  funext k
  simp [Env.vec, Jy, k.2]

/-- The rule of `mfill`. -/
theorem runs_mfill {dd one m A z : ℕ}
    (σ : Env d) (hdd : dd < L.NN) (hone : one < L.NN) (hm : m < L.NN) (hA : A < L.NA) (hz : z < L.NS)
    (hmdd : m ≠ dd) (hmone : m ≠ one) (hd : σ.nat dd = d * d) (h1 : σ.nat one = 1) :
    Runs L w (mfill L dd one m A z) σ (d * d * 5 + 3)
      (fun σ' => σ'.mat A = Matrix.of (fun _ _ => σ.sc z) ∧ Env.Frame σ σ' [m] [] [A] ∧
        ∀ q, d * d ≤ q → σ'.arr A q = σ.arr A q) := by
  let J : ℕ → Env d → Prop := fun t σ' =>
    (∀ k, σ'.arr A k = if k < t then σ.sc z else σ.arr A k) ∧
    (∀ b, b ≠ A → σ'.arr b = σ.arr b) ∧
    (∀ z', σ'.sc z' = σ.sc z') ∧
    (∀ j, j ≠ m → σ'.nat j = σ.nat j) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := aset L A m z) hm hdd hone hmdd hmone (d * d) 2 J σ hd h1
    ⟨fun k => by simp, fun b _ => rfl, fun _ => rfl, fun j hj => by simp [hj], rfl, rfl, rfl⟩
    (fun t ht σ' hJ hit hdt hot => by
      obtain ⟨Jarr, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      have haz : asz d = d * d + d := rfl
      have hk : σ'.nat m < asz d := by
        rw [hit, haz]
        have : t < d * d := ht
        omega
      refine runs_mono (runs_aset hA hm hz hk) (by norm_num) (fun σ5 e5 => ?_)
      subst e5
      simp only [Env.setArr_nat, hit, hdt, hot, true_and]
      refine ⟨?_, ?_, ?_, ?_, Jd, Jr, Jp⟩
      · intro k
        simp
        rw [Jarr k]
        by_cases h_eq : k = t
        · subst h_eq; simp [Js z]
        · by_cases h_lt : k < t
          · simp [h_eq, h_lt, show k ≤ t from by omega]
          · have h_not_le : ¬ (k ≤ t) := by omega
            simp [h_eq, h_lt, h_not_le]
      · intro b hb
        simp [Env.setNat_arr]
        have h_arr_eq : (σ'.setArr A t (σ'.sc z)).arr b = σ'.arr b := by
          ext j; simp [Env.setArr_arr, hb]
        rw [h_arr_eq, Jb b hb]
      · intro z'
        simp [Js z']
      · intro j hj
        simp [hj, Jn j hj])
  refine runs_mono hfor (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨Jarr, Jb, Js, Jn, Jd, Jr, Jp⟩, hm_eq, hdd_eq, hone_eq⟩ := h
  refine ⟨?_, ⟨fun i hi => Jn i (by simpa using hi), fun x hx => Js x, fun a ha => Jb a (by simpa using ha), Jd, Jr, Jp⟩, ?_⟩
  · funext i j
    have hbound : d * (i : ℕ) + (j : ℕ) < d * d := by
      have hi : (i : ℕ) < d := i.2
      have hj : (j : ℕ) < d := j.2
      nlinarith
    simp [Env.mat, Jarr (d * (i : ℕ) + (j : ℕ)), hbound]
  · intro q hq
    rw [Jarr q]
    simp [hq]

/-- The rule of `vcopy`. -/
theorem runs_vcopy {dv one i y x t : ℕ}
    (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hy : y < L.NA) (hx : x < L.NA)
    (ht : t < L.NS) (hidv : i ≠ dv) (hione : i ≠ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (vcopy L dv one i y x t) σ (d * 7 + 3)
      (fun σ' => σ'.vec y = σ.vec x ∧ Env.Frame σ σ' [i] [t] [y] ∧ ∀ k, d ≤ k → σ'.arr y k = σ.arr y k) := by
  let J : ℕ → Env d → Prop := fun t' σ' =>
    (∀ k, σ'.arr y k = if k < t' then σ.arr x k else σ.arr y k) ∧
      (∀ b, b ≠ y → σ'.arr b = σ.arr b) ∧ (∀ z, z ≠ t → σ'.sc z = σ.sc z) ∧
      (∀ j, j ≠ i → σ'.nat j = σ.nat j) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := .seq (aget L t x i) (aset L y i t)) hi hdv hone hidv hione
    d 4 J σ hd h1
    ⟨fun k => by simp, fun b _ => rfl, fun z _ => rfl, fun j hj => by simp [hj], rfl, rfl, rfl⟩
    (fun t' ht' σ' hJ hit hdt hot => by
      obtain ⟨Jy, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      have hk : σ'.nat i < asz d := by rw [hit]; exact lt_asz ht'
      have hxt : σ'.arr x t' = σ.arr x t' := by
        by_cases hxy : x = y
        · subst hxy; rw [Jy]; simp
        · rw [Jb x hxy]
      refine runs_mono (runs_seq_eq (runs_aget (w := w) (σ := σ') ht hx hi hk) <|
        runs_aset hy hi ht (by simpa using hk)) (by norm_num) (fun σ5 e5 => ?_)
      subst e5
      simp only [Env.setArr_nat, Env.setSc_nat, hit, hdt, hot, true_and]
      refine ⟨fun k => ?_, fun b hb => ?_, fun z hz => ?_, fun j hj => ?_, Jd, Jr, Jp⟩
      · simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_sc, hxt]
        by_cases hkt : k = t'
        · subst hkt; simp
        · rw [Jy]
          by_cases hk' : k < t'
          · simp [hkt, hk', show k < t' + 1 by omega]
          · simp [hkt, hk', show ¬ k < t' + 1 by omega]
      · funext k; simp [hb, Jb b hb]
      · simp [Env.setNat_sc, hz, Js z hz]
      · simp [hj, Jn j hj])
  refine runs_mono hfor (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨Jy, Jb, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ⟨fun j hj => Jn j (by simpa using hj), fun z hz => Js z (by simpa using hz),
    fun b hb => Jb b (by simpa using hb), Jd, Jr, Jp⟩, fun k hk => by rw [Jy]; simp; omega⟩
  funext k
  simp [Env.vec, Jy, k.2]

/-- The rule of `nsq`. -/
theorem runs_nsq {dv one i dd : ℕ} (σ : Env d)
    (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hdd : dd < L.NN) (hidv : i ≠ dv) (hione : i ≠ one)
    (hidd : i ≠ dd) (hdddv : dd ≠ dv) (hddone : dd ≠ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (nsq dv one i dd) σ (d * 4 + 4) (fun σ' => σ'.nat dd = d * d ∧ Env.Frame σ σ' [i, dd] [] []) := by
  rw [nsq]
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.nat dd = d * t ∧ (∀ j, j ≠ i → j ≠ dd → σ'.nat j = σ.nat j) ∧
    σ'.sc = σ.sc ∧ σ'.arr = σ.arr ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hN : (σ.setNat dd 0).nat dv = d := by
    simp [hd, hdddv.symm]
  have h1' : (σ.setNat dd 0).nat one = 1 := by
    simp [h1, hddone.symm]
  have h0 : J 0 ((σ.setNat dd 0).setNat i 0) := by
    dsimp [J]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro j hj hji
      simp [hj, hji]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have hbody : ∀ t < d, ∀ σ', J t σ' → σ'.nat i = t → σ'.nat dv = d → σ'.nat one = 1 →
      Runs L w (nadd dd dd dv) σ' 1 (fun σ'' => σ''.nat i = t ∧ σ''.nat dv = d ∧ σ''.nat one = 1 ∧
        J (t + 1) (σ''.setNat i (t + 1))) := by
    intro t ht σ' hJ hit hdt hone'
    rcases hJ with ⟨hdd_val, hframe, hsc, harr, hdraws, hrounds, hpts⟩
    have hbody := runs_nadd (d := d) (L := L) (w := w) (σ := σ') hdd hdd hdv
    refine runs_mono hbody le_rfl (fun σ'' e => ?_)
    subst e
    have hdd_new : σ'.nat dd + σ'.nat dv = d * (t + 1) := by
      rw [hdd_val, hdt]
      ring
    have h_dd_val : (σ'.setNat dd (σ'.nat dd + σ'.nat dv)).nat dd = d * (t + 1) := by
      simp [hdd_new]
    have h_i_val : (σ'.setNat dd (σ'.nat dd + σ'.nat dv)).nat i = t := by
      simp [hit, hidd]
    have h_dv_val : (σ'.setNat dd (σ'.nat dd + σ'.nat dv)).nat dv = d := by
      simp [hdt, hdddv.symm]
    have h_one_val : (σ'.setNat dd (σ'.nat dd + σ'.nat dv)).nat one = 1 := by
      simp [hone', hddone.symm]
    refine ⟨h_i_val, h_dv_val, h_one_val, ?_⟩
    dsimp [J]
    have hJnext : ∀ j, j ≠ i → j ≠ dd → ((σ'.setNat dd (σ'.nat dd + σ'.nat dv)).setNat i (t + 1)).nat j = σ.nat j := by
      intro j hji hjdd
      simp [hji, hjdd, hframe j hji hjdd]
    have htemp : ((σ'.setNat dd (σ'.nat dd + σ'.nat dv)).setNat i (t + 1)).nat dd = σ'.nat dd + σ'.nat dv := by
      simp [hidd.symm]
    have h_dd_val' : ((σ'.setNat dd (σ'.nat dd + σ'.nat dv)).setNat i (t + 1)).nat dd = d * (t + 1) := by
      rw [htemp, hdd_val, hdt]
      ring
    refine ⟨h_dd_val', hJnext, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hsc]
    · simp [harr]
    · simp [hdraws]
    · simp [hrounds]
    · simp [hpts]
  have hfor := runs_forN hi hdv hone hidv hione d 1 J (σ.setNat dd 0) hN h1' h0 hbody
  have hseq := runs_seq_eq (runs_nconst hdd 0) hfor
  have hcost : 1 + (d * (1 + 3) + 3) = d * 4 + 4 := by ring
  have hQ : ∀ σ', (J d σ' ∧ σ'.nat i = d ∧ σ'.nat dv = d ∧ σ'.nat one = 1) → (σ'.nat dd = d * d ∧ Env.Frame σ σ' [i, dd] [] []) := by
    intro σ' h
    rcases h with ⟨hJ, hi_eq, hdv_eq, hone_eq⟩
    rcases hJ with ⟨hdd_val, hframe_nat, hsc, harr, hdraws, hrounds, hpts⟩
    refine ⟨hdd_val, ?_⟩
    have hframe_ns : ∀ j, j ∉ [i, dd] → σ'.nat j = σ.nat j := by
      intro j hj
      have hji : j ≠ i := by
        intro h_eq; apply hj; simp [h_eq]
      have hjdd : j ≠ dd := by
        intro h_eq; apply hj; simp [h_eq]
      exact hframe_nat j hji hjdd
    have hframe_ss : ∀ x, x ∉ ([] : List ℕ) → σ'.sc x = σ.sc x := by
      intro x hx; exact congrFun hsc x
    have hframe_as : ∀ a, a ∉ ([] : List ℕ) → σ'.arr a = σ.arr a := by
      intro a ha; exact congrFun harr a
    exact ⟨hframe_ns, hframe_ss, hframe_as, hdraws, hrounds, hpts⟩
  have hcost_le : 1 + (d * (1 + 3) + 3) ≤ d * 4 + 4 := by omega
  exact runs_mono hseq hcost_le hQ

/-- The rule of `mcopy`. -/
theorem runs_mcopy {dd one m B A t : ℕ}
    (σ : Env d) (hdd : dd < L.NN) (hone : one < L.NN) (hm : m < L.NN) (hB : B < L.NA) (hA : A < L.NA)
    (ht : t < L.NS) (hmdd : m ≠ dd) (hmone : m ≠ one) (hd : σ.nat dd = d * d) (h1 : σ.nat one = 1) :
    Runs L w (mcopy L dd one m B A t) σ (d * d * 7 + 3)
      (fun σ' => σ'.mat B = σ.mat A ∧ Env.Frame σ σ' [m] [t] [B] ∧ ∀ q, d * d ≤ q → σ'.arr B q = σ.arr B q) := by
  let J : ℕ → Env d → Prop := fun s σ' =>
    (∀ k, σ'.arr B k = if k < s then σ.arr A k else σ.arr B k) ∧
    (∀ a, a ≠ B → σ'.arr a = σ.arr a) ∧
    (∀ z, z ≠ t → σ'.sc z = σ.sc z) ∧
    (∀ j, j ≠ m → σ'.nat j = σ.nat j) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have h0 : J 0 (σ.setNat m 0) := by
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · intro k; simp [Env.setNat_arr]
    · intro a ha; simp [Env.setNat_arr]
    · intro z hz; simp [Env.setNat_sc]
    · intro j hj; simp [Env.setNat_nat, hj]
  have hbody : ∀ k < d * d, ∀ σ', J k σ' → σ'.nat m = k → σ'.nat dd = d * d → σ'.nat one = 1 →
      Runs L w (.seq (aget L t A m) (aset L B m t)) σ' 4 (fun σ'' => σ''.nat m = k ∧ σ''.nat dd = d * d ∧ σ''.nat one = 1 ∧
        J (k + 1) (σ''.setNat m (k + 1))) := by
    intro s hs σ' hJ hits hds hots
    have hJ_unfolded : (∀ k, σ'.arr B k = if k < s then σ.arr A k else σ.arr B k) ∧
      (∀ a, a ≠ B → σ'.arr a = σ.arr a) ∧
      (∀ z, z ≠ t → σ'.sc z = σ.sc z) ∧
      (∀ j, j ≠ m → σ'.nat j = σ.nat j) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts := by
      simpa [J] using hJ
    obtain ⟨Jarr, Jab, Js, Jn, Jd, Jr, Jp⟩ := hJ_unfolded
    have hk : σ'.nat m < asz d := by
      rw [hits]
      have : s < d * d := hs
      unfold asz
      omega
    have hAt : σ'.arr A (σ'.nat m) = σ.arr A (σ'.nat m) := by
      by_cases hAB : A = B
      · subst hAB
        have h := Jarr s
        simpa [hits] using h
      · have h := Jab A hAB
        simpa [hits] using congrFun h (σ'.nat m)
    have haget := runs_aget (w := w) (σ := σ') ht hA hm hk
    have hset := runs_aset (w := w) (σ := σ'.setSc t (σ'.arr A (σ'.nat m))) hB hm ht
      (by simpa [Env.setSc_nat] using hk)
    have hseq := runs_seq_eq haget hset
    refine runs_mono hseq (by norm_num) (fun σ5 e5 => ?_)
    subst e5
    simp only [Env.setArr_nat, Env.setSc_nat]
    refine ⟨hits, hds, hots, ?_⟩
    unfold J
    simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_sc, hAt, Jarr, true_and]
    refine ⟨fun k => ?_, fun a ha => ?_, fun z hz => ?_, fun j hj => ?_, Jd, Jr, Jp⟩
    · by_cases hk' : k < s
      · have hk_ne_s : k ≠ s := by omega
        have hk_le_s : k ≤ s := Nat.le_of_lt hk'
        simp [hk', hk_ne_s, hk_le_s, hits]
      · by_cases hk_eq : k = s
        · subst hk_eq; simp [hits]
        · have hk_gt : s < k := by omega
          have hk_not_le_s : ¬ k ≤ s := by omega
          simp [hk_eq, hk_not_le_s, hits, hk']
    · funext k; simp [ha, Jab a ha]
    · simp [hz, Js z hz]
    · simp [hj, Jn j hj]
  have hfor := runs_forN (w := w) (i := m) (n := dd) (one := one) (body := .seq (aget L t A m) (aset L B m t)) hm hdd hone hmdd hmone
    (d * d) 4 J σ hd h1 h0 hbody
  refine runs_mono hfor le_rfl (fun σ' h => ?_)
  obtain ⟨⟨Jarr, Jab, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · -- σ'.mat B = σ.mat A
    ext i j
    simp [Env.mat, Jarr (d * i + j), show d * i + j < d * d by
      have hi : (i : ℕ) < d := i.2
      have hj : (j : ℕ) < d := j.2
      nlinarith]
  · -- Env.Frame σ σ' [m] [t] [B]
    refine ⟨?_, ?_, ?_, Jd, Jr, Jp⟩
    · intro i hi
      simp at hi
      have hi' : i ≠ m := by
        intro heq; subst heq; exact hi rfl
      simp [Jn i hi']
    · intro x hx
      simp at hx
      simp [Js x hx]
    · intro a ha
      simp at ha
      simp [Jab a ha]
  · -- ∀ q, d * d ≤ q → σ'.arr B q = σ.arr B q
    intro q hq
    have hq' : ¬ q < d * d := by omega
    simp [hq', Jarr q]

/-- The rule of `vdot`. -/
theorem runs_vdot {dv one i r x y t1 t2 : ℕ}
    (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hr : r < L.NS) (hx : x < L.NA)
    (hy : y < L.NA) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hidv : i ≠ dv) (hione : i ≠ one) (hr1 : r ≠ t1)
    (hr2 : r ≠ t2) (h12 : t1 ≠ t2) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (vdot L dv one i r x y t1 t2) σ (d * 9 + 4)
      (fun σ' => σ'.sc r = σ.vec x ⬝ᵥ σ.vec y ∧ Env.Frame σ σ' [i] [r, t1, t2] []) := by
  let body : Cmd := .seq (aget L t1 x i) (.seq (aget L t2 y i) (.seq (sop2 L .mul t1 t1 t2) (sop2 L .add r r t1)))
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.sc r = ∑ k ∈ Finset.range t, σ.arr x k * σ.arr y k ∧
    (∀ z, z ≠ r → z ≠ t1 → z ≠ t2 → σ'.sc z = σ.sc z) ∧
    (∀ a, σ'.arr a = σ.arr a) ∧
    (∀ j, j ≠ i → σ'.nat j = σ.nat j) ∧
    σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hN : σ.nat dv = d := hd
  have hconst : Runs L w (sconst L r 0) σ 1 (· = σ.setSc r 0) := by
    have h := runs_sconst (L := L) (w := w) (σ := σ) hr (0 : ℚ)
    refine runs_mono h le_rfl (fun σ' e => ?_)
    subst e
    simp
  have hfor := runs_forN (L := L) (w := w) (body := body) hi hdv hone hidv hione d 6 J (σ.setSc r 0) hN h1
    (by
      refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
      · simp [Env.setNat_sc]
      · intro z hzr hzt1 hzt2; simp [Env.setNat_sc, hzr]
      · intro a; simp [Env.setNat_arr]
      · intro j hj; simp [Env.setNat_nat, hj])
    (fun t ht σ' hJ hit hdt hot => by
      obtain ⟨Jr, Js, Ja, Jn, Jd, Jrr, Jp⟩ := hJ
      have hk : σ'.nat i < asz d := by rw [hit]; exact lt_asz ht
      have hchain := runs_seq_eq (runs_aget (w := w) (σ := σ') ht1 hx hi hk)
        (runs_seq_eq (runs_aget (w := w) ht2 hy hi (by simpa using hk))
          (runs_seq_eq (runs_sop2 (w := w) ht1 ht1 ht2 .mul)
            (runs_sop2 (w := w) hr hr ht1 .add)))
      refine runs_mono hchain (by norm_num) (fun σ5 e5 => ?_)
      subst e5
      simp [Env.setSc_sc, Env.setSc_nat, Env.setSc_arr, hit, hdt, hot, h12, hr1, hr2]
      have hsum : (σ'.sc r + σ'.arr x t * σ'.arr y t) =
          (∑ k ∈ Finset.range t, σ.arr x k * σ.arr y k) + σ.arr x t * σ.arr y t := by rw [Jr, Ja x, Ja y]
      refine ⟨?_, ?_, ?_, ?_, Jd, Jrr, Jp⟩
      · simpa [Op2.eval, Finset.sum_range_succ] using hsum
      · intro z hzr hzt1 hzt2
        simp [Env.setNat_sc, hzr, hzt1, hzt2, Js z hzr hzt1 hzt2]
      · exact Ja
      · intro j hj
        simp [Env.setNat_nat, hj, Jn j hj]
    )
  have hseq := runs_seq_eq hconst hfor
  refine runs_mono hseq (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨Jr, Js, Ja, Jn, Jd, Jrr, Jp⟩, -, -, -⟩ := h
  have hdot : σ.vec x ⬝ᵥ σ.vec y = ∑ k ∈ Finset.range d, σ.arr x k * σ.arr y k := by
    simp [dotProduct, Env.vec, Fin.sum_univ_eq_sum_range (fun k => σ.arr x k * σ.arr y k) d]
  have hframe_arr : ∀ a, σ'.arr a = σ.arr a := Ja
  refine ⟨?_, ?_⟩
  · rw [hdot, Jr]
  · refine ⟨?_, ?_, fun a _ => hframe_arr a, Jd, Jrr, Jp⟩
    · intro j hj
      have hj' : j ≠ i := by
        intro heq; subst heq; exact hj (by simp)
      simpa [hj'] using Jn j hj'
    · intro z hz
      have hzr : z ≠ r := by intro heq; subst heq; exact hz (by simp)
      have hzt1 : z ≠ t1 := by intro heq; subst heq; exact hz (by simp)
      have hzt2 : z ≠ t2 := by intro heq; subst heq; exact hz (by simp)
      exact Js z hzr hzt1 hzt2

/-- The rule of `vgauss`. -/
theorem runs_vgauss {dv one i y t : ℕ}
    (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hy : y < L.NA) (ht : t < L.NS)
    (hidv : i ≠ dv) (hione : i ≠ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (vgauss L dv one i y t) σ (d * 6 + 3)
      (fun σ' => σ'.vec y = (fun k : Fin d => w.gs (σ.draws + k)) ∧ σ'.draws = σ.draws + d ∧
        (∀ j, j ≠ i → σ'.nat j = σ.nat j) ∧ (∀ z, z ≠ t → σ'.sc z = σ.sc z) ∧
        (∀ b, b ≠ y → σ'.arr b = σ.arr b) ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts ∧
        ∀ k, d ≤ k → σ'.arr y k = σ.arr y k) := by
  let J : ℕ → Env d → Prop := fun k σ' =>
    σ'.draws = σ.draws + k ∧
    (∀ j, σ'.arr y j = if j < k then w.gs (σ.draws + j) else σ.arr y j) ∧
    (∀ b, b ≠ y → σ'.arr b = σ.arr b) ∧
    (∀ z, z ≠ t → σ'.sc z = σ.sc z) ∧
    (∀ j, j ≠ i → σ'.nat j = σ.nat j) ∧
    σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hJ0 : J 0 (σ.setNat i 0) := by
    unfold J
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro j; simp
    · intro b _; simp
    · intro z _; simp
    · intro j hj; simp [hj]
    · simp
    · simp
  have hbody_aux : ∀ (t' : ℕ), t' < d → ∀ σ', J t' σ' → σ'.nat i = t' → σ'.nat dv = d → σ'.nat one = 1 →
      Runs L w (.seq (gauss L t) (aset L y i t)) σ' 3
      (fun σ'' => σ''.nat i = t' ∧ σ''.nat dv = d ∧ σ''.nat one = 1 ∧ J (t' + 1) (σ''.setNat i (t' + 1))) := by
    intro t' ht' σ' hJ hit' hdt' hot'
    unfold J at hJ
    rcases hJ with ⟨Jd, Jy, Jb, Js, Jn, Jr, Jp⟩
    have hk : σ'.nat i < asz d := by rw [hit']; exact lt_asz (by omega)
    have hbody := runs_seq_eq (runs_gauss (w := w) (σ := σ') ht) <|
      runs_aset hy hi ht hk
    refine runs_mono hbody (by norm_num) (fun σ5 e5 => ?_)
    subst e5
    dsimp (config := { zeta := true })
    unfold J
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hit']
    · simp [hdt']
    · simp [hot']
    · simp [Env.setNat_draws, Jd]; omega
    · intro j
      simp only [Env.setNat_arr, Env.setArr_arr, hit', Jy j]
      by_cases hj_eq : j = t'
      · subst hj_eq; simp [Jd]
      · by_cases hj_lt : j < t'
        · simp [hj_eq, hj_lt, show j < t' + 1 by omega]
        · simp [hj_eq, hj_lt, show ¬ j < t' + 1 by omega]
    · intro b hb
      ext j
      simp [Env.setNat_arr, Env.setArr_arr, hb, Jb b hb]
    · intro z hz
      simp [Env.setNat_sc, Env.setArr_sc, Env.setSc_sc, hz, Js z hz]
    · intro j hj
      simp [Env.setNat_nat, hj, Jn j hj]
    · simp [Env.setNat_rounds, Jr]
    · simp [Env.setNat_pts, Jp]
  have hfor := runs_forN (L := L) (w := w) (body := .seq (gauss L t) (aset L y i t))
    hi hdv hone hidv hione d 3 J σ hd h1 hJ0 hbody_aux
  refine runs_mono hfor (by ring_nf; omega) (fun σ' h => ?_)
  unfold J at h
  rcases h with ⟨⟨Jd, Jy, Jb, Js, Jn, Jr, Jp⟩, h_i, h_dv, h_one⟩
  refine ⟨?_, Jd, Jn, Js, Jb, Jr, Jp, fun k hk => ?_⟩
  · funext k
    rw [Env.vec]
    simp [Jy, k.2]
  · rw [Jy]
    simp; omega

/-- Rule of `vnorm`: `r := ‖x‖`. -/
theorem runs_vnorm {dv one i r x t1 t2 : ℕ}
    (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hx : x < L.NA) (hr : r < L.NS)
    (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hidv : i ≠ dv) (hione : i ≠ one) (hr1 : r ≠ t1) (hr2 : r ≠ t2)
    (h12 : t1 ≠ t2) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (vnorm L dv one i r x t1 t2) σ (d * 9 + 5)
      (fun σ' => σ'.sc r = Real.sqrt (σ.vec x ⬝ᵥ σ.vec x) ∧ Env.Frame σ σ' [i] [r, t1, t2] []) := by
  have hvdot := runs_vdot (L := L) (w := w) (σ := σ)
    (hdv := hdv) (hone := hone) (hi := hi) (hr := hr) (hx := hx) (hy := hx)
    (ht1 := ht1) (ht2 := ht2)
    (hidv := hidv) (hione := hione) (hr1 := hr1) (hr2 := hr2) (h12 := h12)
    (hd := hd) (h1 := h1)
  have hsop1 : ∀ σ', (σ'.sc r = σ.vec x ⬝ᵥ σ.vec x ∧ Env.Frame σ σ' [i] [r, t1, t2] []) →
      Runs L w (sop1 L .sqrt r r) σ' 1 (fun σ'' => σ''.sc r = Real.sqrt (σ.vec x ⬝ᵥ σ.vec x) ∧ Env.Frame σ σ'' [i] [r, t1, t2] []) := by
    intro σ' ⟨hsc, hframe⟩
    have h := runs_sop1 (L := L) (w := w) (σ := σ') hr hr .sqrt
    refine runs_mono h le_rfl (fun σ'' e => ?_)
    subst e
    have h1 : (σ'.setSc r (Op1.eval .sqrt (σ'.sc r))).sc r = Real.sqrt (σ.vec x ⬝ᵥ σ.vec x) := by
      simp [Env.setSc_sc, hsc, Op1.eval]
    have h2 : Env.Frame σ (σ'.setSc r (Op1.eval .sqrt (σ'.sc r))) [i] [r, t1, t2] [] := by
      obtain ⟨hnat, hsc_frame, harr, hdraws, hrounds, hpts⟩ := hframe
      refine ⟨hnat, ?_, harr, hdraws, hrounds, hpts⟩
      intro y hy
      have hy' : y ≠ r ∧ y ≠ t1 ∧ y ≠ t2 := by
        simpa using hy
      rcases hy' with ⟨hyr, hyt1, hyt2⟩
      simpa [Env.setSc_sc, hyr] using hsc_frame y hy
    exact And.intro h1 h2
  have hseq := runs_seq hvdot hsop1
  refine runs_mono hseq (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨hsc, hframe⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hsc]
  · obtain ⟨hnat, hsc_frame, harr, hdraws, hrounds, hpts⟩ := hframe
    refine ⟨hnat, ?_, harr, hdraws, hrounds, hpts⟩
    intro y hy
    have hy' : y ≠ r ∧ y ≠ t1 ∧ y ≠ t2 := by
      simpa using hy
    rcases hy' with ⟨hyr, hyt1, hyt2⟩
    simpa using hsc_frame y hy

/-- Rule of `nceil`: `i := ⌈x⌉₊`, and `t` its cast. -/
theorem runs_nceil {i one x t : ℕ} (σ : Env d)
    (hi : i < L.NN) (hone : one < L.NN) (hio : i ≠ one) (hx : x < L.NS) (ht : t < L.NS) (hxt : x ≠ t)
    (h1 : σ.nat one = 1) :
    Runs L w (nceil L i one x t) σ (⌈σ.sc x⌉₊ * 4 + 4)
      (· = (σ.setNat i ⌈σ.sc x⌉₊).setSc t ⌈σ.sc x⌉₊) := by
  set N := ⌈σ.sc x⌉₊ with hN
  have hN_def : N = ⌈σ.sc x⌉₊ := rfl
  -- Step 1: nconst i 0
  have h_nconst : Runs L w (nconst i 0) σ 1 (· = σ.setNat i 0) := runs_nconst hi 0
  -- Step 2: ncast L t i on the result of step 1
  have h_ncast : Runs L w (ncast L t i) (σ.setNat i 0) 1 (· = (σ.setNat i 0).setSc t 0) := by
    have := runs_ncast (w := w) ht hi (σ := σ.setNat i 0)
    simpa using this
  -- Invariant for the while loop
  set I : ℕ → Env d → Prop := fun m σ' => σ' = (σ.setNat i m).setSc t m ∧ m ≤ N with hI
  have hI0 : I 0 ((σ.setNat i 0).setSc t 0) := by
    refine ⟨?_, Nat.zero_le _⟩
    simp
  -- hlt: if invariant holds and condition is true, then m < N
  have hlt : ∀ m σ', I m σ' → σ'.sc t < σ'.sc x → m < N := by
    intro m σ' ⟨h_eq, h_le⟩ h_lt
    subst h_eq
    have h_sc_t : ((σ.setNat i m).setSc t m).sc t = (m : ℝ) := by simp
    have h_sc_x : ((σ.setNat i m).setSc t m).sc x = σ.sc x := by simp [hxt]
    rw [h_sc_t, h_sc_x] at h_lt
    exact (Nat.lt_ceil (a := σ.sc x) (n := m)).mpr h_lt
  -- hbody: one iteration of the loop body
  have hbody : ∀ m σ', I m σ' → σ'.sc t < σ'.sc x → Runs L w (.seq (nadd i i one) (ncast L t i)) σ' 2 (I (m + 1)) := by
    intro m σ' ⟨h_eq, h_le⟩ h_lt
    subst h_eq
    have h_nadd : Runs L w (nadd i i one) ((σ.setNat i m).setSc t m) 1
        (· = ((σ.setNat i m).setSc t m).setNat i (((σ.setNat i m).setSc t m).nat i + ((σ.setNat i m).setSc t m).nat one)) :=
      runs_nadd hi hi hone
    have h_nadd_simp : ((σ.setNat i m).setSc t m).nat i = m := by simp
    have h_one_val : ((σ.setNat i m).setSc t m).nat one = 1 := by
      have h_ne : one ≠ i := hio.symm
      simp [h_ne, h1]
    have h_nadd_res : Runs L w (nadd i i one) ((σ.setNat i m).setSc t m) 1
        (· = ((σ.setNat i m).setSc t m).setNat i (m + 1)) := by
      simpa [h_nadd_simp, h_one_val] using h_nadd
    have h_ncast_body : Runs L w (ncast L t i) (((σ.setNat i m).setSc t m).setNat i (m + 1)) 1
        (· = (((σ.setNat i m).setSc t m).setNat i (m + 1)).setSc t ((((σ.setNat i m).setSc t m).setNat i (m + 1)).nat i)) :=
      runs_ncast (w := w) ht hi
    have h_ncast_simp : (((σ.setNat i m).setSc t m).setNat i (m + 1)).nat i = m + 1 := by simp
    have h_ncast_res : Runs L w (ncast L t i) (((σ.setNat i m).setSc t m).setNat i (m + 1)) 1
        (· = (((σ.setNat i m).setSc t m).setNat i (m + 1)).setSc t (m + 1)) := by
      simpa [h_ncast_simp] using h_ncast_body
    have h_seq : Runs L w (.seq (nadd i i one) (ncast L t i)) ((σ.setNat i m).setSc t m) 2
        (· = (((σ.setNat i m).setSc t m).setNat i (m + 1)).setSc t (m + 1)) :=
      runs_seq_eq h_nadd_res h_ncast_res
    have h_eq_env : (((σ.setNat i m).setSc t m).setNat i (m + 1)).setSc t (m + 1) =
        (σ.setNat i (m + 1)).setSc t (m + 1) := by
      cases σ with | mk nat sc arr draws rounds pts =>
      simp [Env.setNat, Env.setSc, Function.update_idem]
    have h_le' : m + 1 ≤ N := by
      have : m < N := hlt m ((σ.setNat i m).setSc t m) ⟨rfl, h_le⟩ h_lt
      omega
    simpa [hI, h_eq_env, h_le'] using h_seq
  -- Apply runs_whileS
  have h_while : Runs L w (whileS L t x (.seq (nadd i i one) (ncast L t i)))
      ((σ.setNat i 0).setSc t 0) ((N - 0) * (2 + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.sc t < σ'.sc x) :=
    runs_whileS ht hx I N 2 hlt hbody 0 ((σ.setNat i 0).setSc t 0) hI0
  -- Chain step 2 and the while loop
  have h_mid : Runs L w (.seq (ncast L t i) (whileS L t x (.seq (nadd i i one) (ncast L t i))))
      (σ.setNat i 0) (1 + ((N - 0) * (2 + 2) + 2))
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.sc t < σ'.sc x) :=
    runs_seq_eq h_ncast h_while
  -- Chain steps 1 and the seq(2, while) to get nceil
  have h_total : Runs L w (nceil L i one x t) σ (1 + (1 + ((N - 0) * (2 + 2) + 2)))
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.sc t < σ'.sc x) := by
    simpa [nceil] using runs_seq_eq h_nconst h_mid
  -- Simplify cost
  have h_final : Runs L w (nceil L i one x t) σ (N * 4 + 4)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.sc t < σ'.sc x) :=
    runs_mono h_total (by omega) (fun _ h => h)
  -- Now extract the final equality from the postcondition
  intro s hs
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h_final s hs
  obtain ⟨t', ⟨h_eq, h_le⟩, h_not⟩ := hq
  have h_le_real : σ.sc x ≤ (t' : ℝ) := by
    have h_sc_t : σ'.sc t = (t' : ℝ) := by subst h_eq; simp
    have h_sc_x : σ'.sc x = σ.sc x := by subst h_eq; simp [hxt]
    rw [h_sc_t, h_sc_x] at h_not
    linarith
  have h_N_le_t' : N ≤ t' := (Nat.ceil_le (a := σ.sc x) (n := t')).mpr h_le_real
  have h_t'_eq_N : t' = N := Nat.le_antisymm h_le h_N_le_t'
  subst h_t'_eq_N
  refine ⟨k, s', σ', hk, he, hr, ?_⟩
  subst h_eq
  simp [hN_def]

/-- One row of `matvec`: `s := s + (A x)_r`, the index `k` running over row `r`. -/
theorem runs_matvecRow
    {dv one j k x A s t1 t2 : ℕ} (σ : Env d) (r : Fin d) (hdv : dv < L.NN) (hone : one < L.NN) (hj : j < L.NN)
    (hk : k < L.NN) (hx : x < L.NA) (hA : A < L.NA) (hs : s < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS)
    (hjdv : j ≠ dv) (hjone : j ≠ one) (hjk : j ≠ k) (hkdv : k ≠ dv) (hkone : k ≠ one) (hs1 : s ≠ t1)
    (hs2 : s ≠ t2) (h12 : t1 ≠ t2) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hkr : σ.nat k = d * r) :
    Runs L w (forN j dv one (.seq (aget L t1 A k) (.seq (aget L t2 x j) (.seq (sop2 L .mul t1 t1 t2)
      (.seq (sop2 L .add s s t1) (nadd k k one)))))) σ (d * 10 + 3)
      (fun σ' => σ'.sc s = σ.sc s + (σ.mat A *ᵥ σ.vec x) r ∧ σ'.nat k = d * r + d ∧
        Env.Frame σ σ' [j, k] [s, t1, t2] []) := by
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.sc s = σ.sc s + ∑ c ∈ Finset.range t, σ.arr A (d * r + c) * σ.arr x c ∧ σ'.nat k = d * r + t ∧
      (∀ z, z ≠ s → z ≠ t1 → z ≠ t2 → σ'.sc z = σ.sc z) ∧ (∀ a, σ'.arr a = σ.arr a) ∧
      (∀ q, q ≠ j → q ≠ k → σ'.nat q = σ.nat q) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := .seq (aget L t1 A k) (.seq (aget L t2 x j)
      (.seq (sop2 L .mul t1 t1 t2) (.seq (sop2 L .add s s t1) (nadd k k one))))) hj hdv hone hjdv hjone d 7 J σ hd h1
    ⟨by simp, by simp [Ne.symm hjk, hkr], fun z _ _ _ => by simp, fun a => by simp,
      fun q hqj _ => by simp [hqj], by simp, by simp, by simp⟩
    (fun t ht σ' hJ hjt hdt hot => by
      obtain ⟨Js, Jk, Jz, Ja, Jn, Jd, Jr, Jp⟩ := hJ
      have hkA : σ'.nat k < asz d := by
        have hr := r.2
        have : d * (r : ℕ) + t < d * d := by
          calc d * (r : ℕ) + t < d * r + d := by omega
            _ = d * (r + 1) := by ring
            _ ≤ d * d := Nat.mul_le_mul_left d hr
        rw [Jk]; unfold asz; omega
      have hjx : σ'.nat j < asz d := by rw [hjt]; exact lt_asz ht
      refine runs_mono (runs_seq_eq (runs_aget (w := w) (σ := σ') ht1 hA hk hkA)
        (runs_seq_eq (runs_aget (w := w) ht2 hx hj (by simpa using hjx))
          (runs_seq_eq (runs_sop2 (w := w) ht1 ht1 ht2 .mul)
            (runs_seq_eq (runs_sop2 (w := w) hs hs ht1 .add) (runs_nadd (w := w) hk hk hone))))) (by norm_num)
        (fun σ5 e5 => ?_)
      subst e5
      refine ⟨by simp [hjk, hjt], by simp [Ne.symm hkdv, hdt], by simp [Ne.symm hkone, hot], ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · simp [hs1, hs2, h12, Op2.eval, Js, Jk, hjt, Ja, Finset.sum_range_succ]; ring
      · simp [Ne.symm hjk, Jk, hot]; ring
      · intro z hz1 hz2 hz3; simp [hz1, hz2, hz3, Jz z hz1 hz2 hz3]
      · intro a; simp [Ja]
      · intro q hqj hqk; simp [hqj, hqk, Jn q hqj hqk]
      · simp [Jd]
      · simp [Jr]
      · simp [Jp])
  refine runs_mono hfor le_rfl (fun σ' h => ?_)
  obtain ⟨⟨Js, Jk, Jz, Ja, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, Jk, fun q hq => ?_, fun z hz => ?_, fun a _ => Ja a, Jd, Jr, Jp⟩
  · rw [Js]; congr 1
    simp only [Matrix.mulVec, dotProduct, Env.mat, Env.vec]
    exact (Fin.sum_univ_eq_sum_range (fun c => σ.arr A (d * r + c) * σ.arr x c) d).symm
  · simp at hq; exact Jn q hq.1 hq.2
  · simp at hz; exact Jz z hz.1 hz.2.1 hz.2.2

/-- The rule of `matvec`: `y := A x`. -/
theorem runs_matvec {dv one i j k y A x s t1 t2 : ℕ} (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN)
    (hi : i < L.NN) (hj : j < L.NN) (hk : k < L.NN) (hy : y < L.NA) (hA : A < L.NA) (hx : x < L.NA)
    (hs : s < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hidv : i ≠ dv) (hione : i ≠ one) (hjdv : j ≠ dv)
    (hjone : j ≠ one) (hkdv : k ≠ dv) (hkone : k ≠ one) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hyx : y ≠ x)
    (hyA : y ≠ A) (hs1 : s ≠ t1) (hs2 : s ≠ t2) (h12 : t1 ≠ t2) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (matvec L dv one i j k y A x s t1 t2) σ (d * (d * 10 + 9) + 4)
      (fun σ' => σ'.vec y = σ.mat A *ᵥ σ.vec x ∧ Env.Frame σ σ' [i, j, k] [s, t1, t2] [y] ∧
        ∀ m, d ≤ m → σ'.arr y m = σ.arr y m) := by
  let mv : ℕ → ℝ := fun m => ∑ c ∈ Finset.range d, σ.arr A (d * m + c) * σ.arr x c
  have hmv : ∀ r : Fin d, (σ.mat A *ᵥ σ.vec x) r = mv r := fun r => by
    simp only [Matrix.mulVec, dotProduct, Env.mat, Env.vec, mv]
    exact Fin.sum_univ_eq_sum_range (fun c => σ.arr A (d * r + c) * σ.arr x c) d
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.nat k = d * t ∧ (∀ m, σ'.arr y m = if m < t then mv m else σ.arr y m) ∧
      (∀ b, b ≠ y → σ'.arr b = σ.arr b) ∧ (∀ z, z ≠ s → z ≠ t1 → z ≠ t2 → σ'.sc z = σ.sc z) ∧
      (∀ q, q ≠ i → q ≠ j → q ≠ k → σ'.nat q = σ.nat q) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧
      σ'.pts = σ.pts
  have hdk : (σ.setNat k 0).nat dv = d := by simp [Ne.symm hkdv, hd]
  have h1k : (σ.setNat k 0).nat one = 1 := by simp [Ne.symm hkone, h1]
  have hfor := runs_forN (L := L) (w := w) (body := .seq (sconst L s 0) (.seq (forN j dv one
      (.seq (aget L t1 A k) (.seq (aget L t2 x j) (.seq (sop2 L .mul t1 t1 t2) (.seq (sop2 L .add s s t1)
        (nadd k k one)))))) (aset L y i s))) hi hdv hone hidv hione d (d * 10 + 6) J (σ.setNat k 0) hdk h1k
    ⟨by simp, fun m => by simp, fun b _ => rfl, fun z _ _ _ => rfl,
      fun q hqi _ hqk => by simp [hqi, hqk], rfl, rfl, rfl⟩
    (fun t ht σ' hJ hit hdt hot => by
      obtain ⟨Jk, Jy, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      have hA' : σ'.arr A = σ.arr A := Jb A (Ne.symm hyA)
      have hx' : σ'.arr x = σ.arr x := Jb x (Ne.symm hyx)
      refine runs_mono (K := 1 + ((d * 10 + 3) + 2)) ?_ (by omega) (fun σ3 h3 => h3)
      refine runs_seq_eq (runs_sconst (w := w) (σ := σ') hs 0) (runs_seq (runs_matvecRow (w := w) (σ'.setSc s ((0 : ℚ) : ℝ)) ⟨t, ht⟩
        hdv hone hj hk hx hA hs ht1 ht2 hjdv hjone hjk hkdv hkone hs1 hs2 h12 (by simpa using hdt)
        (by simpa using hot) (by simpa using Jk)) (fun σ2 h2 => ?_))
      obtain ⟨e2s, e2k, F2n, F2s, F2a, F2d, F2r, F2p⟩ := h2
      have h2i : σ2.nat i = t := by rw [F2n i (by simp [hij, hik])]; simpa using hit
      have hai : σ2.nat i < asz d := by rw [h2i]; exact lt_asz ht
      refine runs_mono (runs_aset (σ := σ2) hy hi hs hai) le_rfl (fun σ3 e3 => ?_)
      subst e3
      have hval : σ2.sc s = mv t := by
        have hm : (σ'.setSc s ((0 : ℚ) : ℝ)).mat A = σ.mat A := by funext a b; simp [Env.mat, hA']
        have hv : (σ'.setSc s ((0 : ℚ) : ℝ)).vec x = σ.vec x := by funext a; simp [Env.vec, hx']
        rw [e2s, hm, hv, hmv ⟨t, ht⟩]; simp
      refine ⟨by simp [h2i], by simp [F2n dv (by simp [Ne.symm hjdv, Ne.symm hkdv]), hdt],
        by simp [F2n one (by simp [Ne.symm hjone, Ne.symm hkone]), hot], ?_⟩
      refine ⟨by simp [Ne.symm hik, e2k]; ring, fun m => ?_, fun b hb => ?_, fun z hzs hz1 hz2 => ?_,
        fun q hqi hqj hqk => ?_, by simp [F2d, Jd], by simp [F2r, Jr], by simp [F2p, Jp]⟩
      · simp only [Env.setNat_arr, Env.setArr_arr, h2i, hval, F2a y (by simp), Env.setSc_arr, Jy]
        by_cases hmt : m = t
        · subst hmt; simp
        · by_cases hm : m < t
          · simp [hmt, hm, show m < t + 1 by omega]
          · simp [hmt, hm, show ¬ m < t + 1 by omega]
      · funext m; simp [Env.setArr_arr, hb, F2a b (by simp), Jb b hb]
      · simp [F2s z (by simp [hzs, hz1, hz2]), hzs, Js z hzs hz1 hz2]
      · simp [hqi, F2n q (by simp [hqj, hqk]), Jn q hqi hqj hqk])
  refine runs_mono (K := 1 + (d * ((d * 10 + 6) + 3) + 3)) (runs_seq_eq (runs_nconst hk 0) hfor)
    (le_of_eq (by ring)) (fun σ' h => ?_)
  obtain ⟨⟨Jk, Jy, Jb, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ⟨fun q hq => ?_, fun z hz => ?_, fun b hb => Jb b (by simpa using hb), Jd, Jr, Jp⟩,
    fun m hm => by rw [Jy]; simp; omega⟩
  · funext r; rw [hmv r]; simp [Env.vec, Jy, r.2]
  · simp at hq; simp [Jn q hq.1 hq.2.1 hq.2.2]
  · simp at hz; exact Js z hz.1 hz.2.1 hz.2.2

/-- Rule of `mtrace`: `r := tr A`. -/
theorem runs_mtrace {dv one i k r A t : ℕ}
    (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hk : k < L.NN) (hr : r < L.NS)
    (hA : A < L.NA) (ht : t < L.NS) (hidv : i ≠ dv) (hione : i ≠ one) (hki : k ≠ i) (hkdv : k ≠ dv)
    (hkone : k ≠ one) (hrt : r ≠ t) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (mtrace L dv one i k r A t) σ (d * 8 + 5)
      (fun σ' => σ'.sc r = (σ.mat A).trace ∧ Env.Frame σ σ' [i, k] [r, t] []) := by
  set σ0 := σ.setSc r 0 with hσ0
  set σ1 := σ0.setNat k 0 with hσ1
  have h_init_dv : σ1.nat dv = d := by
    dsimp [σ1, σ0]
    calc
      ((σ.setSc r 0).setNat k 0).nat dv = (if dv = k then 0 else σ.nat dv) := by
        simp [Env.setNat_nat, Env.setSc_nat]
      _ = σ.nat dv := by
        by_cases h : dv = k
        · exfalso; exact hkdv h.symm
        · simp [h]
      _ = d := hd
  have h_init_one : σ1.nat one = 1 := by
    dsimp [σ1, σ0]
    calc
      ((σ.setSc r 0).setNat k 0).nat one = (if one = k then 0 else σ.nat one) := by
        simp [Env.setNat_nat, Env.setSc_nat]
      _ = σ.nat one := by
        by_cases h : one = k
        · exfalso; exact hkone h.symm
        · simp [h]
      _ = 1 := h1
  let body : Cmd := .seq (aget L t A k) (.seq (sop2 L .add r r t) (.seq (nadd k k dv) (nadd k k one)))
  let J : ℕ → Env d → Prop := fun _t' σ' =>
    σ'.nat k = (d + 1) * _t' ∧
    σ'.nat i = _t' ∧
    σ'.nat dv = d ∧
    σ'.nat one = 1 ∧
    σ'.sc r = ∑ a ∈ Finset.range _t', σ.arr A ((d + 1) * a) ∧
    (∀ x, x ≠ r → x ≠ t → σ'.sc x = σ.sc x) ∧
    (σ'.arr A = σ.arr A) ∧
    (∀ a, a ≠ A → σ'.arr a = σ.arr a) ∧
    (∀ j, j ≠ i → j ≠ k → σ'.nat j = σ.nat j) ∧
    σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hJ0 : J 0 (σ1.setNat i 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · -- (σ1.setNat i 0).nat k = (d + 1) * 0
      simp [hσ1, hσ0, Env.setNat_nat, hki]
    · -- (σ1.setNat i 0).nat i = 0
      simp [hσ1, hσ0, Env.setNat_nat]
    · -- (σ1.setNat i 0).nat dv = d
      rw [hσ1, hσ0]
      simp [Env.setNat_nat, Ne.symm hidv, Ne.symm hkdv, hd]
    · -- (σ1.setNat i 0).nat one = 1
      rw [hσ1, hσ0]
      simp [Env.setNat_nat, Ne.symm hione, Ne.symm hkone, h1]
    · -- (σ1.setNat i 0).sc r = ∑ a ∈ Finset.range 0, σ.arr A ((d + 1) * a)
      simp [hσ1, hσ0, Env.setSc_sc]
    · -- ∀ x, x ≠ r → x ≠ t → (σ1.setNat i 0).sc x = σ.sc x
      intro x hxr hx0
      simp [hσ1, hσ0, Env.setNat_sc, Env.setSc_sc, hxr]
    · -- (σ1.setNat i 0).arr A = σ.arr A
      simp [hσ1, hσ0, Env.setNat_arr, Env.setSc_arr]
    · -- ∀ a, a ≠ A → (σ1.setNat i 0).arr a = σ.arr a
      intro a ha
      simp [hσ1, hσ0, Env.setNat_arr, Env.setSc_arr]
    · -- ∀ j, j ≠ i → j ≠ k → (σ1.setNat i 0).nat j = σ.nat j
      intro j hji hjk
      simp [hσ1, hσ0, Env.setNat_nat, Env.setSc_nat, hji, hjk]
  have hbody : ∀ t' < d, ∀ σ', J t' σ' → σ'.nat i = t' → σ'.nat dv = d → σ'.nat one = 1 →
    Runs L w body σ' 5 (fun σ'' => σ''.nat i = t' ∧ σ''.nat dv = d ∧ σ''.nat one = 1 ∧
      J (t' + 1) (σ''.setNat i (t' + 1))) := by
    intro t' ht' σ' hJ hit' hdt' ho1
    obtain ⟨hJk, hi_eq, hdv_eq, ho1_eq, hJr, hJs, hJa, hJa', hJn, hJd, hJr', hJp⟩ := hJ
    have hk_asz : σ'.nat k < asz d := by
      rw [hJk]
      have h_mul : (d + 1) * t' < (d + 1) * d :=
        Nat.mul_lt_mul_of_pos_left ht' (by omega)
      have h_asz : (d + 1) * d = asz d := by
        unfold asz; ring
      omega
    let σ_t := σ'.setSc t (σ'.arr A (σ'.nat k))
    let σ_tr := σ_t.setSc r (σ_t.sc r + σ_t.sc t)
    have h_aget : Runs L w (aget L t A k) σ' 2 (· = σ_t) := by
      simpa [σ_t] using runs_aget (L := L) (w := w) (σ := σ') ht hA hk hk_asz
    have h_sop2 : Runs L w (sop2 L .add r r t) σ_t 1 (· = σ_tr) := by
      simpa [σ_t, σ_tr, Op2.eval] using runs_sop2 (L := L) (w := w) (σ := σ_t) hr hr ht .add
    let σ_tr2 := σ_tr.setNat k (σ_tr.nat k + σ_tr.nat dv)
    have h_nadd1 : Runs L w (nadd k k dv) σ_tr 1 (· = σ_tr2) := by
      simpa [σ_tr2] using runs_nadd (L := L) (w := w) (σ := σ_tr) hk hk hdv
    have h_nadd2_raw : Runs L w (nadd k k one) σ_tr2 1 (· = σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)) :=
      runs_nadd (L := L) (w := w) (σ := σ_tr2) hk hk hone
    have h_nadd2 : Runs L w (nadd k k one) σ_tr2 1 (· = σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)) :=
      runs_mono h_nadd2_raw (by norm_num) (fun _ e => e)
    have h_inner : Runs L w (.seq (nadd k k dv) (nadd k k one)) σ_tr 2 (fun σ'' =>
      σ''.nat k = (d + 1) * (t' + 1) ∧
      σ''.nat i = t' ∧
      σ''.nat dv = d ∧
      σ''.nat one = 1 ∧
      σ''.sc r = ∑ a ∈ Finset.range (t' + 1), σ.arr A ((d + 1) * a) ∧
      (∀ x, x ≠ r → x ≠ t → σ''.sc x = σ.sc x) ∧
      (σ''.arr A = σ.arr A) ∧ (∀ a, a ≠ A → σ''.arr a = σ.arr a) ∧
      (∀ j, j ≠ i → j ≠ k → σ''.nat j = σ.nat j) ∧
      σ''.draws = σ.draws ∧ σ''.rounds = σ.rounds ∧ σ''.pts = σ.pts) := by
      have h_temp := runs_seq_eq h_nadd1 h_nadd2
      have h_temp' : Runs L w (.seq (nadd k k dv) (nadd k k one)) σ_tr 2 (· = σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)) :=
        runs_mono h_temp (by norm_num) (fun _ e => e)
      refine runs_mono h_temp' (by norm_num) (fun σ'' h => ?_)
      subst h
      have h_final_nat_k : (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).nat k = (d + 1) * (t' + 1) := by
        dsimp [σ_tr2, σ_tr, σ_t]
        rw [Env.setNat_nat]
        simp [hJk, hdt', ho1, Ne.symm hkone]
        ring
      have h_final_nat_i : (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).nat i = t' := by
        dsimp [σ_tr2, σ_tr, σ_t]
        rw [Env.setNat_nat]
        simp [Ne.symm hki, hit']
      have h_final_nat_dv : (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).nat dv = d := by
        dsimp [σ_tr2, σ_tr, σ_t]
        rw [Env.setNat_nat]
        simp [Ne.symm hkdv, hdt']
      have h_final_nat_one : (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).nat one = 1 := by
        dsimp [σ_tr2, σ_tr, σ_t]
        rw [Env.setNat_nat]
        simp [Ne.symm hkone, ho1]
      have h_final_sc_r : (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).sc r = ∑ a ∈ Finset.range (t' + 1), σ.arr A ((d + 1) * a) := by
        dsimp [σ_tr2, σ_tr, σ_t]
        rw [Env.setSc_sc]
        simp [hJr, hJk, hrt]
        rw [hJa, Finset.sum_range_succ]
      have h_final_sc : ∀ x, x ≠ r → x ≠ t → (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).sc x = σ.sc x := by
        intro x hxr hxt
        dsimp [σ_tr2, σ_tr, σ_t]
        simp [Env.setSc_sc]
        split_ifs with hxr'
        · exfalso; exact hxr hxr'
        · exact hJs x hxr hxt
      have h_final_arr_A : (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).arr A = σ.arr A := by
        dsimp [σ_tr2, σ_tr, σ_t]
        simp [hJa]
      have h_final_arr : ∀ a, a ≠ A → (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).arr a = σ.arr a := by
        intro a ha
        dsimp [σ_tr2, σ_tr, σ_t]
        simp [hJa' a ha]
      have h_final_nat_j : ∀ j, j ≠ i → j ≠ k → (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).nat j = σ.nat j := by
        intro j hji hjk
        dsimp [σ_tr2, σ_tr, σ_t]
        rw [Env.setNat_nat]
        simp [hjk, hJn j hji hjk]
      have h_final_draws : (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).draws = σ.draws := by
        dsimp [σ_tr2, σ_tr, σ_t]
        simp [hJd]
      have h_final_rounds : (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).rounds = σ.rounds := by
        dsimp [σ_tr2, σ_tr, σ_t]
        simp [hJr']
      have h_final_pts : (σ_tr2.setNat k (σ_tr2.nat k + σ_tr2.nat one)).pts = σ.pts := by
        dsimp [σ_tr2, σ_tr, σ_t]
        simp [hJp]
      exact ⟨h_final_nat_k, h_final_nat_i, h_final_nat_dv, h_final_nat_one, h_final_sc_r, h_final_sc, h_final_arr_A, h_final_arr, h_final_nat_j, h_final_draws, h_final_rounds, h_final_pts⟩
    have h_mid := runs_seq_eq h_sop2 h_inner
    have h_full := runs_seq_eq h_aget h_mid
    have h_body_chain : Runs L w body σ' 5 (fun σ'' =>
      σ''.nat i = t' ∧ σ''.nat dv = d ∧ σ''.nat one = 1 ∧
      σ''.nat k = (d + 1) * (t' + 1) ∧
      σ''.sc r = ∑ a ∈ Finset.range (t' + 1), σ.arr A ((d + 1) * a) ∧
      (∀ x, x ≠ r → x ≠ t → σ''.sc x = σ.sc x) ∧
      (σ''.arr A = σ.arr A) ∧ (∀ a, a ≠ A → σ''.arr a = σ.arr a) ∧
      (∀ j, j ≠ i → j ≠ k → σ''.nat j = σ.nat j) ∧
      σ''.draws = σ.draws ∧ σ''.rounds = σ.rounds ∧ σ''.pts = σ.pts) := by
      refine runs_mono h_full (by norm_num) (fun σ'' h => ?_)
      obtain ⟨hJk2, hi_eq2, hdv_eq2, ho1_eq2, hJr2, hJs2, hJa2, hJa2', hJn2, hJd2, hJr2', hJp2⟩ := h
      exact ⟨hi_eq2, hdv_eq2, ho1_eq2, hJk2, hJr2, hJs2, hJa2, hJa2', hJn2, hJd2, hJr2', hJp2⟩
    refine runs_mono h_body_chain (by norm_num) (fun σ'' h => ?_)
    obtain ⟨hi_eq2, hdv_eq2, ho1_eq2, hJk2, hJr2, hJs2, hJa2, hJa2', hJn2, hJd2, hJr2', hJp2⟩ := h
    have hJ : J (t' + 1) (σ''.setNat i (t' + 1)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- σ''.nat k = (d + 1) * (t' + 1)
        rw [Env.setNat_nat]
        simp [hki, hJk2]
      · -- σ''.nat i = t' + 1
        rw [Env.setNat_nat]
        simp []
      · -- σ''.nat dv = d
        rw [Env.setNat_nat]
        simp [Ne.symm hidv, hdv_eq2]
      · -- σ''.nat one = 1
        rw [Env.setNat_nat]
        simp [Ne.symm hione, ho1_eq2]
      · -- σ''.sc r = ∑ a ∈ Finset.range (t' + 1), σ.arr A ((d + 1) * a)
        simp [hJr2]
      · -- ∀ x, x ≠ r → x ≠ t → σ''.sc x = σ.sc x
        intro x hxr hxt'
        simp [Env.setNat_sc, hJs2 x hxr hxt']
      · -- σ''.arr A = σ.arr A
        simp [Env.setNat_arr, hJa2]
      · -- ∀ a, a ≠ A → σ''.arr a = σ.arr a
        intro a ha
        simp [Env.setNat_arr, hJa2' a ha]
      · -- ∀ j, j ≠ i → j ≠ k → σ''.nat j = σ.nat j
        intro j hji' hjk
        simpa [Env.setNat_nat, hji'] using hJn2 j hji' hjk
      · exact hJd2
      · exact hJr2'
      · exact hJp2
    refine ⟨hi_eq2, hdv_eq2, ho1_eq2, hJ⟩
  have hfor := runs_forN hi hdv hone hidv hione d 5 J σ1 h_init_dv h_init_one hJ0 hbody
  -- Chain: sconst then nconst then forN
  have h_sconst : Runs L w (sconst L r 0) σ 1 (· = σ0) := by
    simpa [hσ0] using runs_sconst (L := L) (w := w) (σ := σ) hr (0 : ℚ)
  have h_nconst : Runs L w (nconst k 0) σ0 1 (· = σ1) := by
    have h := runs_nconst (L := L) (w := w) (σ := σ0) hk 0
    simpa [hσ1] using h
  have h_rest := runs_seq_eq h_nconst hfor
  have h_mtrace : Runs L w (mtrace L dv one i k r A t) σ (d * 8 + 5)
      (fun σ' => J d σ' ∧ σ'.nat i = d ∧ σ'.nat dv = d ∧ σ'.nat one = 1) := by
    have h := runs_seq_eq h_sconst h_rest
    have hcost : 1 + (1 + (d * (5 + 3) + 3)) = d * 8 + 5 := by omega
    simpa [mtrace, body, hcost] using h
  refine runs_mono h_mtrace (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨hJd, hi_eq, hdv_eq, ho1_eq, hJr, hJs, hJa, hJa', hJn, hJd', hJr', hJp⟩, hi_eq2, hdv_eq2, ho1_eq2⟩ := h
  have hsum : σ'.sc r = (σ.mat A).trace := by
    rw [hJr]
    calc
      ∑ a ∈ Finset.range d, σ.arr A ((d + 1) * a) = ∑ a : Fin d, σ.arr A ((d + 1) * a.val) := by
        rw [Fin.sum_univ_eq_sum_range (fun n => σ.arr A ((d + 1) * n)) d]
      _ = ∑ a : Fin d, σ.arr A (d * a.val + a.val) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring_nf
      _ = ∑ a : Fin d, (σ.mat A) a a := by
        simp [Env.mat]
      _ = (σ.mat A).trace := by simp [Matrix.trace]
  have hframe : Env.Frame σ σ' [i, k] [r, t] [] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hji' : j = i
      · exfalso; apply hj; simp [hji']
      · by_cases hjk' : j = k
        · exfalso; apply hj; simp [hjk']
        · exact hJn j hji' hjk'
    · intro x hx
      by_cases hxr' : x = r
      · exfalso; apply hx; simp [hxr']
      · by_cases hxt' : x = t
        · exfalso; apply hx; simp [hxt']
        · exact hJs x hxr' hxt'
    · intro a ha
      simp at ha
      by_cases haA : a = A
      · subst haA; exact hJa
      · exact hJa' a haA
    · exact hJd'
    · exact hJr'
    · exact hJp
  exact ⟨hsum, hframe⟩

/-- An entry `d r + t` of a `d × d` matrix is below `d²`. -/
theorem idx_lt_sq {r t : ℕ} (hr : r < d) (ht : t < d) : d * r + t < d * d :=
  calc d * r + t < d * r + d := by omega
    _ = d * (r + 1) := by ring
    _ ≤ d * d := Nat.mul_le_mul_left d hr

/-- An entry `d r + t` of a `d × d` matrix is a cell of an array. -/
theorem idx_lt_asz {r t : ℕ} (hr : r < d) (ht : t < d) : d * r + t < asz d := by
  have := idx_lt_sq hr ht; unfold asz; omega

/-- One entry of `mmul`: `s := s + (A B)_{r c}`, the indices `kA` along row `r` of `A` and `kB` down column `c` of
`B`. -/
theorem runs_mmulDot
    {dv one l kA kB A B s t1 t2 : ℕ} (σ : Env d) (r c : Fin d) (hdv : dv < L.NN) (hone : one < L.NN)
    (hl : l < L.NN) (hkA : kA < L.NN) (hkB : kB < L.NN) (hA : A < L.NA) (hB : B < L.NA) (hs : s < L.NS)
    (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hldv : l ≠ dv) (hlone : l ≠ one) (hlA : l ≠ kA) (hlB : l ≠ kB)
    (hAB : kA ≠ kB) (hkAdv : kA ≠ dv) (hkAone : kA ≠ one) (hkBdv : kB ≠ dv) (hkBone : kB ≠ one)
    (hs1 : s ≠ t1) (hs2 : s ≠ t2) (h12 : t1 ≠ t2) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hkAr : σ.nat kA = d * r) (hkBc : σ.nat kB = c) :
    Runs L w (forN l dv one (.seq (aget L t1 A kA) (.seq (aget L t2 B kB) (.seq (sop2 L .mul t1 t1 t2)
      (.seq (sop2 L .add s s t1) (.seq (nadd kA kA one) (nadd kB kB dv))))))) σ (d * 11 + 3)
      (fun σ' => σ'.sc s = σ.sc s + (σ.mat A * σ.mat B) r c ∧ σ'.nat kA = d * r + d ∧ σ'.nat kB = c + d * d ∧
        Env.Frame σ σ' [l, kA, kB] [s, t1, t2] []) := by
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.sc s = σ.sc s + ∑ m ∈ Finset.range t, σ.arr A (d * r + m) * σ.arr B (d * m + c) ∧
      σ'.nat kA = d * r + t ∧ σ'.nat kB = c + d * t ∧
      (∀ z, z ≠ s → z ≠ t1 → z ≠ t2 → σ'.sc z = σ.sc z) ∧ (∀ a, σ'.arr a = σ.arr a) ∧
      (∀ q, q ≠ l → q ≠ kA → q ≠ kB → σ'.nat q = σ.nat q) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧
      σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := .seq (aget L t1 A kA) (.seq (aget L t2 B kB)
      (.seq (sop2 L .mul t1 t1 t2) (.seq (sop2 L .add s s t1) (.seq (nadd kA kA one) (nadd kB kB dv))))))
    hl hdv hone hldv hlone d 8 J σ hd h1
    ⟨by simp, by simp [Ne.symm hlA, hkAr], by simp [Ne.symm hlB, hkBc], fun z _ _ _ => by simp, fun a => by simp,
      fun q hql _ _ => by simp [hql], by simp, by simp, by simp⟩
    (fun t ht σ' hJ hlt hdt hot => by
      obtain ⟨Js, JkA, JkB, Jz, Ja, Jn, Jd, Jr, Jp⟩ := hJ
      have hiA : σ'.nat kA < asz d := by rw [JkA]; exact idx_lt_asz r.2 ht
      have hiB : σ'.nat kB < asz d := by rw [JkB, Nat.add_comm]; exact idx_lt_asz ht c.2
      refine runs_mono (runs_seq_eq (runs_aget (w := w) (σ := σ') ht1 hA hkA hiA)
        (runs_seq_eq (runs_aget (w := w) ht2 hB hkB (by simpa using hiB))
          (runs_seq_eq (runs_sop2 (w := w) ht1 ht1 ht2 .mul)
            (runs_seq_eq (runs_sop2 (w := w) hs hs ht1 .add)
              (runs_seq_eq (runs_nadd (w := w) hkA hkA hone) (runs_nadd (w := w) hkB hkB hdv))))))
        (by norm_num) (fun σ5 e5 => ?_)
      subst e5
      refine ⟨by simp [hlA, hlB, hlt], by simp [Ne.symm hkAdv, Ne.symm hkBdv, hdt],
        by simp [Ne.symm hkAone, Ne.symm hkBone, hot], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hs1, hs2, h12, Op2.eval, Js, JkA, JkB, Ja, Finset.sum_range_succ]; ring_nf
      · simp [Ne.symm hlA, hAB, JkA, hot]; ring
      · simp [Ne.symm hlB, Ne.symm hAB, JkB, Ne.symm hkAdv, hdt]; ring
      · intro z hz1 hz2 hz3; simp [hz1, hz2, hz3, Jz z hz1 hz2 hz3]
      · intro a; simp [Ja]
      · intro q hql hqA hqB; simp [hql, hqA, hqB, Jn q hql hqA hqB]
      · simp [Jd]
      · simp [Jr]
      · simp [Jp])
  refine runs_mono hfor (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨Js, JkA, JkB, Jz, Ja, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, JkA, JkB, fun q hq => ?_, fun z hz => ?_, fun a _ => Ja a, Jd, Jr, Jp⟩
  · rw [Js]; congr 1
    simp only [Matrix.mul_apply, Env.mat]
    exact (Fin.sum_univ_eq_sum_range (fun m => σ.arr A (d * r + m) * σ.arr B (d * m + c)) d).symm
  · simp at hq; exact Jn q hq.1 hq.2.1 hq.2.2
  · simp at hz; exact Jz z hz.1 hz.2.1 hz.2.2

/-- One row of `mtransp`: row `r` of `B` is column `r` of `A`, the indices `kA` down column `r` of `A` and `kB` along
row `r` of `B`. -/
theorem runs_mtranspRow
    {dv one j kA kB B A t : ℕ} (σ : Env d) (r : Fin d) (hdv : dv < L.NN) (hone : one < L.NN) (hj : j < L.NN)
    (hkA : kA < L.NN) (hkB : kB < L.NN) (hB : B < L.NA) (hA : A < L.NA) (ht : t < L.NS) (hBA : B ≠ A)
    (hjdv : j ≠ dv) (hjone : j ≠ one) (hjA : j ≠ kA) (hjB : j ≠ kB) (hAB : kA ≠ kB) (hkAdv : kA ≠ dv)
    (hkAone : kA ≠ one) (hkBdv : kB ≠ dv) (hkBone : kB ≠ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hkAr : σ.nat kA = r) (hkBr : σ.nat kB = d * r) :
    Runs L w (forN j dv one (.seq (aget L t A kA) (.seq (aset L B kB t) (.seq (nadd kA kA dv) (nadd kB kB one)))))
      σ (d * 9 + 3)
      (fun σ' => (∀ m, σ'.arr B m = if d * r ≤ m ∧ m < d * r + d then σ.arr A (d * (m - d * r) + r)
          else σ.arr B m) ∧ σ'.nat kA = r + d * d ∧ σ'.nat kB = d * r + d ∧
        Env.Frame σ σ' [j, kA, kB] [t] [B]) := by
  let J : ℕ → Env d → Prop := fun t' σ' =>
    (∀ m, σ'.arr B m = if d * r ≤ m ∧ m < d * r + t' then σ.arr A (d * (m - d * r) + r) else σ.arr B m) ∧
      σ'.nat kA = r + d * t' ∧ σ'.nat kB = d * r + t' ∧ (∀ z, z ≠ t → σ'.sc z = σ.sc z) ∧
      (∀ a, a ≠ B → σ'.arr a = σ.arr a) ∧ (∀ q, q ≠ j → q ≠ kA → q ≠ kB → σ'.nat q = σ.nat q) ∧
      σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := .seq (aget L t A kA) (.seq (aset L B kB t)
      (.seq (nadd kA kA dv) (nadd kB kB one)))) hj hdv hone hjdv hjone d 6 J σ hd h1
    ⟨fun m => by simp, by simp [Ne.symm hjA, hkAr], by simp [Ne.symm hjB, hkBr], fun z _ => by simp,
      fun a _ => by simp, fun q hqj _ _ => by simp [hqj], by simp, by simp, by simp⟩
    (fun t' ht' σ' hJ hjt hdt hot => by
      obtain ⟨JB, JkA, JkB, Jz, Ja, Jn, Jd, Jr, Jp⟩ := hJ
      have hiA : σ'.nat kA < asz d := by rw [JkA, Nat.add_comm]; exact idx_lt_asz ht' r.2
      have hiB : σ'.nat kB < asz d := by rw [JkB]; exact idx_lt_asz r.2 ht'
      refine runs_mono (runs_seq_eq (runs_aget (w := w) (σ := σ') ht hA hkA hiA)
        (runs_seq_eq (runs_aset (w := w) hB hkB ht (by simpa using hiB))
          (runs_seq_eq (runs_nadd (w := w) hkA hkA hdv) (runs_nadd (w := w) hkB hkB hone))))
        (by norm_num) (fun σ5 e5 => ?_)
      subst e5
      refine ⟨by simp [hjA, hjB, hjt], by simp [Ne.symm hkAdv, Ne.symm hkBdv, hdt],
        by simp [Ne.symm hkAone, Ne.symm hkBone, hot], fun m => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hAA : σ'.arr A = σ.arr A := Ja A (Ne.symm hBA)
        simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_sc, ite_true, Env.setSc_nat, JkB, JkA, true_and,
          hAA, JB m]
        split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; subst_vars; rw [Nat.add_sub_cancel_left]; ring)
      · simp [Ne.symm hjA, hAB, JkA, hdt]; ring
      · simp [Ne.symm hjB, Ne.symm hAB, JkB, hot, Ne.symm hkAone]; omega
      · intro z hz; simp [hz, Jz z hz]
      · intro a ha; funext m; simp [ha, Ja a ha]
      · intro q hqj hqA hqB; simp [hqj, hqA, hqB, Jn q hqj hqA hqB]
      · simp [Jd]
      · simp [Jr]
      · simp [Jp])
  refine runs_mono hfor (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨JB, JkA, JkB, Jz, Ja, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨JB, JkA, JkB, fun q hq => ?_, fun z hz => ?_, fun a ha => ?_, Jd, Jr, Jp⟩
  · simp at hq; exact Jn q hq.1 hq.2.1 hq.2.2
  · simp at hz; exact Jz z hz
  · simp at ha; exact Ja a ha

/-- One row of `rankOne`: row `r` of `A` becomes `α A_r + β u_r v`, the index `k` along row `r`. -/
theorem runs_rankOneRow
    {dv one i j k A α β u v t1 t2 t3 : ℕ} (σ : Env d) (r : Fin d) (hdv : dv < L.NN) (hone : one < L.NN)
    (hi : i < L.NN) (hj : j < L.NN) (hk : k < L.NN) (hA : A < L.NA) (hu : u < L.NA) (hv : v < L.NA)
    (hα : α < L.NS) (hβ : β < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (ht3 : t3 < L.NS)
    (hjdv : j ≠ dv) (hjone : j ≠ one) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hkdv : k ≠ dv)
    (hkone : k ≠ one) (hAu : A ≠ u) (hAv : A ≠ v) (h12 : t1 ≠ t2) (h13 : t1 ≠ t3) (h23 : t2 ≠ t3)
    (hα1 : α ≠ t1) (hα2 : α ≠ t2) (hα3 : α ≠ t3) (hβ1 : β ≠ t1) (hβ2 : β ≠ t2) (hβ3 : β ≠ t3)
    (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hir : σ.nat i = r) (hkr : σ.nat k = d * r) :
    Runs L w (forN j dv one (.seq (aget L t1 A k) (.seq (sop2 L .mul t1 α t1) (.seq (aget L t2 u i)
      (.seq (sop2 L .mul t2 β t2) (.seq (aget L t3 v j) (.seq (sop2 L .mul t2 t2 t3) (.seq (sop2 L .add t1 t1 t2)
        (.seq (aset L A k t1) (nadd k k one)))))))))) σ (d * 16 + 3)
      (fun σ' => (∀ m, σ'.arr A m = if d * r ≤ m ∧ m < d * r + d then
          σ.sc α * σ.arr A m + σ.sc β * σ.arr u r * σ.arr v (m - d * r) else σ.arr A m) ∧
        σ'.nat k = d * r + d ∧ Env.Frame σ σ' [j, k] [t1, t2, t3] [A]) := by
  let J : ℕ → Env d → Prop := fun t σ' =>
    (∀ m, σ'.arr A m = if d * r ≤ m ∧ m < d * r + t then
        σ.sc α * σ.arr A m + σ.sc β * σ.arr u r * σ.arr v (m - d * r) else σ.arr A m) ∧
      σ'.nat k = d * r + t ∧ (∀ z, z ≠ t1 → z ≠ t2 → z ≠ t3 → σ'.sc z = σ.sc z) ∧
      (∀ a, a ≠ A → σ'.arr a = σ.arr a) ∧ (∀ q, q ≠ j → q ≠ k → σ'.nat q = σ.nat q) ∧
      σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := .seq (aget L t1 A k) (.seq (sop2 L .mul t1 α t1)
      (.seq (aget L t2 u i) (.seq (sop2 L .mul t2 β t2) (.seq (aget L t3 v j) (.seq (sop2 L .mul t2 t2 t3)
        (.seq (sop2 L .add t1 t1 t2) (.seq (aset L A k t1) (nadd k k one))))))))) hj hdv hone hjdv hjone d 13 J σ hd h1
    ⟨fun m => by simp, by simp [Ne.symm hjk, hkr], fun z _ _ _ => by simp, fun a _ => by simp,
      fun q hqj _ => by simp [hqj], by simp, by simp, by simp⟩
    (fun t ht σ' hJ hjt hdt hot => by
      obtain ⟨JA, Jk, Jz, Ja, Jn, Jd, Jr, Jp⟩ := hJ
      have hα' : σ'.sc α = σ.sc α := Jz α hα1 hα2 hα3
      have hβ' : σ'.sc β = σ.sc β := Jz β hβ1 hβ2 hβ3
      have hu' : σ'.arr u = σ.arr u := Ja u (Ne.symm hAu)
      have hv' : σ'.arr v = σ.arr v := Ja v (Ne.symm hAv)
      have hi' : σ'.nat i = r := by rw [Jn i hij hik, hir]
      have hiA : σ'.nat k < asz d := by rw [Jk]; exact idx_lt_asz r.2 ht
      refine runs_mono (runs_seq_eq (runs_aget (w := w) (σ := σ') ht1 hA hk hiA)
        (runs_seq_eq (runs_sop2 (w := w) ht1 hα ht1 .mul)
          (runs_seq_eq (runs_aget (w := w) ht2 hu hi (by simp [hi']; exact lt_asz r.2))
            (runs_seq_eq (runs_sop2 (w := w) ht2 hβ ht2 .mul)
              (runs_seq_eq (runs_aget (w := w) ht3 hv hj (by simp [hjt]; exact lt_asz ht))
                (runs_seq_eq (runs_sop2 (w := w) ht2 ht2 ht3 .mul)
                  (runs_seq_eq (runs_sop2 (w := w) ht1 ht1 ht2 .add)
                    (runs_seq_eq (runs_aset (w := w) hA hk ht1 (by simpa using hiA))
                      (runs_nadd (w := w) hk hk hone)))))))))
        (by norm_num) (fun σ5 e5 => ?_)
      subst e5
      refine ⟨by simp [hjk, hjt], by simp [Ne.symm hkdv, hdt], by simp [Ne.symm hkone, hot], fun m => ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_sc, Env.setSc_nat, ite_true, true_and,
          Jk, hjt, hi', JA, hα', hβ', hu', hv', h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23, hα1,
          hβ1, hβ2, ite_false, Op2.eval]
        split_ifs <;> first | rfl | (exfalso; omega) | (subst_vars; simp)
      · simp [Ne.symm hjk, Jk, hot]; omega
      · intro z hz1 hz2 hz3; simp [hz1, hz2, hz3, Jz z hz1 hz2 hz3]
      · intro a ha; funext m; simp [ha, Ja a ha]
      · intro q hqj hqk; simp [hqj, hqk, Jn q hqj hqk]
      · simp [Jd]
      · simp [Jr]
      · simp [Jp])
  refine runs_mono hfor (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨⟨JA, Jk, Jz, Ja, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨JA, Jk, fun q hq => ?_, fun z hz => ?_, fun a ha => ?_, Jd, Jr, Jp⟩
  · simp at hq; exact Jn q hq.1 hq.2
  · simp at hz; exact Jz z hz.1 hz.2.1 hz.2.2
  · simp at ha; exact Ja a ha

/-- The rule of `rankOne`: `A := α A + β u vᵀ`. -/
theorem runs_rankOne {dv one i j k A α β u v t1 t2 t3 : ℕ} (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN)
    (hi : i < L.NN) (hj : j < L.NN) (hk : k < L.NN) (hA : A < L.NA) (hu : u < L.NA) (hv : v < L.NA)
    (hα : α < L.NS) (hβ : β < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (ht3 : t3 < L.NS) (hidv : i ≠ dv)
    (hione : i ≠ one) (hjdv : j ≠ dv) (hjone : j ≠ one) (hkdv : k ≠ dv) (hkone : k ≠ one) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hAu : A ≠ u) (hAv : A ≠ v) (h12 : t1 ≠ t2) (h13 : t1 ≠ t3) (h23 : t2 ≠ t3)
    (hα1 : α ≠ t1) (hα2 : α ≠ t2) (hα3 : α ≠ t3) (hβ1 : β ≠ t1) (hβ2 : β ≠ t2) (hβ3 : β ≠ t3)
    (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (rankOne L dv one i j k A α β u v t1 t2 t3) σ (d * (d * 16 + 6) + 4)
      (fun σ' => σ'.mat A = σ.sc α • σ.mat A + σ.sc β • vecMulVec (σ.vec u) (σ.vec v) ∧
        Env.Frame σ σ' [i, j, k] [t1, t2, t3] [A] ∧ ∀ m, d * d ≤ m → σ'.arr A m = σ.arr A m) := by
  let g : ℕ → ℝ := fun m => σ.sc α * σ.arr A m + σ.sc β * σ.arr u (m / d) * σ.arr v (m % d)
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.nat k = d * t ∧ (∀ m, σ'.arr A m = if m < d * t then g m else σ.arr A m) ∧
      (∀ b, b ≠ A → σ'.arr b = σ.arr b) ∧ (∀ z, z ≠ t1 → z ≠ t2 → z ≠ t3 → σ'.sc z = σ.sc z) ∧
      (∀ q, q ≠ i → q ≠ j → q ≠ k → σ'.nat q = σ.nat q) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧
      σ'.pts = σ.pts
  have hdk : (σ.setNat k 0).nat dv = d := by simp [Ne.symm hkdv, hd]
  have h1k : (σ.setNat k 0).nat one = 1 := by simp [Ne.symm hkone, h1]
  have hfor := runs_forN (L := L) (w := w) (body := forN j dv one (.seq (aget L t1 A k) (.seq (sop2 L .mul t1 α t1)
      (.seq (aget L t2 u i) (.seq (sop2 L .mul t2 β t2) (.seq (aget L t3 v j) (.seq (sop2 L .mul t2 t2 t3)
        (.seq (sop2 L .add t1 t1 t2) (.seq (aset L A k t1) (nadd k k one)))))))))) hi hdv hone hidv hione d
      (d * 16 + 3) J (σ.setNat k 0) hdk h1k
    ⟨by simp, fun m => by simp, fun b _ => rfl, fun z _ _ _ => rfl,
      fun q hqi _ hqk => by simp [hqi, hqk], rfl, rfl, rfl⟩
    (fun t ht σ' hJ hit hdt hot => by
      obtain ⟨Jk, JA, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      refine runs_mono (runs_rankOneRow (w := w) σ' ⟨t, ht⟩ hdv hone hi hj hk hA hu hv hα hβ ht1 ht2 ht3 hjdv hjone
        hij hik hjk hkdv hkone hAu hAv h12 h13 h23 hα1 hα2 hα3 hβ1 hβ2 hβ3 hdt hot hit Jk) le_rfl
        (fun σ2 h2 => ?_)
      obtain ⟨e2A, e2k, F2n, F2s, F2a, F2d, F2r, F2p⟩ := h2
      have hα' : σ'.sc α = σ.sc α := Js α hα1 hα2 hα3
      have hβ' : σ'.sc β = σ.sc β := Js β hβ1 hβ2 hβ3
      have hu' : σ'.arr u = σ.arr u := Jb u (Ne.symm hAu)
      have hv' : σ'.arr v = σ.arr v := Jb v (Ne.symm hAv)
      refine ⟨by rw [F2n i (by simp [hij, hik])]; exact hit, by rw [F2n dv (by simp [Ne.symm hjdv, Ne.symm hkdv])]; exact hdt,
        by rw [F2n one (by simp [Ne.symm hjone, Ne.symm hkone])]; exact hot, ?_⟩
      refine ⟨by simp [Ne.symm hik, e2k]; ring, fun m => ?_, fun b hb => ?_, fun z hz1 hz2 hz3 => ?_,
        fun q hqi hqj hqk => ?_, by simp [F2d, Jd], by simp [F2r, Jr], by simp [F2p, Jp]⟩
      · simp only [Env.setNat_arr]
        rw [e2A m, JA m]
        by_cases hm1 : m < d * t
        · have : m < d * (t + 1) := by rw [Nat.mul_succ]; omega
          simp [hm1, this, show ¬ d * t ≤ m by omega]
        · by_cases hm2 : m < d * t + d
          · have hq : m / d = t := by
              exact Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega) (by rw [Nat.add_mul, one_mul, Nat.mul_comm]; omega)
            have hr : m % d = m - d * t := by
              rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]
            simp only [hm1, ite_false, show d * t ≤ m by omega, hm2, and_self, ite_true,
              show m < d * (t + 1) by rw [Nat.mul_succ]; omega, g, hα', hβ', hu', hv', hq, hr]
          · simp [hm1, hm2, show ¬ m < d * (t + 1) by rw [Nat.mul_succ]; omega]
      · simp only [Env.setNat_arr]; rw [F2a b (by simpa using hb), Jb b hb]
      · simp [F2s z (by simp [hz1, hz2, hz3]), Js z hz1 hz2 hz3]
      · simp [hqi, F2n q (by simp [hqj, hqk]), Jn q hqi hqj hqk])
  refine runs_mono (K := 1 + (d * ((d * 16 + 3) + 3) + 3)) (runs_seq_eq (runs_nconst hk 0) hfor)
    (le_of_eq (by ring)) (fun σ' h => ?_)
  obtain ⟨⟨Jk, JA, Jb, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ⟨fun q hq => ?_, fun z hz => ?_, fun b hb => Jb b (by simpa using hb), Jd, Jr, Jp⟩,
    fun m hm => by rw [JA]; simp; omega⟩
  · funext a b
    have hab : d * (a : ℕ) + b < d * d := by
      have := a.2; have := b.2; nlinarith
    have hpos : 0 < d := Nat.pos_of_ne_zero (fun h => by subst h; exact a.elim0)
    have hq : (d * (a : ℕ) + b) / d = a := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt b.2, Nat.zero_add]
    have hr : (d * (a : ℕ) + b) % d = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.2]
    simp only [Env.mat, JA, hab, ite_true, g, hq, hr, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
      Env.vec, smul_eq_mul]
    ring
  · simp at hq; simp [Jn q hq.1 hq.2.1 hq.2.2]
  · simp at hz; exact Js z hz.1 hz.2.1 hz.2.2

open Classical in
/-- `o := [T y + μ ∈ K]`, with `tmp := T y + μ`. -/
theorem runs_memAff {dv one i j k o mu T y tmp c s t1 t2 : ℕ} (σ : Env d) (hdv : dv < L.NN)
    (hone : one < L.NN) (hi : i < L.NN) (hj : j < L.NN) (hk : k < L.NN) (ho : o < L.NS) (hmu : mu < L.NA)
    (hT : T < L.NA) (hy : y < L.NA) (htmp : tmp < L.NA) (hc : c < L.NS) (hs : s < L.NS) (ht1 : t1 < L.NS)
    (ht2 : t2 < L.NS) (hidv : i ≠ dv) (hione : i ≠ one) (hjdv : j ≠ dv) (hjone : j ≠ one) (hkdv : k ≠ dv)
    (hkone : k ≠ one) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (htmpy : tmp ≠ y) (htmpT : tmp ≠ T)
    (htmpmu : tmp ≠ mu) (hs1 : s ≠ t1) (hs2 : s ≠ t2) (h12 : t1 ≠ t2) (hc1 : c ≠ t1) (hc2 : c ≠ t2)
    (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (memAff L dv one i j k o mu T y tmp c s t1 t2) σ (d * (d * 10 + 9) + d * 11 + 9)
      (fun σ' => σ'.sc o = (if WithLp.toLp 2 (σ.mat T *ᵥ σ.vec y + σ.vec mu) ∈ w.K then 1 else 0) ∧
        σ'.vec tmp = σ.mat T *ᵥ σ.vec y + σ.vec mu ∧ Env.Frame σ σ' [i, j, k] [o, c, s, t1, t2] [tmp] ∧
        ∀ m, d ≤ m → σ'.arr tmp m = σ.arr tmp m) := by
  have hm := runs_matvec (w := w) σ hdv hone hi hj hk htmp hT hy hs ht1 ht2 hidv hione hjdv hjone hkdv hkone hij hik hjk
    htmpy htmpT hs1 hs2 h12 hd h1
  refine runs_mono (K := d * (d * 10 + 9) + 4 + (1 + (d * 11 + 3 + 1))) (runs_seq hm (fun σ1 h1' => ?_))
    (by ring_nf; omega) (fun σ' h => h)
  obtain ⟨e1, F1, hi1⟩ := h1'
  have hd1 : (σ1.setSc c ((1 : ℚ) : ℝ)).nat dv = d := by
    simp [F1.1 dv (by simp [hidv.symm, hjdv.symm, hkdv.symm]), hd]
  have ho1 : (σ1.setSc c ((1 : ℚ) : ℝ)).nat one = 1 := by
    simp [F1.1 one (by simp [hione.symm, hjone.symm, hkone.symm]), h1]
  refine runs_seq_eq (runs_sconst hc 1) (runs_seq (runs_vaxpy (w := w) _ hdv hone hi htmp hmu hc ht1 ht2 hidv hione
    h12 hc1 hc2 hd1 ho1) (fun σ3 h3 => runs_mono (runs_query (w := w) (σ := σ3) ho htmp) le_rfl
      (fun σ4 e4 => ?_)))
  obtain ⟨e3, F3, hi3⟩ := h3
  have hmu1 : σ1.vec mu = σ.vec mu := funext fun r => by
    simp only [Env.vec]; rw [F1.2.2.1 mu (by simp [htmpmu.symm])]
  have hv3 : σ3.vec tmp = σ.mat T *ᵥ σ.vec y + σ.vec mu := by
    have q1 : (σ1.setSc c ((1 : ℚ) : ℝ)).vec tmp = σ1.vec tmp := rfl
    have q2 : (σ1.setSc c ((1 : ℚ) : ℝ)).vec mu = σ1.vec mu := rfl
    have q3 : (σ1.setSc c ((1 : ℚ) : ℝ)).sc c = 1 := by simp
    rw [e3, q1, q2, q3, e1, hmu1, one_smul]
  subst e4
  refine ⟨by simp only [Env.setSc_sc, ite_true]; exact if_congr (by rw [hv3]) rfl rfl, hv3, ?_,
    fun m hm => by simp [hi3 m hm, hi1 m hm]⟩
  refine ⟨fun q hq => ?_, fun x hx => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
  · simp only [Env.setSc_nat]
    rw [F3.1 q (by simp at hq ⊢; exact hq.1), Env.setSc_nat, F1.1 q hq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Env.setSc_sc, hx.1, ite_false]
    rw [F3.2.1 x (by simp [hx.2.2.2.1, hx.2.2.2.2])]
    simp only [Env.setSc_sc, hx.2.1, ite_false]
    rw [F1.2.1 x (by simp [hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2])]
  · simp only [Env.setSc_arr]
    rw [F3.2.2.1 a ha, Env.setSc_arr, F1.2.2.1 a ha]
  · simp [F3.2.2.2.1, F1.2.2.2.1]
  · simp [F3.2.2.2.2.1, F1.2.2.2.2.1]
  · simp [F3.2.2.2.2.2, F1.2.2.2.2.2]

end AdversarialBco.Poly.Mach.VL
