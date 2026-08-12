import RequestProject.Phi

/-!
# The certificate structures, the Bool checker, and its soundness
-/

namespace BandDual

set_option maxRecDepth 40000

/-! ### Certificate structures -/

/-- One recorded band: `[lo,hi]` (scaled by `2^64`), an upper bound `F` for `f`
on it, the square-completion bound `B`, and the interior boundaries of its
sub-cells. -/
structure Bnd where
  lo : ℤ
  hi : ℤ
  F : ℤ
  B : ℤ
  sub : List ℤ

/-- One recorded depth. -/
structure Dep where
  yn : ℤ
  yd : ℤ
  w : ℤ
  K : ℤ
  s2 : ℤ
  Cup : ℤ
  Plo : ℤ
  tail : ℤ
  cap : ℤ
  slack : ℤ
  bands : List Bnd
  segs : List (List ℤ)
  ocells : List ℤ

/-- The resolved bound `G = 98`, scaled. -/
def GSO : ℤ := 98 * SO

/-! ### Comparison helpers -/

/-- The upper endpoint is at most `m / 2^64`. -/
def hiLe (o : EIv) (m : ℤ) : Bool :=
  match o with
  | none => false
  | some a => decide (a.hi ≤ m)

/-- The lower endpoint is at least `m / 2^64`. -/
def loGe (o : EIv) (m : ℤ) : Bool :=
  match o with
  | none => false
  | some a => decide (m ≤ a.lo)

theorem hiLe_sound {o : EIv} {x : ℝ} {m : ℤ} (h : hiLe o m = true) (hm : o.mem x) :
    x ≤ (m : ℝ) / (SO : ℝ) := by
  cases o with
  | none => simp [hiLe] at h
  | some a =>
      simp only [hiLe, decide_eq_true_eq] at h
      obtain ⟨_, h2⟩ := hm
      have h' : ((a.hi : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
      rw [le_div_iff₀ SOR_pos]
      nlinarith

theorem loGe_sound {o : EIv} {x : ℝ} {m : ℤ} (h : loGe o m = true) (hm : o.mem x) :
    (m : ℝ) / (SO : ℝ) ≤ x := by
  cases o with
  | none => simp [loGe] at h
  | some a =>
      simp only [loGe, decide_eq_true_eq] at h
      obtain ⟨h1, _⟩ := hm
      have h' : (m : ℝ) ≤ ((a.lo : ℤ) : ℝ) := by exact_mod_cast h
      rw [div_le_iff₀ SOR_pos]
      nlinarith

/-- A real number in the scaled cell `[lo, hi]`. -/
def inCell (lo hi : ℤ) (g : ℝ) : Prop := (lo : ℝ) ≤ (SO : ℝ) * g ∧ (SO : ℝ) * g ≤ (hi : ℝ)

theorem cell_mem {lo hi : ℤ} {g : ℝ} (h : inCell lo hi g) :
    EIv.mem (some ⟨lo, hi⟩) g := h

/-! ### The depth context -/

/-- Enclosure of `y`. -/
def Yiv (d : Dep) : EIv := EIv.ofQ d.yn d.yd

/-- Enclosure of `sinh (y/2)`. -/
def SHiv (d : Dep) : EIv := (sinhCoshSmall (EIv.divInt (Yiv d) 2)).1

/-- Enclosure of `cosh (y/2)`. -/
def CHiv (d : Dep) : EIv := (sinhCoshSmall (EIv.divInt (Yiv d) 2)).2

/-- The depth of a record, as a real number. -/
noncomputable def yOf (d : Dep) : ℝ := (d.yn : ℝ) / (d.yd : ℝ)

/-- The basic well-formedness of a depth record: `0 < y ≤ 1/2`. -/
def basicOK (d : Dep) : Bool := decide (0 < d.yd ∧ 0 < d.yn ∧ 2 * d.yn ≤ d.yd)

/-- The arithmetic facts about the depth that the soundness proofs use. -/
structure Ctx (d : Dep) : Prop where
  ydpos : 0 < d.yd
  ypos : 0 < yOf d
  yle : yOf d ≤ 1 / 2
  ymem : (Yiv d).mem (yOf d)
  shmem : (SHiv d).mem (Real.sinh (yOf d / 2))
  chmem : (CHiv d).mem (Real.cosh (yOf d / 2))

theorem ctx_of_basic {d : Dep} (h : basicOK d = true) : Ctx d := by
  simp only [basicOK, decide_eq_true_eq] at h
  obtain ⟨hd, hn, hnd⟩ := h
  have hd' : (0:ℝ) < (d.yd : ℝ) := by exact_mod_cast hd
  have hn' : (0:ℝ) < (d.yn : ℝ) := by exact_mod_cast hn
  have hnd' : 2 * (d.yn : ℝ) ≤ (d.yd : ℝ) := by exact_mod_cast hnd
  have hypos : 0 < yOf d := div_pos hn' hd'
  have hyle : yOf d ≤ 1 / 2 := by
    rw [yOf, div_le_div_iff₀ hd' (by norm_num)]
    linarith
  have hymem : (Yiv d).mem (yOf d) := EIv.ofQ_mem hd
  have hhalf : (EIv.divInt (Yiv d) 2).mem (yOf d / 2) := by
    have := EIv.divInt_mem (d := 2) (by norm_num) hymem
    simpa using this
  have habs : |yOf d / 2| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  exact ⟨hd, hypos, hyle, hymem, (sinhCoshSmall_mem hhalf habs).1, (sinhCoshSmall_mem hhalf habs).2⟩

/-! ### Cell checks for `f` -/

/-- On the cell `[lo,hi]` the enclosure of `f` has upper endpoint at most `F`. -/
def cellF (d : Dep) (F lo hi : ℤ) : Bool :=
  hiLe (fIv (some ⟨lo, hi⟩) (Yiv d) (SHiv d) (CHiv d)) F

theorem cellF_sound {d : Dep} (hc : Ctx d) {F lo hi : ℤ} (h : cellF d F lo hi = true)
    {g : ℝ} (hg : inCell lo hi g) : fBig (yOf d) g ≤ (F : ℝ) / (SO : ℝ) :=
  hiLe_sound h (fIv_mem (cell_mem hg) hc.ymem (ne_of_gt hc.ypos) hc.shmem hc.chmem)

/-- Every cell of the segment from `cur` to `fin` bounds `f` by `F`. -/
def segOK (d : Dep) (F : ℤ) : ℤ → List ℤ → ℤ → Bool
  | cur, [], fin => cellF d F cur fin
  | cur, x :: xs, fin => cellF d F cur x && segOK d F x xs fin

theorem segOK_sound {d : Dep} (hc : Ctx d) {F : ℤ} :
    ∀ (bs : List ℤ) (cur fin : ℤ), segOK d F cur bs fin = true →
      ∀ g : ℝ, inCell cur fin g → fBig (yOf d) g ≤ (F : ℝ) / (SO : ℝ)
  | [], cur, fin, h, g, hg => cellF_sound hc h hg
  | x :: xs, cur, fin, h, g, hg => by
      rw [segOK, Bool.and_eq_true] at h
      rcases le_total ((SO:ℝ) * g) ((x : ℤ) : ℝ) with hx | hx
      · exact cellF_sound hc h.1 ⟨hg.1, hx⟩
      · exact segOK_sound hc xs x fin h.2 g ⟨hx, hg.2⟩

/-- The full walk over `(0, G]`: negativity segments alternating with bands. -/
def chainOK (d : Dep) : ℤ → List (List ℤ) → List Bnd → Bool
  | cur, [s], [] => segOK d 0 cur s GSO
  | cur, s :: ss, b :: bs =>
      segOK d 0 cur s b.lo && segOK d b.F b.lo b.sub b.hi && chainOK d b.hi ss bs
  | _, _, _ => false

theorem chainOK_neg {d : Dep} (hc : Ctx d) :
    ∀ (ss : List (List ℤ)) (bs : List Bnd) (cur : ℤ), chainOK d cur ss bs = true →
      ∀ g : ℝ, inCell cur GSO g →
        fBig (yOf d) g ≤ 0 ∨ ∃ b ∈ bs, inCell b.lo b.hi g
  | [s], [], cur, h, g, hg => by
      left
      have h' : segOK d 0 cur s GSO = true := by simpa [chainOK] using h
      have := segOK_sound hc s cur GSO h' g hg
      simpa using this
  | s :: ss, b :: bs, cur, h, g, hg => by
      rw [chainOK, Bool.and_eq_true, Bool.and_eq_true] at h
      rcases le_total ((SO:ℝ) * g) ((b.lo : ℤ) : ℝ) with hx | hx
      · left
        have := segOK_sound hc s cur b.lo h.1.1 g ⟨hg.1, hx⟩
        simpa using this
      · rcases le_total ((SO:ℝ) * g) ((b.hi : ℤ) : ℝ) with hy | hy
        · exact Or.inr ⟨b, List.mem_cons_self .., hx, hy⟩
        · rcases chainOK_neg hc ss bs b.hi h.2 g ⟨hy, hg.2⟩ with h1 | ⟨b', hb', hg'⟩
          · exact Or.inl h1
          · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', hg'⟩
  | [], _ :: _, cur, h, g, hg => by simp [chainOK] at h
  | [], [], cur, h, g, hg => by simp [chainOK] at h
  | _ :: _ :: _, [], cur, h, g, hg => by simp [chainOK] at h

theorem chainOK_band {d : Dep} (hc : Ctx d) :
    ∀ (ss : List (List ℤ)) (bs : List Bnd) (cur : ℤ), chainOK d cur ss bs = true →
      ∀ b ∈ bs, ∀ g : ℝ, inCell b.lo b.hi g → fBig (yOf d) g ≤ (b.F : ℝ) / (SO : ℝ)
  | [s], [], cur, h, b, hb, g, hg => by simp at hb
  | s :: ss, b :: bs, cur, h, b', hb', g, hg => by
      rw [chainOK, Bool.and_eq_true, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hb' with rfl | hmem
      · exact segOK_sound hc b'.sub b'.lo b'.hi h.1.2 g hg
      · exact chainOK_band hc ss bs b.hi h.2 b' hmem g hg
  | [], _ :: _, cur, h, b, hb, g, hg => by simp [chainOK] at h
  | [], [], cur, h, b, hb, g, hg => by simp at hb
  | _ :: _ :: _, [], cur, h, b, hb, g, hg => by simp at hb

/-! ### Cell checks for `ω²` -/

/-- On the cell `[lo,hi]` the enclosure of `ω²` has lower endpoint at least `K`. -/
def cellK (K lo hi : ℤ) : Bool :=
  loGe (EIv.sqr (omgIv (some ⟨lo, hi⟩))) K

theorem cellK_sound {K lo hi : ℤ} (h : cellK K lo hi = true) {r : ℝ} (hr : inCell lo hi r) :
    (K : ℝ) / (SO : ℝ) ≤ (omg r) ^ 2 := by
  have := loGe_sound h (EIv.sqr_mem (omgIv_mem (cell_mem hr)))
  rwa [← pow_two] at this

/-- Every cell of the `ω`-cover from `cur` to `fin` keeps `ω²` above `K`. -/
def omgOK (K : ℤ) : ℤ → List ℤ → ℤ → Bool
  | cur, [], fin => cellK K cur fin
  | cur, x :: xs, fin => cellK K cur x && omgOK K x xs fin

theorem omgOK_sound {K : ℤ} :
    ∀ (bs : List ℤ) (cur fin : ℤ), omgOK K cur bs fin = true →
      ∀ r : ℝ, inCell cur fin r → (K : ℝ) / (SO : ℝ) ≤ (omg r) ^ 2
  | [], cur, fin, h, r, hr => cellK_sound h hr
  | x :: xs, cur, fin, h, r, hr => by
      rw [omgOK, Bool.and_eq_true] at h
      rcases le_total ((SO:ℝ) * r) ((x : ℤ) : ℝ) with hx | hx
      · exact cellK_sound h.1 ⟨hr.1, hx⟩
      · exact omgOK_sound xs x fin h.2 r ⟨hx, hr.2⟩

/-! ### `σ₂` and the scalar arithmetic -/

/-- Enclosure of `σ₂(y) = (Re Phi2(2iy) - A)/(2A)`. -/
def sigIv (d : Dep) : EIv :=
  let Y2 := EIv.ofQ (2 * d.yn) d.yd
  let sc := sinhCoshSmall (EIv.divInt Y2 2)
  let p := phiC (EIv.pt 0) Y2 sc.1 sc.2
  EIv.div (EIv.sub p.1 AIV) (EIv.mulInt AIV 2)

/-- The square-completion check: `B` dominates `max_m [m F - c m(m-1) K]`, `c = 1/200`. -/
def bChk (F K B : ℤ) : Bool :=
  (decide (100 * F ≤ K) && decide (B = F)) || (decide (0 < K) && decide ((200 * F + K) ^ 2 ≤ 800 * K * B))

/-- Per-band data checks. -/
def bandsOK (d : Dep) : Bool :=
  d.bands.all fun b =>
    decide (0 ≤ b.F) && decide (b.lo ≤ b.hi) && decide (0 < b.lo) &&
      decide (b.hi - b.lo ≤ d.w) && bChk b.F d.K b.B

/-- The recorded inter-band gaps are at least `Plo`. -/
def gapsOK (P : ℤ) : List Bnd → Bool
  | [] => true
  | [_] => true
  | b :: b' :: bs => decide (P ≤ b'.lo - b.hi) && gapsOK P (b' :: bs)

/-- The scalar inequalities of the certificate. -/
def arithOK (d : Dep) : Bool :=
  decide (0 ≤ d.K) && decide (0 ≤ d.s2) && decide (0 < d.Plo) && decide (0 < d.w) &&
    loGe (sigIv d) d.s2 &&
    decide (d.slack * SO ≤ 8 * d.s2 * SO + 8 * d.s2 * d.s2) &&
    decide (8 * d.Cup ^ 2 * (d.Plo + 98 * SO) ≤ d.tail * (d.Plo * 98 ^ 2 * SO)) &&
    decide (2 * ((d.bands.map Bnd.B).sum) + d.tail ≤ d.cap) &&
    decide (d.cap ≤ d.slack) &&
    decide (400 * d.Cup ^ 2 ≤ d.K * 98 ^ 2 * SO) &&
    gapsOK d.Plo d.bands

/-- The whole per-depth check. -/
def depOK (d : Dep) : Bool :=
  basicOK d && chainOK d 0 d.segs d.bands && omgOK d.K 0 d.ocells d.w && bandsOK d && arithOK d

end BandDual
