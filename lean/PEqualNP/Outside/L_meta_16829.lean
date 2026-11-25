import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16829
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev ALL : ℕ := 18446744073709551615

theorem all_bit : ∀ p : Fin 64, ALL.testBit p = true := by decide +kernel

def nc (pool : List ℕ) : List ℕ := pool.filter (fun a => decide (a ≠ 0) && decide (a ≠ ALL))

theorem mem_nc (pool : List ℕ) (a : ℕ) : a ∈ nc pool ↔ a ∈ pool ∧ a ≠ 0 ∧ a ≠ ALL := by
  simp [nc, List.mem_filter]

def cand (pool : List ℕ) : List ℕ :=
  pool ++ ((nc pool).map (fun a => ALL ^^^ a) ++
    (nc pool).flatMap (fun a => (nc pool).flatMap (fun b => [a &&& b, a ||| b])))

def Inv (pool : List ℕ) (ws : Fin 64 → List Bool) : Prop :=
  0 ∈ pool ∧ ALL ∈ pool ∧ ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 64, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem cand_not (pool : List ℕ) (h0 : 0 ∈ pool) (hA : ALL ∈ pool) (m : ℕ) (hm : m ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 64, c.testBit p = !m.testBit p := by
  by_cases e0 : m = 0
  · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [e0, all_bit p]; simp⟩
  · by_cases eA : m = ALL
    · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [eA, all_bit p]; simp⟩
    · refine ⟨ALL ^^^ m, List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨m, (mem_nc pool m).mpr ⟨hm, e0, eA⟩, rfl⟩)), fun p => ?_⟩
      rw [Nat.testBit_xor, all_bit p]
      simp

theorem cand_and (pool : List ℕ) (h0 : 0 ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 64, c.testBit p = (ma.testBit p && mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma &&& mb, ?_, fun p => Nat.testBit_and ma mb p⟩
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem cand_or (pool : List ℕ) (hA : ALL ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 64, c.testBit p = (ma.testBit p || mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma ||| mb, ?_, fun p => Nat.testBit_or ma mb p⟩
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem gate_vec (pool : List ℕ) (ws : Fin 64 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ cand pool, ∀ p : Fin 64,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨h0, hA, hw⟩ := h
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by simp [GateOp.eval, all_bit p]⟩
    · exact ⟨0, List.mem_append_left _ h0, fun p => by simp [GateOp.eval]⟩
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by simp [GateOp.eval, all_bit p]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    rcases hop with rfl | rfl | rfl
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_not pool h0 hA ma hma
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p]⟩
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    obtain ⟨mb, hmb, hb⟩ := hw b
    rcases hop with rfl | rfl | rfl
    · obtain ⟨c, hc, hcv⟩ := cand_and pool h0 ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_or pool hA ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_not pool h0 hA ma hma
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p]⟩
  | _ :: _ :: _ :: _, hl => simp at hl

theorem inv_step (pool pool' : List ℕ) (ws : Fin 64 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 64 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 64, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  obtain ⟨h0, hA, hw⟩ := hI
  refine ⟨hsub 0 h0, hsub ALL hA, fun i => ?_⟩
  obtain ⟨m, hm, hmb⟩ := hw i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

def pool0 : List ℕ := [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320, 0, ALL]

def X (p : Fin 64) : List Bool := List.ofFn (fun i : Fin 6 => p.val.testBit i.val)

theorem X_len (p : Fin 64) : (X p).length = 6 := by simp [X]

theorem inv0 : Inv pool0 X := by
  refine ⟨by decide, by decide, fun i => ?_⟩
  by_cases hi : i < 6
  · have key : ∀ j : Fin 6, ∀ p : Fin 64,
        (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide +kernel
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by decide, fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

abbrev Good (T : ℕ) (G : Finset ℕ) : Prop :=
  ∀ p q : Fin 64, T.testBit p = true → T.testBit q = false →
    ∃ w ∈ G, w.testBit p ≠ w.testBit q

theorem good_mono (T : ℕ) (G H : Finset ℕ) (h : G ⊆ H) (hG : Good T G) : Good T H := by
  intro p q hp hq
  obtain ⟨w, hw, h1⟩ := hG p q hp hq
  exact ⟨w, h hw, h1⟩

theorem good_split (T : ℕ) (G : Finset ℕ) (a b c : ℕ) (hG : Good T G)
    (hc : ∀ p q : Fin 64, c.testBit p ≠ c.testBit q →
      a.testBit p ≠ a.testBit q ∨ b.testBit p ≠ b.testBit q) :
    Good T (insert a (insert b (G.erase c))) := by
  intro p q hp hq
  obtain ⟨w, hw, h1⟩ := hG p q hp hq
  by_cases hwc : w = c
  · rw [hwc] at h1
    rcases hc p q h1 with h2 | h2
    · exact ⟨a, Finset.mem_insert_self _ _, h2⟩
    · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h2⟩
  · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hwc, hw⟩)), h1⟩

theorem all_bit' (i : ℕ) : ALL.testBit i = decide (i < 64) := by
  have h : ALL = 2 ^ 64 - 1 := by decide +kernel
  rw [h, Nat.testBit_two_pow_sub_one]

theorem all_lt : ALL < 2 ^ 64 := by decide +kernel

def rep (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | _ :: zs => Nat.add (Nat.mul (2 ^ 64) (rep x zs)) x

theorem rep_bit (x : ℕ) (hx : x < 2 ^ 64) : ∀ (zs : List ℕ) (i : ℕ),
    (rep x zs).testBit i = (decide (i / 64 < zs.length) && x.testBit (i % 64))
  | [], i => by simp [rep]
  | q :: zs, i => by
    rw [rep]
    change (2 ^ 64 * rep x zs + x).testBit i = _
    rw [Nat.testBit_two_pow_mul_add _ hx]
    by_cases hi : i < 64
    · have e1 : i / 64 = 0 := Nat.div_eq_of_lt hi
      have e2 : i % 64 = i := Nat.mod_eq_of_lt hi
      rw [if_pos hi, e1, e2]
      simp
    · have e1 : i / 64 = (i - 64) / 64 + 1 := by omega
      have e2 : i % 64 = (i - 64) % 64 := by omega
      rw [if_neg hi, rep_bit x hx zs (i - 64), e1, e2, List.length_cons]
      simp

theorem mul_rep (x : ℕ) : ∀ zs : List ℕ, x * rep 1 zs = rep x zs
  | [] => by simp [rep]
  | q :: zs => by
    rw [rep, rep]
    change x * (2 ^ 64 * rep 1 zs + 1) = 2 ^ 64 * rep x zs + x
    rw [← mul_rep x zs]
    ring

def msk (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | q :: zs => Nat.add (Nat.mul (2 ^ 64) (msk w zs)) (Nat.mul ALL (Nat.mod (Nat.shiftRight w q) 2))

theorem msk_bit (w : ℕ) : ∀ (zs : List ℕ) (i : ℕ),
    (msk w zs).testBit i = (decide (i / 64 < zs.length) && w.testBit (zs.getD (i / 64) 0))
  | [], i => by simp [msk]
  | q :: zs, i => by
    rw [msk]
    change (2 ^ 64 * msk w zs + ALL * ((w >>> q) % 2)).testBit i = _
    have hb : (w >>> q) % 2 = (w.testBit q).toNat := by
      rw [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]
    rw [hb]
    have hlt : ALL * (w.testBit q).toNat < 2 ^ 64 := by
      cases w.testBit q
      · show ALL * 0 < 2 ^ 64
        rw [Nat.mul_zero]
        exact Nat.two_pow_pos 64
      · show ALL * 1 < 2 ^ 64
        rw [Nat.mul_one]
        exact all_lt
    rw [Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hi : i < 64
    · have e1 : i / 64 = 0 := Nat.div_eq_of_lt hi
      rw [if_pos hi, e1, List.getD_cons_zero]
      cases w.testBit q
      · show (ALL * 0).testBit i = _
        simp
      · show (ALL * 1).testBit i = _
        rw [Nat.mul_one, all_bit']
        simp [hi]
    · have e1 : i / 64 = (i - 64) / 64 + 1 := by omega
      rw [if_neg hi, msk_bit w zs (i - 64), e1, List.getD_cons_succ, List.length_cons]
      simp

def ppos (T : ℕ) (zs : List ℕ) (w : ℕ) : ℕ := Nat.mul (Nat.land T w) (rep 1 zs)

def pneg (T : ℕ) (zs : List ℕ) (w : ℕ) : ℕ := Nat.mul (Nat.land T (Nat.xor ALL w)) (rep 1 zs)

def full (zs : List ℕ) : ℕ := Nat.mul ALL (rep 1 zs)

theorem ppos_bit (T : ℕ) (zs : List ℕ) (w : ℕ) (hT : T < 2 ^ 64) (i : ℕ) :
    (ppos T zs w).testBit i =
      (decide (i / 64 < zs.length) && (T.testBit (i % 64) && w.testBit (i % 64))) := by
  unfold ppos
  change ((T &&& w) * rep 1 zs).testBit i = _
  rw [mul_rep, rep_bit _ (lt_of_le_of_lt Nat.and_le_left hT), Nat.testBit_and]

theorem pneg_bit (T : ℕ) (zs : List ℕ) (w : ℕ) (hT : T < 2 ^ 64) (i : ℕ) :
    (pneg T zs w).testBit i =
      (decide (i / 64 < zs.length) && (T.testBit (i % 64) && !w.testBit (i % 64))) := by
  unfold pneg
  change ((T &&& (ALL ^^^ w)) * rep 1 zs).testBit i = _
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [mul_rep, rep_bit _ (lt_of_le_of_lt Nat.and_le_left hT), Nat.testBit_and, Nat.testBit_xor,
    all_bit']
  simp [hp]

theorem full_bit (zs : List ℕ) (i : ℕ) : (full zs).testBit i = decide (i / 64 < zs.length) := by
  unfold full
  change (ALL * rep 1 zs).testBit i = _
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [mul_rep, rep_bit _ all_lt, all_bit']
  simp [hp]

def pkF (T : ℕ) (zs : List ℕ) (w : ℕ) : ℕ :=
  Nat.lor (Nat.land (ppos T zs w) (msk w zs))
    (Nat.land (pneg T zs w) (Nat.xor (msk w zs) (full zs)))

abbrev Cov (T : ℕ) (zs : List ℕ) (w P : ℕ) : Prop :=
  ∀ i : ℕ, P.testBit i = true → i / 64 < zs.length ∧ T.testBit (i % 64) = true ∧
    w.testBit (i % 64) = w.testBit (zs.getD (i / 64) 0)

theorem cov_pkF (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64) (w : ℕ) : Cov T zs w (pkF T zs w) := by
  intro i h
  unfold pkF at h
  change ((ppos T zs w &&& msk w zs) ||| (pneg T zs w &&& (msk w zs ^^^ full zs))).testBit i =
    true at h
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ppos_bit T zs _ hT,
    pneg_bit T zs _ hT, msk_bit, full_bit] at h
  by_cases hd : i / 64 < zs.length
  · refine ⟨hd, ?_⟩
    revert h
    cases T.testBit (i % 64) <;> cases w.testBit (i % 64) <;>
      cases w.testBit (zs.getD (i / 64) 0) <;> simp [hd]
  · simp [hd] at h

def vand (T : ℕ) (zs : List ℕ) (a b : ℕ) : ℕ :=
  Nat.lor (Nat.land (Nat.land (ppos T zs a) (ppos T zs b)) (Nat.land (msk a zs) (msk b zs)))
    (Nat.land (Nat.lor (pneg T zs a) (pneg T zs b))
      (Nat.xor (Nat.land (msk a zs) (msk b zs)) (full zs)))

theorem cov_and (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64) (a b : ℕ) :
    Cov T zs (a &&& b) (vand T zs a b) := by
  intro i h
  unfold vand at h
  change (((ppos T zs a &&& ppos T zs b) &&& (msk a zs &&& msk b zs)) |||
    ((pneg T zs a ||| pneg T zs b) &&& ((msk a zs &&& msk b zs) ^^^ full zs))).testBit i =
    true at h
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ppos_bit T zs _ hT,
    pneg_bit T zs _ hT, msk_bit, full_bit] at h ⊢
  by_cases hd : i / 64 < zs.length
  · refine ⟨hd, ?_⟩
    revert h
    cases T.testBit (i % 64) <;> cases a.testBit (i % 64) <;> cases b.testBit (i % 64) <;>
      cases a.testBit (zs.getD (i / 64) 0) <;> cases b.testBit (zs.getD (i / 64) 0) <;>
      simp [hd]
  · simp [hd] at h

def vor (T : ℕ) (zs : List ℕ) (a b : ℕ) : ℕ :=
  Nat.lor (Nat.land (Nat.lor (ppos T zs a) (ppos T zs b)) (Nat.lor (msk a zs) (msk b zs)))
    (Nat.land (Nat.land (pneg T zs a) (pneg T zs b))
      (Nat.xor (Nat.lor (msk a zs) (msk b zs)) (full zs)))

theorem cov_or (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64) (a b : ℕ) :
    Cov T zs (a ||| b) (vor T zs a b) := by
  intro i h
  unfold vor at h
  change (((ppos T zs a ||| ppos T zs b) &&& (msk a zs ||| msk b zs)) |||
    ((pneg T zs a &&& pneg T zs b) &&& ((msk a zs ||| msk b zs) ^^^ full zs))).testBit i =
    true at h
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ppos_bit T zs _ hT,
    pneg_bit T zs _ hT, msk_bit, full_bit] at h ⊢
  by_cases hd : i / 64 < zs.length
  · refine ⟨hd, ?_⟩
    revert h
    cases T.testBit (i % 64) <;> cases a.testBit (i % 64) <;> cases b.testBit (i % 64) <;>
      cases a.testBit (zs.getD (i / 64) 0) <;> cases b.testBit (zs.getD (i / 64) 0) <;>
      simp [hd]
  · simp [hd] at h

theorem cov_not (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (a : ℕ) :
    Cov T zs (ALL ^^^ a) (pkF T zs a) := by
  intro i h
  obtain ⟨h1, h2, h3⟩ := cov_pkF T zs hT a i h
  refine ⟨h1, h2, ?_⟩
  have hq := (hzs (zs.getD (i / 64) 0) (by
    rw [List.getD_eq_getElem _ _ h1]
    exact List.getElem_mem h1)).1
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [Nat.testBit_xor, Nat.testBit_xor, all_bit', all_bit', h3, decide_eq_true hp,
    decide_eq_true hq]

def andL (T : ℕ) (zs : List ℕ) (L : List ℕ) : ℕ :=
  L.foldr (fun w acc => Nat.land (pkF T zs w) acc) (ppos T zs ALL)

theorem fold_bits (T : ℕ) (zs : List ℕ) (i : ℕ) : ∀ (L : List ℕ),
    (andL T zs L).testBit i = true →
    (ppos T zs ALL).testBit i = true ∧ ∀ w ∈ L, (pkF T zs w).testBit i = true
  | [], h => ⟨h, by simp⟩
  | w :: L, h => by
    change (pkF T zs w &&& andL T zs L).testBit i = true at h
    rw [Nat.testBit_and, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := fold_bits T zs i L h.2
    refine ⟨h1, fun w' hw' => ?_⟩
    rcases List.mem_cons.mp hw' with e | e
    · rw [e]
      exact h.1
    · exact h2 w' e

abbrev GoodL (T : ℕ) (zs : List ℕ) (L : List ℕ) : Prop := andL T zs L = 0

theorem goodL_of_good (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (L : List ℕ) (hg : Good T L.toFinset) :
    GoodL T zs L := by
  by_contra hne
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  obtain ⟨h0, hall⟩ := fold_bits T zs i L hi
  rw [ppos_bit T zs ALL hT] at h0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
  obtain ⟨hk, hTp, _⟩ := h0
  have hq := hzs (zs.getD (i / 64) 0) (by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk)
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  obtain ⟨w, hw, hsep⟩ := hg ⟨i % 64, hp⟩ ⟨zs.getD (i / 64) 0, hq.1⟩ hTp hq.2
  apply hsep
  show w.testBit (i % 64) = w.testBit (zs.getD (i / 64) 0)
  exact (cov_pkF T zs hT w i (hall w (List.mem_toFinset.mp hw))).2.2

theorem good_zero (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (L : List ℕ) (c P : ℕ)
    (hP : Cov T zs c P) (hg : Good T (insert c L.toFinset)) :
    Nat.land P (andL T zs L) = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  change (P &&& andL T zs L).testBit i = true at hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi
  obtain ⟨_, hall⟩ := fold_bits T zs i L hi.2
  obtain ⟨hk, hTp, hcp⟩ := hP i hi.1
  have hq := hzs (zs.getD (i / 64) 0) (by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk)
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  obtain ⟨w, hw, hsep⟩ := hg ⟨i % 64, hp⟩ ⟨zs.getD (i / 64) 0, hq.1⟩ hTp hq.2
  apply hsep
  show w.testBit (i % 64) = w.testBit (zs.getD (i / 64) 0)
  rcases Finset.mem_insert.mp hw with e | e
  · rw [e]
    exact hcp
  · exact (cov_pkF T zs hT w i (hall w (List.mem_toFinset.mp e))).2.2

def goodC (T : ℕ) (zs : List ℕ) (P : ℕ) (E : List ℕ) : Bool :=
  Nat.beq (Nat.land P (andL T zs E)) 0

theorem goodC_true (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (E : List ℕ) (c P : ℕ)
    (hP : Cov T zs c P) (hg : Good T (insert c E.toFinset)) : goodC T zs P E = true := by
  unfold goodC
  rw [good_zero T zs hT hzs E c P hP hg]
  rfl

def Sym (T : ℕ) (f : ℕ → ℕ) : Prop :=
  Function.Injective f ∧ f 0 = 0 ∧ f ALL = ALL ∧ (∀ a b : ℕ, f (a &&& b) = f a &&& f b) ∧
    (∀ a b : ℕ, f (a ||| b) = f a ||| f b) ∧ (∀ a : ℕ, f (ALL ^^^ a) = ALL ^^^ f a) ∧
    ∀ G : Finset ℕ, Good T (G.image f) → Good T G

theorem sym_id (T : ℕ) : Sym T (fun x => x) :=
  ⟨fun _ _ h => h, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun G h => by rwa [Finset.image_id'] at h⟩

theorem sym_comp (T : ℕ) (f g : ℕ → ℕ) (hf : Sym T f) (hg : Sym T g) :
    Sym T (fun x => f (g x)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hg
  refine ⟨fun a b h => g1 (f1 h), ?_, ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun G h => ?_⟩
  · show f (g 0) = 0
    rw [g2, f2]
  · show f (g ALL) = ALL
    rw [g3, f3]
  · show f (g (a &&& b)) = f (g a) &&& f (g b)
    rw [g4, f4]
  · show f (g (a ||| b)) = f (g a) ||| f (g b)
    rw [g5, f5]
  · show f (g (ALL ^^^ a)) = ALL ^^^ f (g a)
    rw [g6, f6]
  · apply g7
    apply f7
    rw [Finset.image_image]
    exact h

def appG (w : ℕ) : List ℕ → ℕ → ℕ
  | [], init => init
  | j :: π, init => Nat.add (Nat.mul 2 (appG w π init)) (Nat.mod (Nat.shiftRight w j) 2)

theorem appG_cons (w j : ℕ) (π : List ℕ) (init : ℕ) :
    appG w (j :: π) init = Nat.bit (w.testBit j) (appG w π init) := by
  rw [appG]
  show 2 * appG w π init + (w >>> j) % 2 = _
  rw [Nat.bit_val, Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]

def app (π : List ℕ) (w : ℕ) : ℕ := appG w π (w >>> π.length)

theorem appG_bit (w : ℕ) : ∀ (π : List ℕ) (init i : ℕ),
    (appG w π init).testBit i =
      if i < π.length then w.testBit (π.getD i 0) else init.testBit (i - π.length)
  | [], init, i => by simp [appG]
  | j :: π, init, 0 => by simp [appG_cons, Nat.testBit_bit_zero]
  | j :: π, init, i + 1 => by
    rw [appG_cons, Nat.testBit_bit_succ, appG_bit w π init i]
    simp

theorem app_bit (π : List ℕ) (w i : ℕ) :
    (app π w).testBit i = if i < π.length then w.testBit (π.getD i 0) else w.testBit i := by
  unfold app
  rw [appG_bit]
  split
  · rfl
  · rw [Nat.testBit_shiftRight]
    congr 1
    omega

abbrev PermOk (T : ℕ) (π : List ℕ) : Prop :=
  π.length = 64 ∧ (∀ j ∈ π, j < 64) ∧ (∀ j ∈ List.range 64, j ∈ π) ∧
    ∀ i ∈ List.range 64, T.testBit (π.getD i 0) = T.testBit i

theorem sym_app (T : ℕ) (π : List ℕ) (hπ : PermOk T π) : Sym T (app π) := by
  obtain ⟨hlen, hlt, hsurj, hT⟩ := hπ
  have hb : ∀ w i : ℕ, (app π w).testBit i =
      if i < 64 then w.testBit (π.getD i 0) else w.testBit i := by
    intro w i
    rw [app_bit, hlen]
  have hget : ∀ i : ℕ, i < 64 → π.getD i 0 < 64 := by
    intro i hi
    have hi' : i < π.length := by omega
    rw [List.getD_eq_getElem _ _ hi']
    exact hlt _ (List.getElem_mem hi')
  have hidx : ∀ j : ℕ, j < 64 → ∃ i : ℕ, i < 64 ∧ π.getD i 0 = j := by
    intro j hj
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem (hsurj j (List.mem_range.mpr hj))
    exact ⟨i, by omega, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 64
    · obtain ⟨i, hi, e⟩ := hidx j hj
      have h1 := hb a i
      have h2 := hb b i
      rw [if_pos hi, e] at h1 h2
      rw [← h1, ← h2, h]
    · have h1 := hb a j
      have h2 := hb b j
      rw [if_neg hj] at h1 h2
      rw [← h1, ← h2, h]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [hb]
    simp
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [hb, all_bit', all_bit']
    by_cases hi : i < 64
    · rw [if_pos hi, decide_eq_true (hget i hi), decide_eq_true hi]
    · rw [if_neg hi]
  · intro a b
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [hb, Nat.testBit_and]
    split <;> rfl
  · intro a b
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [hb, Nat.testBit_or]
    split <;> rfl
  · intro a
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [hb, Nat.testBit_xor, all_bit']
    by_cases hi : i < 64
    · rw [if_pos hi, if_pos hi, decide_eq_true (hget i hi), decide_eq_true hi]
    · rw [if_neg hi, if_neg hi]
  · intro G hG p q hp hq
    obtain ⟨p', hp', ep⟩ := hidx p.val p.isLt
    obtain ⟨q', hq', eq⟩ := hidx q.val q.isLt
    have hTp : T.testBit p' = true := by
      rw [← hT p' (List.mem_range.mpr hp'), ep]
      exact hp
    have hTq : T.testBit q' = false := by
      rw [← hT q' (List.mem_range.mpr hq'), eq]
      exact hq
    obtain ⟨w, hw, hne⟩ := hG ⟨p', hp'⟩ ⟨q', hq'⟩ hTp hTq
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨w0, hw0, ?_⟩
    have h1 := hb w0 p'
    have h2 := hb w0 q'
    rw [if_pos hp', ep] at h1
    rw [if_pos hq', eq] at h2
    rw [← h1, ← h2]
    exact hne

def Leaf (T : ℕ) (S : Finset ℕ) : Prop :=
  S.card ≠ 1 ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c : ℕ, (c = a &&& b ∨ c = a ||| b) →
    ¬ Good T (insert c ((S.erase a).erase b))

theorem leaf_sym (T : ℕ) (f : ℕ → ℕ) (hf : Sym T f) (S : Finset ℕ) (h : Leaf T S) :
    Leaf T (S.image f) := by
  obtain ⟨f1, _, _, f4, f5, _, f7⟩ := hf
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Finset.card_image_of_injective _ f1]; exact h1, ?_⟩
  intro a ha b hb hab c hc hg
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
  have hab0 : a0 ≠ b0 := fun e => hab (by rw [e])
  have him : ∀ c0 : ℕ, insert (f c0) (((S.image f).erase (f a0)).erase (f b0)) =
      (insert c0 ((S.erase a0).erase b0)).image f := by
    intro c0
    rw [Finset.image_insert, Finset.image_erase f1, Finset.image_erase f1]
  rcases hc with e | e
  · refine h2 a0 ha0 b0 hb0 hab0 (a0 &&& b0) (Or.inl rfl) (f7 _ ?_)
    rw [← him, f4, ← e]
    exact hg
  · refine h2 a0 ha0 b0 hb0 hab0 (a0 ||| b0) (Or.inr rfl) (f7 _ ?_)
    rw [← him, f5, ← e]
    exact hg

def InF (T D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (δ : ℕ) (S : Finset ℕ) : Prop :=
  (∃ e ∈ fam, e.1 ≤ δ ∧ ∃ f : ℕ → ℕ, Sym T f ∧ e.2.1.toFinset.image f = S) ∨
    (D ≤ δ + 1 ∧ Leaf T S)

theorem inF_mono (T D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (δ δ' : ℕ) (h : δ ≤ δ') (S : Finset ℕ)
    (hS : InF T D fam δ S) : InF T D fam δ' S := by
  rcases hS with ⟨e, he, h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨e, he, le_trans h1 h, h2⟩
  · exact Or.inr ⟨by omega, h2⟩

def Clos (T D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) : Prop :=
  ∀ δ : ℕ, ∀ S : Finset ℕ, InF T D fam δ S → ∀ a ∈ S, ∀ b ∈ S, ∀ c : ℕ,
    ((a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a)) →
    c ∉ S → c ≠ 0 → c ≠ ALL →
    ∀ E : Finset ℕ, E ⊆ S → S ⊆ insert a (insert b E) → Good T (insert c E) →
    ∀ δ' : ℕ, δ' < D → δ' + S.card = δ + E.card + 2 → InF T D fam δ' (insert c E)

def Jn (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (pool : List ℕ) (j : ℕ) : Prop :=
  ∀ G : Finset ℕ, G ⊆ pool.toFinset → 0 ∉ G → ALL ∉ G → Good T G →
    N ≤ G.card + j ∧ ∀ δ : ℕ, δ < D → G.card + j = N + δ → InF T D fam δ G

theorem jn_weak (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (pool : List ℕ) (j : ℕ)
    (h : Jn T N D fam pool j) : Jn T N D fam pool (j + 1) := by
  intro G hG hG0 hGA hg
  obtain ⟨h1, h2⟩ := h G hG hG0 hGA hg
  exact ⟨by omega, fun δ hδ hcd =>
    inF_mono T D fam (δ - 1) δ (by omega) G (h2 (δ - 1) (by omega) (by omega))⟩

theorem jn_step (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (hcl : Clos T D fam)
    (pool : List ℕ) (j c : ℕ) (h : Jn T N D fam pool j) (hc : c ∈ cand pool) (hcn : c ∉ pool) :
    Jn T N D fam (pool ++ [c]) (j + 1) := by
  intro G hG hG0 hGA hg
  have hmem : ∀ x ∈ G, x ≠ c → x ∈ pool.toFinset := by
    intro x hx hxc
    have h1 := hG hx
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset,
      List.mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact List.mem_toFinset.mpr h1
    · exact absurd h1 hxc
  by_cases hcG : c ∈ G
  · have hsubE : G.erase c ⊆ pool.toFinset := by
      intro x hx
      obtain ⟨hxc, hxG⟩ := Finset.mem_erase.mp hx
      exact hmem x hxG hxc
    have hcard : (G.erase c).card + 1 = G.card := Finset.card_erase_add_one hcG
    have hIns : insert c (G.erase c) = G := Finset.insert_erase hcG
    have hc0 : c ≠ 0 := fun e => hG0 (e ▸ hcG)
    have hcA : c ≠ ALL := fun e => hGA (e ▸ hcG)
    have key : ∃ a b : ℕ, a ∈ pool ∧ b ∈ pool ∧ a ≠ 0 ∧ a ≠ ALL ∧ b ≠ 0 ∧ b ≠ ALL ∧
        ((a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a)) ∧
        ∀ p q : Fin 64, c.testBit p ≠ c.testBit q →
          a.testBit p ≠ a.testBit q ∨ b.testBit p ≠ b.testBit q := by
      simp only [cand, List.mem_append, List.mem_map, List.mem_flatMap] at hc
      rcases hc with hc | ⟨a, ha, hc⟩ | ⟨a, ha, b, hb, hc⟩
      · exact absurd hc hcn
      · obtain ⟨ha1, ha2, ha3⟩ := (mem_nc pool a).mp ha
        refine ⟨a, a, ha1, ha1, ha2, ha3, ha2, ha3, Or.inr ⟨rfl, hc.symm⟩,
          fun p q hpq => Or.inl ?_⟩
        intro e
        apply hpq
        rw [← hc, Nat.testBit_xor, Nat.testBit_xor, all_bit p, all_bit q, e]
      · obtain ⟨ha1, ha2, ha3⟩ := (mem_nc pool a).mp ha
        obtain ⟨hb1, hb2, hb3⟩ := (mem_nc pool b).mp hb
        have hc' : c = a &&& b ∨ c = a ||| b := by simpa using hc
        have hab : a ≠ b := by
          intro e
          apply hcn
          rcases hc' with e2 | e2
          · rw [e2, e, Nat.and_self]
            exact hb1
          · rw [e2, e, Nat.or_self]
            exact hb1
        refine ⟨a, b, ha1, hb1, ha2, ha3, hb2, hb3, Or.inl ⟨hab, hc'⟩, fun p q hpq => ?_⟩
        by_contra hno
        rw [not_or, not_not, not_not] at hno
        apply hpq
        rcases hc' with e2 | e2
        · rw [e2, Nat.testBit_and, Nat.testBit_and, hno.1, hno.2]
        · rw [e2, Nat.testBit_or, Nat.testBit_or, hno.1, hno.2]
    obtain ⟨a, b, ha, hb, ha0, haA, hb0, hbA, hcand, hsep⟩ := key
    have hgA : Good T (insert a (insert b (G.erase c))) := good_split T G a b c hg hsep
    have hsubA : insert a (insert b (G.erase c)) ⊆ pool.toFinset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · rw [hx]
        exact List.mem_toFinset.mpr ha
      · rcases Finset.mem_insert.mp hx with hx | hx
        · rw [hx]
          exact List.mem_toFinset.mpr hb
        · exact hsubE hx
    have h0A : 0 ∉ insert a (insert b (G.erase c)) := by
      intro e
      rcases Finset.mem_insert.mp e with e | e
      · exact ha0 e.symm
      · rcases Finset.mem_insert.mp e with e | e
        · exact hb0 e.symm
        · exact hG0 (Finset.mem_of_mem_erase e)
    have hAA : ALL ∉ insert a (insert b (G.erase c)) := by
      intro e
      rcases Finset.mem_insert.mp e with e | e
      · exact haA e.symm
      · rcases Finset.mem_insert.mp e with e | e
        · exact hbA e.symm
        · exact hGA (Finset.mem_of_mem_erase e)
    obtain ⟨h1, h2⟩ := h _ hsubA h0A hAA hgA
    have hcA' : c ∉ insert a (insert b (G.erase c)) :=
      fun e => hcn (List.mem_toFinset.mp (hsubA e))
    have hEA : G.erase c ⊆ insert a (insert b (G.erase c)) :=
      fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
    have h3 := Finset.card_insert_le a (insert b (G.erase c))
    have h4 := Finset.card_insert_le b (G.erase c)
    refine ⟨by omega, fun δ hδ hcd => ?_⟩
    have hfin := hcl ((insert a (insert b (G.erase c))).card + j - N) _
      (h2 _ (by omega) (by omega)) a (Finset.mem_insert_self _ _) b
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) c hcand hcA' hc0 hcA
      (G.erase c) hEA (Finset.Subset.refl _) (by rw [hIns]; exact hg) δ hδ (by omega)
    rw [hIns] at hfin
    exact hfin
  · have hsubG : G ⊆ pool.toFinset := fun x hx => hmem x hx (fun e => hcG (e ▸ hx))
    exact jn_weak T N D fam pool j h G hsubG hG0 hGA hg

theorem filter_ne (L : List ℕ) (a : ℕ) :
    (L.filter (fun x => decide (x ≠ a))).toFinset = L.toFinset.erase a := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_erase, decide_eq_true_eq]
  tauto

theorem filter_ne2 (L : List ℕ) (a b : ℕ) :
    (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))).toFinset =
      (L.toFinset.erase a).erase b := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_erase, decide_eq_true_eq,
    Bool.and_eq_true]
  tauto

theorem sub_cases (S E : Finset ℕ) (a b : ℕ) (h1 : E ⊆ S) (h2 : S ⊆ insert a (insert b E)) :
    E = S ∨ E = S.erase a ∨ E = S.erase b ∨ E = (S.erase a).erase b := by
  have hx : ∀ x ∈ S, x = a ∨ x = b ∨ x ∈ E := by
    intro x hx
    rcases Finset.mem_insert.mp (h2 hx) with e | e
    · exact Or.inl e
    · exact Or.inr (Finset.mem_insert.mp e)
  by_cases ha : a ∈ E
  · by_cases hb : b ∈ E
    · left
      refine Finset.Subset.antisymm h1 (fun x hxS => ?_)
      rcases hx x hxS with e | e | e
      · rw [e]
        exact ha
      · rw [e]
        exact hb
      · exact e
    · right; right; left
      ext x
      rw [Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => hb (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2 with e | e | e
      · rw [e]
        exact ha
      · exact absurd e hxS.1
      · exact e
  · by_cases hb : b ∈ E
    · right; left
      ext x
      rw [Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => ha (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2 with e | e | e
      · exact absurd e hxS.1
      · rw [e]
        exact hb
      · exact e
    · right; right; right
      ext x
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => hb (by rw [← e]; exact hxE),
        fun e => ha (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2.2 with e | e | e
      · exact absurd e hxS.2.1
      · exact absurd e hxS.1
      · exact e

abbrev LeafL (T : ℕ) (zs : List ℕ) (L : List ℕ) : Prop :=
  L.length ≠ 1 ∧ ∀ a ∈ L, ∀ b ∈ L, a < b →
    goodC T zs (vand T zs a b) (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))) = false ∧
    goodC T zs (vor T zs a b) (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))) = false

theorem leaf_of_leafL (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (L : List ℕ) (hnd : L.Nodup)
    (h : LeafL T zs L) : Leaf T L.toFinset := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [List.toFinset_card_of_nodup hnd]; exact h1, ?_⟩
  intro a ha b hb hab c hc hg
  have key : ∀ a' b' : ℕ, a' ∈ L → b' ∈ L → a' < b' → (c = a' &&& b' ∨ c = a' ||| b') →
      Good T (insert c ((L.toFinset.erase a').erase b')) → False := by
    intro a' b' ha' hb' hlt hc' hg'
    obtain ⟨hA, hO⟩ := h2 a' ha' b' hb' hlt
    rw [← filter_ne2] at hg'
    rcases hc' with e | e
    · rw [e] at hg'
      rw [goodC_true T zs hT hzs _ _ _ (cov_and T zs hT a' b') hg'] at hA
      exact absurd hA (by decide)
    · rw [e] at hg'
      rw [goodC_true T zs hT hzs _ _ _ (cov_or T zs hT a' b') hg'] at hO
      exact absurd hO (by decide)
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact key a b (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hlt hc hg
  · refine key b a (List.mem_toFinset.mp hb) (List.mem_toFinset.mp ha) hgt ?_ ?_
    · rcases hc with e | e
      · exact Or.inl (e.trans (Nat.and_comm a b))
      · exact Or.inr (e.trans (Nat.or_comm a b))
    · rw [Finset.erase_right_comm]
      exact hg

def leafB (T : ℕ) (zs : List ℕ) (L : List ℕ) : Bool :=
  decide (LeafL T zs L)

theorem leafB_ok (T : ℕ) (zs : List ℕ) (L : List ℕ)
    (h : leafB T zs L = true) : LeafL T zs L := by
  unfold leafB at h
  exact of_decide_eq_true h

theorem map_fin (f : ℕ → ℕ) (L : List ℕ) : (L.map f).toFinset = L.toFinset.image f := by
  ext y
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

def ent (parts : List (List (ℕ × List ℕ × List ℕ))) (t : ℕ) : ℕ × List ℕ × List ℕ :=
  (parts.getD (t / 16) []).getD (t % 16) (0, [], [])

abbrev Hit2 (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Prop :=
  (w % 1000) / 16 < parts.length ∧
    (w % 1000) % 16 < (parts.getD ((w % 1000) / 16) []).length ∧
    (w / 1000) % 10 < perms.length ∧ (ent parts (w % 1000)).1 ≤ lv ∧
    (if (w / 1000) % 10 = 0 then (ent parts (w % 1000)).2.1
      else ((ent parts (w % 1000)).2.1.map (app (perms.getD ((w / 1000) % 10) []))).insertionSort
        (fun x y => x ≤ y)) = E.orderedInsert (fun x y => x ≤ y) c

def hit2B (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Bool :=
  decide (Hit2 parts perms lv E c w)

theorem hit2B_ok (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ)
    (h : hit2B parts perms lv E c w = true) : Hit2 parts perms lv E c w := by
  unfold hit2B at h
  exact of_decide_eq_true h

abbrev Hit (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Prop :=
  w / 10000 = (c + 3 * E.sum) % 100 ∧ hit2B parts perms lv E c w = true

def hitB (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Bool :=
  decide (Hit parts perms lv E c w)

theorem hitB_ok (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ)
    (h : hitB parts perms lv E c w = true) : Hit parts perms lv E c w := by
  unfold hitB at h
  exact of_decide_eq_true h

abbrev Opt (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (wit : List ℕ) (c P lv : ℕ) (E : List ℕ) : Prop :=
  D ≤ lv ∨ goodC T zs P E = false ∨ (∃ w ∈ wit, hitB parts perms lv E c w = true) ∨
    (D ≤ lv + 1 ∧ leafB T zs (c :: E) = true)

def optB (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (wit : List ℕ) (c P lv : ℕ) (E : List ℕ) : Bool :=
  decide (Opt T zs D parts perms wit c P lv E)

theorem optB_ok (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (wit : List ℕ) (c P lv : ℕ) (E : List ℕ)
    (h : optB T zs D parts perms wit c P lv E = true) : Opt T zs D parts perms wit c P lv E := by
  unfold optB at h
  exact of_decide_eq_true h

abbrev OkOne (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a b c P : ℕ) : Prop :=
  c ∈ L ∨ c = 0 ∨ c = ALL ∨ (optB T zs D parts perms wit c P (i + 2) L = true ∧
      optB T zs D parts perms wit c P (i + 1) (L.filter (fun x => decide (x ≠ a))) = true ∧
      optB T zs D parts perms wit c P (i + 1) (L.filter (fun x => decide (x ≠ b))) = true ∧
      optB T zs D parts perms wit c P i
        (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))) = true)

def okOneB (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a b c P : ℕ) : Bool :=
  decide (OkOne T zs D parts perms i L wit a b c P)

theorem okOneB_ok (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a b c P : ℕ)
    (h : okOneB T zs D parts perms i L wit a b c P = true) : OkOne T zs D parts perms i L wit a b c P := by
  unfold okOneB at h
  exact of_decide_eq_true h

abbrev OkNot (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a c P : ℕ) : Prop :=
  c ∈ L ∨ c = 0 ∨ c = ALL ∨ (optB T zs D parts perms wit c P (i + 2) L = true ∧
      optB T zs D parts perms wit c P (i + 1) (L.filter (fun x => decide (x ≠ a))) = true)

def okNotB (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a c P : ℕ) : Bool :=
  decide (OkNot T zs D parts perms i L wit a c P)

theorem okNotB_ok (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a c P : ℕ)
    (h : okNotB T zs D parts perms i L wit a c P = true) : OkNot T zs D parts perms i L wit a c P := by
  unfold okNotB at h
  exact of_decide_eq_true h

abbrev OkEntry (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (e : ℕ × List ℕ × List ℕ) : Prop :=
  e.2.1.Nodup ∧ e.2.1.length ≠ 1 ∧ ∀ a ∈ e.2.1, ∀ b ∈ e.2.1,
    (a < b → okOneB T zs D parts perms e.1 e.2.1 e.2.2 a b (a &&& b) (vand T zs a b) = true ∧
      okOneB T zs D parts perms e.1 e.2.1 e.2.2 a b (a ||| b) (vor T zs a b) = true) ∧
    (a = b → okNotB T zs D parts perms e.1 e.2.1 e.2.2 a (ALL ^^^ a) (pkF T zs a) = true)

theorem opt_inF (T D : ℕ) (zs : List ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (hT : T < 2 ^ 64) (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false)
    (hperm : ∀ π ∈ perms, PermOk T π) (wit : List ℕ) (c P : ℕ) (hP : Cov T zs c P) (lv : ℕ)
    (El : List ℕ) (hopt : optB T zs D parts perms wit c P lv El = true) (hnd : El.Nodup)
    (hc : c ∉ El) (hg : Good T (insert c El.toFinset)) (δ' : ℕ) (hδ' : δ' < D) (hle : lv ≤ δ') :
    InF T D parts.flatten δ' (insert c El.toFinset) := by
  have hcons : (c :: El).toFinset = insert c El.toFinset := List.toFinset_cons
  rcases optB_ok T zs D parts perms wit c P lv El hopt with h3 | h3 | ⟨w, hw, hh⟩ | ⟨h3, h4⟩
  · omega
  · rw [goodC_true T zs hT hzs El c P hP hg] at h3
    exact absurd h3 (by decide)
  · obtain ⟨hkey, hh2⟩ := hitB_ok parts perms lv El c w hh
    obtain ⟨hp1, hp2, hp3, hlv', heq⟩ := hit2B_ok parts perms lv El c w hh2
    left
    have hmem : ent parts (w % 1000) ∈ parts.flatten := by
      refine List.mem_flatten.mpr ⟨parts.getD ((w % 1000) / 16) [], ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hp1]
        exact List.getElem_mem hp1
      · unfold ent
        rw [List.getD_eq_getElem _ _ hp2]
        exact List.getElem_mem hp2
    by_cases h0 : (w / 1000) % 10 = 0
    · rw [if_pos h0] at heq
      refine ⟨ent parts (w % 1000), hmem, le_trans hlv' hle, fun x => x, sym_id T, ?_⟩
      rw [Finset.image_id', heq, List.toFinset_eq_of_perm _ _ (List.perm_orderedInsert _ _ _),
        hcons]
    · rw [if_neg h0] at heq
      refine ⟨ent parts (w % 1000), hmem, le_trans hlv' hle,
        app (perms.getD ((w / 1000) % 10) []), sym_app T _ (hperm _ ?_), ?_⟩
      · rw [List.getD_eq_getElem _ _ hp3]
        exact List.getElem_mem hp3
      · rw [← map_fin, ← List.toFinset_eq_of_perm _ _
          (List.perm_insertionSort (fun x y : ℕ => x ≤ y) _),
          heq, List.toFinset_eq_of_perm _ _ (List.perm_orderedInsert _ _ _), hcons]
  · right
    refine ⟨by omega, ?_⟩
    rw [← hcons]
    exact leaf_of_leafL T zs hT hzs (c :: El) (List.nodup_cons.mpr ⟨hc, hnd⟩)
      (leafB_ok T zs _ h4)

theorem clos_rep (T D : ℕ) (zs : List ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (hT : T < 2 ^ 64) (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false)
    (hperm : ∀ π ∈ perms, PermOk T π)
    (hok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry T zs D parts perms e)
    (e : ℕ × List ℕ × List ℕ) (he : e ∈ parts.flatten) (δ : ℕ) (hlv : e.1 ≤ δ)
    (a : ℕ) (ha : a ∈ e.2.1.toFinset) (b : ℕ) (hb : b ∈ e.2.1.toFinset) (c : ℕ)
    (hcand : (a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a))
    (hcS : c ∉ e.2.1.toFinset) (hc0 : c ≠ 0) (hcA : c ≠ ALL) (E : Finset ℕ)
    (hES : E ⊆ e.2.1.toFinset) (hSE : e.2.1.toFinset ⊆ insert a (insert b E))
    (hg : Good T (insert c E)) (δ' : ℕ) (hδ' : δ' < D)
    (hlev : δ' + e.2.1.toFinset.card = δ + E.card + 2) :
    InF T D parts.flatten δ' (insert c E) := by
  obtain ⟨part, hpart, hep⟩ := List.mem_flatten.mp he
  obtain ⟨hnd, _, hall⟩ := hok part hpart e hep
  have hcL : c ∉ e.2.1 := fun h => hcS (List.mem_toFinset.mpr h)
  have fin : ∀ (P : ℕ), Cov T zs c P → ∀ (lv : ℕ) (El : List ℕ),
      optB T zs D parts perms e.2.2 c P lv El = true → El.Nodup →
      (∀ x ∈ El, x ∈ e.2.1) → El.toFinset = E → lv ≤ δ' →
      InF T D parts.flatten δ' (insert c E) := by
    intro P hP lv El hopt hEl hsub hEq hle
    have h := opt_inF T D zs parts perms hT hzs hperm e.2.2 c P hP lv El hopt hEl
      (fun h2 => hcL (hsub c h2)) (by rw [hEq]; exact hg) δ' hδ' hle
    rw [hEq] at h
    exact h
  have same : E = e.2.1.toFinset → δ' = δ + 2 := by
    intro h1
    rw [h1] at hlev
    omega
  have one : ∀ x : ℕ, x ∈ e.2.1.toFinset → E = e.2.1.toFinset.erase x → δ' = δ + 1 := by
    intro x hx h1
    have hpos : 0 < e.2.1.toFinset.card := Finset.card_pos.mpr ⟨x, hx⟩
    rw [h1, Finset.card_erase_of_mem hx] at hlev
    omega
  have two : ∀ x y : ℕ, x ∈ e.2.1.toFinset → y ∈ e.2.1.toFinset → x ≠ y →
      E = (e.2.1.toFinset.erase x).erase y → δ' = δ := by
    intro x y hx hy hxy h1
    have h2 : 1 < e.2.1.toFinset.card := Finset.one_lt_card.mpr ⟨x, hx, y, hy, hxy⟩
    rw [h1, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩),
      Finset.card_erase_of_mem hx] at hlev
    omega
  have bin : ∀ a' b' : ℕ, a' ∈ e.2.1.toFinset → b' ∈ e.2.1.toFinset → a' < b' →
      (c = a' &&& b' ∨ c = a' ||| b') → e.2.1.toFinset ⊆ insert a' (insert b' E) →
      InF T D parts.flatten δ' (insert c E) := by
    intro a' b' ha' hb' hlt hc hSE'
    obtain ⟨hA, hO⟩ := (hall a' (List.mem_toFinset.mp ha') b' (List.mem_toFinset.mp hb')).1 hlt
    have hP : ∃ P : ℕ, Cov T zs c P ∧
        okOneB T zs D parts perms e.1 e.2.1 e.2.2 a' b' c P = true := by
      rcases hc with e2 | e2
      · rw [e2]
        exact ⟨_, cov_and T zs hT a' b', hA⟩
      · rw [e2]
        exact ⟨_, cov_or T zs hT a' b', hO⟩
    obtain ⟨P, hcov, hok1⟩ := hP
    rcases okOneB_ok T zs D parts perms e.1 e.2.1 e.2.2 a' b' c P hok1 with
      h | h | h | ⟨o2, o1a, o1b, o0⟩
    · exact absurd h hcL
    · exact absurd h hc0
    · exact absurd h hcA
    · rcases sub_cases e.2.1.toFinset E a' b' hES hSE' with h1 | h1 | h1 | h1
      · have h2 := same h1
        exact fin _ hcov _ e.2.1 o2 hnd (fun x hx => hx) h1.symm (by rw [h2]; exact Nat.add_le_add_right hlv 2)
      · have h2 := one a' ha' h1
        exact fin _ hcov _ _ o1a (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne, h1]) (by rw [h2]; exact Nat.add_le_add_right hlv 1)
      · have h2 := one b' hb' h1
        exact fin _ hcov _ _ o1b (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne, h1]) (by rw [h2]; exact Nat.add_le_add_right hlv 1)
      · have h2 := two a' b' ha' hb' (Nat.ne_of_lt hlt) h1
        exact fin _ hcov _ _ o0 (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne2, h1]) (by rw [h2]; exact hlv)
  rcases hcand with ⟨hab, hc⟩ | ⟨hab, hc⟩
  · rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact bin a b ha hb hlt hc hSE
    · refine bin b a hb ha hgt ?_ (by rw [Finset.insert_comm]; exact hSE)
      rcases hc with e2 | e2
      · exact Or.inl (e2.trans (Nat.and_comm a b))
      · exact Or.inr (e2.trans (Nat.or_comm a b))
  · subst hab
    subst hc
    have hcov := cov_not T zs hT hzs a
    rcases okNotB_ok T zs D parts perms e.1 e.2.1 e.2.2 a (ALL ^^^ a) (pkF T zs a)
      ((hall a (List.mem_toFinset.mp ha) a (List.mem_toFinset.mp ha)).2 rfl) with
      h | h | h | ⟨o2, o1⟩
    · exact absurd h hcL
    · exact absurd h hc0
    · exact absurd h hcA
    · have fin1 : E = e.2.1.toFinset.erase a → InF T D parts.flatten δ' (insert (ALL ^^^ a) E) := by
        intro h1
        have h2 := one a ha h1
        exact fin _ hcov _ _ o1 (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne, h1]) (by rw [h2]; exact Nat.add_le_add_right hlv 1)
      rcases sub_cases e.2.1.toFinset E a a hES hSE with h1 | h1 | h1 | h1
      · have h2 := same h1
        exact fin _ hcov _ e.2.1 o2 hnd (fun x hx => hx) h1.symm (by rw [h2]; exact Nat.add_le_add_right hlv 2)
      · exact fin1 h1
      · exact fin1 h1
      · rw [Finset.erase_idem] at h1
        exact fin1 h1

theorem clos_of_ok (T D : ℕ) (zs : List ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (hT : T < 2 ^ 64) (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false)
    (hperm : ∀ π ∈ perms, PermOk T π)
    (hok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry T zs D parts perms e) :
    Clos T D parts.flatten := by
  intro δ S hS a ha b hb c hcand hcS hc0 hcA E hES hSE hg δ' hδ' hlev
  rcases hS with ⟨e, he, hlv, f, hf, himg⟩ | ⟨hD, hl1, hl2⟩
  · have hf' := hf
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
    subst himg
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
    have hc0ex : ∃ c0 : ℕ, f c0 = c ∧ ((a0 ≠ b0 ∧ (c0 = a0 &&& b0 ∨ c0 = a0 ||| b0)) ∨
        (a0 = b0 ∧ c0 = ALL ^^^ a0)) := by
      rcases hcand with ⟨hab, hc | hc⟩ | ⟨hab, hc⟩
      · exact ⟨a0 &&& b0, by rw [f4, hc], Or.inl ⟨fun e2 => hab (by rw [e2]), Or.inl rfl⟩⟩
      · exact ⟨a0 ||| b0, by rw [f5, hc], Or.inl ⟨fun e2 => hab (by rw [e2]), Or.inr rfl⟩⟩
      · exact ⟨ALL ^^^ a0, by rw [f6, hc], Or.inr ⟨f1 hab, rfl⟩⟩
    obtain ⟨c0, rfl, hcand0⟩ := hc0ex
    have hE0 : (e.2.1.toFinset.filter (fun x => f x ∈ E)).image f = E := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩
        exact hx
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hES hy)
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    have hS0E : e.2.1.toFinset ⊆
        insert a0 (insert b0 (e.2.1.toFinset.filter (fun x => f x ∈ E))) := by
      intro x hx
      rcases Finset.mem_insert.mp (hSE (Finset.mem_image_of_mem f hx)) with h1 | h1
      · rw [f1 h1]
        exact Finset.mem_insert_self _ _
      · rcases Finset.mem_insert.mp h1 with h1 | h1
        · rw [f1 h1]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_filter.mpr ⟨hx, h1⟩))
    have himg2 : (insert c0 (e.2.1.toFinset.filter (fun x => f x ∈ E))).image f =
        insert (f c0) E := by rw [Finset.image_insert, hE0]
    have hcard1 : (e.2.1.toFinset.image f).card = e.2.1.toFinset.card :=
      Finset.card_image_of_injective _ f1
    have hcard2 : E.card = (e.2.1.toFinset.filter (fun x => f x ∈ E)).card := by
      conv_lhs => rw [← hE0]
      exact Finset.card_image_of_injective _ f1
    have hrep := clos_rep T D zs parts perms hT hzs hperm hok e he δ hlv a0 ha0 b0 hb0 c0
      hcand0 (fun h => hcS (Finset.mem_image_of_mem f h)) (fun h => hc0 (by rw [h, f2]))
      (fun h => hcA (by rw [h, f3])) _ (Finset.filter_subset _ _) hS0E
      (f7 _ (by rw [himg2]; exact hg)) δ' hδ' (by omega)
    rw [← himg2]
    rcases hrep with ⟨e', he', hlv', g, hgs, hgi⟩ | ⟨hD', hleaf'⟩
    · refine Or.inl ⟨e', he', hlv', fun x => f (g x), sym_comp T f g hf' hgs, ?_⟩
      rw [← hgi, Finset.image_image]
      rfl
    · exact Or.inr ⟨hD', leaf_sym T f hf' _ hleaf'⟩
  · exfalso
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
    rcases hcand with ⟨hab, hc⟩ | ⟨hab, hc⟩
    · rcases sub_cases S E a b hES hSE with h1 | h1 | h1 | h1
      · rw [h1] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem ha] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem hb] at hlev
        omega
      · rw [h1] at hg
        exact hl2 a ha b hb hab c hc hg
    · subst hab
      rcases sub_cases S E a a hES hSE with h1 | h1 | h1 | h1
      · rw [h1] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem ha] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem ha] at hlev
        omega
      · rw [h1, Finset.erase_idem, Finset.card_erase_of_mem ha] at hlev
        omega

theorem jn_base (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (base : List ℕ)
    (hpool : pool0 = base ++ [0, ALL])
    (hnec : ∀ a ∈ base, ¬ GoodL T zs (base.filter (fun x => decide (x ≠ a))))
    (hbase : ∃ e ∈ fam, e.1 = 0 ∧ e.2.1 = base) (hcard : base.length = N) (hnd : base.Nodup) :
    Jn T N D fam pool0 0 := by
  intro G hG hG0 hGA hg
  have hGb : G ⊆ base.toFinset := by
    intro x hx
    have h1 := List.mem_toFinset.mp (hG hx)
    rw [hpool] at h1
    rcases List.mem_append.mp h1 with h1 | h1
    · exact List.mem_toFinset.mpr h1
    · exfalso
      rcases List.mem_cons.mp h1 with h1 | h1
      · exact hG0 (by rw [← h1]; exact hx)
      · exact hGA (by rw [← List.mem_singleton.mp h1]; exact hx)
  have hbG : base.toFinset ⊆ G := by
    intro a ha
    by_contra hna
    apply hnec a (List.mem_toFinset.mp ha)
    apply goodL_of_good T zs hT hzs
    rw [filter_ne]
    exact good_mono T G _ (fun x hx => Finset.mem_erase.mpr
      ⟨fun e => hna (by rw [← e]; exact hx), hGb hx⟩) hg
  have hEq : G = base.toFinset := Finset.Subset.antisymm hGb hbG
  have hc : G.card = N := by rw [hEq, List.toFinset_card_of_nodup hnd, hcard]
  obtain ⟨e0, he0, h01, h02⟩ := hbase
  exact ⟨by omega, fun δ _ _ => Or.inl ⟨e0, he0, by omega, fun x => x, sym_id T, by
    rw [Finset.image_id', h02]
    exact hEq.symm⟩⟩

theorem main (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (hcl : Clos T D fam)
    (hT1 : ∃ p : Fin 64, T.testBit p = true) (hT0 : ∃ q : Fin 64, T.testBit q = false) :
    ∀ (gs : List Gate) (pool : List ℕ) (ws : Fin 64 → List Bool) (L j o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    (∀ p, (ws p).length = L) → Inv pool ws → Jn T N D fam pool j →
    (∀ p : Fin 64, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = T.testBit p) →
    N ≤ 1 + (j + gs.length) ∧
      ∀ δ : ℕ, δ < D → 1 + (j + gs.length) = N + δ → ∃ m : ℕ, InF T D fam δ {m}
  | [], pool, ws, L, j, o, _, _, hI, hJ, hout => by
    obtain ⟨m, hm, hmb⟩ := hI.2.2 o
    have hmT : ∀ p : Fin 64, m.testBit p = T.testBit p := fun p => (hmb p).trans (hout p)
    have hg : Good T {m} := by
      intro p q hp hq
      refine ⟨m, Finset.mem_singleton_self m, ?_⟩
      rw [hmT p, hmT q, hp, hq]
      simp
    have hm0 : (0 : ℕ) ∉ ({m} : Finset ℕ) := by
      intro e
      obtain ⟨p, hp⟩ := hT1
      have h1 := hmT p
      rw [← Finset.mem_singleton.mp e, Nat.zero_testBit, hp] at h1
      exact absurd h1 (by simp)
    have hmA : ALL ∉ ({m} : Finset ℕ) := by
      intro e
      obtain ⟨q, hq⟩ := hT0
      have h1 := hmT q
      rw [← Finset.mem_singleton.mp e, all_bit q, hq] at h1
      exact absurd h1 (by simp)
    obtain ⟨h1, h2⟩ := hJ {m} (by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact List.mem_toFinset.mpr hm) hm0 hmA hg
    rw [Finset.card_singleton] at h1 h2
    simp only [List.length_nil, Nat.add_zero]
    exact ⟨by omega, fun δ hδ e => ⟨m, h2 δ hδ (by omega)⟩⟩
  | g :: gs, pool, ws, L, j, o, hg, hL, hI, hJ, hout => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hout' : ∀ p : Fin 64, (gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)])).getD o false =
          T.testBit p :=
      fun p => by
        have h3 := hout p
        rw [List.foldl_cons] at h3
        exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 :=
      fun p => by simp [hL p]
    have hlen2 : 1 + (j + (g :: gs).length) = 1 + ((j + 1) + gs.length) := by
      simp only [List.length_cons]
      omega
    rw [hlen2]
    by_cases hcin : c ∈ pool
    · exact main T N D fam hcl hT1 hT0 gs pool _ (L + 1) (j + 1) o hg' hL'
        (inv_step pool pool ws L hL hI _ c hcv (fun m hm => hm) hcin)
        (jn_weak T N D fam pool j hJ) hout'
    · exact main T N D fam hcl hT1 hT0 gs (pool ++ [c]) _ (L + 1) (j + 1) o hg' hL'
        (inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
        (jn_step T N D fam hcl pool j c hJ hc hcin) hout'

theorem lower (T N D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ))
    (zs base : List ℕ) (hT : T < 2 ^ 64)
    (hT1 : ∃ p : Fin 64, T.testBit p = true) (hT0 : ∃ q : Fin 64, T.testBit q = false)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (hperm : ∀ π ∈ perms, PermOk T π)
    (hok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry T zs D parts perms e)
    (hpool : pool0 = base ++ [0, ALL])
    (hnec : ∀ a ∈ base, ¬ GoodL T zs (base.filter (fun x => decide (x ≠ a))))
    (hbase : ∃ e ∈ parts.flatten, e.1 = 0 ∧ e.2.1 = base) (hcard : base.length = N)
    (hnd : base.Nodup)
    (C : Circuit) (hC : FanInTwo C) (hev : ∀ p : Fin 64, C.eval (X p) = T.testBit p) :
    N + D ≤ C.gates.length + 1 := by
  obtain ⟨h1, h2⟩ := main T N D parts.flatten (clos_of_ok T D zs parts perms hT hzs hperm hok)
    hT1 hT0 C.gates pool0 X 6 0 C.output hC X_len inv0
    (jn_base T N D parts.flatten zs hT hzs base hpool hnec hbase hcard hnd) hev
  by_contra hlt
  obtain ⟨m, hm⟩ := h2 (1 + (0 + C.gates.length) - N) (by omega) (by omega)
  rcases hm with ⟨e, he, _, f, hf, hem⟩ | ⟨_, hl1, _⟩
  · obtain ⟨part, hpart, hep⟩ := List.mem_flatten.mp he
    obtain ⟨hnd', hlen, _⟩ := hok part hpart e hep
    apply hlen
    rw [← List.toFinset_card_of_nodup hnd', ← Finset.card_image_of_injective _ hf.1, hem,
      Finset.card_singleton]
  · exact hl1 (Finset.card_singleton m)

def tab : ℕ := 18369882623157661408

def zs : List ℕ := [0, 1, 2, 3, 4, 8, 12, 16, 20, 24, 32, 34, 36, 40, 44, 48, 52, 56]

def t0 : ℕ := 65535
def t1 : ℕ := 1431655765
def t2 : ℕ := 2863311530
def t3 : ℕ := 3435973836
def t4 : ℕ := 4042322160
def t5 : ℕ := 4294967295
def t6 : ℕ := 1095216660735
def t7 : ℕ := 93823560602965
def t8 : ℕ := 93823560603135
def t9 : ℕ := 93823560646655
def t10 : ℕ := 93827855548415
def t11 : ℕ := 187647121162240
def t12 : ℕ := 187647121205930
def t13 : ℕ := 225176545447116
def t14 : ℕ := 264913582878960
def t15 : ℕ := 281470681743360
def t16 : ℕ := 281470681808895
def t17 : ℕ := 281474976710655
def t18 : ℕ := 71777214294589695
def t19 : ℕ := 72057589759737855
def t20 : ℕ := 1229782938247303441
def t21 : ℕ := 1229782938819965747
def t22 : ℕ := 2459565876494606882
def t23 : ℕ := 3472328296227680304
def t24 : ℕ := 3689348813882916864
def t25 : ℕ := 3689348814741910323
def t26 : ℕ := 3689573991287357439
def t27 : ℕ := 4919131752989213764
def t28 : ℕ := 4919131755279862988
def t29 : ℕ := 5787213827046133840
def t30 : ℕ := 5787213829741015280
def t31 : ℕ := 6148914689804861440
def t32 : ℕ := 6148914691236517205
def t33 : ℕ := 6148914691236560895
def t34 : ℕ := 6148914694099828735
def t35 : ℕ := 6149102338357723135
def t36 : ℕ := 8608480567731124087
def t37 : ℕ := 9259542123273814144
def t38 : ℕ := 9838263503687778304
def t39 : ℕ := 9838263505978427528
def t40 : ℕ := 11529390970613309440
def t41 : ℕ := 11574427651397386240
def t42 : ℕ := 11574427654092267680
def t43 : ℕ := 12153149036796881064
def t44 : ℕ := 12295014589755599520
def t45 : ℕ := 12297641735351828480
def t46 : ℕ := 12297829379609722880
def t47 : ℕ := 12297829381765628032
def t48 : ℕ := 12297829381900372104
def t49 : ℕ := 12297829382294118400
def t50 : ℕ := 12297829382304604320
def t51 : ℕ := 12297829382472379040
def t52 : ℕ := 12297829382472990720
def t53 : ℕ := 12297829382473034410
def t54 : ℕ := 12297829383904690175
def t55 : ℕ := 12297923203170369535
def t56 : ℕ := 12297923206033637375
def t57 : ℕ := 13527612317570695168
def t58 : ℕ := 13527612318429688627
def t59 : ℕ := 13527612320720337851
def t60 : ℕ := 13835269164735971328
def t61 : ℕ := 13889313181676863488
def t62 : ℕ := 13889313184910721216
def t63 : ℕ := 14468034567480590528
def t64 : ℕ := 14468034567615334600
def t65 : ℕ := 14754017507706719424
def t66 : ℕ := 14757170082422194176
def t67 : ℕ := 14757395207428033728
def t68 : ℕ := 14757395255531667456
def t69 : ℕ := 14757395257822316680
def t70 : ℕ := 14757395258765525184
def t71 : ℕ := 14757395258967641292
def t72 : ℕ := 14757395259540303598
def t73 : ℕ := 14757395259826634751
def t74 : ℕ := 14757451553104003071
def t75 : ℕ := 15987178197214944733
def t76 : ℕ := 16204198715729174752
def t77 : ℕ := 16927600440168677376
def t78 : ℕ := 16927600443402535104
def t79 : ℕ := 16927600443941511392
def t80 : ℕ := 16927600444109941482
def t81 : ℕ := 17072280789247118540
def t82 : ℕ := 17072280789786094828
def t83 : ℕ := 17216961131453612032
def t84 : ℕ := 17216961134316923562
def t85 : ℕ := 17216961134889585868
def t86 : ℕ := 17216961135226446048
def t87 : ℕ := 17216961135428562156
def t88 : ℕ := 17216961135462248174
def t89 : ℕ := 17293822573129236480
def t90 : ℕ := 17294086451893370880
def t91 : ℕ := 17294086455919964160
def t92 : ℕ := 17339123139388436480
def t93 : ℕ := 17339123139398922400
def t94 : ℕ := 17348130476094714048
def t95 : ℕ := 17357137812790505696
def t96 : ℕ := 17361376567555522560
def t97 : ℕ := 17361640450346250240
def t98 : ℕ := 17361641477096079360
def t99 : ℕ := 17361641479790960800
def t100 : ℕ := 17361641480329937088
def t101 : ℕ := 17361641481122672640
def t102 : ℕ := 17361641481138401520
def t103 : ℕ := 17361641481391046655
def t104 : ℕ := 17361658038237331455
def t105 : ℕ := 17578661999652631539
def t106 : ℕ := 17723342345328784885
def t107 : ℕ := 17723342345497214975
def t108 : ℕ := 17940362863843014904
def t109 : ℕ := 18062436906849446570
def t110 : ℕ := 18062524863574179840
def t111 : ℕ := 18062524867600773120
def t112 : ℕ := 18062524867779689130
def t113 : ℕ := 18082228416801733360
def t114 : ℕ := 18085043205308416000
def t115 : ℕ := 18085043208171727530
def t116 : ℕ := 18085043209350738160
def t117 : ℕ := 18085043209502784000
def t118 : ℕ := 18085043209518512880
def t119 : ℕ := 18085043209519168250
def t120 : ℕ := 18216159773593488588
def t121 : ℕ := 18216212550151634124
def t122 : ℕ := 18226345803934399728
def t123 : ℕ := 18229723550950883328
def t124 : ℕ := 18229723554386857164
def t125 : ℕ := 18229723554993205488
def t126 : ℕ := 18229723555195321596
def t127 : ℕ := 18374403896593350656
def t128 : ℕ := 18374403900635672816
def t129 : ℕ := 18374403900871474942
def t130 : ℕ := 18374966859414961920
def t131 : ℕ := 18374967589559402240
def t132 : ℕ := 18413248040363163392
def t133 : ℕ := 18420003542883434240
def t134 : ℕ := 18420003542893920160
def t135 : ℕ := 18422724877111787520
def t136 : ℕ := 18422724877122972330
def t137 : ℕ := 18422817605455773440
def t138 : ℕ := 18422817605466914560
def t139 : ℕ := 18422818335600213760
def t140 : ℕ := 18422818335610699680
def t141 : ℕ := 18422818335611354880
def t142 : ℕ := 18422818335611355050
def t143 : ℕ := 18442505391958978800
def t144 : ℕ := 18442521880339415040
def t145 : ℕ := 18442521884381737200
def t146 : ℕ := 18442521884633399280
def t147 : ℕ := 18445336673056194560
def t148 : ℕ := 18445336677098516720
def t149 : ℕ := 18445336677350178800
def t150 : ℕ := 18445336677350834170
def t151 : ℕ := 18445899635894321148
def t152 : ℕ := 18446462598732840960
def t153 : ℕ := 18446462603027742720
def t154 : ℕ := 18446463333172183040
def t155 : ℕ := 18446612720724672512
def t156 : ℕ := 18446639212082954240
def t157 : ℕ := 18446639212082995360
def t158 : ℕ := 18446650245854003200
def t159 : ℕ := 18446650250148904960
def t160 : ℕ := 18446650250148937856
def t161 : ℕ := 18446650250148945920
def t162 : ℕ := 18446650250148946080
def t163 : ℕ := 18446650250148948480
def t164 : ℕ := 18446650250148948640
def t165 : ℕ := 18446650250148948650
def t166 : ℕ := 18446674533894045888
def t167 : ℕ := 18446686903399861248
def t168 : ℕ := 18446687487515413504
def t169 : ℕ := 18446687779573189836
def t170 : ℕ := 18446709855705096416
def t171 : ℕ := 18446720893770989568
def t172 : ℕ := 18446720893771038912
def t173 : ℕ := 18446725308997369856
def t174 : ℕ := 18446725308997422284
def t175 : ℕ := 18446725308997431022
def t176 : ℕ := 18446727516610621680
def t177 : ℕ := 18446738554676572400
def t178 : ℕ := 18446742978492890880
def t179 : ℕ := 18446744009285042160
def t180 : ℕ := 18446744069414584320
def t181 : ℕ := 18446744069414649855
def t182 : ℕ := 18446744069700915473
def t183 : ℕ := 18446744070273577779
def t184 : ℕ := 18446744070846240085
def t185 : ℕ := 18446744071705233544
def t186 : ℕ := 18446744072109465760
def t187 : ℕ := 18446744072277895850
def t188 : ℕ := 18446744072648442048
def t189 : ℕ := 18446744072850558156
def t190 : ℕ := 18446744073187418336
def t191 : ℕ := 18446744073423220462
def t192 : ℕ := 18446744073441177600
def t193 : ℕ := 18446744073456906480
def t194 : ℕ := 18446744073625336570
def t195 : ℕ := 18446744073659022588
def t196 : ℕ := 18446744073692839680
def t197 : ℕ := 18446744073708568560
def t198 : ℕ := 18446744073709486080
def t199 : ℕ := 18446744073709547760
def t200 : ℕ := 18446744073709551600

def base : List ℕ := [t53, t71, t102, t130, t153, t180]

def perms : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
  [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 40, 41, 42, 43, 44, 45, 46, 47, 56, 57, 58, 59, 60, 61, 62, 63],
  [0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15, 16, 17, 18, 19, 24, 25, 26, 27, 20, 21, 22, 23, 28, 29, 30, 31, 32, 33, 34, 35, 40, 41, 42, 43, 36, 37, 38, 39, 44, 45, 46, 47, 48, 49, 50, 51, 56, 57, 58, 59, 52, 53, 54, 55, 60, 61, 62, 63],
  [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27, 4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31, 32, 33, 34, 35, 40, 41, 42, 43, 48, 49, 50, 51, 56, 57, 58, 59, 36, 37, 38, 39, 44, 45, 46, 47, 52, 53, 54, 55, 60, 61, 62, 63],
  [0, 1, 2, 3, 16, 17, 18, 19, 4, 5, 6, 7, 20, 21, 22, 23, 8, 9, 10, 11, 24, 25, 26, 27, 12, 13, 14, 15, 28, 29, 30, 31, 32, 33, 34, 35, 48, 49, 50, 51, 36, 37, 38, 39, 52, 53, 54, 55, 40, 41, 42, 43, 56, 57, 58, 59, 44, 45, 46, 47, 60, 61, 62, 63],
  [0, 1, 2, 3, 16, 17, 18, 19, 8, 9, 10, 11, 24, 25, 26, 27, 4, 5, 6, 7, 20, 21, 22, 23, 12, 13, 14, 15, 28, 29, 30, 31, 32, 33, 34, 35, 48, 49, 50, 51, 40, 41, 42, 43, 56, 57, 58, 59, 36, 37, 38, 39, 52, 53, 54, 55, 44, 45, 46, 47, 60, 61, 62, 63]]

def fam0 : List (ℕ × List ℕ × List ℕ) := [
  (0, [t53, t71, t102, t130, t153, t180], [210064, 510224, 930048, 690208, 814032, 414192, 811032, 411192, 810032, 410192, 810016, 410176, 740240, 440112, 200320, 260256, 960368, 262256, 962368, 263256, 963368, 660080, 260272, 960416, 620288, 420384, 822288, 222384, 223288, 823384, 20304, 20432, 60336, 260400, 61336, 261400, 60352, 660096, 260448, 64336, 264400, 62352, 662096, 262448, 63352, 663096, 263448]),
  (2, [t27, t32, t102, t130, t153, t180], [420017]),
  (2, [t88, t102, t114, t130, t153], [210461, 371381, 370381, 780143, 24160, 24479, 620018]),
  (3, [t16, t18, t53, t71, t102, t130, t180], []),
  (3, [t25, t46, t53, t102, t130, t153, t180], []),
  (3, [t37, t53, t71, t102, t130, t153, t180], []),
  (3, [t53, t62, t71, t102, t130, t166, t180], []),
  (3, [t53, t71, t102, t116, t130, t153, t180], [940684, 660363, 864731, 860273, 660096]),
  (3, [t53, t88, t102, t130, t153, t180, t187], [320586]),
  (3, [t16, t53, t88, t102, t130, t193], [572413, 470237]),
  (3, [t39, t53, t71, t102, t130, t159], [580637]),
  (3, [t50, t53, t88, t102, t130, t153], [324737, 521654, 520654]),
  (3, [t53, t71, t102, t130, t165, t199], [240655, 60689]),
  (3, [t8, t53, t71, t102, t130], []),
  (3, [t46, t88, t102, t130, t156], [20160]),
  (3, [t71, t80, t102, t130, t171], [])]

def fam1 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t5, t53, t71, t102, t130, t153], [60000, 910176, 460528, 760290, 180512, 64496, 664274, 61496, 661274, 60496, 660274, 160480, 10178, 460354, 70210, 220402, 310242, 410257, 260466, 312242, 412257, 262466, 313242, 413257, 263466, 990306, 690544, 450418, 510322, 210482, 512322, 212482, 513322, 213482, 870370, 670498, 72370, 472498, 473370, 73498, 310434, 510514, 311434, 511514, 314434, 514514]),
  (2, [t27, t53, t102, t130, t153, t180], [210209, 370001, 440112, 820409]),
  (2, [t88, t102, t116, t130, t153], [10477, 171397, 170397, 740127, 644527, 940175, 822255, 24543, 823255, 25543, 20463, 21463]),
  (3, [t16, t25, t53, t102, t130, t153, t180], []),
  (3, [t25, t53, t59, t102, t130, t153, t180], []),
  (3, [t38, t46, t53, t71, t102, t130, t153], [984186, 581186, 780186, 984745, 981745, 980745, 60729]),
  (3, [t53, t62, t71, t126, t130, t153, t180], []),
  (3, [t53, t71, t102, t119, t130, t153, t193], [440700, 460289]),
  (3, [t53, t88, t102, t130, t153, t180, t189], [500602, 660682, 380481]),
  (3, [t16, t53, t88, t102, t130, t198], [470253]),
  (3, [t41, t46, t88, t102, t130, t153], [221014, 220014, 220669, 221653, 220653]),
  (3, [t50, t71, t88, t102, t130, t153], [784753, 981063, 980063]),
  (3, [t53, t71, t102, t136, t178, t180], []),
  (3, [t9, t18, t53, t71, t102], []),
  (3, [t46, t88, t102, t130, t157], [220114]),
  (3, [t71, t80, t116, t130, t153], [744160])]

def fam2 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t16, t53, t71, t102, t130, t180], [60000, 910192, 460624, 760035, 180608, 62592, 662003, 60592, 660003, 60496, 10626, 460147, 870658, 420211, 310690, 260291, 312690, 262291, 710560, 310738, 260451, 990067, 690688, 450227, 510083, 210307, 512083, 212307, 910640, 510131, 210467, 870163, 670323, 72163, 472323, 270195, 270483, 310243, 510339, 310275, 910656, 510499, 312275, 912656, 512499]),
  (2, [t32, t46, t71, t102, t130, t153], [60080, 580265, 464488, 461488, 460488, 560049, 990393, 290362, 30505, 714625, 310585, 114489, 711625, 312585, 111489, 710625, 313585, 110489]),
  (2, [t88, t102, t130, t159, t180], [540207, 840575, 820287, 20591, 822287, 22591, 220479, 20607]),
  (3, [t16, t32, t53, t71, t102, t130, t180], [760488]),
  (3, [t25, t53, t62, t102, t130, t153, t180], []),
  (3, [t38, t53, t71, t102, t130, t153, t180], []),
  (3, [t53, t62, t88, t102, t130, t153, t180], [440588, 300330, 401396, 200396, 800284]),
  (3, [t53, t71, t102, t119, t130, t153, t196], [440716, 364012, 860443]),
  (3, [t53, t88, t102, t130, t153, t180, t191], [680618]),
  (3, [t16, t88, t102, t119, t130, t180], [972413, 270381]),
  (3, [t41, t53, t71, t102, t130, t159], [700542, 860366, 940653]),
  (3, [t50, t71, t119, t130, t153, t193], []),
  (3, [t53, t71, t102, t139, t159, t180], []),
  (3, [t9, t46, t88, t102, t130], []),
  (3, [t46, t88, t102, t130, t166], []),
  (3, [t71, t84, t102, t130, t159], [740160])]

def fam3 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t25, t53, t102, t130, t153, t180], [620000, 310208, 140720, 440707, 744608, 344019, 741608, 341019, 740608, 340019, 740512, 210611, 210209, 900020, 430643, 780116, 232643, 982116, 833643, 383116, 30675, 180180, 190739, 890132, 192739, 892132, 193739, 893132, 590736, 190004, 890196, 990084, 190164, 991084, 191164, 990100, 590752, 190228, 994084, 194164, 992100, 592752, 192228, 993100, 593752, 193228]),
  (2, [t32, t71, t102, t130, t153, t184], [210305]),
  (2, [t88, t102, t130, t165, t198], [510493, 674413, 671413, 520655, 522655, 20160, 420607, 520495]),
  (3, [t16, t32, t71, t102, t130, t153, t180], []),
  (3, [t25, t53, t68, t102, t130, t153, t180], []),
  (3, [t39, t46, t53, t71, t102, t130, t153], [704010, 701010, 700010, 780761]),
  (3, [t53, t62, t102, t126, t130, t153, t180], []),
  (3, [t53, t71, t102, t121, t130, t153, t180], []),
  (3, [t53, t88, t102, t130, t153, t180, t193], [924764, 220634, 820059]),
  (3, [t16, t88, t102, t130, t165, t180], []),
  (3, [t41, t53, t71, t116, t130, t153], [700558, 865414, 864414, 940669]),
  (3, [t50, t88, t102, t130, t153, t180], [624034, 820128]),
  (3, [t53, t72, t102, t130, t153, t180], []),
  (3, [t9, t53, t71, t102, t139], []),
  (3, [t46, t88, t102, t130, t170], []),
  (3, [t71, t88, t102, t130, t162], [])]

def fam4 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t32, t71, t102, t130, t153, t180], [260000, 410224, 780720, 664624, 264051, 661624, 261051, 660624, 260051, 660528, 190001, 950276, 640516, 710308, 160580, 712308, 162580, 713308, 163580, 710340, 560049, 160644, 470484, 270612, 672484, 72612, 73484, 673612, 870500, 870676, 910548, 110628, 911548, 111628, 910564, 510065, 110692, 914548, 114628, 912564, 512065, 112692, 913564, 513065, 113692]),
  (2, [t32, t71, t102, t130, t153, t193], [60096]),
  (2, [t9, t88, t102, t130], [20160]),
  (3, [t16, t39, t53, t71, t102, t130, t180], []),
  (3, [t25, t53, t88, t102, t130, t153, t180], [130460, 510297]),
  (3, [t39, t53, t71, t102, t130, t153, t193], []),
  (3, [t53, t64, t71, t102, t130, t153, t180], [980513]),
  (3, [t53, t71, t102, t122, t130, t153, t180], []),
  (3, [t62, t71, t80, t102, t130, t153, t180], []),
  (3, [t20, t46, t53, t102, t130, t153], []),
  (3, [t42, t46, t88, t102, t130, t153], [220673, 421030, 420030, 420701, 421685, 420685]),
  (3, [t50, t88, t102, t130, t153, t193], [424607, 621623, 620623]),
  (3, [t53, t85, t102, t116, t130, t153], [340018]),
  (3, [t9, t53, t85, t102, t130], [590066]),
  (3, [t46, t88, t102, t139, t159], []),
  (3, [t71, t88, t102, t139, t159], [])]

def fam5 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t46, t53, t71, t102, t130, t153], [210097, 610708, 10033, 310404, 730736, 490755, 614640, 214115, 611640, 211115, 610640, 210115, 300021, 180129, 940357, 660117, 864144, 460289, 264113, 860421, 662117, 861144, 462289, 261113, 862421, 663117, 860144, 463289, 260113, 863421, 540053, 940128, 700161, 240145, 373, 60149, 760437, 62149, 762437, 63149, 763437, 420325, 220453, 622325, 22453, 23325, 623453, 860389, 60469, 861389, 61469, 864389, 64469]),
  (2, [t32, t88, t102, t130, t153, t180], [720112, 120168, 190001, 20617]),
  (2, [t16, t88, t102, t139], [821160]),
  (3, [t16, t42, t53, t71, t102, t130, t180], []),
  (3, [t25, t53, t91, t102, t130, t153, t180], []),
  (3, [t39, t53, t88, t102, t130, t153, t180], [660761]),
  (3, [t53, t65, t71, t102, t130, t153, t180], [144433, 941433]),
  (3, [t53, t71, t102, t123, t130, t153, t180], []),
  (3, [t71, t88, t102, t119, t130, t153, t180], [980513, 484540, 780492]),
  (3, [t20, t46, t71, t102, t130, t153], []),
  (3, [t42, t53, t71, t102, t130, t159], [580574, 60382, 60689, 140685]),
  (3, [t51, t53, t71, t102, t130, t153], [64689, 61689, 660302, 740158]),
  (3, [t53, t85, t102, t130, t159, t180], [340034]),
  (3, [t9, t53, t88, t102, t130], []),
  (3, [t47, t88, t102, t130, t153], [24160]),
  (3, [t71, t102, t109, t178, t180], [])]

def fam6 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t53, t71, t102, t130, t153, t193], [10065, 310452, 730752, 614672, 214387, 611656, 211371, 610656, 210371, 214464, 614146, 540069, 240497, 342, 60181, 164417, 760023, 62197, 762039, 63197, 763039, 60193, 460629, 960535, 420741, 220135, 622757, 22151, 23757, 623151, 100166, 140551, 860406, 60231, 861406, 61231, 864422, 64263, 662598, 460369, 860583, 663598, 461369, 861583]),
  (2, [t34, t53, t71, t102, t130, t153], [660080, 264504, 261504, 260504, 160480, 910136, 30425, 110457, 610379, 112457, 612379, 113457, 613379, 590641, 350713, 890697]),
  (2, [t20, t102, t130, t159], [740160]),
  (3, [t16, t45, t53, t71, t102, t130, t180], []),
  (3, [t25, t53, t98, t102, t130, t153, t180], []),
  (3, [t40, t53, t71, t102, t130, t153, t180], []),
  (3, [t53, t68, t71, t102, t130, t153, t193], []),
  (3, [t53, t71, t102, t124, t130, t153, t180], []),
  (3, [t0, t53, t71, t102, t130, t165], []),
  (3, [t20, t46, t88, t102, t130, t153], []),
  (3, [t42, t53, t71, t116, t130, t153], [580590, 65430, 64430, 140701]),
  (3, [t53, t57, t71, t102, t130, t153], []),
  (3, [t53, t86, t88, t102, t130, t153], [220673]),
  (3, [t9, t71, t88, t102, t130], []),
  (3, [t49, t88, t102, t130, t153], [24160, 21160]),
  (3, [t76, t88, t102, t130, t159], [])]

def fam7 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t53, t88, t102, t130, t153, t180], [670081, 970468, 110704, 330595, 274688, 874531, 271688, 871531, 270688, 870531, 270544, 870578, 720261, 120529, 420711, 722261, 122529, 422711, 723261, 123529, 423711, 820128, 420177, 120145, 720565, 420008, 440647, 340743, 842647, 942743, 643647, 143743, 640465, 240663, 540040, 520679, 720759, 521679, 721759, 520695, 120497, 720056, 524679, 724759, 522695, 122497, 722056, 523695, 123497, 723056]),
  (2, [t46, t53, t71, t102, t130, t159], [410665, 210489, 930281, 814520, 811520, 210248, 100745, 980721, 740235, 380298, 460042, 62705, 660427, 462250, 462042, 60705, 662427, 460250, 140657, 900410, 440314]),
  (2, [t88, t102, t130, t162], []),
  (3, [t16, t46, t53, t71, t102, t130, t153], [260344, 712712, 710712, 710696, 790584]),
  (3, [t25, t53, t102, t105, t130, t153, t180], []),
  (3, [t41, t46, t53, t71, t102, t130, t153], [900266, 61202, 60202, 60058, 61042, 60042, 140026]),
  (3, [t53, t68, t88, t102, t130, t153, t180], [500346]),
  (3, [t53, t71, t102, t125, t130, t153, t180], [660096]),
  (3, [t0, t53, t88, t102, t130, t153], []),
  (3, [t20, t46, t102, t130, t153, t180], []),
  (3, [t46, t53, t55, t71, t102, t130], [312174, 310174, 390717]),
  (3, [t53, t62, t71, t102, t130, t159], [580766, 220702, 541462, 380334]),
  (3, [t53, t87, t102, t130, t153, t193], []),
  (3, [t11, t16, t88, t102, t130], []),
  (3, [t50, t88, t102, t130, t162], []),
  (3, [t76, t88, t116, t130, t153], [])]

def fam8 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t46, t88, t102, t130, t153], [370641, 770649, 610593, 830105, 774561, 374584, 771561, 371584, 770561, 370584, 820026, 24160, 620018, 424657, 20506, 822026, 21160, 622018, 421657, 22506, 823026, 20160, 623018, 420657, 23506, 940426, 840554, 342426, 442554, 143426, 643554, 20474, 220570, 21474, 221570, 24474, 224570]),
  (2, [t46, t53, t85, t102, t130, t153], [490681, 290505, 970217, 894536, 891536, 890536, 144721, 740076, 544298, 141721, 742076, 541298, 140721, 743076, 540298, 940128, 980458, 240145]),
  (2, [t88, t102, t139, t159], []),
  (3, [t16, t46, t53, t71, t102, t130, t180], [712728, 710728, 790600]),
  (3, [t25, t53, t102, t119, t130, t153, t180], [494377, 790345]),
  (3, [t41, t53, t71, t102, t130, t153, t180], []),
  (3, [t53, t69, t71, t102, t130, t153, t180], []),
  (3, [t53, t71, t102, t126, t130, t153, t193], []),
  (3, [t2, t34, t71, t102, t130, t153], []),
  (3, [t20, t53, t83, t102, t130, t153], [830593]),
  (3, [t46, t53, t58, t102, t130, t153], []),
  (3, [t53, t62, t71, t116, t130, t153], [580031, 220718, 543478, 342478]),
  (3, [t53, t88, t91, t146, t153, t180], [820733]),
  (3, [t11, t88, t102, t130, t153], [20160]),
  (3, [t50, t88, t116, t130, t153], []),
  (3, [t77, t88, t102, t130, t153], [24160])]

def fam9 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t53, t71, t102, t130, t159], [810625, 110553, 530609, 290329, 414577, 14712, 411577, 11712, 810545, 610280, 340010, 740160, 500753, 40737, 800251, 860090, 560475, 862090, 562475, 263730, 560603, 220123, 20491, 422123, 822491, 743155, 900635, 660283, 860507, 861331, 60667, 864331, 62667]),
  (2, [t46, t53, t88, t102, t130, t153], [670697, 470521, 910073, 74552, 71552, 70552, 324737, 920188, 724314, 321737, 922188, 721314, 320737, 923188, 720314, 220074, 920522, 222074, 922522, 223074, 923522]),
  (3, [t0, t53, t71, t102, t130, t153, t198], []),
  (3, [t16, t53, t56, t71, t102, t130, t180], []),
  (3, [t25, t53, t102, t126, t130, t153, t180], []),
  (3, [t42, t46, t53, t71, t102, t130, t153], [60193, 780282, 261218, 260218, 260106, 261090, 260090, 340074]),
  (3, [t53, t70, t71, t102, t130, t153, t180], [340337]),
  (3, [t53, t71, t102, t126, t130, t153, t196], []),
  (3, [t2, t46, t71, t102, t130, t153], []),
  (3, [t20, t53, t102, t130, t153, t182], [830593]),
  (3, [t46, t53, t59, t102, t130, t153], []),
  (3, [t53, t63, t71, t116, t130, t153], [580031, 580734, 703494, 102494]),
  (3, [t53, t88, t95, t130, t153, t180], [100749]),
  (3, [t16, t18, t46, t88, t102], []),
  (3, [t51, t88, t102, t130, t153], [224114, 221114]),
  (3, [t78, t88, t102, t130, t153], [24160])]

def fam10 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t88, t102, t130, t159], [410098, 574082, 571082, 970066, 740111, 640431, 142111, 242431, 343191, 440527, 820239, 20447, 21271, 220559, 24271, 222559]),
  (2, [t46, t71, t88, t102, t130, t153], [130713, 650297, 370089, 534568, 531568, 530568, 460729, 100458, 784753, 380508, 184410, 781753, 382508, 181410, 780753, 383508, 180410, 580330, 380538, 782330, 182538, 183330, 783538]),
  (3, [t1, t53, t71, t102, t130, t153, t180], [710305]),
  (3, [t16, t53, t62, t71, t102, t130, t180], []),
  (3, [t25, t53, t102, t130, t146, t153, t180], []),
  (3, [t42, t53, t71, t102, t130, t153, t186], []),
  (3, [t53, t70, t71, t102, t130, t153, t193], []),
  (3, [t53, t71, t102, t129, t130, t153, t180], []),
  (3, [t5, t32, t88, t102, t130, t153], [370641]),
  (3, [t20, t53, t102, t130, t153, t193], [334493, 230445]),
  (3, [t46, t53, t71, t91, t146, t153], [263398, 460222, 860206, 940733]),
  (3, [t53, t67, t102, t130, t153, t180], []),
  (3, [t53, t88, t102, t114, t130, t153], [820128, 324737]),
  (3, [t16, t18, t53, t71, t116], []),
  (3, [t53, t55, t71, t102, t139], []),
  (3, [t79, t88, t102, t130, t153], [24160])]

def fam11 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t5, t53, t71, t102, t130, t153, t180], [760194, 210645, 820226, 970182, 60258, 10614, 62258, 12614, 63258, 13614, 290578, 510338, 210530, 270386, 270546, 310450, 510562, 312450, 512562, 313450, 513562]),
  (2, [t46, t88, t102, t130, t153, t180], [210121, 374600, 371600, 370600, 370184, 624034, 220684, 24650, 621034, 222684, 21650, 620034, 223684, 20650, 740442, 40618, 20490, 220634, 22490, 222634, 23490, 223634]),
  (3, [t2, t5, t53, t71, t102, t130, t153], []),
  (3, [t16, t53, t66, t71, t102, t130, t180], []),
  (3, [t25, t53, t102, t130, t153, t180, t183], []),
  (3, [t42, t53, t71, t102, t130, t153, t193], []),
  (3, [t53, t71, t73, t102, t130, t153, t180], []),
  (3, [t53, t71, t102, t130, t143, t153, t180], []),
  (3, [t5, t46, t88, t102, t130, t153], []),
  (3, [t20, t59, t102, t130, t153, t180], []),
  (3, [t46, t53, t71, t102, t130, t155], [624350, 621350, 860144, 700765]),
  (3, [t53, t68, t71, t102, t130, t159], [380047, 420750]),
  (3, [t53, t88, t102, t116, t130, t153], [20701, 724495, 220673]),
  (3, [t16, t20, t46, t102, t130], []),
  (3, [t53, t71, t89, t179, t180], []),
  (3, [t79, t88, t116, t130, t153], [])]

def fam12 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t53, t71, t102, t130, t153, t180], [60051, 780019, 664003, 661003, 660274, 760642, 210661, 620674, 170198, 60706, 10630, 62706, 12630, 460576, 60754, 310722, 10327, 290531, 510099, 210403, 510115, 470179, 70419, 310259, 510435, 510371, 312259, 512435, 512371, 310355, 910672, 510515, 510387]),
  (2, [t50, t53, t71, t102, t130, t153], [814633, 210537, 930313, 814632, 811616, 810616, 260762, 864144, 460289, 460730, 61689, 662459, 661714, 60689, 663459, 660714, 140673, 900027, 440011, 360746]),
  (3, [t2, t53, t71, t102, t130, t153, t180], [680060, 260152]),
  (3, [t16, t53, t68, t71, t102, t130, t180], []),
  (3, [t25, t53, t102, t130, t153, t180, t187], []),
  (3, [t42, t53, t71, t102, t130, t153, t196], []),
  (3, [t53, t71, t74, t102, t130, t153, t180], []),
  (3, [t53, t71, t102, t130, t144, t153, t180], []),
  (3, [t5, t53, t71, t102, t130, t159], []),
  (3, [t20, t102, t119, t130, t153, t180], [734493, 30461]),
  (3, [t46, t53, t71, t102, t130, t156], [464414, 461366, 860144, 540014]),
  (3, [t53, t71, t77, t102, t130, t153], [820143, 864144, 141318, 940318]),
  (3, [t53, t88, t102, t127, t130, t153], [820128]),
  (3, [t16, t34, t88, t102, t130], [970066]),
  (3, [t53, t71, t91, t146, t159], []),
  (3, [t83, t88, t102, t130, t159], [])]

def fam13 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t25, t53, t71, t102, t130, t153, t180], [280627, 970677, 500659, 850646, 302659, 52646, 903659, 453646, 100691, 250343, 670723, 130068, 350755, 550036, 350148, 752036, 152148, 153036, 753148, 950052, 950212]),
  (2, [t53, t59, t102, t130, t153, t180], [340017, 430154]),
  (3, [t3, t5, t53, t71, t102, t130, t153], []),
  (3, [t16, t53, t71, t74, t102, t130, t180], []),
  (3, [t25, t53, t102, t130, t153, t180, t189], []),
  (3, [t42, t53, t71, t102, t130, t157, t180], []),
  (3, [t53, t71, t75, t102, t130, t153, t180], [350362]),
  (3, [t53, t71, t102, t130, t145, t153, t180], [660096]),
  (3, [t7, t53, t71, t102, t130, t198], []),
  (3, [t21, t46, t53, t102, t130, t153], []),
  (3, [t46, t53, t71, t102, t130, t157], [64430, 61382, 60689, 140030]),
  (3, [t53, t71, t78, t102, t130, t153], [660159, 864144, 181334, 380334]),
  (3, [t53, t88, t102, t128, t130, t153], [404639, 220673]),
  (3, [t16, t46, t88, t102, t139], []),
  (3, [t53, t71, t91, t149, t153], []),
  (3, [t85, t88, t102, t130, t159], [])]

def fam14 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t32, t53, t71, t102, t130, t153, t180], [80707, 964035, 961035, 960035, 960290, 340017, 100292, 490260, 790214, 860324, 310662, 862324, 312662, 863324, 313662, 860356, 710305, 310359, 860436, 590372, 290081, 50532, 590468, 110388, 810596, 112388, 812596, 113388, 813596, 510033, 110420, 810404, 810660, 810452, 812452, 813452]),
  (2, [t53, t71, t83, t102, t130, t153], [800465, 660080]),
  (3, [t3, t53, t71, t102, t130, t153, t180], []),
  (3, [t16, t53, t71, t88, t102, t130, t180], [830568]),
  (3, [t25, t53, t102, t130, t153, t180, t193], []),
  (3, [t42, t53, t71, t119, t130, t153, t180], []),
  (3, [t53, t71, t76, t102, t130, t153, t180], [980513, 980449]),
  (3, [t53, t71, t102, t130, t146, t153, t193], [460369]),
  (3, [t7, t88, t102, t130, t153, t180], []),
  (3, [t22, t25, t46, t102, t130, t153], []),
  (3, [t46, t53, t71, t102, t130, t166], [902478, 900462, 380334, 980046]),
  (3, [t53, t71, t85, t102, t130, t159], [780223, 500753]),
  (3, [t53, t88, t102, t130, t153, t182], [820128]),
  (3, [t16, t50, t88, t102, t130], [272082]),
  (3, [t53, t71, t92, t149, t153], []),
  (3, [t88, t91, t102, t130, t159], [])]

def fam15 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t39, t53, t71, t102, t130, t153, t180], [330756, 50372, 770723, 654067, 651067, 650067, 650306, 900005, 500678, 702005, 702678, 303005, 103678, 500037, 900375, 280085, 500053, 500069, 502069, 503069]),
  (2, [t53, t71, t91, t146, t153, t180], [440140, 963028, 660170, 463267, 660315]),
  (3, [t4, t5, t53, t71, t102, t130, t153], []),
  (3, [t16, t53, t71, t91, t102, t130, t180], []),
  (3, [t26, t53, t71, t102, t130, t153, t180], []),
  (3, [t42, t53, t82, t102, t130, t153, t180], []),
  (3, [t53, t71, t80, t102, t130, t153, t180], [600588, 820378, 440112, 620203]),
  (3, [t53, t71, t102, t130, t146, t153, t197], []),
  (3, [t9, t46, t53, t71, t102, t130], [830077, 912061, 910061, 990045]),
  (3, [t22, t46, t71, t102, t130, t153], [940128, 24509, 21509, 20509]),
  (3, [t46, t53, t71, t102, t139, t159], [180606, 260526, 340078]),
  (3, [t53, t71, t88, t102, t130, t159], [500637]),
  (3, [t53, t88, t102, t130, t153, t184], [820128]),
  (3, [t16, t52, t88, t102, t130], []),
  (3, [t53, t71, t102, t130, t154], []),
  (3, [t88, t91, t102, t139, t153], [])]

def fam16 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t42, t53, t71, t102, t130, t153, t180], [814740, 610388, 330739, 214099, 211083, 210083, 210322, 900005, 980449, 740262, 380245, 860101, 461385, 62710, 861213, 861101, 460385, 63710, 860213, 860133, 460321, 60391, 860165, 840261, 60277, 760229, 60149, 60181, 60197, 61197]),
  (2, [t53, t71, t102, t103, t130, t153], [464576]),
  (3, [t4, t53, t71, t102, t130, t153, t180], [660096]),
  (3, [t16, t53, t71, t96, t102, t130, t180], []),
  (3, [t27, t32, t53, t102, t130, t153, t180], [290081, 670393]),
  (3, [t42, t53, t88, t102, t130, t153, t180], [921348, 920348, 920268, 220074]),
  (3, [t53, t71, t82, t102, t130, t153, t180], []),
  (3, [t53, t71, t102, t130, t146, t153, t198], [860571]),
  (3, [t9, t53, t71, t102, t130, t153], []),
  (3, [t25, t32, t46, t102, t130, t153], [610593, 644525, 641525, 640525]),
  (3, [t46, t53, t81, t102, t130, t153], [300558, 301542, 300542, 940128]),
  (3, [t53, t71, t89, t102, t178, t180], [60095, 780686, 660190]),
  (3, [t53, t88, t102, t130, t153, t186], [220673]),
  (3, [t16, t53, t71, t102, t131], []),
  (3, [t53, t71, t102, t130, t160], []),
  (3, [t88, t92, t102, t139, t153], [])]

def fam17 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t46, t53, t71, t102, t130, t153, t180], [810724, 610420, 330004, 214131, 211131, 210131, 210338, 500037, 380481, 140326, 780549, 860133, 464401, 60007, 864533, 862133, 461401, 62007, 861533, 863133, 460401, 63007, 860533, 540177, 300581, 840565, 760485, 820341, 820501, 860405, 60517, 862405, 62517, 863405, 63517]),
  (2, [t53, t71, t102, t114, t130, t153], [610569, 330345, 214680, 14312, 211648, 210648, 540002, 300492, 840172, 660080, 864144, 864587, 460289, 62539, 63539]),
  (3, [t5, t16, t53, t71, t102, t130, t153], [210464]),
  (3, [t16, t53, t71, t98, t102, t130, t180], []),
  (3, [t27, t32, t71, t102, t130, t153, t180], []),
  (3, [t42, t71, t102, t119, t130, t153, t180], []),
  (3, [t53, t71, t83, t88, t102, t130, t153], [580161]),
  (3, [t53, t71, t102, t130, t150, t153, t180], [240732, 460523]),
  (3, [t9, t53, t71, t102, t130, t159], []),
  (3, [t25, t46, t53, t102, t130, t159], []),
  (3, [t46, t53, t82, t102, t130, t153], [940590, 941574, 940574, 940128]),
  (3, [t53, t71, t91, t102, t130, t159], [540239, 460206]),
  (3, [t53, t88, t102, t130, t153, t188], [340094]),
  (3, [t16, t53, t71, t102, t140], []),
  (3, [t53, t71, t102, t130, t161], []),
  (3, [t88, t98, t102, t130, t159], [])]

def fam18 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t62, t71, t102, t130, t153, t180], [690484, 454244, 410036, 294179, 291163, 290163, 290370, 900005, 980513, 460072, 280246, 920038, 140325, 740693, 941433, 542071, 421006, 941693, 740433, 343071, 220006, 340709, 340337, 940407, 820725, 140054, 300022, 140741, 140757, 141757]),
  (2, [t53, t71, t102, t116, t130, t153], [410585, 130361, 14696, 414264, 11664, 10664, 340018, 100508, 640188, 860106, 564603, 60193, 220139, 24619, 662299, 864651, 663299, 865651, 860555, 861555]),
  (3, [t5, t32, t53, t71, t102, t130, t153], [210097, 540168]),
  (3, [t16, t53, t71, t102, t104, t130, t180], []),
  (3, [t27, t53, t71, t102, t130, t153, t180], []),
  (3, [t43, t53, t71, t102, t130, t153, t180], [980449]),
  (3, [t53, t71, t83, t102, t130, t153, t180], [380481]),
  (3, [t53, t71, t102, t130, t151, t153, t180], []),
  (3, [t9, t53, t71, t102, t130, t180], []),
  (3, [t25, t46, t88, t102, t130, t153], []),
  (3, [t46, t53, t85, t102, t130, t159], [342606, 340606, 140657]),
  (3, [t53, t71, t91, t102, t139, t153], [540255, 460222]),
  (3, [t53, t88, t102, t130, t153, t190], [220673]),
  (3, [t16, t53, t71, t102, t141], []),
  (3, [t53, t71, t102, t130, t164], []),
  (3, [t88, t98, t116, t130, t153], [])]

def fam19 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t68, t71, t102, t130, t153, t180], [890500, 610052, 494195, 491195, 490195, 490386, 500037, 80310, 120118, 340341, 340709, 340119, 942709, 742119, 143709, 543119, 340102, 342102, 343102]),
  (2, [t53, t71, t102, t130, t153, t184], [160049, 160480, 390252, 660080]),
  (3, [t5, t39, t53, t71, t102, t130, t153], []),
  (3, [t16, t53, t71, t102, t119, t130, t180], [890041, 812744, 110648]),
  (3, [t29, t32, t71, t102, t130, t153, t180], []),
  (3, [t44, t53, t71, t102, t130, t153, t180], [464385, 461385]),
  (3, [t53, t71, t84, t102, t130, t153, t180], [220394, 440112, 180225]),
  (3, [t53, t71, t102, t130, t153, t179, t180], [980171, 660315, 661315, 664315, 860571]),
  (3, [t10, t53, t71, t102, t130, t153], []),
  (3, [t25, t50, t53, t102, t130, t153], [794609]),
  (3, [t46, t53, t88, t102, t130, t159], [522670, 520670]),
  (3, [t53, t71, t91, t153, t179, t180], [260190]),
  (3, [t53, t88, t102, t130, t153, t192], [20110]),
  (3, [t16, t53, t71, t116, t139], []),
  (3, [t53, t71, t102, t130, t171], []),
  (3, [t88, t102, t110, t130, t153], [24160, 21160])]

def fam20 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t71, t88, t102, t130, t153, t180], [430532, 150068, 870579, 34227, 31227, 30227, 30418, 200085, 880088, 882088, 883088, 580161, 180581, 880373, 80038, 880727, 282038, 682727, 683038, 283727, 480118, 480024, 980230, 880167, 382230, 482167, 183230, 683167, 180225, 780294, 400278, 80423, 880342, 882342, 883342]),
  (2, [t53, t71, t102, t130, t153, t186], [640268, 60193, 660096]),
  (3, [t5, t42, t53, t71, t102, t130, t153], []),
  (3, [t16, t53, t71, t102, t126, t130, t180], []),
  (3, [t29, t53, t71, t102, t130, t153, t180], []),
  (3, [t46, t53, t62, t71, t102, t130, t153], [900219, 340139, 341123, 340123, 780378, 420330, 741234, 540234]),
  (3, [t53, t71, t85, t102, t130, t153, t180], [180225]),
  (3, [t53, t71, t102, t130, t153, t180, t181], []),
  (3, [t11, t16, t53, t71, t102, t130], [912269, 910269, 990125]),
  (3, [t25, t53, t71, t102, t130, t159], [580509]),
  (3, [t46, t62, t88, t102, t130, t153], [60159, 500718, 501702, 500702, 901046, 700046]),
  (3, [t53, t71, t92, t102, t139, t153], [140271, 60238]),
  (3, [t53, t88, t102, t130, t153, t197], [724655, 721655, 420158]),
  (3, [t16, t53, t85, t102, t139], [990082]),
  (3, [t53, t71, t102, t130, t172], []),
  (3, [t88, t102, t111, t130, t153], [24160, 21160])]

def fam21 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t71, t91, t102, t130, t153, t180], [10548, 730084, 13563, 614259, 611259, 610243, 610434, 240679, 860101, 760694, 460389, 740693, 700055, 260358, 463183, 260374, 860353, 460439, 660390, 860241, 462438, 460438, 462454, 460406, 460454, 462406, 460422]),
  (2, [t53, t71, t102, t130, t153, t188], [280284, 180666, 660096]),
  (3, [t5, t46, t53, t71, t102, t130, t153], [260152, 714200, 711200, 710200, 790184]),
  (3, [t16, t53, t71, t102, t130, t146, t180], []),
  (3, [t31, t32, t71, t102, t130, t153, t180], []),
  (3, [t46, t53, t68, t71, t102, t130, t153], [180225, 544187, 541187, 540187, 580394, 620346]),
  (3, [t53, t71, t88, t102, t130, t153, t193], [84540, 980027]),
  (3, [t53, t71, t102, t130, t153, t180, t183], []),
  (3, [t11, t53, t71, t102, t130, t153], [664254, 661254, 860144, 740141]),
  (3, [t25, t53, t102, t114, t130, t153], [794609]),
  (3, [t46, t68, t88, t102, t130, t153], [704750, 701750, 700750]),
  (3, [t53, t71, t98, t102, t130, t159], [540287]),
  (3, [t53, t88, t102, t130, t157, t180], [20030]),
  (3, [t16, t53, t88, t102, t139], []),
  (3, [t53, t71, t102, t132, t159], []),
  (3, [t88, t102, t116, t130, t159], [])]

def fam22 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t71, t98, t102, t130, t153, t180], [10564, 730100, 14547, 614355, 611275, 610275, 610450, 240695, 860133, 760758, 460405, 340709, 100103, 260374, 462215, 261374, 463215, 460518, 460534, 461534]),
  (2, [t53, t71, t102, t130, t153, t192], [840316, 860698, 660096, 662096]),
  (3, [t5, t53, t54, t71, t102, t130, t153], []),
  (3, [t16, t53, t71, t102, t130, t152, t180], []),
  (3, [t31, t53, t71, t102, t130, t153, t180], []),
  (3, [t46, t53, t71, t85, t102, t130, t153], [904235, 901235, 900235, 980458, 700161]),
  (3, [t53, t71, t89, t102, t130, t153, t180], [860556, 580428, 463267, 462267, 460267]),
  (3, [t53, t71, t102, t130, t153, t180, t184], []),
  (3, [t12, t16, t88, t102, t130, t180], [670125]),
  (3, [t25, t53, t102, t116, t130, t153], []),
  (3, [t46, t71, t75, t102, t130, t153], []),
  (3, [t53, t71, t98, t116, t130, t153], [540303]),
  (3, [t53, t88, t102, t130, t159, t180], [20657]),
  (3, [t16, t71, t88, t102, t139], []),
  (3, [t53, t71, t102, t133, t159], []),
  (3, [t88, t102, t117, t130, t153], [224114])]

def fam23 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t71, t102, t119, t130, t153, t180], [710596, 430132, 314403, 114610, 311307, 310307, 310482, 640529, 400088, 940711, 460277, 160229, 160437, 460070, 880167, 164599, 165599, 564417, 164615, 160023, 462470, 160279, 463470, 161279, 860273, 460742, 360726, 160455, 160039, 161039]),
  (2, [t53, t71, t102, t130, t153, t197], [640332, 564012, 561012, 260091, 860571]),
  (3, [t5, t53, t62, t71, t102, t130, t153], []),
  (3, [t16, t53, t71, t102, t130, t153, t193], []),
  (3, [t32, t39, t71, t102, t130, t153, t180], []),
  (3, [t46, t53, t71, t88, t102, t130, t153], [84251, 81251, 80251, 700761]),
  (3, [t53, t71, t90, t102, t130, t153, t180], []),
  (3, [t53, t71, t102, t130, t153, t180, t185], []),
  (3, [t12, t88, t102, t130, t153, t180], [420141]),
  (3, [t25, t53, t102, t130, t165, t198], [790609]),
  (3, [t46, t71, t80, t102, t130, t153], [20031, 21766, 20766, 940128]),
  (3, [t53, t71, t102, t107, t130, t153], []),
  (3, [t53, t88, t102, t130, t165, t198], [320737]),
  (3, [t16, t88, t102, t114, t130], [272082]),
  (3, [t53, t71, t102, t134, t159], []),
  (3, [t88, t102, t118, t130, t153], [])]

def fam24 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t71, t102, t126, t130, t153, t180], [90612, 810148, 694419, 691323, 690323, 690498, 320727, 100293, 880167, 540453, 740054, 900022, 544631, 545631, 540135, 142486, 940295, 343486, 741295, 740087, 340471, 540151, 541151]),
  (2, [t53, t71, t102, t130, t157, t180], [640348, 860218]),
  (3, [t5, t53, t68, t71, t102, t130, t153], []),
  (3, [t16, t53, t71, t102, t130, t153, t198], [460576]),
  (3, [t32, t42, t71, t102, t130, t153, t180], []),
  (3, [t46, t53, t71, t91, t102, t130, t153], [60411, 662299, 660299, 660283, 740474, 660170]),
  (3, [t53, t71, t91, t102, t130, t153, t192], []),
  (3, [t53, t71, t102, t130, t153, t180, t186], []),
  (3, [t15, t16, t53, t88, t102, t130], [670125]),
  (3, [t27, t32, t46, t102, t130, t153], []),
  (3, [t46, t71, t84, t102, t130, t153], [424047, 421047, 420047, 940128]),
  (3, [t53, t71, t102, t110, t130, t153], [740319, 864144, 861144]),
  (3, [t53, t88, t102, t130, t166, t180], [860046]),
  (3, [t16, t88, t102, t116, t130], []),
  (3, [t53, t71, t102, t135, t178], []),
  (3, [t88, t102, t119, t130, t159], [])]

def fam25 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t71, t102, t130, t146, t153, t180], [610628, 330164, 214435, 211435, 813594, 210339, 210514, 840759, 764599, 761599, 660309, 160279, 60469, 224631, 21631, 700086, 940295, 260241, 862438, 860438, 863454, 60231, 865454, 62231, 863502, 60311, 860199, 460369, 60487, 860247, 60263]),
  (2, [t53, t71, t102, t130, t159, t180], [14728, 11728, 410296, 10200, 340034, 100524, 640364, 860113, 560683, 620187, 620699, 660347, 860715, 662347, 862715, 60587, 860731]),
  (3, [t5, t53, t71, t73, t102, t130, t153], []),
  (3, [t16, t53, t71, t102, t130, t165, t180], [890057, 110680]),
  (3, [t32, t46, t53, t71, t102, t130, t153], [710305, 140409, 14553, 11553, 10553, 90521]),
  (3, [t46, t53, t71, t98, t102, t130, t153], [860273, 660363, 661347, 660347, 740490]),
  (3, [t53, t71, t91, t102, t130, t153, t193], []),
  (3, [t53, t71, t102, t130, t153, t180, t188], []),
  (3, [t15, t53, t88, t102, t130, t153], [420141]),
  (3, [t27, t46, t53, t102, t130, t153], [940128, 24541, 21541, 20541]),
  (3, [t46, t71, t88, t102, t130, t159], [260621, 900223, 982079, 980079]),
  (3, [t53, t71, t102, t111, t130, t153], [140335, 864144, 63398, 861144]),
  (3, [t53, t88, t102, t130, t170, t180], [700062]),
  (3, [t16, t88, t102, t142, t196], [270082]),
  (3, [t53, t71, t102, t137, t159], []),
  (3, [t88, t102, t126, t130, t159], [])]

def fam26 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t71, t102, t130, t153, t180, t187], [710660, 430196, 314467, 311467, 310467, 310530, 110162, 940008, 160485, 260134, 80423, 160503, 460550, 160455, 162503, 462550, 162455, 163503, 463550, 163455]),
  (2, [t53, t71, t102, t130, t165, t198], [910601, 630377, 514744, 511744, 310216, 110104, 840050, 600540, 140380, 63043, 963746, 360012, 362012, 860144, 260731, 360603]),
  (3, [t5, t53, t71, t88, t102, t130, t153], []),
  (3, [t16, t53, t71, t102, t130, t169, t180], []),
  (3, [t32, t46, t71, t102, t130, t153, t180], []),
  (3, [t46, t53, t71, t102, t116, t130, t153], [580076, 460058, 661427, 660427, 740506]),
  (3, [t53, t71, t91, t102, t130, t153, t198], []),
  (3, [t53, t71, t102, t130, t153, t180, t191], []),
  (3, [t16, t18, t46, t53, t71, t102], [360173, 440157]),
  (3, [t28, t34, t53, t102, t130, t153], [590641]),
  (3, [t46, t76, t88, t102, t130, t153], [940175, 580127, 581111, 580111, 381062, 980062]),
  (3, [t53, t71, t102, t116, t130, t159], [540351]),
  (3, [t53, t102, t120, t130, t153, t180], [943686, 942686, 940686]),
  (3, [t20, t46, t102, t130, t159], []),
  (3, [t53, t71, t102, t138, t159], []),
  (3, [t88, t102, t129, t130, t159], [])]

def fam27 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t71, t102, t130, t153, t180, t189], [890676, 610212, 494483, 491483, 490483, 490546, 120024, 340501, 500597, 80423, 340519, 340566, 340471, 342519, 942566, 742471, 343519, 143566, 543471]),
  (2, [t53, t71, t102, t130, t166, t180], [480396, 700234]),
  (3, [t5, t53, t71, t91, t102, t130, t153], []),
  (3, [t16, t53, t71, t102, t130, t176, t180], []),
  (3, [t32, t53, t71, t102, t130, t153, t184], [240617, 510033]),
  (3, [t46, t53, t71, t102, t119, t130, t153], [364603, 361475, 360475, 440522]),
  (3, [t53, t71, t91, t102, t146, t153, t180], []),
  (3, [t53, t71, t102, t130, t153, t180, t192], []),
  (3, [t16, t18, t53, t88, t102, t180], [320157]),
  (3, [t28, t46, t53, t102, t130, t153], [940128, 744557, 741557, 740557]),
  (3, [t46, t83, t88, t102, t130, t153], [984207, 981207, 980207]),
  (3, [t53, t71, t102, t117, t130, t153], [540367, 64689]),
  (3, [t54, t88, t102, t130, t153, t180], [820128]),
  (3, [t20, t50, t102, t130, t153], [34098]),
  (3, [t53, t71, t102, t139, t163], []),
  (3, [t88, t102, t130, t146, t159], [])]

def fam28 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t53, t71, t102, t130, t153, t180, t193], [610692, 330228, 214515, 211499, 210499, 210562, 840056, 764615, 60517, 760503, 660613, 160455, 820102, 820519, 300150, 340471, 860518, 862534, 60567, 862582, 60487, 863534, 61567, 863582, 61487]),
  (2, [t53, t82, t102, t130, t153, t180], [440112, 740282]),
  (3, [t5, t53, t71, t98, t102, t130, t153], [410257]),
  (3, [t16, t53, t71, t102, t130, t180, t181], []),
  (3, [t32, t53, t71, t102, t130, t153, t193], [14601, 910537]),
  (3, [t46, t53, t71, t102, t126, t130, t153], [744619, 741491, 740491, 820538]),
  (3, [t53, t71, t91, t102, t153, t178, t180], [460267, 660315]),
  (3, [t53, t71, t102, t130, t153, t180, t194], []),
  (3, [t16, t20, t53, t102, t130, t180], [80189]),
  (3, [t30, t34, t53, t71, t130, t153], []),
  (3, [t46, t85, t88, t102, t130, t153], [64223, 61223, 60223]),
  (3, [t53, t71, t102, t118, t130, t153], [940383]),
  (3, [t59, t88, t102, t130, t153, t180], []),
  (3, [t20, t102, t114, t130, t153], [34098]),
  (3, [t53, t71, t102, t139, t166], []),
  (3, [t88, t102, t130, t149, t153], [])]

def fam29 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t0, t53, t71, t102, t130, t153], [663096, 413257, 890120, 810104]),
  (2, [t53, t83, t88, t102, t130, t153], [470137, 634760, 631760, 630760, 820128, 780442, 120145, 480604, 482604, 483604, 480220, 282220, 883220]),
  (3, [t5, t53, t71, t102, t103, t130, t153], []),
  (3, [t16, t53, t71, t102, t130, t180, t187], []),
  (3, [t32, t53, t88, t102, t130, t153, t180], [340017, 170252, 970521]),
  (3, [t46, t53, t71, t102, t130, t146, t153], [264651, 261651, 860555, 260507, 340570, 60170]),
  (3, [t53, t71, t93, t102, t130, t153, t180], [461385]),
  (3, [t53, t71, t102, t130, t153, t180, t195], []),
  (3, [t16, t25, t46, t53, t102, t130], []),
  (3, [t30, t46, t53, t71, t130, t153], [864144, 661589, 660589, 740573]),
  (3, [t46, t88, t91, t102, t130, t153], [220335, 822255, 820255, 820239, 820733]),
  (3, [t53, t71, t102, t119, t130, t159], [240399]),
  (3, [t71, t77, t80, t102, t130, t153], [820143, 20031, 301015, 100015]),
  (3, [t20, t102, t116, t130, t153], []),
  (3, [t53, t71, t102, t139, t167], []),
  (3, [t88, t102, t130, t158, t159], [])]

def fam30 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t2, t53, t71, t102, t130, t153], [710305]),
  (2, [t53, t85, t102, t130, t153, t180], [440112, 940129]),
  (3, [t5, t53, t71, t102, t119, t130, t153], []),
  (3, [t16, t53, t71, t102, t130, t180, t189], []),
  (3, [t32, t62, t71, t102, t130, t153, t180], []),
  (3, [t46, t53, t71, t102, t130, t153, t187], [364683, 361683, 360683, 440586]),
  (3, [t53, t71, t94, t102, t130, t153, t180], [941433]),
  (3, [t53, t71, t102, t130, t153, t180, t197], []),
  (3, [t16, t32, t46, t71, t102, t130], []),
  (3, [t32, t46, t71, t102, t130, t159], []),
  (3, [t46, t88, t98, t102, t130, t153], [20002, 820303, 821287, 820287]),
  (3, [t53, t71, t102, t126, t130, t159], [620415]),
  (3, [t71, t88, t102, t114, t130, t153], [784753]),
  (3, [t20, t102, t130, t165, t198], [30098]),
  (3, [t53, t71, t102, t139, t168], []),
  (3, [t88, t102, t130, t159, t165], [])]

def fam31 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t5, t16, t53, t71, t102, t130], [310032, 310016]),
  (2, [t53, t88, t102, t130, t153, t193], [910169, 74025, 71009, 70009, 674120, 324050, 920700, 624380, 922716, 923716, 220673, 620075, 520011, 800108, 920332, 921332]),
  (3, [t5, t53, t71, t102, t126, t130, t153], []),
  (3, [t16, t53, t71, t102, t130, t180, t193], []),
  (3, [t32, t68, t71, t102, t130, t153, t180], []),
  (3, [t46, t53, t71, t102, t130, t153, t189], [544699, 541699, 540699, 620602]),
  (3, [t53, t71, t97, t102, t130, t153, t180], []),
  (3, [t53, t71, t102, t130, t153, t187, t193], [460321]),
  (3, [t16, t34, t53, t71, t102, t130], [810545, 840205]),
  (3, [t32, t46, t85, t102, t130, t153], []),
  (3, [t46, t88, t102, t116, t130, t153], [620669, 821351, 820351]),
  (3, [t53, t71, t102, t130, t146, t159], [140447, 860206]),
  (3, [t71, t88, t102, t116, t130, t153], [380718]),
  (3, [t22, t71, t102, t130, t159], [740160]),
  (3, [t53, t71, t102, t140, t162], []),
  (3, [t88, t102, t130, t159, t174], [])]

def fam32 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t5, t25, t53, t102, t130, t153], [990048, 870016]),
  (2, [t71, t80, t102, t130, t153, t180], [600588, 780476]),
  (3, [t5, t53, t71, t102, t130, t146, t153], []),
  (3, [t16, t53, t71, t102, t130, t180, t198], []),
  (3, [t32, t71, t75, t102, t130, t153, t180], []),
  (3, [t46, t53, t71, t102, t130, t153, t193], [264731, 261715, 260715, 340634]),
  (3, [t53, t71, t98, t102, t130, t153, t193], []),
  (3, [t53, t71, t102, t130, t153, t189, t193], [340337]),
  (3, [t16, t46, t53, t71, t102, t139], [810174, 230333, 310317, 390221]),
  (3, [t32, t46, t88, t102, t130, t153], []),
  (3, [t46, t88, t102, t119, t130, t153], [524495, 521399, 520399]),
  (3, [t53, t71, t102, t130, t147, t153], []),
  (3, [t71, t88, t102, t130, t159, t180], [780750]),
  (3, [t25, t32, t102, t130, t159], [410098]),
  (3, [t53, t71, t116, t139, t159], []),
  (3, [t88, t102, t130, t159, t175], [])]

def fam33 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t5, t32, t71, t102, t130, t153], [910064, 510016]),
  (2, [t88, t102, t119, t130, t153, t180], [310201, 474057, 274232, 471041, 470041, 40572, 440588, 840604, 324748, 325748, 724050, 324764, 320700, 320732, 321732, 20002, 620652, 520636, 320716, 321716]),
  (3, [t5, t53, t71, t102, t130, t153, t187], [160480]),
  (3, [t16, t53, t88, t102, t130, t153, t180], [920376, 920408, 370057, 670584, 370025]),
  (3, [t32, t71, t88, t102, t130, t153, t180], []),
  (3, [t46, t53, t71, t102, t130, t159, t180], [580092, 662044, 660044, 740650]),
  (3, [t53, t71, t98, t102, t130, t153, t196], []),
  (3, [t53, t71, t102, t130, t153, t193, t194], []),
  (3, [t16, t46, t53, t85, t102, t130], [392333, 390333, 190561]),
  (3, [t32, t50, t71, t102, t130, t153], [714625]),
  (3, [t46, t88, t102, t126, t130, t153], [901415, 900415]),
  (3, [t53, t71, t102, t130, t148, t153], []),
  (3, [t71, t88, t102, t130, t165, t198], [780753]),
  (3, [t27, t53, t102, t130, t159], [740160]),
  (3, [t53, t81, t102, t130, t159], [740160]),
  (3, [t88, t102, t130, t159, t176], [])]

def fam34 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t5, t53, t88, t102, t130, t153], [520112, 920168]),
  (2, [t9, t53, t71, t102, t130], [860144, 262029, 260029, 590066, 350109, 890093]),
  (3, [t5, t53, t71, t102, t130, t153, t189], []),
  (3, [t17, t53, t71, t102, t130, t153, t180], [460576]),
  (3, [t32, t71, t91, t102, t130, t153, t180], []),
  (3, [t46, t53, t85, t102, t130, t153, t180], [744092, 741092, 740092, 540177]),
  (3, [t53, t71, t99, t102, t130, t153, t180], [460321]),
  (3, [t53, t71, t102, t130, t153, t193, t195], []),
  (3, [t16, t46, t53, t88, t102, t130], [572349, 570349]),
  (3, [t32, t53, t71, t102, t130, t159], [940541]),
  (3, [t46, t88, t102, t129, t130, t153], [284527, 281431, 280431, 182749, 583749]),
  (3, [t53, t71, t102, t130, t149, t153], [540463, 260222]),
  (3, [t71, t102, t109, t130, t153, t180], [863095, 862095, 860095]),
  (3, [t28, t53, t102, t130, t159], [740160]),
  (3, [t53, t81, t116, t130, t153], [744160]),
  (3, [t88, t102, t130, t159, t177], [])]

def fam35 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t15, t16, t53, t71, t102, t130], [260576, 510328, 890392]),
  (2, [t16, t46, t88, t102, t130], [20128, 620205, 860189, 22157, 20157, 670125, 170717, 272082, 870397, 672221, 270082, 872397, 670221]),
  (3, [t5, t53, t71, t102, t130, t153, t193], []),
  (3, [t19, t53, t71, t102, t130, t153, t180], []),
  (3, [t32, t71, t98, t102, t130, t153, t180], []),
  (3, [t46, t53, t88, t102, t130, t153, t180], [924364, 921364, 920364, 920586]),
  (3, [t53, t71, t100, t102, t130, t153, t180], [340337]),
  (3, [t53, t71, t102, t130, t153, t193, t196], [860353, 460369]),
  (3, [t16, t46, t71, t88, t102, t130], [32365, 30365]),
  (3, [t32, t71, t102, t114, t130, t153], [714625]),
  (3, [t46, t88, t102, t130, t146, t153], [424543, 421543, 20463, 420447, 220733]),
  (3, [t53, t71, t102, t130, t153, t200], []),
  (3, [t76, t88, t119, t130, t153, t180], []),
  (3, [t30, t46, t88, t130, t153], [24160]),
  (3, [t53, t82, t102, t130, t159], [740160]),
  (3, [t88, t102, t130, t159, t191], [])]

def fam36 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t15, t53, t71, t102, t130, t153], [413257, 10560, 260344, 663096, 640408]),
  (2, [t16, t53, t71, t102, t139], [661144, 662173, 61029, 990082, 750365, 290349]),
  (3, [t5, t53, t88, t102, t130, t153, t180], [370444, 670184]),
  (3, [t20, t53, t71, t102, t130, t153, t180], [590089]),
  (3, [t32, t71, t102, t106, t130, t153, t180], []),
  (3, [t46, t71, t88, t102, t130, t153, t180], [384524, 381524, 380524, 980346, 980602]),
  (3, [t53, t71, t101, t102, t130, t153, t180], [860353]),
  (3, [t53, t71, t102, t130, t153, t193, t197], []),
  (3, [t16, t46, t88, t102, t130, t153], [420141]),
  (3, [t32, t71, t102, t116, t130, t153], []),
  (3, [t46, t88, t102, t130, t153, t187], []),
  (3, [t53, t71, t102, t130, t158, t159], [740479]),
  (3, [t80, t88, t102, t130, t153, t180], [780143]),
  (3, [t30, t53, t71, t130, t159], []),
  (3, [t53, t82, t116, t130, t153], [744160]),
  (3, [t88, t102, t130, t159, t193], [])]

def fam37 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t18, t53, t71, t102, t180], [311032, 310032, 940440, 160424]),
  (2, [t20, t46, t102, t130, t153], [940128, 784189, 781189, 780189, 34098, 630477, 434429, 31098, 632477, 431429, 30098, 633477, 430429]),
  (3, [t6, t53, t71, t102, t130, t153, t180], []),
  (3, [t20, t53, t88, t102, t130, t153, t180], [130460, 50236, 50105, 650137]),
  (3, [t32, t71, t102, t119, t130, t153, t180], [414601, 710569]),
  (3, [t48, t53, t71, t102, t130, t153, t180], [380481, 660080, 260682]),
  (3, [t53, t71, t101, t102, t130, t153, t196], []),
  (3, [t53, t71, t102, t130, t165, t176, t180], [440748, 460385, 360012]),
  (3, [t16, t46, t88, t102, t130, t180], []),
  (3, [t32, t71, t102, t130, t165, t198], [710625]),
  (3, [t46, t88, t102, t130, t153, t189], []),
  (3, [t53, t71, t102, t130, t159, t165], [240495]),
  (3, [t83, t88, t102, t119, t130, t153], [84639, 780143]),
  (3, [t34, t88, t102, t130, t159], []),
  (3, [t53, t85, t102, t139, t159], [940130]),
  (3, [t88, t102, t130, t159, t198], [])]

def fam38 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t25, t53, t102, t130, t180], [990048, 870032, 840472]),
  (2, [t25, t53, t102, t130, t159], [220144, 740525]),
  (3, [t7, t53, t71, t102, t130, t153, t180], [90232, 10216]),
  (3, [t22, t25, t53, t102, t130, t153, t180], [750233]),
  (3, [t32, t71, t102, t126, t130, t153, t180], []),
  (3, [t50, t53, t71, t102, t130, t153, t180], [464401, 661747, 660747, 660080, 460321, 740059]),
  (3, [t53, t71, t102, t103, t130, t153, t180], []),
  (3, [t53, t71, t102, t130, t165, t180, t198], [440764, 460401]),
  (3, [t16, t50, t53, t71, t102, t130], [112577, 310285, 390237]),
  (3, [t32, t88, t102, t130, t153, t184], []),
  (3, [t46, t88, t102, t130, t153, t191], [884575, 881575, 880575]),
  (3, [t53, t71, t102, t130, t159, t169], []),
  (3, [t88, t102, t112, t130, t153, t180], [420319]),
  (3, [t38, t88, t102, t130, t159], []),
  (3, [t53, t87, t102, t130, t162], [340114]),
  (3, [t88, t102, t130, t162, t193], [])]

def fam39 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t32, t71, t102, t130, t180], [910064, 510032]),
  (2, [t32, t71, t102, t130, t159], [860144, 380525]),
  (3, [t12, t16, t53, t71, t102, t130, t180], [510328, 290360]),
  (3, [t22, t53, t71, t102, t130, t153, t180], [440112, 820249]),
  (3, [t32, t71, t102, t130, t146, t153, t180], []),
  (3, [t50, t53, t71, t102, t130, t153, t193], [60124, 264731, 461763, 460763, 540075, 460043]),
  (3, [t53, t71, t102, t104, t130, t153, t180], []),
  (3, [t53, t71, t102, t130, t169, t176, t180], [740433]),
  (3, [t16, t52, t53, t71, t102, t130], [312301, 310301, 390253]),
  (3, [t33, t53, t71, t102, t130, t153], []),
  (3, [t46, t88, t102, t130, t153, t193], [424607, 421591, 420591]),
  (3, [t53, t71, t102, t130, t159, t174], [260511]),
  (3, [t88, t102, t114, t119, t130, t153], [524495]),
  (3, [t39, t88, t102, t130, t159], []),
  (3, [t53, t87, t116, t130, t153], [744160]),
  (3, [t88, t102, t130, t165, t173], [20160])]

def fam40 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t46, t53, t71, t102, t130], [860080, 460504, 260488, 980472, 862424, 860424, 510328, 10122, 430536, 112577, 710664, 512520, 110577, 712664, 510520, 190561, 950568, 490552]),
  (2, [t34, t88, t102, t130, t153], [820128, 424205, 421205, 420205]),
  (3, [t12, t53, t71, t102, t130, t153, t180], [260344, 40376]),
  (3, [t23, t25, t53, t102, t130, t153, t180], []),
  (3, [t32, t71, t102, t130, t153, t180, t184], []),
  (3, [t53, t54, t71, t102, t130, t153, t180], [390444, 660080]),
  (3, [t53, t71, t102, t105, t130, t153, t180], []),
  (3, [t53, t76, t88, t102, t130, t153, t180], [440588, 80572, 380426, 881412, 480412, 680300]),
  (3, [t16, t53, t71, t102, t114, t130], [790381, 112577]),
  (3, [t34, t46, t88, t102, t130, t153], [620573, 622573, 623573, 74605, 71605, 70605]),
  (3, [t46, t88, t102, t130, t159, t180], []),
  (3, [t53, t71, t102, t130, t159, t176], [140543]),
  (3, [t88, t102, t114, t130, t153, t180], [624034]),
  (3, [t41, t88, t102, t130, t159], []),
  (3, [t53, t88, t102, t130, t162], []),
  (3, [t88, t102, t130, t165, t199], [220114])]

def fam41 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t53, t71, t102, t130, t193], [860096, 490009, 412744, 310616]),
  (2, [t46, t88, t102, t130, t159], [570605, 810429, 974221, 971221, 370045, 620653, 222130, 820351, 622078, 622653, 220130, 822351, 620078]),
  (3, [t13, t16, t53, t71, t102, t130, t180], []),
  (3, [t23, t53, t71, t102, t130, t153, t180], []),
  (3, [t32, t71, t102, t130, t153, t180, t187], []),
  (3, [t53, t56, t71, t102, t130, t153, t180], []),
  (3, [t53, t71, t102, t106, t130, t153, t180], []),
  (3, [t53, t83, t88, t102, t130, t153, t180], [420177, 780442]),
  (3, [t16, t53, t71, t102, t116, t130], [590397]),
  (3, [t34, t53, t71, t102, t130, t159], [180557, 260589, 262589, 790605]),
  (3, [t47, t53, t71, t102, t130, t153], [864144, 221270, 820270, 500094]),
  (3, [t53, t71, t102, t130, t159, t177], [740559, 461238]),
  (3, [t88, t102, t115, t130, t153, t180], [20002]),
  (3, [t41, t88, t116, t130, t153], []),
  (3, [t53, t88, t102, t139, t159], [])]

def fam42 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t53, t71, t102, t130, t198], [863096, 710560, 490025, 310632]),
  (2, [t50, t88, t102, t130, t153], [810445, 974253, 971237, 970237, 24160, 620018, 620142, 221114, 822383, 821126, 220114, 823383, 820126]),
  (3, [t13, t53, t71, t102, t130, t153, t180], []),
  (3, [t24, t25, t53, t102, t130, t153, t180], []),
  (3, [t32, t71, t102, t130, t153, t180, t189], []),
  (3, [t53, t59, t71, t102, t130, t153, t180], [670460, 540107]),
  (3, [t53, t71, t102, t108, t130, t153, t180], []),
  (3, [t53, t88, t91, t102, t130, t153, t180], [920620, 620474, 320316, 320140]),
  (3, [t16, t53, t71, t102, t130, t158], []),
  (3, [t34, t53, t85, t102, t130, t153], [590641]),
  (3, [t48, t88, t102, t130, t153, t180], [820128]),
  (3, [t53, t71, t102, t130, t159, t187], []),
  (3, [t88, t102, t116, t130, t153, t180], [820303, 24607, 20002]),
  (3, [t42, t88, t102, t130, t159], [220114]),
  (3, [t53, t102, t120, t178, t180], [])]

def fam43 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t53, t88, t102, t130, t180], [520112, 360456, 522440, 520440, 170360, 170392, 370041, 372041, 70561, 670600, 370552, 890760, 370009, 372009]),
  (2, [t53, t71, t102, t130, t162], [14301, 11285, 612013, 340114, 100063, 640654]),
  (3, [t14, t16, t53, t71, t102, t130, t180], []),
  (3, [t24, t53, t71, t102, t130, t153, t180], []),
  (3, [t32, t71, t102, t130, t153, t180, t193], []),
  (3, [t53, t60, t71, t102, t130, t153, t180], []),
  (3, [t53, t71, t102, t112, t130, t153, t180], [40620, 963028, 260395]),
  (3, [t53, t88, t98, t102, t130, t153, t180], [920668, 620490]),
  (3, [t16, t53, t71, t102, t130, t159], []),
  (3, [t34, t53, t88, t102, t130, t153], []),
  (3, [t49, t53, t71, t102, t130, t153], [864144, 861144, 460286, 540110]),
  (3, [t53, t71, t102, t130, t159, t189], []),
  (3, [t88, t102, t119, t130, t153, t193], [620018]),
  (3, [t42, t88, t116, t130, t153], []),
  (3, [t62, t88, t102, t130, t159], [])]

def fam44 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t20, t53, t102, t130, t153, t180], [440112, 284456, 281456, 280456, 210209, 140185, 60153, 130201, 132201, 133201, 830593, 430121, 130073, 130169, 132169, 133169]),
  (2, [t53, t71, t102, t139, t159], [614317, 11061, 10061, 940130, 700079, 240670]),
  (3, [t14, t53, t71, t102, t130, t153, t180], []),
  (3, [t25, t32, t53, t102, t130, t153, t180], [110704, 440265]),
  (3, [t34, t46, t53, t71, t102, t130, t153], [260152, 380441, 460473, 462473, 463473, 830681, 914665, 911665, 910665, 990649]),
  (3, [t53, t61, t71, t102, t130, t153, t180], []),
  (3, [t53, t71, t102, t113, t130, t153, t180], []),
  (3, [t53, t88, t102, t119, t130, t153, t180], [320522, 24380, 320172]),
  (3, [t16, t53, t71, t102, t139, t153], []),
  (3, [t34, t71, t88, t102, t130, t153], []),
  (3, [t50, t53, t71, t102, t130, t162], [460622, 662446, 860510, 940126]),
  (3, [t53, t71, t102, t130, t159, t193], [140591]),
  (3, [t88, t102, t119, t130, t153, t196], [524655, 20367]),
  (3, [t46, t55, t88, t102, t130], []),
  (3, [t62, t88, t116, t130, t153], [])]

def fam45 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t25, t32, t102, t130, t153, t180], [470064, 190048]),
  (2, [t53, t85, t102, t130, t159], [694333, 691333, 90077, 740160, 780223, 40737]),
  (3, [t15, t16, t53, t71, t102, t130, t153], [910672]),
  (3, [t25, t39, t53, t102, t130, t153, t180], [210209]),
  (3, [t34, t53, t71, t102, t130, t153, t180], []),
  (3, [t53, t62, t71, t102, t130, t153, t188], []),
  (3, [t53, t71, t102, t114, t119, t130, t153], [40636, 364603]),
  (3, [t53, t88, t102, t126, t130, t153, t180], [700538, 980449]),
  (3, [t16, t53, t71, t102, t139, t180], []),
  (3, [t38, t46, t88, t102, t130, t153], [144765, 741765, 940765, 144621, 141621, 140621]),
  (3, [t50, t53, t71, t116, t130, t153], [860638, 263446, 262446, 340142]),
  (3, [t53, t71, t102, t130, t159, t198], [140607]),
  (3, [t88, t102, t130, t150, t153, t180], []),
  (3, [t46, t88, t91, t146, t153], []),
  (3, [t63, t88, t116, t130, t153], [])]

def fam46 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t25, t46, t53, t102, t130, t153], [420080, 940265, 544472, 541472, 540472, 770138, 710233, 10154, 794609, 390361, 194281, 791609, 392361, 191281, 790609, 393361, 190281]),
  (2, [t53, t88, t102, t130, t159], [874349, 871349, 270093, 20685, 720399, 22685, 722399, 423142, 720495]),
  (3, [t15, t16, t53, t71, t102, t130, t180], []),
  (3, [t25, t42, t53, t102, t130, t153, t180], []),
  (3, [t35, t53, t71, t102, t130, t153, t180], []),
  (3, [t53, t62, t71, t102, t130, t153, t193], []),
  (3, [t53, t71, t102, t114, t130, t153, t180], [140652, 464401]),
  (3, [t53, t88, t102, t129, t130, t153, t180], [80554, 682156, 83156, 880204]),
  (3, [t16, t53, t71, t102, t142, t196], [90413, 110577]),
  (3, [t38, t53, t71, t102, t130, t159], [782350, 380350, 860621]),
  (3, [t50, t53, t71, t119, t130, t153], []),
  (3, [t53, t71, t102, t130, t162, t180], []),
  (3, [t88, t102, t130, t165, t176, t180], [520655]),
  (3, [t46, t88, t95, t130, t153], []),
  (3, [t68, t88, t102, t130, t159], [])]

def fam47 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t25, t53, t102, t130, t153, t193], [420096, 94377, 990313]),
  (2, [t71, t88, t102, t130, t159], [334365, 331365, 730109, 380702, 180415, 582702, 982415, 903734, 60511]),
  (3, [t15, t53, t71, t102, t130, t153, t180], []),
  (3, [t25, t46, t53, t71, t102, t130, t153], [780249, 554329, 551329, 550329, 630297]),
  (3, [t36, t53, t71, t102, t130, t153, t180], [340017]),
  (3, [t53, t62, t71, t102, t130, t153, t196], []),
  (3, [t53, t71, t102, t115, t130, t153, t180], [40668, 860273]),
  (3, [t53, t88, t102, t130, t146, t153, t180], [924748, 921748, 320732, 220570, 720140, 920332]),
  (3, [t16, t53, t83, t88, t102, t130], [70561]),
  (3, [t39, t46, t88, t102, t130, t153], [864637, 861637, 860637]),
  (3, [t50, t53, t87, t102, t130, t153], [780638, 981622, 980622, 140673]),
  (3, [t53, t71, t102, t130, t162, t193], [740623]),
  (3, [t88, t102, t130, t165, t180, t198], [620034]),
  (3, [t46, t88, t102, t130, t155], [20160]),
  (3, [t71, t80, t102, t130, t159], [740160])]

def chunk0 : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14, fam15, fam16, fam17, fam18, fam19]

def chunk1 : List (List (ℕ × List ℕ × List ℕ)) := [fam20, fam21, fam22, fam23, fam24, fam25, fam26, fam27, fam28, fam29, fam30, fam31, fam32, fam33, fam34, fam35, fam36, fam37, fam38, fam39]

def chunk2 : List (List (ℕ × List ℕ × List ℕ)) := [fam40, fam41, fam42, fam43, fam44, fam45, fam46, fam47]

def parts : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14, fam15, fam16, fam17, fam18, fam19,
  fam20, fam21, fam22, fam23, fam24, fam25, fam26, fam27, fam28, fam29, fam30, fam31, fam32, fam33, fam34, fam35, fam36, fam37, fam38, fam39,
  fam40, fam41, fam42, fam43, fam44, fam45, fam46, fam47]

set_option maxRecDepth 8000 in
theorem parts_eq : parts = chunk0 ++ chunk1 ++ chunk2 := rfl

set_option synthInstance.maxSize 4000 in
def okB (e : ℕ × List ℕ × List ℕ) : Bool := decide (OkEntry tab zs 4 parts perms e)

set_option synthInstance.maxSize 4000 in
theorem okB_ok (e : ℕ × List ℕ × List ℕ) (h : okB e = true) : OkEntry tab zs 4 parts perms e := by
  unfold okB at h
  exact of_decide_eq_true h

theorem ok0 : fam0.all okB = true := by decide +kernel

theorem ok1 : fam1.all okB = true := by decide +kernel

theorem ok2 : fam2.all okB = true := by decide +kernel

theorem ok3 : fam3.all okB = true := by decide +kernel

theorem ok4 : fam4.all okB = true := by decide +kernel

theorem ok5 : fam5.all okB = true := by decide +kernel

theorem ok6 : fam6.all okB = true := by decide +kernel

theorem ok7 : fam7.all okB = true := by decide +kernel

theorem ok8 : fam8.all okB = true := by decide +kernel

theorem ok9 : fam9.all okB = true := by decide +kernel

theorem ok10 : fam10.all okB = true := by decide +kernel

theorem ok11 : fam11.all okB = true := by decide +kernel

theorem ok12 : fam12.all okB = true := by decide +kernel

theorem ok13 : fam13.all okB = true := by decide +kernel

theorem ok14 : fam14.all okB = true := by decide +kernel

theorem ok15 : fam15.all okB = true := by decide +kernel

theorem ok16 : fam16.all okB = true := by decide +kernel

theorem ok17 : fam17.all okB = true := by decide +kernel

theorem ok18 : fam18.all okB = true := by decide +kernel

theorem ok19 : fam19.all okB = true := by decide +kernel

theorem ok20 : fam20.all okB = true := by decide +kernel

theorem ok21 : fam21.all okB = true := by decide +kernel

theorem ok22 : fam22.all okB = true := by decide +kernel

theorem ok23 : fam23.all okB = true := by decide +kernel

theorem ok24 : fam24.all okB = true := by decide +kernel

theorem ok25 : fam25.all okB = true := by decide +kernel

theorem ok26 : fam26.all okB = true := by decide +kernel

theorem ok27 : fam27.all okB = true := by decide +kernel

theorem ok28 : fam28.all okB = true := by decide +kernel

theorem ok29 : fam29.all okB = true := by decide +kernel

theorem ok30 : fam30.all okB = true := by decide +kernel

theorem ok31 : fam31.all okB = true := by decide +kernel

theorem ok32 : fam32.all okB = true := by decide +kernel

theorem ok33 : fam33.all okB = true := by decide +kernel

theorem ok34 : fam34.all okB = true := by decide +kernel

theorem ok35 : fam35.all okB = true := by decide +kernel

theorem ok36 : fam36.all okB = true := by decide +kernel

theorem ok37 : fam37.all okB = true := by decide +kernel

theorem ok38 : fam38.all okB = true := by decide +kernel

theorem ok39 : fam39.all okB = true := by decide +kernel

theorem ok40 : fam40.all okB = true := by decide +kernel

theorem ok41 : fam41.all okB = true := by decide +kernel

theorem ok42 : fam42.all okB = true := by decide +kernel

theorem ok43 : fam43.all okB = true := by decide +kernel

theorem ok44 : fam44.all okB = true := by decide +kernel

theorem ok45 : fam45.all okB = true := by decide +kernel

theorem ok46 : fam46.all okB = true := by decide +kernel

theorem ok47 : fam47.all okB = true := by decide +kernel

theorem okc0 : ∀ part ∈ chunk0, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  simp only [chunk0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok0 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok1 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok2 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok3 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok4 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok5 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok6 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok7 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok8 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok9 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok10 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok11 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok12 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok13 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok14 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok15 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok16 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok17 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok18 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok19 e he)

theorem okc1 : ∀ part ∈ chunk1, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  simp only [chunk1, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok20 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok21 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok22 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok23 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok24 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok25 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok26 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok27 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok28 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok29 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok30 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok31 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok32 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok33 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok34 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok35 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok36 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok37 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok38 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok39 e he)

theorem okc2 : ∀ part ∈ chunk2, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  simp only [chunk2, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok40 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok41 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok42 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok43 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok44 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok45 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok46 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok47 e he)

set_option maxRecDepth 8000 in
theorem ok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  rw [parts_eq] at hp
  simp only [List.mem_append] at hp
  rcases hp with (h | h) | h
  · exact okc0 part h
  · exact okc1 part h
  · exact okc2 part h

theorem perms_ok : ∀ π ∈ perms, PermOk tab π := by decide +kernel

theorem tab_lt : tab < 2 ^ 64 := by decide +kernel

theorem tab_one : ∃ p : Fin 64, tab.testBit p = true := by decide +kernel

theorem tab_zero : ∃ q : Fin 64, tab.testBit q = false := by decide +kernel

theorem zs_ok : ∀ q ∈ zs, q < 64 ∧ tab.testBit q = false := by decide +kernel

theorem pool_eq : pool0 = base ++ [0, ALL] := by decide +kernel

theorem nec : ∀ a ∈ base, ¬ GoodL tab zs (base.filter (fun x => decide (x ≠ a))) := by
  decide +kernel

theorem base_mem : ∃ e ∈ parts.flatten, e.1 = 0 ∧ e.2.1 = base :=
  ⟨(0, base, [210064, 510224, 930048, 690208, 814032, 414192, 811032, 411192, 810032, 410192, 810016, 410176, 740240, 440112, 200320, 260256, 960368, 262256, 962368, 263256, 963368, 660080, 260272, 960416, 620288, 420384, 822288, 222384, 223288, 823384, 20304, 20432, 60336, 260400, 61336, 261400, 60352, 660096, 260448, 64336, 264400, 62352, 662096, 262448, 63352, 663096, 263448]), by decide +kernel, rfl, rfl⟩

theorem base_len : base.length = 6 := by decide +kernel

theorem base_nd : base.Nodup := by decide +kernel

theorem tab_eq : ∀ p : Fin 64, (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4277071584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (fun i : Fin 6 => p.val.testBit i.val) =
    tab.testBit p.val := by
  decide +kernel

def upper : Circuit :=
  ⟨[⟨GateOp.and, [0, 5]⟩,
   ⟨GateOp.and, [3, 4]⟩,
   ⟨GateOp.and, [2, 7]⟩,
   ⟨GateOp.or, [6, 8]⟩,
   ⟨GateOp.or, [0, 1]⟩,
   ⟨GateOp.or, [2, 3]⟩,
   ⟨GateOp.or, [4, 11]⟩,
   ⟨GateOp.and, [10, 12]⟩,
   ⟨GateOp.or, [9, 13]⟩], 14⟩

theorem upper_mono : Monotone2 upper := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_size : upper.size = 9 := rfl

theorem upper_eval : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) =
    Nat.testBit (4277071594 * 2 ^ 32 + 4277071584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_16829

theorem PEqualNP.Outside.L_meta_16829 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4277071584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4277071584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro t ⟨C, hC, hs, hev⟩
  have h := PEqualNP.Outside.L_meta_16829.lower PEqualNP.Outside.L_meta_16829.tab 6 4 PEqualNP.Outside.L_meta_16829.parts PEqualNP.Outside.L_meta_16829.perms PEqualNP.Outside.L_meta_16829.zs PEqualNP.Outside.L_meta_16829.base PEqualNP.Outside.L_meta_16829.tab_lt
    PEqualNP.Outside.L_meta_16829.tab_one PEqualNP.Outside.L_meta_16829.tab_zero PEqualNP.Outside.L_meta_16829.zs_ok PEqualNP.Outside.L_meta_16829.perms_ok PEqualNP.Outside.L_meta_16829.ok PEqualNP.Outside.L_meta_16829.pool_eq
    PEqualNP.Outside.L_meta_16829.nec PEqualNP.Outside.L_meta_16829.base_mem PEqualNP.Outside.L_meta_16829.base_len PEqualNP.Outside.L_meta_16829.base_nd
    C hC (fun p => (hev _).trans (PEqualNP.Outside.L_meta_16829.tab_eq p))
  have hs' : C.gates.length ≤ t := hs
  have hu : PEqualNP.Outside.L_meta_16829.upper.size = 9 := PEqualNP.Outside.L_meta_16829.upper_size
  exact ⟨PEqualNP.Outside.L_meta_16829.upper, PEqualNP.Outside.L_meta_16829.upper_mono, by omega, PEqualNP.Outside.L_meta_16829.upper_eval⟩
