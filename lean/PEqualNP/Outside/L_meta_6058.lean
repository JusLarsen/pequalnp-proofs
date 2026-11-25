import Mathlib
import PEqualNP.Defs
-- Rows are the 16 pairs of a left and a right vertex (row 4 u + v); a wire is the number whose
-- binary digit r is the value of the wire on row r (tab is the table itself, ALL the constant
-- true). The upper bound is the circuit in upper.
-- A set of tables is Good when every true row of tab is told from every false row on some
-- member (the member is true on the first and false on the second).
-- If a Good set holds the table c of a gate, replacing c by the two tables the gate reads
-- gives a Good set again. So every Good set G of non-constant tables that exist after j gates
-- has 8 ≤ |G| + j, and the family fam lists, with a level, every set that can occur with
-- |G| + j = 8 + level for a level below 1 (Jn; base_ok is the case j = 0). The family is closed
-- under one gate (Clos): the table of an AND or OR gate that takes the place of both, of one,
-- or of none of the two tables it reads keeps the level, raises it by one, or raises it by two.
-- The output of a circuit with j gates is a Good set of one table, so 8 + 1 ≤ 1 + j unless
-- fam holds a one-element set, and it holds none (OkEntry). The kernel checks the closure on
-- sorted lists (ok0, ok1, ...); the family itself was found by a search program and is only
-- checked here.
-- The shape of the link from circuits to tables (Inv, getD_snoc, gate_vec, inv_step, inv0)
-- and of the induction over the gate list in main follows L_meta_5471.lean (PR 11305,
-- willakone).

namespace PEqualNP.Outside.L_meta_6058
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev ALL : ℕ := 65535

theorem all_bit : ∀ p : Fin 16, ALL.testBit p = true := by decide +kernel

def nc (pool : List ℕ) : List ℕ := pool.filter (fun a => decide (a ≠ 0) && decide (a ≠ ALL))

theorem mem_nc (pool : List ℕ) (a : ℕ) : a ∈ nc pool ↔ a ∈ pool ∧ a ≠ 0 ∧ a ≠ ALL := by
  simp [nc, List.mem_filter]

def cand (pool : List ℕ) : List ℕ :=
  pool ++ (nc pool).flatMap (fun a => (nc pool).flatMap (fun b => [a &&& b, a ||| b]))

def Inv (pool : List ℕ) (ws : Fin 16 → List Bool) : Prop :=
  0 ∈ pool ∧ ALL ∈ pool ∧ ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 16, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem cand_and (pool : List ℕ) (h0 : 0 ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 16, c.testBit p = (ma.testBit p && mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma &&& mb, ?_, fun p => Nat.testBit_and ma mb p⟩
          refine List.mem_append_right _ ?_
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem cand_or (pool : List ℕ) (hA : ALL ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 16, c.testBit p = (ma.testBit p || mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma ||| mb, ?_, fun p => Nat.testBit_or ma mb p⟩
          refine List.mem_append_right _ ?_
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem gate_vec (pool : List ℕ) (ws : Fin 16 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ cand pool, ∀ p : Fin 16,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨h0, hA, hw⟩ := h
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by simp [GateOp.eval, all_bit p]⟩
    · exact ⟨0, List.mem_append_left _ h0, fun p => by simp [GateOp.eval]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    rcases hop with rfl | rfl
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    obtain ⟨mb, hmb, hb⟩ := hw b
    rcases hop with rfl | rfl
    · obtain ⟨c, hc, hcv⟩ := cand_and pool h0 ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_or pool hA ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
  | _ :: _ :: _ :: _, hl => simp at hl

theorem inv_step (pool pool' : List ℕ) (ws : Fin 16 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 16 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 16, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  obtain ⟨h0, hA, hw⟩ := hI
  refine ⟨hsub 0 h0, hsub ALL hA, fun i => ?_⟩
  obtain ⟨m, hm, hmb⟩ := hw i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

def pool0 : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952, 0, ALL]

def X (p : Fin 16) : List Bool :=
  oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4)

theorem X_len (p : Fin 16) : (X p).length = 8 := by simp [X, oneEach]

theorem inv0 : Inv pool0 X := by
  refine ⟨by decide, by decide, fun i => ?_⟩
  by_cases hi : i < 8
  · have key : ∀ j : Fin 8, ∀ p : Fin 16,
        (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide +kernel
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by decide, fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

abbrev Good (T : ℕ) (G : Finset ℕ) : Prop :=
  ∀ p q : Fin 16, T.testBit p = true → T.testBit q = false →
    ∃ w ∈ G, w.testBit p = true ∧ w.testBit q = false

theorem good_mono (T : ℕ) (G H : Finset ℕ) (h : G ⊆ H) (hG : Good T G) : Good T H := by
  intro p q hp hq
  obtain ⟨w, hw, h1⟩ := hG p q hp hq
  exact ⟨w, h hw, h1⟩

theorem good_split (T : ℕ) (G : Finset ℕ) (a b c : ℕ) (hG : Good T G)
    (hc : ∀ p q : Fin 16, c.testBit p = true → c.testBit q = false →
      (a.testBit p = true ∧ a.testBit q = false) ∨ (b.testBit p = true ∧ b.testBit q = false)) :
    Good T (insert a (insert b (G.erase c))) := by
  intro p q hp hq
  obtain ⟨w, hw, h1, h2⟩ := hG p q hp hq
  by_cases hwc : w = c
  · rw [hwc] at h1 h2
    rcases hc p q h1 h2 with h3 | h3
    · exact ⟨a, Finset.mem_insert_self _ _, h3⟩
    · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h3⟩
  · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hwc, hw⟩)), h1, h2⟩

def sel (q w : ℕ) : ℕ := if w.testBit q = true then ALL else ALL ^^^ w

abbrev GoodL (T : ℕ) (zs : List ℕ) (L : List ℕ) : Prop :=
  ∀ q ∈ zs, L.foldl (fun acc w => acc &&& sel q w) T = 0

theorem fold_bits (q i : ℕ) : ∀ (L : List ℕ) (acc : ℕ),
    (L.foldl (fun acc w => acc &&& sel q w) acc).testBit i = true →
    acc.testBit i = true ∧ ∀ w ∈ L, (sel q w).testBit i = true
  | [], acc, h => ⟨h, by simp⟩
  | w :: L, acc, h => by
    have h' : (L.foldl (fun acc w => acc &&& sel q w) (acc &&& sel q w)).testBit i = true := h
    obtain ⟨h1, h2⟩ := fold_bits q i L _ h'
    rw [Nat.testBit_and, Bool.and_eq_true] at h1
    refine ⟨h1.1, fun w' hw' => ?_⟩
    rcases List.mem_cons.mp hw' with e | e
    · rw [e]
      exact h1.2
    · exact h2 w' e

theorem goodL_of_good (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 16)
    (hzs : ∀ q ∈ zs, q < 16 ∧ T.testBit q = false) (L : List ℕ) (hg : Good T L.toFinset) :
    GoodL T zs L := by
  intro q hq
  obtain ⟨hq1, hq2⟩ := hzs q hq
  by_contra hne
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  obtain ⟨hTi, hall⟩ := fold_bits q i L T hi
  have hiR : i < 16 := by
    by_contra hge
    have hf : T.testBit i = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hf] at hTi
    exact absurd hTi (by simp)
  obtain ⟨w, hw, hs1, hs2⟩ := hg ⟨i, hiR⟩ ⟨q, hq1⟩ hTi hq2
  have hwi : (sel q w).testBit i = true := hall w (List.mem_toFinset.mp hw)
  have hAi : ALL.testBit i = true := all_bit ⟨i, hiR⟩
  have hs1' : w.testBit i = true := hs1
  have hs2' : w.testBit q = false := hs2
  unfold sel at hwi
  rw [if_neg (by rw [hs2']; simp), Nat.testBit_xor, hAi, hs1'] at hwi
  exact absurd hwi (by simp)

def InF (fam : List (ℕ × List ℕ)) (δ : ℕ) (S : Finset ℕ) : Prop :=
  ∃ e ∈ fam, e.1 ≤ δ ∧ e.2.toFinset = S

theorem inF_mono (fam : List (ℕ × List ℕ)) (δ δ' : ℕ) (h : δ ≤ δ') (S : Finset ℕ)
    (hS : InF fam δ S) : InF fam δ' S := by
  obtain ⟨e, he, h1, h2⟩ := hS
  exact ⟨e, he, le_trans h1 h, h2⟩

def Clos (T D : ℕ) (fam : List (ℕ × List ℕ)) : Prop :=
  ∀ δ : ℕ, ∀ S : Finset ℕ, InF fam δ S → ∀ a ∈ S, ∀ b ∈ S, ∀ c : ℕ,
    (a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) →
    c ∉ S → c ≠ 0 → c ≠ ALL →
    ∀ E : Finset ℕ, E ⊆ S → S ⊆ insert a (insert b E) → Good T (insert c E) →
    ∀ δ' : ℕ, δ' < D → δ' + S.card = δ + E.card + 2 → InF fam δ' (insert c E)

def Jn (T N D : ℕ) (fam : List (ℕ × List ℕ)) (pool : List ℕ) (j : ℕ) : Prop :=
  ∀ G : Finset ℕ, G ⊆ pool.toFinset → 0 ∉ G → ALL ∉ G → Good T G →
    N ≤ G.card + j ∧ ∀ δ : ℕ, δ < D → G.card + j = N + δ → InF fam δ G

theorem jn_weak (T N D : ℕ) (fam : List (ℕ × List ℕ)) (pool : List ℕ) (j : ℕ)
    (h : Jn T N D fam pool j) : Jn T N D fam pool (j + 1) := by
  intro G hG hG0 hGA hg
  obtain ⟨h1, h2⟩ := h G hG hG0 hGA hg
  exact ⟨by omega, fun δ hδ hcd =>
    inF_mono fam (δ - 1) δ (by omega) G (h2 (δ - 1) (by omega) (by omega))⟩

theorem jn_step (T N D : ℕ) (fam : List (ℕ × List ℕ)) (hcl : Clos T D fam)
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
        (a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∧
        ∀ p q : Fin 16, c.testBit p = true → c.testBit q = false →
          (a.testBit p = true ∧ a.testBit q = false) ∨
            (b.testBit p = true ∧ b.testBit q = false) := by
      simp only [cand, List.mem_append, List.mem_flatMap] at hc
      rcases hc with hc | ⟨a, ha, b, hb, hc⟩
      · exact absurd hc hcn
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
        refine ⟨a, b, ha1, hb1, ha2, ha3, hb2, hb3, ⟨hab, hc'⟩, fun p q hp hq => ?_⟩
        rcases hc' with e2 | e2
        · rw [e2, Nat.testBit_and, Bool.and_eq_true] at hp
          rw [e2, Nat.testBit_and, Bool.and_eq_false_iff] at hq
          rcases hq with hq | hq
          · exact Or.inl ⟨hp.1, hq⟩
          · exact Or.inr ⟨hp.2, hq⟩
        · rw [e2, Nat.testBit_or, Bool.or_eq_true] at hp
          rw [e2, Nat.testBit_or, Bool.or_eq_false_iff] at hq
          rcases hp with hp | hp
          · exact Or.inl ⟨hp, hq.1⟩
          · exact Or.inr ⟨hp, hq.2⟩
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

def opts (L : List ℕ) (a b : ℕ) : List (List ℕ) :=
  [L, L.filter (fun x => decide (x ≠ a)), L.filter (fun x => decide (x ≠ b)),
    L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))]

abbrev OkOne (T : ℕ) (zs : List ℕ) (D : ℕ) (fam : List (ℕ × List ℕ)) (i : ℕ) (L : List ℕ)
    (a b c : ℕ) : Prop :=
  c ∈ L ∨ c = 0 ∨ c = ALL ∨ ∀ E ∈ opts L a b,
    D + L.length ≤ i + E.length + 2 ∨ ¬ GoodL T zs (c :: E) ∨
      ∃ e ∈ fam, e.1 + L.length ≤ i + E.length + 2 ∧
        e.2 = E.orderedInsert (fun x y => x ≤ y) c

abbrev OkEntry (T : ℕ) (zs : List ℕ) (D : ℕ) (fam : List (ℕ × List ℕ)) (e : ℕ × List ℕ) :
    Prop :=
  e.2.Nodup ∧ e.2.length ≠ 1 ∧ ∀ a ∈ e.2, ∀ b ∈ e.2,
    a < b → ∀ c ∈ [a &&& b, a ||| b], OkOne T zs D fam e.1 e.2 a b c

theorem clos_of_ok (T D : ℕ) (zs : List ℕ) (fam : List (ℕ × List ℕ)) (hT : T < 2 ^ 16)
    (hzs : ∀ q ∈ zs, q < 16 ∧ T.testBit q = false)
    (hok : ∀ e ∈ fam, OkEntry T zs D fam e) : Clos T D fam := by
  intro δ S hS a ha b hb c hcand hcS hc0 hcA E hES hSE hg δ' hδ' hlev
  obtain ⟨e, he, hlv, heS⟩ := hS
  obtain ⟨hnd, _, hall⟩ := hok e he
  have haL : a ∈ e.2 := List.mem_toFinset.mp (by rw [heS]; exact ha)
  have hbL : b ∈ e.2 := List.mem_toFinset.mp (by rw [heS]; exact hb)
  have hcL : c ∉ e.2 := fun h => hcS (by rw [← heS]; exact List.mem_toFinset.mpr h)
  have hSc : S.card = e.2.length := by
    rw [← heS]
    exact List.toFinset_card_of_nodup hnd
  have hone : ∃ a' b' : ℕ, OkOne T zs D fam e.1 e.2 a' b' c ∧ S ⊆ insert a' (insert b' E) := by
    obtain ⟨hab, hc⟩ := hcand
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · refine ⟨a, b, hall a haL b hbL hlt c ?_, hSE⟩
      rcases hc with e2 | e2
      · exact List.mem_cons.mpr (Or.inl e2)
      · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr e2)
    · refine ⟨b, a, hall b hbL a haL hgt c ?_, ?_⟩
      · rcases hc with e2 | e2
        · exact List.mem_cons.mpr (Or.inl (e2.trans (Nat.and_comm a b)))
        · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr (e2.trans (Nat.or_comm a b)))
      · rw [Finset.insert_comm]
        exact hSE
  obtain ⟨a', b', hone, hSE'⟩ := hone
  rcases hone with h | h | h | h
  · exact absurd h hcL
  · exact absurd h hc0
  · exact absurd h hcA
  · have hopt : ∃ El ∈ opts e.2 a' b', El.toFinset = E ∧ El.Nodup := by
      have hsc := sub_cases S E a' b' hES hSE'
      rw [← heS] at hsc
      rcases hsc with h1 | h1 | h1 | h1
      · exact ⟨e.2, by simp [opts], h1.symm, hnd⟩
      · exact ⟨e.2.filter (fun x => decide (x ≠ a')), by simp [opts],
          by rw [filter_ne, h1], hnd.filter _⟩
      · exact ⟨e.2.filter (fun x => decide (x ≠ b')), by simp [opts],
          by rw [filter_ne, h1], hnd.filter _⟩
      · exact ⟨e.2.filter (fun x => decide (x ≠ a') && decide (x ≠ b')), by simp [opts],
          by rw [filter_ne2, h1], hnd.filter _⟩
    obtain ⟨El, hEl, hElE, hElnd⟩ := hopt
    have hElc : El.length = E.card := by
      rw [← hElE]
      exact (List.toFinset_card_of_nodup hElnd).symm
    have hcons : (c :: El).toFinset = insert c E := by rw [List.toFinset_cons, hElE]
    rcases h El hEl with h3 | h3 | ⟨e', he', hlv', heq⟩
    · omega
    · exact absurd (goodL_of_good T zs hT hzs (c :: El) (by rw [hcons]; exact hg)) h3
    · refine ⟨e', he', by omega, ?_⟩
      rw [heq, List.toFinset_eq_of_perm _ _ (List.perm_orderedInsert _ _ _), hcons]

theorem jn_base (T N D : ℕ) (fam : List (ℕ × List ℕ)) (zs : List ℕ) (hT : T < 2 ^ 16)
    (hzs : ∀ q ∈ zs, q < 16 ∧ T.testBit q = false) (ins : List ℕ)
    (hpool : ∀ x ∈ pool0, x ∈ ins ∨ x = 0 ∨ x = ALL) (hnd : ins.Nodup)
    (hbase : ∀ Gl ∈ ins.sublists, GoodL T zs Gl → N ≤ Gl.length ∧
      (Gl.length < N + D → ∃ e ∈ fam, e.1 + N ≤ Gl.length ∧ e.2 = Gl)) :
    Jn T N D fam pool0 0 := by
  intro G hG hG0 hGA hg
  have hGi : ∀ x ∈ G, x ∈ ins := by
    intro x hx
    rcases hpool x (List.mem_toFinset.mp (hG hx)) with h1 | h1 | h1
    · exact h1
    · exact absurd (by rw [← h1]; exact hx) hG0
    · exact absurd (by rw [← h1]; exact hx) hGA
  have hfin : (ins.filter (fun x => decide (x ∈ G))).toFinset = G := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hGi x h, h⟩⟩
  have hlen := List.toFinset_card_of_nodup (hnd.filter (fun x => decide (x ∈ G)))
  rw [hfin] at hlen
  obtain ⟨h1, h2⟩ := hbase _ (List.mem_sublists.mpr List.filter_sublist)
    (goodL_of_good T zs hT hzs _ (by rw [hfin]; exact hg))
  refine ⟨by omega, fun δ hδ hcd => ?_⟩
  obtain ⟨e, he, hle, heq⟩ := h2 (by omega)
  exact ⟨e, he, by omega, by rw [heq, hfin]⟩

theorem main (T N D : ℕ) (fam : List (ℕ × List ℕ)) (hcl : Clos T D fam)
    (hT1 : ∃ p : Fin 16, T.testBit p = true) (hT0 : ∃ q : Fin 16, T.testBit q = false) :
    ∀ (gs : List Gate) (pool : List ℕ) (ws : Fin 16 → List Bool) (L j o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    (∀ p, (ws p).length = L) → Inv pool ws → Jn T N D fam pool j →
    (∀ p : Fin 16, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = T.testBit p) →
    N ≤ 1 + (j + gs.length) ∧
      ∀ δ : ℕ, δ < D → 1 + (j + gs.length) = N + δ → ∃ m : ℕ, InF fam δ {m}
  | [], pool, ws, L, j, o, _, _, hI, hJ, hout => by
    obtain ⟨m, hm, hmb⟩ := hI.2.2 o
    have hmT : ∀ p : Fin 16, m.testBit p = T.testBit p := fun p => (hmb p).trans (hout p)
    have hg : Good T {m} := by
      intro p q hp hq
      exact ⟨m, Finset.mem_singleton_self m, (hmT p).trans hp, (hmT q).trans hq⟩
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
    have hout' : ∀ p : Fin 16, (gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)])).getD o false =
          T.testBit p :=
      fun p => by
        have h3 := hout p
        rw [List.foldl_cons] at h3
        exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
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

theorem lower (T N D : ℕ) (fam : List (ℕ × List ℕ)) (zs ins : List ℕ) (hT : T < 2 ^ 16)
    (hT1 : ∃ p : Fin 16, T.testBit p = true) (hT0 : ∃ q : Fin 16, T.testBit q = false)
    (hzs : ∀ q ∈ zs, q < 16 ∧ T.testBit q = false)
    (hok : ∀ e ∈ fam, OkEntry T zs D fam e)
    (hpool : ∀ x ∈ pool0, x ∈ ins ∨ x = 0 ∨ x = ALL) (hnd : ins.Nodup)
    (hbase : ∀ Gl ∈ ins.sublists, GoodL T zs Gl → N ≤ Gl.length ∧
      (Gl.length < N + D → ∃ e ∈ fam, e.1 + N ≤ Gl.length ∧ e.2 = Gl))
    (C : Circuit) (hC : Monotone2 C) (hev : ∀ p : Fin 16, C.eval (X p) = T.testBit p) :
    N + D ≤ C.gates.length + 1 := by
  obtain ⟨h1, h2⟩ := main T N D fam (clos_of_ok T D zs fam hT hzs hok) hT1 hT0 C.gates pool0 X
    8 0 C.output hC X_len inv0 (jn_base T N D fam zs hT hzs ins hpool hnd hbase) hev
  by_contra hlt
  obtain ⟨m, e, he, _, hem⟩ := h2 (1 + (0 + C.gates.length) - N) (by omega) (by omega)
  obtain ⟨hnd', hlen, _⟩ := hok e he
  apply hlen
  rw [← List.toFinset_card_of_nodup hnd', hem, Finset.card_singleton]

def tab : ℕ := 5071

def zs : List ℕ := [4, 5, 10, 11, 13, 14, 15]

def ins : List ℕ := [15, 240, 3840, 4369, 8738, 17476, 34952, 61440]

def fam0 : List (ℕ × List ℕ) := [
  (0, [15, 240, 3840, 4369, 8738, 17476, 34952, 61440]),
  (0, [15, 240, 3840, 4369, 8738, 17476, 63624]),
  (0, [15, 240, 3840, 4369, 8738, 34952, 62532]),
  (0, [15, 240, 3840, 4369, 8738, 52428, 61440]),
  (0, [15, 240, 3840, 4369, 17476, 34952, 61986]),
  (0, [15, 240, 4369, 8738, 17476, 36744, 61440]),
  (0, [15, 240, 4369, 8738, 20292, 34952, 61440]),
  (0, [15, 3840, 4369, 8946, 17476, 34952, 61440])]

def fam1 : List (ℕ × List ℕ) := [
  (0, [15, 3840, 4593, 8738, 17476, 34952, 61440]),
  (0, [15, 192, 3840, 4369, 8738, 61440]),
  (0, [15, 240, 3840, 4369, 8738, 64716]),
  (0, [15, 240, 3840, 4369, 52428, 61986]),
  (0, [15, 240, 4369, 8738, 20292, 63624]),
  (0, [15, 240, 4369, 8738, 36744, 62532]),
  (0, [15, 240, 4369, 8738, 53196, 61440]),
  (0, [15, 3840, 4369, 8946, 52428, 61440])]

def fam2 : List (ℕ × List ℕ) := [
  (0, [15, 3840, 4593, 8738, 17476, 63624]),
  (0, [15, 3840, 4593, 8738, 34952, 62532]),
  (0, [15, 3840, 4593, 8738, 52428, 61440]),
  (0, [15, 4369, 8946, 17476, 36744, 61440]),
  (0, [15, 4369, 8946, 20292, 34952, 61440]),
  (0, [15, 4593, 8738, 17476, 36744, 61440]),
  (0, [15, 4593, 8738, 20292, 34952, 61440]),
  (0, [15, 192, 3840, 4369, 61986])]

def fam3 : List (ℕ × List ℕ) := [
  (0, [15, 3840, 4593, 8738, 64716]),
  (0, [15, 4369, 8946, 53196, 61440]),
  (0, [15, 4593, 8738, 20292, 63624]),
  (0, [15, 4593, 8738, 36744, 62532]),
  (0, [15, 4593, 8738, 53196, 61440]),
  (0, [207, 3840, 4369, 8738, 61440]),
  (0, [207, 3840, 4369, 61986])]

def fam : List (ℕ × List ℕ) := fam0 ++ fam1 ++ fam2 ++ fam3

set_option synthInstance.maxSize 4000 in
theorem ok0 : ∀ e ∈ fam0, OkEntry tab zs 1 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok1 : ∀ e ∈ fam1, OkEntry tab zs 1 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok2 : ∀ e ∈ fam2, OkEntry tab zs 1 fam e := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem ok3 : ∀ e ∈ fam3, OkEntry tab zs 1 fam e := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem ok : ∀ e ∈ fam, OkEntry tab zs 1 fam e := by
  intro e he
  simp only [fam, List.mem_append] at he
  rcases he with ((h | h) | h) | h
  · exact ok0 e h
  · exact ok1 e h
  · exact ok2 e h
  · exact ok3 e h

theorem tab_lt : tab < 2 ^ 16 := by decide +kernel

theorem tab_one : ∃ p : Fin 16, tab.testBit p = true := by decide +kernel

theorem tab_zero : ∃ q : Fin 16, tab.testBit q = false := by decide +kernel

theorem zs_ok : ∀ q ∈ zs, q < 16 ∧ tab.testBit q = false := by decide +kernel

theorem pool_ok : ∀ x ∈ pool0, x ∈ ins ∨ x = 0 ∨ x = ALL := by decide +kernel

theorem ins_nd : ins.Nodup := by decide +kernel

set_option synthInstance.maxSize 4000 in
theorem base_ok : ∀ Gl ∈ ins.sublists, GoodL tab zs Gl → 8 ≤ Gl.length ∧
    (Gl.length < 8 + 1 → ∃ e ∈ fam, e.1 + 8 ≤ Gl.length ∧ e.2 = Gl) := by
  decide +kernel

theorem tab_eq : ∀ p : Fin 16, (5071 : ℕ).testBit (4 * (p.val / 4) + p.val % 4) = tab.testBit p.val := by
  decide +kernel

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (5071 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_6058

theorem PEqualNP.Outside.L_meta_6058 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5071 : ℕ).testBit (4 * u.val + v.val)) 8 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5071 : ℕ).testBit (4 * u.val + v.val)) 7 :=
  ⟨PEqualNP.Outside.L_meta_6058.upper, fun ⟨C, hC, hs, hrep⟩ => by
    have h := PEqualNP.Outside.L_meta_6058.lower PEqualNP.Outside.L_meta_6058.tab 8 1 PEqualNP.Outside.L_meta_6058.fam PEqualNP.Outside.L_meta_6058.zs PEqualNP.Outside.L_meta_6058.ins PEqualNP.Outside.L_meta_6058.tab_lt PEqualNP.Outside.L_meta_6058.tab_one
      PEqualNP.Outside.L_meta_6058.tab_zero PEqualNP.Outside.L_meta_6058.zs_ok PEqualNP.Outside.L_meta_6058.ok PEqualNP.Outside.L_meta_6058.pool_ok PEqualNP.Outside.L_meta_6058.ins_nd PEqualNP.Outside.L_meta_6058.base_ok
      C hC (fun p => (hrep ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩).trans (PEqualNP.Outside.L_meta_6058.tab_eq p))
    have hs' : C.gates.length ≤ 7 := hs
    omega⟩
