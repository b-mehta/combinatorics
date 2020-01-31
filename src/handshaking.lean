import data.finset
-- import data.fintype
import data.set.finite
import data.nat.parity
import algebra.big_operators
import to_mathlib
import tactic.fin_cases

-- open finset
-- open fintype
open nat

structure graph (α : Type*) :=
(edge : α → α → Prop)
(loopless : ∀ a, ¬ edge a a)
(undirected : ∀ {a₁ a₂}, edge a₁ a₂ → edge a₂ a₁)

variable {α : Type*}

-- def neighbours (G : graph α) (x₁ : α) : set α := {x₂ | G.edge x₁ x₂}

-- lemma fin_neighbours_eq_neighbours [fintype α] (x₁ : α) : 
--   ↑(fin_neighbours G x₁) = neighbours G x₁ := 
-- by ext; rw finset.mem_coe; apply mem_fin_neighbours

section fin_graph
  open finset fintype
  variables [fintype α] (G : graph α) [decidable_rel G.edge]
  local notation `V` := elems α

  lemma neq_of_edge {x₁ x₂ : α} : G.edge x₁ x₂ → x₁ ≠ x₂ := begin rintro q rfl, apply G.loopless _ q end

  def neighbours (x₁ : α) : finset α := filter (G.edge x₁) V
  lemma mem_neighbours (x₁ x₂ : α) :
    x₂ ∈ neighbours G x₁ ↔ G.edge x₁ x₂ :=
  by simp [neighbours, fintype.complete]

  def degree (x₁ : α) : ℕ := finset.card (neighbours G x₁)

  def ordered_edge_set : finset (α × α) := (univ.product univ).filter (λ t, G.edge t.1 t.2)
  lemma mem_ordered_edge_set (i j : α) : (i,j) ∈ ordered_edge_set G ↔ G.edge i j :=
  by simp [ordered_edge_set, mem_product]

  def edge_set [decidable_eq α] : finset (finset α) := univ.bind (λ t, finset.image (λ u, {t,u}) (neighbours G t))

  lemma mem_edge_set [decidable_eq α] (A : finset α) : A ∈ edge_set G ↔ ∃ x₁ x₂, G.edge x₁ x₂ ∧ A = {x₁, x₂} := 
  begin
    simp [edge_set, ext, mem_neighbours], split, 
      rintro ⟨i, j, edg, q⟩, refine ⟨i, j, edg, λ t, (q t).symm⟩, 
    rintro ⟨i, j, edg, q⟩, refine ⟨i, j, edg, λ t, (q t).symm⟩, 
  end

  def pair_to_finset {β : Type*} [decidable_eq β] : β × β → finset β := λ t, {t.1, t.2}
  lemma mem_pair_to_finset {β : Type*} [decidable_eq β] (x : β) (t : β × β) : x ∈ pair_to_finset t ↔ x = t.1 ∨ x = t.2 :=
  by simp [pair_to_finset]; rw or.comm
  lemma same_finset {β : Type*} [decidable_eq β] (x y i j : β) : 
    pair_to_finset (x,y) = pair_to_finset (i,j) ↔ (x,y) = (i,j) ∨ (x,y) = (j,i)
    := 
  begin
    split, intro, simp [ext, mem_pair_to_finset] at a, 
    rcases (a x).1 (or.inl rfl) with rfl | rfl;
    rcases (a y).1 (or.inr rfl) with rfl | rfl,
      rcases (a j).2 (or.inr rfl) with rfl | rfl, left, refl, left, refl,
      left, refl,
      right, refl, 
      rcases (a i).2 (or.inl rfl) with rfl | rfl, left, refl, left, refl,
    rintro (h | h); injection h with q₁ q₂; rw [q₁, q₂] at *, ext a, simp [mem_pair_to_finset], rw or.comm
  end
  lemma card_diff_pair_to_finset {β : Type*} [decidable_eq β] (x y : β) (h : x ≠ y) : card (pair_to_finset (x,y)) = 2 :=
  begin
    rw pair_to_finset, simp, rw card_insert_of_not_mem, rw card_singleton, rw mem_singleton, intro, apply h, exact a.symm
  end

  lemma degree_sum [decidable_eq α] : univ.sum (degree G) = 2 * card (edge_set G) := 
  begin
    have: ordered_edge_set G = univ.bind (λ t, finset.image (λ u, (t,u)) (neighbours G t)),
      simp [ext, mem_ordered_edge_set, mem_neighbours], 
      refine (λ i j, ⟨λ p, ⟨i, j, p, rfl, rfl⟩, λ ⟨k, l, q, rfl, rfl⟩, q⟩), 
    have: card (ordered_edge_set G) = univ.sum (degree G),
      rw this, rw card_bind, congr, funext t, rw degree, rw card_image_of_inj_on, simp, 
      intros, rw disjoint_left, simp [mem_neighbours], intros, cc,
    rw ← this, 
    have := card_eq_sum_card_image pair_to_finset (ordered_edge_set G),
    rw this,
    clear this this this, rw mul_comm, convert sum_const_nat _, 
      simp [ext, mem_edge_set, mem_ordered_edge_set, pair_to_finset], intro E, split, 
        rintro ⟨i, j, edg, z⟩, refine ⟨i, j, edg, λ a, (z a).symm⟩, 
      rintro ⟨i, j, edg, z⟩, refine ⟨i, j, edg, λ a, (z a).symm⟩, 
    simp [mem_ordered_edge_set], rintros E i j edg rfl, 
    set z : finset (α × α) := filter (λ (x : α × α), pair_to_finset x = pair_to_finset (i, j)) (ordered_edge_set G),
    suffices: z = pair_to_finset ((i,j), (j,i)),
      rw this, apply card_diff_pair_to_finset, simp, rintro rfl q, apply G.loopless i edg,
    ext ⟨a,b⟩, simp [mem_ordered_edge_set], rw mem_pair_to_finset, dsimp, rw same_finset, 
    split, exact and.right, rintro (t | t); simp at t; rw [t.1, t.2], refine ⟨edg, or.inl rfl⟩, refine ⟨G.undirected edg, or.inr rfl⟩,
  end

  lemma even_sum_evens [decidable_eq α] {f : α → ℕ} {s : finset α} : (∀ x ∈ s, even (f x)) → even (s.sum f) :=
  begin
    refine finset.induction_on s (by simp) _,
    intros i s₁ hi ih h, rw [sum_insert hi, even_add, iff_true_left], apply ih, intros x hx, apply h x (mem_insert_of_mem hx), 
    apply h i (mem_insert_self _ _), 
  end
  lemma even_sum_odds_iff [decidable_eq α] {f : α → ℕ} {s : finset α} : (∀ x ∈ s, ¬ even (f x)) → (even (sum s f) ↔ even (card s)) := 
  begin
    apply finset.induction_on s, simp, intros i s₁ hi ih h,
    rw [sum_insert hi, card_insert_of_not_mem hi, even_succ, ← not_iff_not, not_not, ← ih, even_add, not_iff], 
    apply iff_true_left (h _ (mem_insert_self _ _)), intros x hx, apply h x (mem_insert_of_mem hx), 
  end

  lemma big_sum_evens [decidable_eq α] (s : finset α) (f : α → ℕ) : even (s.sum f) ↔ even (card (s.filter (λ t, ¬ even (f t)))) := 
  begin
    set evens := s.filter (λ t, even (f t)),
    set odds := s.filter (λ t, ¬ even (f t)),
    have: evens ∪ odds = s := filter_union_filter_neg_eq _,
    have: s.sum f = evens.sum f + odds.sum f := this ▸ sum_union (disjoint_iff_inter_eq_empty.2 (filter_inter_filter_neg_eq s)),
    rw this, 
    have: even (evens.sum f) := even_sum_evens _, rw even_add, rw iff_true_left this, apply even_sum_odds_iff,
    intros x hx, rw mem_filter at hx, exact hx.2,
    intros x hx, rw mem_filter at hx, exact hx.2
  end

  lemma handshaking [decidable_eq α] : even (card (univ.filter (λ x, ¬ even (degree G x)))) := 
  by rw ← big_sum_evens; simp [even_iff, degree_sum]

end fin_graph

-- local attribute  [instance, priority 10] classical.prop_decidable

lemma pigeonhole {α : Type*} [decidable_eq α]
  (s : finset α) (f g : α → ℕ) (big : s.sum f < s.sum g) :
  ∃ (a ∈ s), f a < g a :=
begin
  by_contra, push_neg at a, apply not_le_of_lt big (finset.sum_le_sum a)
end
lemma strong_pigeonhole {α β : Type*} [decidable_eq α] [decidable_eq β] 
  (s : finset α) (f : α → ℕ) (g : α → finset β) (tot : s.sum f < finset.card (s.bind g)):
  ∃ a ∈ s, f a < finset.card (g a) :=
pigeonhole s f _ (lt_of_lt_of_le tot finset.card_bind_le)

lemma finite_pigeonhole_const {α β : Type*} [decidable_eq α] [decidable_eq β] 
  (s : finset α) (f : α → ℕ) (k : ℕ) (big : s.sum f < finset.card s * k) :
  ∃ a ∈ s, f a < k :=
begin
  apply pigeonhole s f, rwa [finset.sum_const, smul_eq_mul]
end
-- lemma finite_pigeonhole_const' {α β : Type*} [decidable_eq α] [decidable_eq β] 
--   (s : finset α) (f : α → ℕ) (k : ℕ) (big : card s * k < s.sum f) :
--   ∃ a ∈ s, k < f a :=
-- begin
--   apply finite_pigeonhole s _ f, rwa [sum_const, smul_eq_mul], 
-- end

section ramsey
  local notation `[`n`]` := fin n
  local attribute [instance, priority 10] classical.prop_decidable
  open finset fintype

  @[reducible] def rset (r : ℕ) (α : Type*) : Type* := {x : finset α // x.card = r}
  
  -- lemma eq_of_veq (r : ℕ) (α : Type*) (a b : rset r α) : a.1 = b.1 → a = b := subtype.eq
  local notation X`^(`r`)` := rset r X
  -- instance {r : ℕ} {α : Type*} [fintype α] : fintype (rset r α) := sorry

  def mk_edge {α : Type*} [decidable_eq α] (x y : α) (h : x ≠ y) : α^(2) :=
  ⟨{x,y}, begin simp, rw [card_insert_of_not_mem]; simp, intro, apply h, symmetry, exact a end⟩

  def adjacent_edges {α : Type*} [fintype α] [decidable_eq α] (x : α) : finset (α × (α^(2))) := 
  (univ.erase x).attach.image (λ y, ⟨y.1, mk_edge x y.1 (mem_erase.1 y.2).1.symm⟩)

  lemma card_adjacent_edges {α : Type*} [fintype α] [decidable_eq α] (x : α) : card (adjacent_edges x) = card α - 1 :=
  begin
    rw adjacent_edges, rw card_image_of_inj_on, 
    rw card_attach, rw card_erase_of_mem, refl, apply complete, intros t ht y hy _, simp at a, exact subtype.eq a.1
  end

  def colour_components {r k : ℕ} (x : [r]) (c : [r]^(2) → [k]) (i : [k]) : finset [r] := 
    ((univ.erase x).attach.filter (λ (x₂: {t // t ∈ erase univ x}), c (mk_edge x x₂.1 (mem_erase.1 x₂.2).1.symm) = i)).image (λ y, y.1)

  lemma mem_colour_components {r k : ℕ} (x : [r]) (c : [r]^(2) → [k]) (i : [k]) (y : [r]) : 
    y ∈ colour_components x c i ↔ ∃ (h : x ≠ y), c (mk_edge x y h) = i :=
  begin
    rw colour_components, simp, split, rintro ⟨_, _, _⟩, rw mem_erase at a_w, use a_w.1.symm, 
    rintro ⟨_, rfl⟩, refine ⟨_, _⟩, rw mem_erase, exact ⟨a_w.symm, complete _⟩, refl
  end

  lemma all_colours_is_all {r k : ℕ} (x : [r]) (c : [r]^(2) → [k]) : univ.bind (colour_components x c) = univ.erase x :=
  begin
    ext, simp [mem_colour_components], split, rintro ⟨_, p, _⟩ _, apply p, symmetry, assumption, 
    intro b, have h: x ≠ a, symmetry, exact b, refine ⟨c (mk_edge x a h), h, rfl⟩, 
  end

  def monochromatic {n r k : ℕ} (M : finset [n]) (c : [n]^(r) → [k]) : Prop := ∃ (col : [k]), ∀ (e : [n]^(r)), e.1 ⊆ M → c e = col

  theorem easy_ramsey {n : ℕ} (c : [6]^(2) → [2]) : ∃ M, monochromatic M c ∧ 3 ≤ M.card := 
  begin
    set v₀ : fin 6 := 0,
    have tot: card (univ.erase v₀) = 5, rw card_erase_of_mem, simp [card_univ, card_fin], apply complete,
    have q: card (univ.bind (colour_components v₀ c)) ≤ univ.sum _ := card_bind_le, 
    rw [all_colours_is_all, tot] at q, clear tot,
    have cols: ∃ (i : [2]), 2 < card (colour_components v₀ c i),   
      by_contra a, push_neg at a, have b := trans q (sum_le_sum (λ t _, a t)), rw sum_const_nat at b, swap,
      intros _ _, refl, rw card_univ at b, rw card_fin at b, norm_num at b, clear q,
    cases cols with col hc,
    by_cases monochromatic (colour_components v₀ c col) c,
    refine ⟨_, h, hc⟩, 
    rw monochromatic at h, push_neg at h, 
    specialize h (⟨1, by norm_num⟩ - col), 
    rcases h with ⟨e₁, t, ncol⟩, 
    refine ⟨insert v₀ e₁.1, _, _⟩, 
    swap,
    rw card_insert_of_not_mem, rw e₁.2, intro, specialize t a, rw mem_colour_components at t, cases t, apply t_w, refl,
    use col, intros e he, by_cases (v₀ ∈ e.1),
    have: ∃ v₁, erase e.val v₀ = finset.singleton v₁, rw ← card_eq_one, rw card_erase_of_mem h, rw e.2, norm_num, 
    cases this with v₁, rw subset_insert_iff at he, rw this_h at he, have: v₁ ∈ colour_components v₀ c col := t (he (mem_singleton_self _)), 
    rw mem_colour_components at this, cases this, convert this_h_1, apply subtype.eq, dunfold mk_edge, 
    have: e.val = insert v₀ (finset.singleton v₁), rw ← this_h, rwa insert_erase, rw this, ext i, simp, rw or_comm,
    have: e.val ⊆ e₁.val, rw subset_insert_iff at he, rwa erase_eq_of_not_mem h at he, 
    have := eq_of_subset_of_card_le this (le_of_eq _), swap, rw e₁.2, rw e.2, rw subtype.eq this,
    set r := c e₁, fin_cases r, any_goals { rw h_1 at *, fin_cases col }, 
    any_goals { rw [ne.def, fin.eq_iff_veq, fin.sub_def] at ncol, simp at ncol }, 
    any_goals { exfalso, assumption }
  end

  def mk_edge' [decidable_eq α] (x y : α) : finset α := {x,y}
  lemma size_mk_edge' {x y : ℕ} (h : x ≠ y) : card (mk_edge' x y) = 2 := 
  begin
    rw [mk_edge', has_insert_eq_insert, card_insert_of_not_mem, insert_empty_eq_singleton, card_singleton], 
    rw [insert_empty_eq_singleton, mem_singleton], intro, apply h, symmetry, assumption
  end
  def mk_edge'_in_pow_len {x y : ℕ} {V : finset ℕ} (h : x ≠ y) (hx : x ∈ V) (hy : y ∈ V) : mk_edge' x y ∈ powerset_len 2 V := 
  begin
    rw mem_powerset_len, rw mk_edge', split, intro t, simp, rintro (rfl | rfl), assumption, assumption,
    simp [mk_edge'], rw card_insert_of_not_mem, rw card_singleton, rw mem_singleton, cc
  end
  def colour_components' {V : finset ℕ} (c : Π a ∈ powerset_len 2 V, ℕ) {v : ℕ} (hv : v ∈ V) (col : ℕ) : finset ℕ :=
  ((V.erase v).attach.filter (λ (x : {t // t ∈ erase V v}), c (mk_edge' v x.1) (mk_edge'_in_pow_len (mem_erase.1 x.2).1.symm hv (erase_subset v V x.2)) = col)).image subtype.val

  lemma mem_colour_components' {V : finset ℕ} (c : Π a ∈ powerset_len 2 V, ℕ) {v w : ℕ} (hv : v ∈ V) (col : ℕ) : 
    w ∈ colour_components' c hv col ↔ ∃ (h : v ≠ w), ∃ (hw : w ∈ V), c (mk_edge' v w) (mk_edge'_in_pow_len h hv hw) = col :=
  begin
    rw colour_components', simp, split; simp, intros x hx, refine ⟨_, _, hx⟩, intros x _ hx, refine ⟨_, hx⟩, rw mem_erase, refine ⟨x.symm, h⟩
  end

  lemma colour_components'_sub {V : finset ℕ} (c : Π a ∈ powerset_len 2 V, ℕ) {v : ℕ} (hv : v ∈ V) (col : ℕ) : colour_components' c hv col ⊆ V :=
  begin
    intro, rw mem_colour_components', rintro ⟨_, _, _⟩, assumption
  end

  lemma main_not_in_colour_components' {V : finset ℕ} (c : Π a ∈ powerset_len 2 V, ℕ) {v : ℕ} (hv : v ∈ V) (col : ℕ) : v ∉ colour_components' c hv col :=
  begin
    intro, rw mem_colour_components' at a, cases a, apply a_w, refl
  end

  lemma all_colours_is_all' {V K : finset ℕ} {c : Π a ∈ powerset_len 2 V, ℕ} (h : ∀ e ∈ powerset_len 2 V, c e ‹_› ∈ K) {v : ℕ} (hv : v ∈ V) :
    K.bind (colour_components' c hv) = V.erase v :=
  begin
    ext w, simp [mem_colour_components'], split, rintro ⟨_, _, dist, hw, _⟩, refine ⟨dist.symm, hw⟩, 
    rintro ⟨dist, _⟩, refine ⟨_, _, _, ‹_›, rfl⟩, symmetry, exact dist, apply h
  end

  def ramsey_form (r k t : ℕ) : Prop := ∃ n, ∀ (V : finset ℕ), n ≤ card V → 
    ∀ (K : finset ℕ), K.card = k → ∀ (c : Π a ∈ powerset_len r V, ℕ), (∀ e ∈ powerset_len r V, c e ‹_› ∈ K) → 
    ∃ (M ⊆ V), t ≤ M.card ∧ ∃ col : ℕ, ∀ e ∈ powerset_len r M, c e (powerset_len_mono ‹_› ‹_›) = col

  lemma trivial_ramsey {r t : ℕ} : ramsey_form r 0 t := 
  begin
    use r, intros V hV K hK c hc, exfalso, rw card_eq_zero at hK, rw hK at hc, 
    cases exists_smaller_set V r hV with V' hV', apply hc V', rw mem_powerset_len, exact hV'
  end
  -- k colours, 3-mono, graph
  theorem tri_ramsey (k : ℕ) : ramsey_form 2 k 3 := 
  begin
    induction k with k ih,
      apply trivial_ramsey,
    cases ih with m ih, 
    use (k+1) * (m-1) + 2, intros V hV K hK c hc, 
    have: ∃ v, v ∈ V, rw exists_mem_iff_ne_empty, rw ← card_eq_zero, apply ne_of_gt, apply lt_of_lt_of_le _ hV,
    apply lt_add_left, apply zero_lt_two,
    cases this with v hv, have cols: ∃ (k ∈ K), m - 1 < card (colour_components' c hv k), by_contra, push_neg at a, 
      have q := @card_bind_le _ _ _ K (colour_components' c hv), rw [all_colours_is_all' hc, card_erase_of_mem hv] at q, 
      have b := trans q (sum_le_sum a), clear q, rw [sum_const, nat.smul_eq_mul] at b, 
      have: (k + 1) * (m - 1) + 1 ≤ (k + 1) * (m - 1) := 
      calc (k+1) * (m-1) + 1 ≤ pred (card V) : le_pred_of_lt hV
           ... ≤ card K * (m - 1) : b
           ... ≤ (k + 1) * (m - 1) : by rw hK,
      apply not_lt_of_le this, apply lt_add_one, 
    rcases cols with ⟨red, redK, big⟩, 
    have HV := colour_components'_sub c hv red,
    set H := colour_components' c hv red, 
    by_cases (∃ e ∈ powerset_len 2 H, c e (powerset_len_mono (colour_components'_sub c hv red) H) = red),
      rcases h with ⟨red_edge, is_edge, is_red⟩, rw mem_powerset_len at is_edge, 
      refine ⟨insert v red_edge, _, _, red, _⟩, intro t, rw mem_insert, rintro (rfl | _), exact hv,
          exact HV (is_edge.1 a), rw card_insert_of_not_mem, rw is_edge.2,
        intro, apply main_not_in_colour_components', exact is_edge.1 a, intros e he, 
      by_cases v ∈ e, rw mem_powerset_len at he, have: ∃ v₂, erase e v = finset.singleton v₂, 
          rw ← card_eq_one, rw card_erase_of_mem h, rw he.2, simp,
        cases this with v₂ hv₂, have z: v₂ ∈ H, apply is_edge.1, rw subset_insert_iff at he, apply he.1, rw hv₂, apply mem_singleton_self,
        rw mem_colour_components' at z, rcases z with ⟨diff, inV, col⟩, convert col, 
        symmetry, apply eq_of_subset_of_card_le, intro t, rw mk_edge', simp, rintro (rfl | rfl), apply mem_of_mem_erase, rw hv₂, 
        apply mem_singleton_self, exact h,
        rw he.2, rw size_mk_edge', rintro rfl, simp [ext] at hv₂, specialize hv₂ v, tauto, 
      convert is_red, rw [mem_powerset_len, subset_insert_iff, erase_eq_of_not_mem h] at he, 
      apply eq_of_subset_of_card_le he.1, rw he.2, rw is_edge.2,
    push_neg at h, specialize ih H (le_of_pred_lt big) (erase K red) _ (λ e he, c e (powerset_len_mono HV he)) _, 
    swap, rw [card_erase_of_mem redK, hK, pred_succ], swap, intros e he, rw mem_erase, split, apply h e he, apply hc, 
    rcases ih with ⟨M, MH, tri, col, q⟩, refine ⟨M, trans MH HV, tri, col, q⟩, 
  end

  -- 2 colours, s,t-mono, graph
  lemma ramsey_helper (s t : ℕ) : ∃ n, ∀ (V : finset ℕ), n ≤ card V →
    ∀ (c : Π a ∈ powerset_len 2 V, ℕ), (∀ e ∈ powerset_len 2 V, c e ‹_› < 2) →
    (∃ M ⊆ V, s ≤ M.card ∧ ∀ e ∈ powerset_len 2 M, c e (powerset_len_mono ‹_› ‹_›) = 0) ∨ 
    (∃ M ⊆ V, t ≤ M.card ∧ ∀ e ∈ powerset_len 2 M, c e (powerset_len_mono ‹_› ‹_›) = 1) :=
  begin
    revert s t, 
    suffices z: ∀ s : (ℕ × ℕ), ∃ n, ∀ (V : finset ℕ), n ≤ card V →
    ∀ (c : Π a ∈ powerset_len 2 V, ℕ), (∀ e ∈ powerset_len 2 V, c e ‹_› < 2) →
    (∃ M ⊆ V, s.1 ≤ M.card ∧ ∀ e ∈ powerset_len 2 M, c e (powerset_len_mono ‹_› ‹_›) = 0) ∨ 
    (∃ M ⊆ V, s.2 ≤ M.card ∧ ∀ e ∈ powerset_len 2 M, c e (powerset_len_mono ‹_› ‹_›) = 1),
      intros s t, exact z (s,t), 
    intro s, refine @well_founded.recursion (ℕ × ℕ) (measure (λ (a : ℕ × ℕ), a.1 + a.2)) (measure_wf _) _ s _, 
    clear s, rintros ⟨s,t⟩ ih,
    cases nat.eq_zero_or_pos s with h sp, rw h at *,
      use 0, intros V hV c hc, left, refine ⟨∅, empty_subset _, _, _⟩, rw finset.card_empty,
      intros e he, exfalso, rw mem_powerset_len at he, rw subset_empty at he, have z := he.2, 
      rw he.1 at z, rw finset.card_empty at z, norm_num at z,
    rcases ih ⟨s-1, t⟩ _ with ⟨a, ha⟩, 
    swap, rw [measure, inv_image, add_lt_add_iff_right], apply nat.sub_lt sp zero_lt_one, 
    cases nat.eq_zero_or_pos t with h tp, rw h at *,
      use 0, intros V hV c hc, right, refine ⟨∅, empty_subset _, _, _⟩, rw finset.card_empty,
      intros e he, exfalso, rw mem_powerset_len at he, rw subset_empty at he, have z := he.2, 
      rw he.1 at z, rw finset.card_empty at z, norm_num at z,
    rcases ih ⟨s, t-1⟩ _ with ⟨b, hb⟩, 
    swap, rw [measure, inv_image, add_lt_add_iff_left], apply nat.sub_lt tp zero_lt_one,
    clear ih,
    use max 1 (a + b), intros V hV c hc, 
    have Vcard: 1 ≤ card V := trans (le_max_left _ _) hV,
    have: ∃ v, v ∈ V, rw exists_mem_iff_ne_empty, rw ← card_eq_zero, intro, 
      rw a_1 at Vcard, norm_num at Vcard,
    cases this with v hv,
    have cards: card ((range 2).bind (colour_components' c hv)) = card (V.erase v), congr, apply all_colours_is_all' _ hv, 
      intros e he, specialize hc e he, rwa mem_range, 
    have: ¬ (card (colour_components' c hv 0) < a ∧ card (colour_components' c hv 1) < b),
      rintro ⟨smallred, smallgreen⟩, rw card_erase_of_mem hv at cards, 
      rw [range_succ, bind_insert, range_one, insert_empty_eq_singleton, singleton_bind, card_disjoint_union] at cards,
        apply ne_of_lt _ cards, apply lt_of_lt_of_le _ (pred_le_pred (trans (le_max_right _ _) hV)), 
        rw pred_eq_sub_one, rw nat.add_sub_assoc (one_le_of_lt smallgreen), rw nat.add_comm, apply lt_of_lt_of_le, 
        rw add_lt_add_iff_right, exact smallred, apply add_le_add_left (le_pred_of_lt smallgreen),
      rw disjoint_left, simp [mem_colour_components'], rintro _ _ _ wgreen _ ⟨_, wred⟩, rw wred at wgreen, apply zero_ne_one wgreen,
    push_neg at this, cases this with red green,
      specialize ha (colour_components' c hv 0) red (λ e he, c e (powerset_len_mono (colour_components'_sub _ _ _) he)) (λ e _, hc e _),
      clear hb,
      rcases ha with ⟨reds, redssub, redsbig, redsred⟩ | ⟨greens, greenssub, greensbig, greensgreen⟩, 
      left, refine ⟨insert v reds, _, _, _⟩, rw insert_subset, refine ⟨hv, trans redssub (colour_components'_sub _ _ _)⟩, 
          rw card_insert_of_not_mem, rw ← nat.sub_le_right_iff_le_add, exact redsbig, intro, 
          apply (main_not_in_colour_components' _ _ _) (redssub a_1), 
        intros e he, by_cases e ∈ powerset_len 2 reds, apply redsred _ h, rw mem_powerset_len at h, 
        obtain ⟨he₁, he₂⟩ := mem_powerset_len.1 he, simp [he₂] at h, rw subset_insert_iff at he₁, 
        have: v ∈ e, by_contra, apply h, rwa erase_eq_of_not_mem a_1 at he₁, 
        have v₂: ∃ v₂, erase e v = finset.singleton v₂, rw ← card_eq_one, rw card_erase_of_mem ‹v ∈ e›, rw he₂, refl,
        cases v₂ with v₂ hv₂, have: v₂ ∈ colour_components' c hv 0, apply redssub, apply he₁, rw hv₂, apply mem_singleton_self,
        rw mem_colour_components' at this, rcases this with ⟨_, _, c'⟩, convert c', symmetry, apply eq_of_subset_of_card_le, 
          intro, rw mk_edge', simp, rintro (rfl | rfl), apply mem_of_mem_erase, rw hv₂, apply mem_singleton_self,
          assumption, rw he₂, rw size_mk_edge', assumption, 
      right, refine ⟨greens, trans greenssub (colour_components'_sub _ _ _), greensbig, greensgreen⟩, 
    specialize hb (colour_components' c hv 1) green (λ e he, c e (powerset_len_mono (colour_components'_sub _ _ _) he)) (λ e _, hc e _),
    clear ha,
    rcases hb with ⟨reds, redssub, redsbig, redsred⟩ | ⟨greens, greenssub, greensbig, greensgreen⟩,
      left, refine ⟨reds, trans redssub (colour_components'_sub _ _ _), redsbig, redsred⟩,
    right, refine ⟨insert v greens, _, _, _⟩, rw insert_subset, refine ⟨hv, trans greenssub (colour_components'_sub _ _ _)⟩, 
      rw card_insert_of_not_mem, rw ← nat.sub_le_right_iff_le_add, exact greensbig, intro, 
      apply (main_not_in_colour_components' _ _ _) (greenssub a_1), 
    intros e he, by_cases e ∈ powerset_len 2 greens, apply greensgreen _ h, rw mem_powerset_len at h, 
    obtain ⟨he₁, he₂⟩ := mem_powerset_len.1 he, simp [he₂] at h, rw subset_insert_iff at he₁, 
    have: v ∈ e, by_contra, apply h, rwa erase_eq_of_not_mem a_1 at he₁, 
    have v₂: ∃ v₂, erase e v = finset.singleton v₂, rw ← card_eq_one, rw card_erase_of_mem ‹v ∈ e›, rw he₂, refl,
    cases v₂ with v₂ hv₂, have: v₂ ∈ colour_components' c hv 1, apply greenssub, apply he₁, rw hv₂, apply mem_singleton_self,
    rw mem_colour_components' at this, rcases this with ⟨_, _, c'⟩, convert c', symmetry, apply eq_of_subset_of_card_le, 
      intro, rw mk_edge', simp, rintro (rfl | rfl), apply mem_of_mem_erase, rw hv₂, apply mem_singleton_self,
      assumption, rw he₂, rw size_mk_edge', assumption, 
  end

  -- lemma big_ramsey (K : finset ℕ) (num : ℕ → ℕ) : ∃ n, ∀ (V : finset ℕ), n ≤ card V →
  -- ∀ (c : Π a ∈ powerset_len 2 V, ℕ), (∀ e ∈ powerset_len 2 V, c e ‹_› ∈ K) →
  -- ∃ col ∈ K, ∃ M ⊆ V, (num col ≤ M.card) ∧ (∀ e ∈ powerset_len 2 M, c e (powerset_len_mono ‹_› ‹_›) = col) :=
  -- begin
  -- end

  theorem multi_ramsey {s k : ℕ} : ramsey_form 2 k s := 
  begin
    induction k with k ih, apply trivial_ramsey,
    cases ih with m ih, cases ramsey_helper s m with n help, 
    use n, intros V hV K hK c hc, have: ∃ red, red ∈ K, rw exists_mem_iff_ne_empty,
      rw ← card_eq_zero, rw hK, exact of_to_bool_ff rfl,
    rcases this with ⟨red, redK⟩,
    specialize help V hV (λ a ha, ite (c a ha = red) 0 1) _, swap,
    intros, dsimp, split_ifs, exact zero_lt_two, exact one_lt_two,
    rcases help with ⟨reds, redV, bigred, isred⟩ | ⟨greens, greenV, biggreen, isgreen⟩,
    refine ⟨reds, redV, bigred, red, _⟩, intros e he, specialize isred e he, dsimp at isred,
    split_ifs at isred, exact h, exfalso, apply nat.zero_ne_one isred.symm,
    rcases ih greens biggreen (erase K red) _ (λ e he, c e (powerset_len_mono greenV he)) _ 
      with ⟨M, Mgreen, cardM, col, mono⟩, 
    refine ⟨M, trans Mgreen greenV, cardM, col, mono⟩, rw [card_erase_of_mem redK, hK, pred_succ], 
    intros e he, specialize isgreen e he, dsimp at isgreen, split_ifs at isgreen, 
    exfalso, apply zero_ne_one isgreen, dsimp, rw mem_erase, refine ⟨h, hc _ _⟩,
  end
end ramsey