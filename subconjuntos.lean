import tactic

open set

variables {X : Type}  {A B C: set X} 

def restringe {X : Type} (A : set X): set X → set A := λ B , {x | ↑x ∈ B} 

notation d ` ↓∩ ` A := restringe A d 

@[simp]
lemma pert_restringe_def (x : A) : x ∈ (B ↓∩ A) ↔ ↑x ∈ B := by refl

@[simp]
lemma restringe_coe {X : Type} {A : set X} ( C : set X) : ((coe : A → X)  ⁻¹' C) = (restringe A C)  := rfl 

@[simp]
lemma restringe_vacio : (∅ ↓∩ A )=  ∅ := rfl

@[simp] 
lemma restringe_total : restringe A univ = (univ  : set A) :=
begin
  refl,
end

@[simp]
lemma restringe_conjunto : restringe A A = univ := 
begin
  ext x,
  simp only [pert_restringe_def, subtype.coe_prop, mem_univ],
end

@[simp]
lemma restringe_union  :   ((B ∪ C) ↓∩ A) = (B ↓∩ A) ∪ (C ↓∩ A) :=
begin
  ext x,
  simp only [mem_union, pert_restringe_def],
end

@[simp]
lemma restringe_interseccion :   ((B ∩ C) ↓∩ A)  = (B ↓∩ A) ∩ (C ↓∩ A):=
begin
  ext x,
  simp only [mem_inter_iff, pert_restringe_def],
end

@[simp]
lemma restringe_complementario (U : set X) :   (Uᶜ ↓∩ A) = (U ↓∩ A)ᶜ := rfl

@[simp]
lemma restringe_contenido : (B ↓∩ A) ⊆ (C ↓∩ A) ↔ (B ∩ A) ⊆ (C ∩ A) :=
begin
  split,
  {
    intro h,
    simp only [subset_inter_iff, inter_subset_right, and_true],
    intros x hx,
    cases hx with hxb hxa,
    have haux : (⟨x,hxa⟩ : A) ∈ (B ↓∩ A),
    {
      exact hxb,
    },
    specialize h haux,
    exact h,
  },
  {
    intro h,
    simp only [and_true, set.subset_inter_iff, set.inter_subset_right] at h,
    intros x hx,
    apply h,
    simp only [and_true, subtype.coe_prop, set.mem_inter_iff],
    exact hx,
  }
end

@[simp]
lemma restringe_igual : (B ↓∩ A) = (C ↓∩ A) ↔ (B ∩ A) = (C ∩ A) :=
begin
  simp only [subset_antisymm_iff, restringe_contenido],
end

@[simp]
lemma restringe_union_familia (F : set (set X)) : (⋃₀ F  ↓∩ A) = ⋃₀ {(U ↓∩  A) | U ∈ F}  :=
begin
  ext,
  simp only [pert_restringe_def, mem_sUnion, exists_prop, mem_set_of_eq, exists_exists_and_eq_and],
end

@[simp]
lemma restringe_interseccion_familia (F : set (set X)) : (⋂₀ F  ↓∩ A) = ⋂₀ {(U ↓∩  A) | U ∈ F} :=
begin
  ext,
  simp only [pert_restringe_def, mem_sInter, mem_set_of_eq, forall_exists_index, forall_apply_eq_imp_iff₂],
end

instance {X : Type} {A : set X}: has_coe (set A) (set X) := { coe :=  λ B, {(↑x) | x ∈ B}}

@[simp]
lemma coe_injec (x y : A) : (x : X) = (y : X) ↔ x = y :=
begin
  rw subtype.ext_iff,
end

@[simp]
lemma pertenece_eleva_def (x : A) (U : set A) : (x  : X) ∈ (U : set X) ↔ (x ∈ U) :=
begin
  split,
  {
    intro h,
    cases h with  y hy,
    simp only [coe_injec, exists_prop] at hy,
    rw ← hy.2,
    exact hy.1,
  },
  {
    intro h,
    use x,
    simp only [h, eq_self_iff_true, and_self],
  },
end

@[simp]
lemma eleva_vacio : (↑(∅ : set A) : set X) = (∅ : set X) :=
begin
  ext x,
  simp only [set.mem_empty_eq, iff_false],
  intro h,
  cases h with y hy,
  cases hy with hy1 hy2,
  exact hy1,
end

@[simp]
lemma eleva_total : ↑(univ : set A) = A :=
begin
  ext x,
  split,
  {
    intro hx,
    cases hx with y hy,
    simp only [pertenece_eleva_def, exists_prop] at hy,
    rw ← hy.2,
    simp only [subtype.coe_prop],
  },
  {
    intro hx,
    use ⟨x,hx⟩,
    simp only [set.mem_univ, eq_self_iff_true, and_self, subtype.coe_mk],
  }
end

@[simp]
lemma eleva_restringe (U : set A) : ((U : set X) ↓∩ A) = U :=
begin
  ext x,
  simp only [pert_restringe_def, pertenece_eleva_def],
end

@[simp]
lemma restringe_eleva : ((B ↓∩ A) : set X) = B ∩ A :=
begin
  ext x,
  split,
  {
    intro hx,
    cases hx with x' hx',
    cases hx' with hx'b hx'x,
    rw ← hx'x,
    exact ⟨hx'b, x'.2⟩,
  },
  {
    intro hx,
    use ⟨x,hx.2⟩,
    exact ⟨hx.1, rfl⟩,
  }
end

lemma eleva_contenido (B : set A) : ↑B ⊆ A :=
begin
  intros x hxB,
  cases hxB with x' hx',
  cases hx' with hx'B hx'x,
  cases hx'x,
  exact x'.2,
end

@[simp]
lemma eleva_inter_A (B : set A) : ↑B ∩ A = ↑B :=
begin
  simp only [set.inter_eq_left_iff_subset],
  apply eleva_contenido,
end


@[simp]
lemma eleva_union (B C : set A) :  ↑(B ∪ C) = ((↑B : set X)  ∪ (↑C : set X)) :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with x' hx',
    cases hx' with hx'BC hx'x,
    induction hx'x,
    cases hx'BC,
    {
      left,
      use x',
      tauto,
    },
    {
      right,
      use x',
      tauto,
    }
  },
  {
    intro h,
    cases h,
    {
      cases h with x' hx',
      cases hx' with hx'B hx'x,
      cases hx'x,
      use x',
      split,
      {
        left,
        exact hx'B,
      },
      {
        exact hx'x,
      },
    },
    {
      cases h with x' hx',
      cases hx' with hx'B hx'x,
      use x',
      split,
      {
        right,
        exact hx'B,
      },
      {
        exact hx'x,
      },
    },
  },
end

@[simp]
lemma eleva_interseccion (B C : set A) : ↑(B ∩  C) = ((↑B : set X)  ∩  (↑C : set X)) :=
begin
  ext x,
  split,
  {
    intro hx,
    cases hx with x' hx',
    cases hx' with hx'bc hx'x,
    cases hx'bc with hx'b hx'c,
    split,
    repeat {
      use x',
      simp only [and_true, eq_self_iff_true, hx'x],
      assumption,
    },
  },
  {
    intro hx,
    cases hx with hxb hxc,
    cases hxb with y1 hy1,
    cases hy1 with hy1b hy1x,
    induction hy1x,
    simp only [pertenece_eleva_def] at hxc,
    use y1,
    exact ⟨⟨hy1b,hxc⟩,rfl⟩,
  }
end

@[simp]
lemma eleva_complementario (U : set A) :  (↑(Uᶜ) : set X) = (↑U : set X)ᶜ ∩ A  :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with z hz,
    cases hz with hzUc hzx,
    induction hzx,
    split,
    {
      intros hx,
      cases hx with y hy,
      cases hy with hyU hyx,
      apply hzUc,
      have haux : z = y,
      {
        ext,
        simp [hyx],
      },
      rw haux,
      exact hyU,
    },
    {
      exact z.2,
    }
  },
  {
    intro h,
    cases h with hxUc hxA,
    let y : A := ⟨x,hxA⟩,
    use y,
    simp only [and_true, eq_self_iff_true, set.mem_compl_iff, subtype.coe_mk],
    intro hy,
    apply hxUc,
    use y,
    simp only [hy, eq_self_iff_true, and_self, subtype.coe_mk],
  }
end

@[simp]
lemma eleva_union_familia (F : set (set A)) : (↑(⋃₀ F) : set X) = ⋃₀ { (↑U) | U ∈ F} :=
begin
  ext x,
  split,
  {
    intro hx,
    cases hx with y hy,
    cases hy with hyUF hyx,
    cases hyUF with U hU,
    cases hU with hUF hyU,
    use U,
    split,
    {
      use U,
      simp only [eq_self_iff_true, hUF, and_self],
    },
    {
      induction hyx,
      simp only [pertenece_eleva_def,hyU],
    },
  },
  {
    intro hx,
    cases hx with U hU,
    cases hU with hU hxU,
    cases hU with V hV,
    cases hV with hVF hVU,
    rw ←  hVU at hxU,
    cases hxU with y hy,
    cases hy with hyV hyx,
    use y,
    split,
    {
      use V,
      exact ⟨hVF,hyV⟩,
    },
    {
      exact hyx,
    },
  },
end

@[simp]
lemma eleva_interseccion_familia (F : set (set A)) : (↑(⋂₀ F) : set X) = ⋂₀ { (↑U) | U ∈ F} ∩ A :=
begin
  ext x,
  split,
  {
    intro hx,
    cases hx with y hy,
    cases hy with hyUF hyx,
    induction hyx,
    split,
    {
      intros U hU,
      cases hU with V hV,
      cases hV with hVF hVU,
      specialize hyUF V hVF,
      rw ← hVU,
      simp only [pertenece_eleva_def,hyUF],
    },
    {
      simp only [subtype.coe_prop],
    }
  },
  {
    intro hx,
    cases hx with hxUF hxA,
    use ⟨x,hxA⟩,
    simp only [set.mem_sInter, and_true, eq_self_iff_true, subtype.coe_mk],
    intros U hU,
    simp only [set.mem_sInter, forall_apply_eq_imp_iff₂, mem_set_of_eq, forall_exists_index] at hxUF,
    specialize hxUF U hU,
    cases hxUF with y hy,
    cases hy with hyU hyx,
    induction hyx,
    simp only [subtype.coe_eta,hyU],
  },
end

@[simp]
lemma interseccion_elevacion {B : set A} (U : set X ) :  U ∩ A ∩ ↑B = U ∩ ↑B :=
begin
  ext x,
  simp only [mem_inter_iff, and.congr_left_iff, and_iff_left_iff_imp],
  intros hxb hxU,
  apply eleva_contenido,
  exact hxb,
end

@[simp]
lemma preimagen_composicion_inclusion {Y : Type} (f : X → Y) (U : set Y): ((f ∘ (coe : A → X)) ⁻¹' U) = ((f ⁻¹' U) ↓∩ A) := rfl