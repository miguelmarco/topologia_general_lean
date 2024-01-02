import .sucesiones

open topologicos topologicos.espacio_topologico set


variables {X : Type} [espacio_topologico X]

/-
## Definición 4.5.1.
Si V es entorno de todos los puntos de un conjunto A ⊂ X,
diremos que V es un *entorno* de A.
-/

def entorno_de_conjunto (A U : set X) :=  ∀ x ∈ A, entorno x U


/-
(es decir, si existe U ∈ T tal que A ⊂ U ⊂ V ).
-/
lemma entorno_de_conjunto_sii_existe_abierto (A U : set  X) : entorno_de_conjunto A U ↔ ∃ (V : set X), abierto V ∧ A ⊆ V ∧ V ⊆ U :=
begin
  split,
  {
    intro h,
    let V := ⋃₀ { E | abierto E  ∧ E ⊆ U},
    use V,
    split,
    {
      apply abierto_union,
      intros E hE,
      use hE.1,
    },
    split,
    {
      intros x hx,
      specialize h x hx,
      cases h with E hE,
      use E,
      split,
      split,
        exact hE.1,
        exact hE.2.2,
        exact hE.2.1,
    },
    {
      apply set.sUnion_subset,
      simp only [set.mem_set_of_eq, and_imp, imp_self, implies_true_iff],
    },
  },
  {
    intro h,
    intros x hx,
    cases h with E hE,
    use E,
    split,
      exact hE.1,
    split,
      exact hE.2.1 hx,
      exact hE.2.2,
  },
end

/-
## Definición 4.5.2.
Sea (X, T ) un e.t. y sean A, B ⊂ X. Diremos que A y B se pueden separar en (X, T ) si existen 
entornos disjuntos Va, Vb ⊂ X de A y B respectivamente.
-/
def se_pueden_separar (A B : set X) :=  ∃ (Va Vb : set X), (entorno_de_conjunto A  Va) ∧ (entorno_de_conjunto B Vb) ∧ Va ∩ Vb = ∅ 

/-
## Observaciones 4.5.3.

### (AxS1)
Observa que si A = {x}, entonces V ⊂ X es entorno de A si y s´olo si es
entorno de x en el sentido clásico.
-/
lemma obs_AxS1 (x : X) (V : set X) : entorno x V ↔ entorno_de_conjunto {x} V := 
begin
  simp only [entorno_de_conjunto, set.mem_singleton_iff, forall_eq],
end

/-

### (AxS2)
Todo abierto que contenga a A es un entorno de A.
-/
lemma obs_AxS2 (A U : set X) (hU : abierto U) (hUA : A ⊆ U) : entorno_de_conjunto A U :=
begin
  rw entorno_de_conjunto_sii_existe_abierto,
  use U,
  tauto,
end

/-
### (AxS3) 
Observa que las Propiedades de entornos tienen fácil tradducción para entornos de conjuntos.
#### (N 1)
  Todo conjunto A ⊂ X admite algún entorno (ya que por ejemplo el
espacio total es entorno de cualquier subconjunto suyo).
-/
lemma AxS3N1 (A : set X) : ∃ U , entorno_de_conjunto A U :=
begin
  use univ,
  rw entorno_de_conjunto_sii_existe_abierto,
  use univ,
  simp only [abierto_total, abierto_def, subset_univ, and_self],
end
/-
#### (N 2) 
Si V es entorno de A ⊂ X, entonces A ⊂ V.
-/
lemma AxS3N2 (A V : set X) (h : entorno_de_conjunto A V) : A ⊆ V :=
begin
  rw entorno_de_conjunto_sii_existe_abierto at h,
  cases h with U hU,
  cases hU with hUab hU2,
  cases hU2 with hAU hUV,
  calc
    A   ⊆  U : by {exact hAU,}
    ... ⊆  V : by {exact hUV,}
end
/-
#### (N 3)
Si Va1 y Va2 son entornos de A ⊂ X, entonces Va1 ∩ Va2 es entorno de
A.
-/
lemma AxSN3N3 (A V1 V2 : set X) (h1 : entorno_de_conjunto A V1) (h2 : entorno_de_conjunto A V2) :
    entorno_de_conjunto A (V1 ∩ V2) :=
begin
  intros x hx,
  specialize h1 x hx,
  specialize h2 x hx,
  apply entornos_N3,
    exact h1,
    exact h2,
end


/-
#### (N 4)
Si V es entorno de A y V ⊂ W , entonces W es entorno de A.
-/
lemma AxSN3N4 (A V W: set X) (hV : entorno_de_conjunto A V) (hVW : V ⊆ W) :
    entorno_de_conjunto A W :=
begin
  intros x hx,
  specialize hV x hx,
  apply entornos_N4 ,
    exact hV,
    exact hVW,
end
/-
#### (AxS4) 
La propiedad de que dos conjuntos A, B ⊂ X se pueden separar también
se puede expresar con las siguientes propiedades equivalentes:
(a) Existen abiertos Ua, Ub tal que A ⊂ Ua, B ⊂ Ub y Ua ∩ Ub = ∅
(abreviando, existen entornos abiertos disjuntos).
-/
lemma caracterizacion_se_pueden_separar_abiertos (A B : set X) :
    se_pueden_separar A B ↔ ∃ (Ua Ub : set X), abierto Ua ∧ abierto Ub ∧ A ⊆ Ua ∧ B ⊆ Ub ∧ Ua ∩ Ub = ∅ :=
begin
  split,
  {
    intro h,
    rcases h with ⟨Va,⟨Vb,⟨hVaen, ⟨hVben,hVaVbdisj⟩⟩⟩⟩,
    rw entorno_de_conjunto_sii_existe_abierto at hVaen hVben,
    rcases hVaen with ⟨Ua,⟨hUaab,⟨haUa,hUaVa⟩⟩⟩,
    rcases hVben with ⟨Ub,⟨hUbab,⟨hbUb,hUbVb⟩⟩⟩,
    use Ua,
    use Ub,
    split, exact hUaab,
    split, exact hUbab,
    split, exact haUa,
    split, exact hbUb,
    rw conjunto_vacio_sii_todo_elemento_no at ⊢ hVaVbdisj,
    intros x hx,
    specialize hVaVbdisj x,
    apply hVaVbdisj,
    split,
      exact hUaVa hx.1,
      exact hUbVb hx.2,
  },
  {
    intro h,
    rcases h with ⟨Ua,⟨Ub,⟨hUaab,⟨hUbab,⟨hAUa,⟨hBUb,hUaUb⟩⟩⟩⟩⟩⟩,
    use Ua,
    use Ub,
    simp  only [entorno_de_conjunto_sii_existe_abierto],
    split,
    {
      use Ua,
      tauto,
    },
    split,
    {
      use Ub,
      tauto,
    },
    exact hUaUb,
  }
end
/-
(b) Existe un superconjunto abierto U de A tal que clausura U  ∩ B = ∅.
-/
lemma caracterizacion_entorno_de_conjunto_abierto_clausura (A B:  set X) : 
    se_pueden_separar A B ↔  ∃ U, abierto U ∧ A ⊆ U ∧ clausura U  ∩ B = ∅ :=
begin
  rw caracterizacion_se_pueden_separar_abiertos,
  split,
  {
    intro h,
    rcases h with ⟨Ua,⟨ Ub, ⟨ hUaab,⟨ hUbab,⟨ hAUa,⟨ hBUb,hUAUB⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ,
    use Ua,
    split, exact hUaab,
    split, exact hAUa,
    rw inter_comm,
    rw disjuntos_sii_contenido_en_complemento,
    rw interior_complementario_clausura_complementario,
    have hBin : Ub ⊆ Uaᶜ,
    {
      rw ← disjuntos_sii_contenido_en_complemento,
      rw inter_comm,
      assumption,
    },
    calc
      B   ⊆ Ub   : by {exact hBUb,}
      ... ⊆ interior Uaᶜ  : by {apply interior_mayor_abierto _  _ hUbab hBin,}
  },
  {
    intro h,
    rcases h with ⟨Ua,⟨hUaab,⟨hAUa,hclauUa⟩⟩⟩,
    use Ua,
    use (clausura Ua)ᶜ,
    split, exact hUaab,
    split,
    {
      have haux := clausura_cerrado Ua,
      simp at haux,
      exact haux,
    },
    split,exact hAUa,
    split,
    {
      rw inter_comm at hclauUa,
      rw  disjuntos_sii_contenido_en_complemento at hclauUa,
      exact hclauUa,
    },
    simp [disjuntos_sii_contenido_en_complemento],
    apply clausura_contiene,
  },
end

/-
(c) Existe un entorno Va de A tal que clausura Va ∩ B = ∅.
-/
lemma caracterizacion_entorno_de_conjunto_entorno_clausura (A B:  set X) : 
    se_pueden_separar A B ↔  ∃ U, entorno_de_conjunto A U ∧ clausura U  ∩ B = ∅ :=
begin
  rw caracterizacion_entorno_de_conjunto_abierto_clausura,
  split,
  {
    intro h,
    rcases h with ⟨ U,⟨ hUab, ⟨hAUA,hclauUa⟩ ⟩⟩,
    use U,
    split,
    {
      rw entorno_de_conjunto_sii_existe_abierto,
      use U,
      tauto,
    },
    exact hclauUa,
  },
  {
    intro h,
    rcases h with ⟨V,⟨hVen,hclauV⟩⟩,
    rw entorno_de_conjunto_sii_existe_abierto at hVen,
    rcases hVen with ⟨U,⟨ hUab,⟨hAU,hUV⟩ ⟩⟩,
    use U,
    split, exact hUab,
    split, exact hAU,
    rw disjuntos_sii_contenido_en_complemento at ⊢ hclauV,
    calc
      clausura U ⊆ clausura V : by {apply clausura_monotona, exact hUV,}
      ...        ⊆ Bᶜ         : by {exact hclauV,}
  },
end

/-
(d) Existe un entorno cerrado Va de A tal que Va ∩ B = ∅
-/
lemma caracterizacion_entorno_de_conjunto_entorno_cerrado (A B:  set X) : 
    se_pueden_separar A B ↔  ∃ U, entorno_de_conjunto A U ∧ cerrado U  ∧ U ∩ B = ∅ :=
begin
  rw caracterizacion_entorno_de_conjunto_entorno_clausura,
  split,
  {
    intro h,
    rcases h with ⟨U,⟨ hUen,hclauU⟩⟩,
    use clausura U,
    split,
    {
      rw entorno_de_conjunto_sii_existe_abierto at ⊢ hUen,
      cases hUen with V hV,
      use V,
      simp only [true_and, hV],
      calc 
        V   ⊆ U          : by {tauto,}
        ... ⊆ clausura U : by {apply clausura_contiene,}
    },
    split, 
      exact clausura_cerrado U,
      exact hclauU,
  },
  {
    intro h,
    rcases h with ⟨U,⟨ hUen,⟨hUcer,hUB⟩ ⟩⟩,
    use U,
    split, exact hUen,
    {
      rw ← clausura_eq_sii_cerrado at hUcer,
      rw hUcer,
      exact hUB,
    }
  }
end