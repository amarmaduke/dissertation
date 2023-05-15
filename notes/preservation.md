
# Preservation

    Γ ⊢ u : V -> u -β> v -> Γ ⊢ v : V

by induction on t -β> s

Case 1. (λ x:B. t) s -β> t[x := s]
    Have:
    1. u := (λ x:U. t) s
    2. v := t[x := s]
    3. Γ ⊢ (λ x:U. t) s : V[x := s]
    By 3:
    4. Γ ⊢ λ x:U. t : (x:U) -> V
    5. Γ ⊢ s : U
    By 4:
    6. x:U,Γ ⊢ t : V
    By Substitution Lemma 1
    Γ ⊢ t[x := s] : V

Case 2: (Λ x:A. t) s -β> t[x := s]
    similar to case 2

Case 3: fst -A -P [t, s] -β> t
    Have:
    1. u := fst -A -P [t, s]
    2. v := t
    3. Γ ⊢ fst -V -P [t, s] : V
    By 3:
    4. Γ ⊢ [t, s] : (x:V) ∩ P
    By 4:
    5. Γ ⊢ t : V

Case 4: snd -A -P [t, s] -β> s