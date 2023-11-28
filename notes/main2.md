# CC

    --------- ax1
    Γ ⊢ * : □

    x:A ∈ Γ
    --------- var1
    Γ ⊢ x : A

    Γ ⊢ A:K    Γ,x:A ⊢ B:L
    ------------------------ prod1
    Γ ⊢ (x:A) -> B : L

    Γ ⊢ A:K    Γ,x:A ⊢ N:A
    ------------------------- lam1
    Γ ⊢ λ x:A. N : (x:A) -> B

    Γ ⊢ M : (x:A) -> B    Γ ⊢ N:A
    ----------------------------- app1
    Γ ⊢ M N : B[x := N]

    Γ ⊢ M:A    A =β B    Γ ⊢ B:K
    ---------------------------- conv1
    Γ ⊢ M : B

# BiCC

    ---------- ax2
    Γ ⊢ * |> □

    x:A ∈ Γ
    ---------- var2
    Γ ⊢ x |> A

    Γ ⊢ A |> K    Γ,x:A ⊢ B |> L
    ---------------------------- prod2
    Γ ⊢ (x:A) -> B |> L

    Γ,x:A ⊢ N <| B
    ------------------------ lam2
    Γ ⊢ λ x. N <| (x:A) -> B

    C -β>* (x:A) -> B
    Γ ⊢ M |> C    Γ ⊢ N <| A
    --------------------------------- app2
    Γ ⊢ M N |> B[x := N] 

    Γ ⊢ M |> A    A =β= B
    --------------------- conv2
    Γ ⊢ M <| B

# Equivalence

    1. Given Γ ⊢ t : A then Γ ⊢ [t] <| A
    2. Given Γ ⊢ t <| A then Γ ⊢ t |> A
    3. Given Γ ⊢ t <| A then Γ ⊢ [Γ;A;t] : A
    
    4. Given Γ ⊢ t <| A and t -β>* t' then Γ ⊢ t' <| A
        Proof sketch.
        by (3) we know that Γ ⊢ [Γ;A;t'] : A by preservation
        by (1) we're done

    5. Given Γ ⊢ t <| A then t ∈ SN
        Proof sketch.
        by (3) we know that Γ ⊢ t : A
