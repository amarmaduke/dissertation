

[*]Γ = *
[x]Γ = x
[(x:A) -t> B]Γ = Π x:[A]Γ. [B]Γ,x:[A]Γ
[(x:A) -ω> B]Γ = Π x:[A]Γ. [B]Γ,x:[A]Γ
[(x:A) -0> B]Γ = ∀ x:[A]Γ. [B]Γ,x:[A]Γ
[λ_t x:A. t]Γ = λ x:[A]Γ. [t]Γ,x:[A]Γ
[λ_ω x:A. t]Γ = λ x. [t]Γ,x:[A]Γ
[λ_0 x:A. t]Γ = Λ x. [t]Γ,x:[A]Γ
[f ∙_t a]Γ = [f]Γ ∙[a]Γ
[f ∙_ω a]Γ = [f]Γ [a]Γ
[f ∙_0 a]Γ = [f]Γ -[a]Γ

[(x:A) ∩ B]Γ = ι x:[A]Γ. [B]Γ,x:[A]Γ
[[t, s, T]]Γ = [[t]Γ, [s]Γ]
[t.1]Γ = ([t]Γ).1
[t.2]Γ = ([t]Γ).2

[t =[A] s]Γ = ι e:{[t]Γ = [s]Γ}. {e = β{λ x. x}}
[refl(t)]Γ = [β{id}, β{id}]
[θ(e)]Γ = [e]Γ
[φ(a,f,e)]Γ = φ ([e]Γ [a]Γ).1 - ([f]Γ [a]Γ) { [a]Γ }
[δ(e)]Γ = δ - ([e]Γ).1
[J(A,P,x,y,e,w)]Γ = 
    ρ e.1 @ i[[y]Γ]. [P]Γ i [y]Γ [e]Γ -
    ρ e.2 @ i[[refl(y)]Γ]. [P]Γ [y]Γ [y]Γ i -
    [w]Γ -[y]Γ

Lemma FV(|s|) = FV(|[s]|)
Lemma [|t|] = |[t]|
Lemma t === s then [t] =β= [s]
Lemma t =β= s then [t] =β= [s]
Lemma [[x := t]s] = [x/[t]][s]

Soundness: Given Γ ⊢ t |> A
    1. t kind then [Γ] ⊢ [t]
    2. t type then [Γ] ⊢ [t] |> [A]
    3. t term then [Γ] ⊢ [t] <| [A] 
    
    by induction on inference judgment
    (Axiom Case)
    t is a kind, holds by axiom

    (Var Case)
    identical rules in type/term case (cannot be a kind)

    (HdInf Case) ?
    (Check Case) ?
    (CtxEmpty Case) ?
    (CtxApp Case) ?

    (Pi Case) t = (x:A) -m> B
    Suppose t is a kind, then m = t and [t] = Π x:A. B
        A is either a type or a kind
        type: by induction, use appropriate rule, done
        kind: by induction, use appropriate rule, done
    Suppose t is a type, then m = ω or 0
        in either case, straightforward by induction



Consistency: ¬ (∙ ⊢ t |> (X : *) -0> X)
    Proof by negation.
    Suppose that ∙ ⊢ t |> (X : *) -0> X
    by soundness, we have:
    ∙ ⊢ [t]Γ <| [(X:*) -0> X]Γ which is
    ∙ ⊢ [t]Γ <| ∀ X:*. X
    by consistency of Cedille1 we derive a contradiction

