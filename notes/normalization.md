
# Translation Functions
note that the kind fragment is unchanged, so V is exactly the same as the standard translation for CC to Fω

## Translation of Kinds
    V(□) = *
    V(*) = *
    V((x:A) -> B) =
        V(A) -> V(B) if A is a kind
        V(B)         otherwise

## Translation of Γ-constructors (CC-fragment)
    ⟦□⟧Γ = 0
    ⟦*⟧Γ = 0
    ⟦x⟧Γ = x
    ⟦(x:A) -> B⟧Γ =
        (x:V(A)) -> ⟦A⟧Γ -> ⟦B⟧Γ,x:A if A is a kind
        (x:⟦A⟧Γ) -> ⟦B⟧Γ,x:A         if A is a Γ-type
    ⟦λ x:A. B⟧Γ =
        λ x:V(A). ⟦B⟧Γ,x:A if A is a kind
        ⟦B⟧Γ               if A is a Γ-type
    ⟦A B⟧ =
        ⟦A⟧Γ ⟦B⟧Γ if B is a Γ-constructor
        ⟦A⟧Γ      if B is a Γ-term
    
    ⟦x:A⟧Γ =
        x:⟦A⟧Γ, w(x):x if A is a Γ-kind
        x:⟦A⟧Γ         if A is a Γ-type
    ⟦Γ⟧ = 0:*, z:(x:*) -> *, ⟦x:A⟧, ⟦y:B⟧,...

## Translation of Γ-constructors (Cedille2-additions)
    ⟦(x:A) => B⟧Γ = (x:⟦A⟧Γ) -> ⟦B⟧Γ,x:A
    ⟦(x:A) ∩ B⟧ = (X:*) -> ((x:⟦A⟧Γ) -> ⟦B⟧Γ,x:A -> X) -> X
    ⟦t =A s⟧ = (X:*) -> X -> X

    need to extend ⟦Γ⟧ with ⊥:(X:*) -> X
    (Note, this means the model does not preserve consistency)

## Translation of Γ-terms (CC-fragment)
    [*]Γ = c(0)
    [x]Γ =
        w(x) if x is a Γ-type
        x    if x is a Γ-term
    [(x:A) -> B]Γ =
        c(0->0->0) [A]Γ ([B]Γ,x:A [w(x) := c(⟦A⟧Γ)] [x := c(V(A))]) if A is a kind
        c(0->0->0) [A]Γ ([B]Γ,x:A [x := ⟦A⟧Γ] )                     if A is a Γ-type
    [λ x:A. b]Γ =
        (λ y:0 x:V(A) w(x):⟦A⟧Γ. [b]Γ,x:A) [A]Γ if A is a kind, picking y fresh
        (λ y:0 x:⟦A⟧Γ. [b]Γ,x:A) [A]Γ           if A is a Γ-type, picking y fresh
    [A B]Γ =
        [A]Γ ⟦B⟧Γ [B]Γ if B is a Γ-type
        [A]Γ [B]Γ      if B is a Γ-term

    where c(B) =
        z B          if B is a type
        0            if B = *
        λ x:A. c(B') if B = (x:A) -> B'

## Translation of Γ-terms (Cedille2-additions)
    [(x:A) => B]Γ = c(0->0->0) [A]Γ ([B]Γ,x:A [x := ⟦A⟧Γ])
    [Λ x:A. b]Γ = (λ y:0 x:⟦A⟧Γ. [b]Γ,x:A) [A]Γ
    [A -B]Γ = [A]Γ [B]Γ

    [(x:A) ∩ B]Γ = c(0->0->0) [A]Γ ([B]Γ,x:A [x := ⟦A⟧Γ])
    [[t, s]]Γ = Λ X:* f:(⟦A⟧Γ -> ⟦B⟧Γ -> X) -> X. f [t]Γ [s]Γ
    [fst -A -B t]Γ = (λ x:⟦B⟧Γ. [t]Γ [A]Γ (λ x:⟦A⟧Γ y:⟦B⟧Γ. x)) [B]Γ
    [snd -A -B t]Γ = (λ x:⟦A⟧Γ. [t]Γ [B]Γ (λ x:⟦A⟧Γ y:⟦B⟧Γ. y)) [A]Γ

    [t =A s]Γ = c(0->A->A->0) [A]Γ [t]Γ [s]Γ
    [refl -A -t]Γ = (λ X:* t:⟦A⟧Γ. λ Y:* x:Y. x) [A]Γ [t]Γ
    [J -A -P -a -b e r]Γ = (λ _ _ _. [e]Γ ⟦P⟧Γ ([r]Γ [a]Γ)) [A]Γ [P]Γ [b]Γ
    [I -A -P -a -b e]Γ = (λ _ _ _. [e]Γ) [b]Γ [(x:A) ∩ P]Γ [a]Γ
    [δ⊤ -A -a e]Γ = (λ _ _. [e]Γ) [A]Γ [a]Γ
    [δ e]Γ = (λ _. ⊥) [e]Γ
    [[a, b; e]]Γ = (λ _ _. [b]Γ) [a]Γ [e]Γ

# Lemmas

## Substitution for ⟦_⟧ (Lemma 1)
    Let A be a kind of a Γ-constructor. When x:B ∈ Γ and Γ ⊢ b:B then
    1. ⟦A[x := b]⟧Γ = ⟦A⟧Γ [x := ⟦b⟧Γ] if B is a kind
    2. ⟦A[x := b]⟧Γ = ⟦A⟧Γ             if B is a Γ-type

Proof sketch.
    Extension is trivial, standard proof goes through (kind language not extended)

## Preservation of Conversion for ⟦_⟧ (Lemma 2)
    Suppose A and B are kinds or Γ-constructors such that A ≡ B then ⟦A⟧Γ ≡ ⟦B⟧Γ

Proof sketch.
    Because ⟦_⟧ erases dependencies, erasure is a no-op, so ⟦|A|⟧ = ⟦A⟧

## Soundness of ⟦_⟧ (Lemma 3)
    Suppose A is a sort, kind or Γ-type such that Γ ⊢ A : B then ⟦Γ⟧ ⊢ ⟦A⟧Γ : V(B)

Proof sketch.
    Extension is trivial, standard proof goes through (kind language not extended)

## Soundness of [_] (Lemma 4)
    If Γ ⊢ a : A then ⟦Γ⟧ ⊢ [a]Γ : ⟦A⟧Γ

Proof sketch (focusing on additions). By induction on judgement

    Goal: ⟦Γ⟧ ⊢ [(x:A) => B]Γ : [*]Γ
        simplifies to ⟦Γ⟧ ⊢ c(0->0->0) [A]Γ ([B]Γ,x:A [x := ⟦A⟧Γ]) : 0
        simplifies to ⟦Γ⟧ ⊢ z 0 : 0 which is trivially true

    Goal: ⟦Γ⟧ ⊢ [Λ x:A. t] : ⟦(x:A) => B⟧
        simplifies to ⟦Γ⟧ ⊢ (λ y:0 x:⟦A⟧Γ. [b]Γ,x:A) [A]Γ : (x:⟦A⟧Γ) -> ⟦B⟧Γ,x:A
        simplifies to ⟦Γ⟧ ⊢ λ x. [b]Γ,x:A : (x:⟦A⟧Γ) -> ⟦B⟧Γ,x:A
    By lam rule of Fω need only that ⟦Γ,x:A⟧ ⊢ [b]Γ,x:A : ⟦B⟧Γ,x:A
    which holds by IH

    Goal: ⟦Γ⟧ ⊢ [f -a]Γ : ⟦B[x := a]⟧Γ
        simplifies to ⟦Γ⟧ ⊢ [f]Γ [a]Γ : ⟦B⟧Γ (because B cannot be a kind)
    by IH ⟦Γ⟧ ⊢ [f]Γ : (x:⟦A⟧Γ) -> ⟦B⟧Γ,x:A and ⟦Γ⟧ ⊢ [a]Γ : ⟦A⟧Γ
    finished by app rule of Fω

    Goal: ⟦Γ⟧ ⊢ [(x:A) ∩ B]Γ : ⟦*⟧Γ
        simplifies to ⟦Γ⟧ ⊢ c(0->0->0) [A]Γ ([B]Γ,x:A [x := ⟦A⟧Γ]) : 0
        simplifies to ⟦Γ⟧ ⊢ z 0 : 0 which is trivially true
    
    Goal: ⟦Γ⟧ ⊢ [[t,s]]Γ : ⟦(x:A) ∩ B⟧Γ
        simplifies to ⟦Γ⟧ ⊢
            Λ X:* f:(⟦A⟧Γ -> ⟦B⟧Γ -> X) -> X. f [t]Γ [s]Γ
            : (X:*) -> ((x:⟦A⟧Γ) -> ⟦B⟧Γ,x:A -> X) -> X
    by IH [t] : ⟦A⟧ and [s] : ⟦B⟧, by function rules of Fω goal is finished

    Goal: ⟦Γ⟧ ⊢ [fst -A -B t]Γ : ⟦A⟧Γ
        simplifies to ⟦Γ⟧ ⊢ (λ x:⟦B⟧Γ. [t]Γ [A]Γ (λ x:⟦A⟧Γ y:⟦B⟧Γ. x)) [B]Γ : ⟦A⟧Γ
        simplifies to ⟦Γ⟧ ⊢ [t]Γ [A]Γ (λ x:⟦A⟧Γ y:⟦B⟧Γ. x) : ⟦A⟧Γ
    by IH [t]Γ : (X:*) -> ((x:⟦A⟧Γ) -> ⟦B⟧Γ,x:A -> X) -> X
    finished by app/fun rules of Fω

    Goal: ⟦Γ⟧ ⊢ [t =A s]Γ : ⟦*⟧Γ
        simplifies to ⟦Γ⟧ ⊢ c(0->A->A->0) [A]Γ [t]Γ [s]Γ : 0
        simplifies to ⟦Γ⟧ ⊢ z 0 : 0 which is trivially true

    Goal: ⟦Γ⟧ ⊢ [refl -A -t]Γ : ⟦t =A t⟧Γ
        simplifies to ⟦Γ⟧ ⊢ (λ X:* t:⟦A⟧Γ. λ Y:* x:Y. x) [A]Γ [t]Γ : (X:*) -> X -> X
        trivial

    Goal: ⟦Γ⟧ ⊢ [J -A -P -a -b e r]Γ : ⟦P a b e⟧Γ
        simplifies to ⟦Γ⟧ ⊢ (λ _ _. [e]Γ ⟦P⟧Γ ([r]Γ [a]Γ)) [A]Γ [b]Γ : ⟦P⟧Γ
        simplifies to ⟦Γ⟧ ⊢ [e]Γ ⟦P⟧Γ ([r]Γ [a]Γ) : ⟦P⟧Γ
    by IH [e] : (X:*) -> X -> X, [r]Γ (x:⟦A⟧Γ) -> ⟦P⟧Γ,x:A, [a]Γ : ⟦A⟧Γ
    by app rule of Fω goal is finished
    
    Goal: ⟦Γ⟧ ⊢ [I -A -P -a -b e]Γ : ⟦a =(x:A∩P) b⟧Γ
        simplifies to ⟦Γ⟧ ⊢ (λ _ _ _. [e]Γ) [b]Γ [(x:A) ∩ P]Γ [a]Γ : (X:*) -> X -> X
        simplifies to ⟦Γ⟧ ⊢ [e]Γ : (X:*) -> X -> X
    immediate by IH

    Goal: ⟦Γ⟧ ⊢ [δ⊤ -A -a e]Γ : ⟦(B:*) -> B -> B⟧Γ
        simplifies to ⟦Γ⟧ ⊢ (λ _ _. [e]Γ) [A]Γ [a]Γ : (B:*) -> B -> B
        simplifies to ⟦Γ⟧ ⊢ [e]Γ : (B:*) -> B -> B
    immediate by IH

    Goal: ⟦Γ⟧ ⊢ [δ e]Γ : [(B:*) -> B]Γ
        simplifies to ⟦Γ⟧ ⊢ (λ _. ⊥) [e]Γ : (B:*) -> B
        simplifies to ⟦Γ⟧ ⊢ ⊥ : (B:*) -> B
    trivially true

    Goal: ⟦Γ⟧ ⊢ [[a, b; e]] : [(x:A) ∩ B]Γ
        simplifies to ⟦Γ⟧ ⊢ (λ _ _. [b]Γ) [a]Γ [e]Γ : [(x:A) ∩ B]Γ
        reduces to ⟦Γ⟧ ⊢ [b]Γ : [(x:A) ∩ B]Γ
    which holds by IH

## Substitution for [_] (Lemma 5)
    Suppose Γ ⊢ a : A and (x:B) ∈ Γ then
    1. [a[x := b]]Γ = [a]Γ [w(x) := [b]Γ] [x := ⟦b⟧Γ] if B is a kind and b is a Γ-type
    2. [a[x := b]]Γ = [a]Γ [x := [b]Γ]                if B is a Γ-type and b is a Γ-term

## Preservation of Reduction for [_] (Lemma 6)
    Suppose Γ ⊢ a : A and a -β> a' then [a]Γ -β>+ [a']Γ (where -β>+ is at least one step)

Proof sketch

    Goal: [J -A -P -a -a (refl -A -a) r]Γ -β>+ [r -a]Γ
        simplifies to (λ _ _. [refl -A -a]Γ ⟦P⟧Γ ([r]Γ [a]Γ)) [A]Γ [a]Γ -β>+ [r]Γ [a]Γ
        reduces to [refl -A -a]Γ ⟦P⟧Γ ([r]Γ [a]Γ) -β>* [r]Γ [a]Γ
        reduces to (λ X:* t:⟦A⟧Γ. λ Y:* x:Y. x) [A]Γ [t]Γ ⟦P⟧Γ ([r]Γ [a]Γ) -β>* [r]Γ [a]Γ
        reduces to (λ Y x. x) ⟦P⟧Γ ([r]Γ [a]Γ) -β>* [r]Γ [a]Γ
        reduces to [r]Γ [a]Γ -β>* [r]Γ [a]Γ
    Have: Γ ⊢ J -A -P -a -a (refl -A -a) : P a a (refl -A -a)

    Goal : [I -A -P -a -a (refl -A -(fst -A -P a))]Γ -β>+ [refl -((x:A) ∩ P) -a]Γ
        simplifies to (λ _ _ _. [refl -A -(fst -A -P a)]Γ) [b]Γ [(x:A) ∩ P]Γ [a]Γ
            -β>+ (λ _ _. λ Y:* x:Y. x) [((x:A) ∩ P)]Γ [a]Γ
    Need to show that [refl -A -(fst -A -P a)]Γ -β>* λ Y x. x
        simplifies to (λ X t Y x. x) [A]Γ [fst -A -P a]Γ -β>* λ Y x. x
        reduces to λ Y x. x -β>* λ Y x. x

    Goal: [[a, b; e]]Γ -β>+ [b]Γ
        simplifies to (λ _ _. [b]Γ) [a]Γ [e]Γ -β>+ [b]Γ
        reduces to [b]Γ -β>* [b]Γ
    holds trivially

    Congruence rules will hold as long as every subterm of [t]Γ appears intrepreted in the resultkng expression

    Goal: [I -A -P -a -b e]Γ -β>+ [I -A -P' -a -b e]Γ
        simplifies to (λ _ _ _. [e]Γ) [b]Γ [(x:A) ∩ P]Γ [a]Γ
            -β>+ (λ _ _ _. [e]Γ) [b]Γ [(x:A) ∩ P']Γ [a]Γ
    Need to show that [(x:A) ∩ P]Γ -β>+ [(x:A) ∩ P']Γ
        simplifies to c(0->0->0) [A]Γ ([P]Γ,x:A [x := ⟦A⟧Γ])
            -β>+ c(0->0->0) [A]Γ ([P']Γ,x:A [x := ⟦A⟧Γ])
    Need to show that [P]Γ -β>+ [P']Γ
    but this is immediate from IH

# Theorem
    If Γ ⊢ a : A then a is strongly normalizing

Proof.
    Let f be any arbitrary normalization strategy.
    Because Fω terms are a subset of Cedille2 terms, f may be used to reduce Fω terms.
    Let g be f with an explicit gas input, stopping reduction when gas is empty
    Let h be f with an explicit gas output, returning however much gas was used

    By strong normalization of Fω we know that f, g, and h are well-defined on Fω terms
    Note that g is always well-defined for any syntax and reduction relation
    Let a', u = h([a]Γ) with u the gas output
    By Lemma 6, we know that f(a) must normalize in fewer or exactly many steps as h([a]Γ)
    Therefore, g(a, u) = a'