# Type System

    x:T ∈ Γ
    ------- variable
    Γ ⊢ x:T

    --------- axiom
    Γ ⊢ * : □

    Γ ⊢ t:A  Γ ⊢ A:k  A ≡ B
    ----------------------- conversion
    Γ ⊢ t:B

    Γ ⊢ A:*  x:A,Γ ⊢ B:*
    -------------------- Π1
    Γ ⊢ (x:A) -> B : *

    Γ ⊢ A:k  x:A,Γ ⊢ B:*
    -------------------- Π2
    Γ ⊢ (x:A) -> B : □

    Γ ⊢ A:k  x:A,Γ ⊢ B:*
    -------------------- ∀
    Γ ⊢ (x:A) => B : *

    Γ ⊢ (x:A) -> B : k  x:A,Γ ⊢ t:B
    ------------------------------- λ
    Γ ⊢ λ x:A. t : (x:A) -> B

    Γ ⊢ (x:A) => B : k  x:A,Γ ⊢ t:B  x ∉ FV(|t|)
    -------------------------------------------- Λ
    Γ ⊢ Λ x:A. t : (x:A) => B

    Γ ⊢ f : (x:A) -> B  Γ ⊢ a:A
    --------------------------- app1
    Γ ⊢ f a : B[x := a]

    Γ ⊢ f : (x:A) => B  Γ ⊢ a:A
    --------------------------- app2
    Γ ⊢ f -a : B[x := a]

    Γ ⊢ A:*  x:A,Γ ⊢ B:*
    -------------------- ∩
    Γ ⊢ (x:A) ∩ B : *

    Γ ⊢ t:A  Γ ⊢ s:B[x := t]  x:A,Γ ⊢ B:k  t ≡ s
    -------------------------------------------- pair
    Γ ⊢ [t,s] : (x:A) ∩ B

    Γ ⊢ t : (a:A) ∩ B
    ------------------- fst
    Γ ⊢ fst -A -B t : A

    Γ ⊢ t : (a:A) ∩ B
    -------------------------------------- snd
    Γ ⊢ snd -A -B t : B [x := fst -A -B t]

    Γ ⊢ A:*  Γ ⊢ t,s:A
    ------------------ equal
    Γ ⊢ t =A s : *

    Γ ⊢ A:*  Γ ⊢ t:A
    ----------------------- refl
    Γ ⊢ refl -A -t : t =A t
    
    Γ ⊢ A:*  Γ ⊢ a,b:A  Γ ⊢ e : a =A b
    Γ ⊢ P : (x,y:A) -> (e : x =A y) -> *
    Γ ⊢ r : (x:A) => P x x (refl -A -x)
    ------------------------------------ J
    Γ ⊢ J -A -P -a -b e r : P a b e

    Γ ⊢ (x:A) ∩ P : *  Γ ⊢ a,b : (x:A) ∩ P
    Γ ⊢ e : (fst -A -P a) =A (fst -A -P b)
    -------------------------------------- I
    Γ ⊢ I -A -P -a -b e : a =(x:A)∩P b

    Γ ⊢ A:k  Γ ⊢ a:A  Γ ⊢ e : a =A a
    -------------------------------- δ⊤
    Γ ⊢ δ⊤ -A -a e : (B:*) -> B -> B

    Γ ⊢ e : true =Bool false
    ------------------------ δ
    Γ ⊢ δ e : (B:*) -> B

    Γ ⊢ A, B : *  Γ ⊢ a:A  Γ ⊢ b : (x:A) ∩ B
    Γ ⊢ e : (fst -A -B b) =A a
    FV(Γ)∩FV(|b|) ⊆ {a}  FV(Γ)∩FV(|e|) ⊆ {a}
    ---------------------------------------- φ
    Γ ⊢ [a, b; e] : (x:A) ∩ B

# Reduction and Conversion

    (λ x:A. t) s -β> t[x := s]
    (Λ x:A. t) -s -β> t[x := s]
    fst -A -P [t,s] -β> t
    snd -A -P [t,s] -β> s
    J -A -P -a -a (refl -A -a) r -β> r -a
    I -A -P -a -a (refl -A -(fst -A -P a))
        -β> refl -((x:A) ∩ P) -a
    δ⊤ -A -a (refl -A -a) -β> Λ B:*. λ y:B. y
    [a, b; e] -β> b  if |b| = |a|

    + congruence rules

    t ≡ s if and only if ∃ t',s'. t -β>* t' /\ s -β>* s' /\ |t'| = |s'|

# Erasure

    |x| = x
    |*| = *
    |□| = □
    |(x:A) -> B| = (x:|A|) -> |B|
    |(x:A) => B| = (x:|A|) => |B|
    |λ x:A. t| = λ x. |t|
    |Λ x:A. t| = |t|
    |f a| = |f| |a|
    |f -a| = |f|
    |(x:A) ∩ B| = (x:|A|) ∩ |B|
    |[t,s]| = |t|
    |fst -A -B t| = |t|
    |snd -A -B t| = |t|
    |t =A s| = |t| =|A| |s|
    |refl -A -t| = λ x. x
    |J -A -P -a -b e r| = |e| |r|
    |I -A -P -a -b e| = |e|
    |δ⊤ -A -a e| = |e|
    |δ e| = |e|
    |[a, b; e]| = |a|
