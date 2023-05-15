
# Object-Proof reduction
    Given Γ ⊢ t : A and t -β> t' then |t| -β>* |t'|

Proof Sketch: by induction on t -β> t'

    Goal: |(λ x:A. t) s| -β>* |t[x := s]|
        simplifies to (λ x. |t|) |s| -β>* |t|[x := s]
    which holds immediately

    Goal: |(Λ x:A. t) s| -β>* |t[x := s]|
        simplifies to |t| -β>* |t|[x := s]
    by the typing judgement we know that x ∉ FV(|t|)
    so |t|[x := s] = |t|

    Goal: |fst -A -P [t,s]| -β>* |t|
        simplifies to |t| -β>* |t|
    
    Goal: |snd -A -P [t,s]| -β>* |s|
        simplifies to |s| -β>* |s|

    Goal: |J -A -P -a -a (refl -A -a) r| -β>* |r -a|
        simplifies to |refl -A -a| |r| -β>* |r|
        simplifies to (λ x. x) |r| -β>* |r|
        reduces to |r| -β>* |r|

    Goal: |I -A -P -a -a (refl -A -(fst -A -P a))| -β>* |refl -((x:A) ∩ P) -a|
        simplifies to |refl -A -(fst -A -P a)| -β>* λ x. x
        simplifies to λ x. x -β>* λ x. x

    Goal: |δ⊤ -A -a (refl -A -a)| -β>* |Λ B:*. λ y:B. y|
        simplifies to |refl -A -a| -β>* λ x. x
        simplifies to λ x. x -β>* λ x. x

# Proof-Object reduction
    Given Γ ⊢ t, t' : A and |t| -β> |t'| then t -β>+ t'

Proof sketch
    - Erasure of |t| does not remove any standard redexes, so every standard redex in t is mirrored in |t|
    - There may be some sequence of non-standard redexes in t required to contract a standard redex in t
    - Thus, it takes at least one contraction in t to contract the corresponding redex in |t|

# Strong Normalization of Object Reduction
    Given Γ ⊢ t : A then |t| is strongly normalizing

Proof sketch
    Same upper-bounding argument on gas using the fact that t is strongly normalizing

# Object Conversion
    Given Γ ⊢ t, s : A then |t| =β= |s| iff t ≡ s

