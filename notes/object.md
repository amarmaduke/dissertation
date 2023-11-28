
# Object-Proof reduction
    Given Γ ⊢ t : A and t -β> t' then |t| -β>{0,1} |t'|

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

    Goal: |[a, b; e]| -β>* |b|
        simplifies to |a| -β>* |b|
    by hypothesis, we know that |b| = |a| (because the reduction is not possible otherwise)

# Proof-Object reduction
    Given Γ ⊢ t, t' : A and |t| -β> |t'| then
        ∃ k. t' -β>* k /\ |k| = |t'| /\ t -β>+ k

Proof sketch
    Let Γ ⊢ t, t' : A and |t| -β> |t'|
    by induction on t
    
    Case: x, * are impossible because there can be no reduction

    Case: t = (x:U) -> V
        then t' = (x:U') -> V'
        suppose A = *
            then Γ ⊢ U, U' : * and Δ ⊢ V, V' : *
            moreover, |U| -β> |U'| and |V| -β> |V'|
            thus, ∃ k1, k2 such that U' -β>* k1 and |k1| = |U'| and U -β>+ k1
            and V' -β>* k2 and |k2| = |V'| and V -β>+ k2
            pick k = (x:k1) -> k2
            then (x:U') -> V' -β>* (x:k1) -> k2
            and |(x:U') -> V'| = |(x:k1) -> |k2|
            and (x:U') -> V' -β>+ (x:k1) -> k2
        suppose A = □
            similar to above
    
    Case: t = (x:U) => V
        similar to above (all non-redex forming cases will be)

    Case: t = λ x:U. s
        similar to above

    Case: t = Λ x:U. s
        similar to above

    Case: t = f a
        congruence cases are easy, let's focus on f = (λ x:U. s)
        have: Γ ⊢ λ x:U. s : (x:U -> V) and Γ ⊢ a:U
        because |(λ x:U s) a| -β> |t'| we have two possibilities
        1. t' = (λ x:U'. s') a'
        2. t' = s' [x := a']
        focus on (2), pick k = s' [x := a'], done
    

# Strong Normalization of Object Reduction
    Given Γ ⊢ t : A then |t| is strongly normalizing

Proof sketch
    Same upper-bounding argument on gas using the fact that t is strongly normalizing

# Object Conversion
    Given Γ ⊢ t, s : A then |t| =β= |s| iff t ≡ s

