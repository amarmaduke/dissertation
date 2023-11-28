
    for every term `t`, we can transform it into a term with no phi-ctors

    `φ a f e` becomes `(f a)`

    these terms will be strongly normalizing, and their objects will also be strongly normalizing

    Suppose we have a term with no nested phi-ctors

    `φ a f e`, where `a` has no phi-ctors

    what do we know about `f a` versus `a`?
    Computationally they should be contextually equivalent

    `e` must look like `λ t. t z1 ... zn` where `z1 ... zn` can only have `t` as a free variable
    `f` _also_ must look like this
    
    Consider `a x1 ... xn` versus
    `(f a) x1 ... xn` = `(a z1 ... zn) x1 ... xn`





