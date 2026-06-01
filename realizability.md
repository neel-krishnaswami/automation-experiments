# The realizability topos

# Partial combinatory algebras

These are basically models of the untyped lambda calculus. It consists of a set S 
with a partial binary operator (·) : S × S ⇀ S, along with two elements s,k ∈ A, 
such that: 

1. ∀a,b ∈ S. k a and k a b are defined, and k a b = a 
2. For all a,b ∈ S. s and s a b are defined. 
3. For all a,b,c∈S. s a b c ≃ (a c) (b c)

Note that you can use s and k to define the identity combinator i x = x. 

(where x ≃ y is Kleene equality: either both sides are defined and equal, or both 
sides are undefined). 

We'll take the untyped lambda calculus, quotiented by β, as our PCA. We'll feel free
to add pairs, numbers, and whatever other data structures we want, and we'll assume 
that "dynamic type errors" (like "fst 5") are undefined. 

# Assemblies

An *assembly* is a pair (X, E : X → P⁺(S)), where we write r ⊩ x to mean r ∈ E(x), 
and read this as "r realizes x". 

The definition requires every element of X to be realized by at least one element of S. 

A *morphism of assemblies* f : (X,⊩) → (Y,⊩) is a function f : X → Y, such that there 
exists a realizer r ∈ S, with the property that ∀x ∈ X, r' ∈ S. if r' ⊩ x then r·r' ⊩ f x. 

Example: the integers: 

(ℤ, ⊩) 

r ⊩ n  iff  fst r ⊩ true ∈ Bool and snd r ⊩ n ∈ Nat    when n ≥ 0 
            snd r ⊩ 0 ∈ Nat                             when n = 0 
            fst r ⊩ false ∈ Bool and snd r ⊩ |n| ∈ Nat when n < 0
           

Example: the rational numbers 

We define (ℚ, ⊩) as r ⊩ q, when fst r ⊩ i ∈ Int and  and snd r ⊩ j ∈ Int and q = i/j. 

Notice that in general the same rational can have many realizers. 

* An assembly is a *modest set* when r ⊩ x and r ⊩ y implies that x = y. (i.e., different
  elements of the set do not share realizers)

* A *partitioned assembly* is an assembly where there is exactly one realizer for every 
  element (i.e, E(x) is a singleton). 

# The realizability topos as an ex/lex completion


## Kernel pairs 

Given a function h : A → B, a kernel pair is a pair of functions f,g : Y → A, 
such that (Y, f, g) form a pullback of h with itself: f;h = g;h, and any other
u,v : X → A such that u;h = v;h factor through the kernel pair: there exists a
k : X → Y such that u = k;f and v = k;g. 

In Set, the fiber product of h with itself is:

  Pullback(h,h) = { (a, a') ∈ A × A | h(a) = h(a') } 

with projection p1 = π1, and p2 = π2. So any other kernel pair is isomorphic to this. 


Next, consider the Pullback(p2, p1): 

  Pullback(p2, p1) = { ((a0, a1), (a1', a2)) ∈ Pullback(h,h)² | a1 = a1' ∧ h(a0) = h(a1) ∧ h(a1') = h(a2) }
                   ≃ { ((a0, a1), (a1, a2)) ∈ (A × A)² | h(a0) = h(a1) = h(a2) }

  p1((a0, _), (_, _)) = a0 
  p1((_, _), (_, a1)) = a1 


Note that Pullback(h,h) is an equivalence relation: 

  0. There is a mono in : Pullback(h,h) → A × A 
  1. There is a map refl : A → Pullback(h,h) given by a ↦ (a,a)
  2. There is a map sym : Pullback(h,h) → Pullback(h,h) given by (a1,a2) ↦ (a2, a1)
  3. There eis a map trans : Pullback(p2, p1) ↦ Pullback(h,h) 
      given by ((a0, a1), (a1, a2)) ↦ (a0, a2)




## Exact forks








