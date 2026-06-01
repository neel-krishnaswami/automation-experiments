1. Take an algebraic theory T. 

2. Construct the free T-algera over X, T(X). 

- for each x, we have var(x) : T(X) 
- if we have t : T(X) and a substitution σ : X → T(Y), you can construct a T(Y) by substituing σ(x) for each var(x) ∈ t. 

This means T(-) has the structure of a monad on Set. 

var : X → T(X) is the unit
subst : T(X) → (X → T(Y)) → T(Y) is the Kleisli lift 


Example 
Theory T is: 
- generators are 0 and + (0 is nullary, + is binary) 
- equations are: 0 is a unit, and + is ACI

  0 + x = x 
  x + 0 = x
  x + y = y + x 
  (x + y) + z = x + (y + z)
  x + x = x 

T(X) are going to be terms given by 

 t ::= 0 | t + t | var(x ∈ X)

quotiented by the above equations

(so T(X) ≃ P^fin(X)) 


Suppose we have monads T and S arising from algebraic theories 

A distributive law is a natural transformation TS ⇒ ST 


——————
If you have theories S and T 

U is a composite theory of S over T 

when (a) U has all the symbols and equations of S and of T 
     (b) every term in U(X) can be rewritten to the form S(T(X))

Example: ring 

S is the free monoid functor
T is the free group functor 

Every ring expression can be written in the form

(a[1,1]·...·x[n,1]) + ... + (a[1,m] · ... · a[n,m])

This follows from the distributive law of addition over multiplication. 















