Here's what I want: 

* MLTT plus:
  0. Types are sets
  1. intuitionistic, impredicative prop (a "resizing axiom") 
  2. function extensionality 
  3. quotients
  4. univalent prop/propositional extensionality (this makes quotients effective!)
  5. unique choice 

Here's what I *don't* care about: 

* Fancy definitional equalities beyond basic beta-eta stuff (or even most etas, 
  honestly). 

* Canonicity: this is actually an overstatement! I am willing to make a reasonable
  effort for canonicity, but 

What I *do* care about: 

* Normalization

* Realizability 

  The philosophy of this type theory is that: 

  1. Don't sacrifice the ability to do actual math for "efficiency"
	 reasons: in particular, don't assume that Prop is irrelevant, because 
	 unique choice is critical! 

  2. If we want to compute,  just pick a realizer for a term. The
	 realizers for propositions actually do matter!  
  

This is basically the internal logic of a topos. To get this, I will introduce a 
a  universe Prop, plus a type hierarchy Type[i]. The plan is to just use Pataraia's 
theorem to  define things like induction-recursion. 

Define u ::= _ | i 

max 

Define Sort(_) = Prop
       Sort(i) = Type[i]

The Type universe: 

   A : Sort(u)   x:A ⊢ B[x] : Type[j]  k = max(i,j)
   —————————————————————————————————————————————————
   Π[u,v]x:A.B[x] : Type[k]


   A : Prop   x:A ⊢ B[x] : Type[i]
   ———————————————————————————————
   Π[_,i]x:A.B[x] : Type[i]


   A : Type[i]   x:A ⊢ B[x] : Prop
   ————————————————————————————————
   Π[i,_]x:A.B[x] : Type[i]


   A : Type[i]   x:A ⊢ B[x] : Type[j]  k = max(i,j)
   —————————————————————————————————————————————————
   Σ[i,j]x:A.B[x] : Type[k]


   A : Prop   x:A ⊢ B[x] : Type[i]
   ———————————————————————————————
   Σ[_,i]x:A.B[x] : Type[i]


   A : Type[i]   x:A ⊢ B[x] : Prop
   ————————————————————————————————
   Σ[i,_]x:A.B[x] : Type[i]



   —————————————————
   Unit[i] : Type[i]


   —————————————————
   Void[i] : Type[i]


   ————————————————
   Nat[i] : Type[i]
   


   A : Type[i]   B : Type[j]  k = max(i,j)
   ——————————————————————————————————————————
   A +[i,j] B : Type[k]


   ———————————————————
   Type[i] : Type[i+1]



   ——————————————————————————————


   a : A 
   —————————————————————————
   nil(a) : Closure(X, a, a)

  
   x : X a b    pf : Closure(X, b, c)
   ————————————————————————————————
   cons(x, pf) : Closure(X, a, c)


   x : X b a    pf : Closure(X, b, c)
   ——————————————————————————————————
   cons'(x, pf) : Closure(X, a, c)



   A : Type[i]    R : A → A → Prop
   ————————————————————————————————
   Quotient(A, R) : Type[i]


   a : A 
   —————————————————————————
   [a] : Quotient(A, R)

  
   pf : Id[Quotient(A,R)] (x, y)
   —————————————————————————————
   eff(pf) : Closure(R, x, y)


   pf : Closure(R, x, y)
   ———————————————————————————————————
   embed(pf) : Id[Quotient(A,R)] (x,y)


The Prop universe: 

   A : Type[i]     pf : (a b : A) → Id[A](a,b)
   ———————————————————————————————————————————
   hprop(A, pf) : Prop 


   A : Type[i]   a : A    b : A
   —————————————————————————————
   Id[A](a,b) : Prop 


   A : Type[i]
   —————————————
   {A} : Prop 


   a : A 
   ————————————————————
   refl a : Id[A](a, a)


   A : Type[i]     x:A ⊢ P[x] : Prop
   ——————————————————————————————————
   Π[i]x:A. P[x] : Prop 


   P : Prop     x:A ⊢ Q[x] : Prop
   ——————————————————————————————————
   Πx:P. Q[x] : Prop 


   P : Prop     x:A ⊢ Q[x] : Prop
   ——————————————————————————————————
   Σx:P. Q[x] : Prop 


Once we have the identity type, we can use it to define heterogenous equality: 

   (e1 : A = e2 : B) ≜ Σpf : A = B. Id[B] (cast(e1, p), e2) 

We can define the logical quantifiers as: 

  * ⊤ as    as {Unit[0]}
  * P ∧ Q   as Σx:P. Q 
  * P → Q   as Πx:P. Q
  * ⊥ as    as {Void[0]}
  * P ∨ Q   as {P +[_,_] Q}
  * ∀x:A. P  as Π[i,_]x:A. P[x]
  * ∃x:A. P  as {Σ[i,_]x:A. P[x]}
  * e1=e2:A  as Id[A] (e1, e2) 


contractible(A) = Πa:A.Πb:A. a=b

We have a distinct universe of propositions, but inhabit it via various term formers,
which include a truncation operator [A], the identity prop (which is now itself a prop)
and the hprop constructor, which turns any contractible type into a proposition itself. 

funext : (f g : (x:A) → B(x)) → 
         ((a b : A) → (pf : Id(a,b)) → (f a : B(a) = g b : B(b)/pf)) → 
         Id[(x:A) → B(x)] (f,g)

choice : contractible(A) → [A] → A 

uprop : (P Q : Prop) → (P → Q) → (Q → P) → Id[Prop] (P,Q)


Conversion: 

The conversion relation is the congruent closure of β-equality. 

x:A ⊢ B : Type[u]
p : Id[A](e1, e2)
e' : [e1/x]B 
—————————————————————————————
cast[x:A.B](p, e') : [e2/x]B






    





