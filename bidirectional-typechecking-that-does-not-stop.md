# Bidirectional Typechecking That Does Not Stop

I've been implementing a new language, and one of the things I have been
doing is implementing a language server for the first time. Interestingly, this has
changed how I will write bidirectional typecheckers from now on! 

A bidirectional type system is a set of (syntax-directed) rules with a
mode assignment, telling you which bits of the rules are inputs, and
which bits are outputs. This lets you transcribe the rules more or
less directly to a functional program, which halts with an error when
the rule that is supposed to apply, doesn't.

For example, here are some rules for the simply-typed lambda calculus with 
booleans, functions, and n-ary tuples: 

$$
\newcommand{\Rule}[2]{\frac{\displaystyle #1}{\displaystyle #2}}
\newcommand{\judgsyn}[3]{{#1} \vdash {#2} \Rightarrow {#3}}
\newcommand{\judgchk}[3]{{#1} \vdash {#2} \Leftarrow {#3}}
\newcommand{\bnfalt}{\;\;|\;\;}
\newcommand{\ms}[1]{\mathsf{#1}}
\newcommand{\True}{\ms{true}}
\newcommand{\False}{\ms{false}}
\newcommand{\ifte}[3]{\ms{if}\;{#1}\;\ms{then}\;{#2}\;\ms{else}\;{#3}}
\newcommand{\fun}[1]{\lambda {#1}.\,}
\newcommand{\tuple}[2]{\left\langle {#1}_{0}, ..., {#1}_{#2} \right\rangle}
\newcommand{\letv}[2]{\ms{let}\;{#1} = {#2}\;\ms{in}\;}
\newcommand{\lettuple}[4]{\letv{\tuple{#1}{#2}}{#3}{#4}}
$$

$$
\begin{array}{cc}
\Rule{ \ms{b} \in \{\True, \False\} }
     { \judgchk{\Gamma}{\ms{b}}{2} }
	 & 
\Rule{ \judgsyn{\Gamma}{e_1}{2} \qquad
       \judgchk{\Gamma}{e_2}{A} \qquad
       \judgchk{\Gamma}{e_3}{A} }
	 { \judgchk{\Gamma}{\ifte{e_1}{e_2}{e_3}}{A} }
\\[1em]
\Rule{ \judgchk{\Gamma, x:A}{e}{B} }
     { \judgchk{\Gamma}{\fun{x}{e}}{A \to B} }
	 &
\Rule{ \judgsyn{\Gamma}{e_1}{A \to B} \qquad
       \judgchk{\Gamma}{e_2}{A} }
	 { \judgsyn{\Gamma}{e_1\,e_2}{B} }
\\[1em]
\Rule{ \forall i \in [n]. \judgchk{\Gamma}{e_i}{A_i} }
     { \judgchk{\Gamma}{\tuple{e}{n}}{A_1 \times \ldots \times A_n} }
     & 
\Rule{ \judgsyn{\Gamma}{e_1}{A_1 \times \ldots \times A_n} \qquad
       \judgchk{\Gamma, x_1:A_1, \ldots, x_n:A_n}{e_2}{C} 
	 }
     { \judgchk{\Gamma}{\lettuple{x}{n}{e_1}{e_2}}{C} }
\\[1em]
\Rule{ x:A \in \Gamma }
     { \judgsyn{\Gamma}{x}{A} }
	 &
\Rule{ \judgsyn{\Gamma}{e_1}{A} \qquad 
       \judgchk{\Gamma, x:A}{e_2}{C} 
	 }
	 { \judgchk{\Gamma}{\letv{x}{e_1}{e_2}}{C} }
\\[1em]
\Rule{ \judgsyn{\Gamma}{e}{A} \qquad A = C }
     { \judgchk{\Gamma}{e}{C} }
    &
\Rule{ \judgchk{\Gamma}{e}{A} }
     { \judgsyn{\Gamma}{(e:A)}{A} }
\end{array}
$$

Here's some Ocaml that takes an expression language like this, and
then typechecks it, annotating every subexpression with its type. You
can think of it as an implementation of [Conor McBride's *subject* mode](https://pigworker.wordpress.com/2018/08/06/basics-of-bidirectionalism/)
in her approach to bidirectional typechecking. 

She explains the subject mode as you start out with a
possibly-incorrect program, but if typechecking succeeds, then you
have learned that it is actually a well-typed program. I tend to think
of modes as just input and output (albeit possibly interleaved), and I
think of her subject mode as the simplest form of elaboration: you
input an untyped term, and the algorithm outputs a typed term
identical in shape.

To do this, obviously we're going to need a type of types and
expressions, with the expressions having the ability to carry some
extra information on each subterm. This is easy to do with a mutually
recursive datatype, where we have the constructors, and a node
constructor that takes a pair of some info plus a constructor:

```ocaml
type tp = Bool | Arrow of tp * tp | Tuple of tp list 

module Exp = struct
  type var = string

  type 'info exp' = 
    | BLit of bool 
    | If of 'info t * 'info t * 'info t 
    | Lam of var * 'info t 
    | App of 'info t * 'info t 
    | Annot of 'info t * tp 
    | Var of var 
    | Let of var * 'info t * 'info t 
    | Tuple of 'info t list 
    | LetTuple of var list * 'info t * 'info t 

  and 'info t = In of ('info * 'info exp')
```
We will also need some auxilliary functions to get the shape and info, and 
to build terms without too many parentheses. 

```ocaml
  let shape (In(info, e')) = e' 
  let info (In(info, e')) = info 
  let make info e' = In(info, e') 
  let update f e = make (f (info e)) (shape e)
  
  module Mk = struct
    let blit info b = make info (BLit b)
    let if' info e1 e2 e3 = make info (If(e1, e2, e3))
    let lam info x e = make info (Lam(x, e))
    let app info e1 e2 = make info (App(e1, e2))
    let annot info e tp = make info (Annot(e, tp))
    let var info x = make info (Var x)
    let let' info x e1 e2 = make info (Let(x, e1, e2))
    let tuple info es = make info (Tuple es)
    let lettuple info xs e1 e2 = make info (LetTuple(xs, e1, e2))
  end
end
```

Then, we can turn the rules above into a mutually recursive function,
which analyses the shape of the term and applies the appropriate rule
to it. But before we do that, we're going to take on board a useful
idea of Conor's: the idea of a *pattern*.

In the inference rules above, many of the rules look at the shape of a
type -- is it an boolean, a tuple, an arrow?  They all say things like
$A \to B$, where we look at the outermost level, and if it's an arrow,
we bind the domain to $A$ and the codomain to $B$. These shapes are
what Conor calls patterns, and she's able to use them together with
the information flow in the rules to do really impressive things like
[give ultra-generic type safety proofs.](https://www.youtube.com/watch?v=-QUqGYEQZCM)

After I thought about her talk and experimented a bit, I realized that
patterns are an idea well worth making into their own abstraction,
because they can dramatically reduce the control-flow branching in the 
typechecker, and make the code in each clause much more linear and
straight-line. This ends up giving a **big** improvement in readability. 

Below, I give the module `Get`, which has a collection of functions
which takes a type and return an option with the subterms of the type,
depending on whether the corresponding constructor was passed as an
argument. `Get.bool` and `Get.arrow` take a type directly, and
`Get.tuple n` takes an integer `n` and returns a pattern function
succeeding if its argument is a tuple with `n` elements. `Get.eq tp`
takes a type, and returns a pattern function testing if the argument
is equal to `tp`.

```ocaml
module Get : sig
    val bool : tp -> unit option
    val arrow : tp -> (tp * tp) option
    val tuple : int -> tp -> tp list option 
    val eq : tp -> tp -> unit option
  end = 
struct
  let bool tp = 
    let (return, fail, (let+)) = Option.(some, none, bind) in 
    match tp with 
    | Bool -> return () 
    | _ -> fail 

  let arrow tp = 
    let (return, fail, (let+)) = Option.(some, none, bind) in 
    match tp with 
    | Arrow(tp1, tp2) -> return (tp1, tp2)
    | _ -> fail 

  let tuple n tp = 
    let (return, fail, (let+)) = Option.(some, none, bind) in 
    match tp with 
    | Tuple ts when List.length ts = n -> return ts
    | _ -> fail 

  let eq tp1 tp2 = 
    if tp1 = tp2 then Some () else None
end
```

These functions make it easy to write an elaborator, which takes a context, 
a term, and a type (if it's checking), and returns an expression which is
fully annotated with its type. The whole thing lives in the option monad, 
to handle the case where typechecking fails. (In a real implementation you'd
want to use a sum type so that you can return an informative error!)

```ocaml
module ElabFail : sig
    type ctx = (var * tp) list
    val lookup : ctx -> var -> tp option
    val check : ctx -> 'a Exp.t -> tp -> tp Exp.t option
    val synth : ctx -> 'a Exp.t -> tp Exp.t option
  end = 
struct
  open Exp 
```
Contexts are just lists of variables and their types:
```ocaml 
  type ctx = (var * tp) list 

  let lookup ctx x = List.assoc_opt x ctx 
```
The check function takes a context, an expression, and a type, and 
returns an option contain an type-annotated expression if it succeeds. 
IMO, the use of pattern functions makes this really pretty, because all
the shape checking is hidden behind function calls, and each clause is
just a straight-line sequence of checks: 

```ocaml 
  (* check : ctx -> 'a exp -> tp -> tp exp option *)
  let rec check ctx e tp = 
    let (return, fail, (let+)) = Option.(some, none, bind) in 
    match shape e with 
    | BLit b ->
       let+ () = Get.bool tp in (* check that tp = Bool *)	   
       return (Mk.blit tp b)    (* return a type-annotated literal *)
	   
    | Lam(x, e') -> 
       let+ (tp1, tp2) = Get.arrow tp in         (* check that tp is an arrow type tp1 -> tp2 *)
       let+ t = check ((x,tp1) :: ctx) e' tp2 in (* check that x :tp1 |- e' <== tp2 *)
       return (Mk.lam tp x t)                    (* return a type-annotated lambda-term *)
	   
    | If(e1, e2, e3) -> 
       let+ t1 = synth ctx e1 in         (* synthesize a type for e1 *)
       let+ () = Get.bool (info t1) in   (* check that it's a boolean *)
       let+ t2 = check ctx e2 tp in      (* check that e2 <== tp *)
       let+ t3 = check ctx e3 tp in      (* check that e3 <== tp *)
       return (Mk.if' tp t1 t2 t3)       (* return an annotated AST *)
	   
    | Tuple es -> 
       let+ tps = Get.tuple (List.length es) tp in      (* check tp = tp1 * ... * tpn *)
       let+ ts = dist (List.map2 (check ctx) es tps) in (* check that ei <== tpi for all i *)
       return (Mk.tuple tp ts)                          (* build an annotated tuple *) 
	   
    | LetTuple(xs, e1, e2) -> 
       (* Infer a type for e1 *)
       let+ t1 = synth ctx e1 in                            
       (* Check that e1's type is an n-element tuple *)
       let+ tps = Get.tuple (List.length xs) (info t1) in 
       (* If so, check e2 in an extended context *)
       let+ t2 = check (List.combine xs tps @ ctx) e2 tp in
       return (Mk.lettuple tp xs t1 t2)

    | Let(x, e1, e2) -> 
       let+ t1 = synth ctx e1 in 
       let+ t2 = check ((x, info t1) :: ctx) e2 tp in
       return (Mk.let' tp x t1 t2)

    | _ -> 
       (* Infer a type for e *)
       let+ t = synth ctx e in 
       (* Check that it's the same type as we expect *)
       let+ () = Get.eq (info t) tp in
       (* Return the annotated term *)
       return t 

  (* synth : ctx -> 'a exp -> tp exp option *)
  and synth ctx e = 
    let (return, fail, (let+)) = Option.(some, none, bind) in 
    match shape e with 
    | App(e1, e2) -> 
       (* Infer a type for e1 *)
       let+ t1 = synth ctx e1 in 
       (* Check that it's an arrow type *)
       let+ (tp2, tp) = Get.arrow (info t1) in 
       (* Check the argument against the argument type *)
       let+ t2 = check ctx e2 tp2 in 
       (* Return an application typed at the result type *)
       return (Mk.app tp t1 t2)

    | Var x -> 
        (* Lookup the type of the variable *)
        let+ tp = lookup ctx x in
        (* Annotate the variable reference with its type *)
        return (Mk.var tp x)

    | Annot(e, tp) -> 
       (* Check that e has the type tp *)
       let+ t = check ctx e tp in 
       (* Return an annotated term *)
       return (Mk.annot tp t tp)

    | _ -> fail (* We can't infer a type for a checking term *)
end
```

This also works great, until you try to use it to build LSP tooling. Then,
you have an annotated AST with all the type information you could want. You 
can give types to every subterm, show the types of everything in scope, and
all kinds of stuff like that -- until your program fails to typecheck. 

Then you have nothing, because your elaborator hands you an error
instead of an AST.

Obviously, IDE information is at its *most* helpful when your program
is incorrect, because you need that data to help you fix it. So it's
tragically funny to get no feedback when the program is wrong.


Luckily, [Cyrus Omar](https://web.eecs.umich.edu/~comar/) and his
collaborators have spent the last several years thinking about live
programming and IDEs while developing [the Hazel
language](https://hazel.org/), and they have been using bidirectional
typechecking as their workhorse typechecking technique. Their paper,
**[Total Type Error Localization and Recovery with
Holes](https://hazel.org/papers/marking-popl24.pdf), by Eric Zhao,
Raef Maroof, Anand Dukkipati, Andrew Blinn, Zhiyi Pan, and Cyrus Omar,
does a wonderful job explaining this problem and how to fix it.

Basically, their idea was to adapt an idea from gradual typing, the
unknown type $?$, which they use as the "type of incorrect programs". 
Using this type, they can ascribe *every* program a type (even if the
type is just $?$), ensuring that typechecking doesn't have to error-stop. 

The key thing that makes this work is the _compatibility_ relation
from gradual types, which is like an equality relation on types,
except that $?$ is compatible with everything. So the application rule
ends up looking like:

$$
\Rule{\judgsyn{\Gamma}{e_1}{A} \qquad A \equiv_\to B \to C \qquad \judgchk{\Gamma}{e}{B} }
      {\judgsyn{\Gamma}{e_1\,e_2}{C}}
$$

Instead of saying that $A$ has to *equal* $B \to C$, we say that only
that it has to be compatible with an arrow type $B \to C$. 

But you know what the $A \equiv_\to B \to C$ judgement is? **It's an
implementation of patterns as a judgement!** This turns out to be the 
key to making a non-stop implementation of bidirectional typechecking, 
which looks almost the same as the error-stop implementation. 

Eric Zhao and his coauthors permitted $?$ to occur in any subterm of a
type, because that lets them track partial type information. The
simple bidirectional algorithm doesn't do that: we fail as soon as any
part of a type is unknown. So if we want an algorithm that types terms
exactly like the standard one, but just doesn't stop when we hit an
error, we don't need the full machinery needed to allow $?$ anywhere: 
we can just use the option type `tp option` to represent types
which are either fully known or fully unknown.

What this does is let us implement patterns somewhat differently. The
idea is that if we receive a `tp option`, and we want to check if it's
an arrow, we can *unconditionally* return two `tp option`s as the
return. If the input is `Some(Arrow(tp1, tp2))`, we return `(Some tp1, Some tp2)`, 
and in all other cases we return `(None, None)`. Because the rest of our 
algorithm  is expected to handle types being absent/unknown, this isn't 
a problem. 

We will additionally need the ability to reconstruct types from their components. 
If we want to annotate a lambda term, and we knew that the domain and 
codomain were both `None`, we want to annotate it with a `None`. But if
its domain and codomain were `Some tp1` and `Some tp2`, we want to 
annotate it as `Some(Arrow(tp1, tp2))`. 

To do this, we will introduce the `TpView` module: 

```ocaml
module TpView : sig
    type 'a t = { get : tp option -> 'a; put : 'a -> tp option; }
    val bool : unit option t
    val arrow : (tp option * tp option) t
    val tuple : int -> tp option list t
    val eq : tp option -> unit option t
    val is : 'a t -> tp option -> tp option
  end = 
struct
  type 'a t = { 
      get : (tp option -> 'a); 
      put : ('a -> tp option);
    }
```
A `'a TpView.t` is a record containing two fields, one which takes a `tp option`
and returns an `'a`, and one which takes a `'a` and returns a `tp option`. (This
looks a bit like either lenses or prisms, but I haven't been fussed enough to
work out the connection.) Basically, `'a` is the type you deconstruct a type to,
and reconstruct it from. 

So we have a `TpView.bool` item, which has the type `unit option t`. `TpView.bool.get tp`
will return `Some ()` if `tp` is a boolean type, and `None` otherwise. Conversely, 
`TpView.bool.put v` will return `Some Bool` if `v` is `Some()`, and will return `None`
otherwise. 
```ocaml
  let bool = 
    let get tp' = 
      match tp' with 
      | Some Bool -> Some () 
      | _ -> None 
    in
    let put tp' = 
      match tp' with 
      | Some () -> Some Bool
      | None -> None
    in
    {get; put}
```
The `arrow` record has the type `(tp option * tp option) t`, meaning that its `get` field 
returns two subcomponents if it receives a `Some(Arrow(tp1, tp2))` argument, and returns 
`(None, None)` otherwise. 
```ocaml
  let arrow = 
    let get tp' = 
      match tp' with 
      | Some (Arrow(tp1, tp2)) -> (Some tp1, Some tp2)
      | _ -> (None, None)
    in
    let put (tp1', tp2') = 
      match tp1', tp2' with 
      | Some tp1, Some tp2 -> Some (Arrow(tp1, tp2))
      | _, _ -> None 
    in
    {get; put}
```
For `tuple`, we give an extra parameter `n`, which lets `(tuple n).get` check if the argument is a 
tuple of length `n`. Similarly `(tuple n).put tps'` takes a list, and if `tps'` is of length `n` and 
has no `None` entries, we return a `Some (Tuple ...)`, and otherwise return `None`. 
```ocaml
  let tuple n = 
    let get = function
      | Some (Tuple tps) when List.length tps = n -> List.map Option.some tps 
      | _ -> List.init n (fun _ -> None)
    in
    let put tps' = 
      match dist tps' with
      | Some tps when List.length tps = n -> Some (Tuple tps)
      | _ -> None
  in
  {get; put}
```
We can also make equality a view with `eq`, with `eq tp` returning a view that 
returns `Some ()` if `(eq tp).get` is passed `Some tp`, and returns `None` otherwise. 
Conversely, `(eq tp).put` returns `Some tp` if it is passed `Some ()`, and `None` otherwise. 
```ocaml
  let eq (tp' : tp option) = 
    let get = function
      | tp'' when tp' = tp'' -> Some ()
      | _ -> None
    in 
    let put = function
      | Some () -> tp'
      | _ -> None
    in
    {get; put}
```
It is often useful to compose the `get` and `put` parts of a view, because this will yield a 
filter on whether a type fits a pattern or not. That is `arrow.put (arrow.get tp)` will return `None`
if `tp` is not `Some(Arrow(tp1, tp2))`, and will be the identity if it is.
```ocaml
  let is view tp = view.put (view.get tp)
end
```

With this slightly fancier pattern implementation, writing a nonstop
elaborator turns out to be nearly identical to the stopping one:

```ocaml
module ElabNonstop = struct
  open TpView
  open Exp 
```
We change the type of the context to hold `tp option`s instead of `tp`s, because
we want the ability to add variables we know are in scope, but of unknown type, 
to the context: 
```ocaml
  type ctx = (var * tp option) list 
  let lookup ctx x = Option.join (List.assoc_opt x ctx)
```
With that, the rest of the typechecking code is nearly identical to the original 
version. The *complete* list of differences are as follows: 

1. All of the monadic `let+` expressions turn into ordinary `let`-bindings, and all of the
   `return` calls go away. 
2. We write `arrow.get` instead of `Get.arrow`. 
3. In intro forms, we need to use the `is` function to explicitly check the type has the 
   right shape, because we don't immediately fail if a type has the wrong shape. 
4. When synthesizing a checking term, we can invoke `check ctx exp None` instead of 
   failing, to check a term against an unknown type. 

```ocaml
  (* check : ctx -> 'a exp -> tp option -> tp exp option *)
  let rec check ctx e tp = 
    match shape e with 
    | BLit b ->
       Mk.blit (is bool tp) b

    | Lam(x, e') -> 
       let (tp1, tp2) = arrow.get tp in
       let t = check ((x,tp1) :: ctx) e' tp2 in 
       Mk.lam (is arrow tp) x t

    | If(e1, e2, e3) -> 
       let t1 = update (is bool) (synth ctx e1) in 
       let t2 = check ctx e2 tp in
       let t3 = check ctx e3 tp in 
       Mk.if' tp t1 t2 t3

    | Tuple es -> 
       let n = List.length es in 
       let tps = (tuple n).get tp in 
       let ts = List.map2 (check ctx) es tps in 
       Mk.tuple (is (tuple n) tp) ts

    | LetTuple(xs, e1, e2) -> 
       let n = List.length xs in 
       let t1 = synth ctx e1 in 
       let tps = (tuple n).get (info t1) in 
       let t2 = check (List.combine xs tps @ ctx) e2 tp in
       Mk.lettuple tp xs t1 t2 

    | Let(x, e1, e2) -> 
       let t1 = synth ctx e1 in 
       let t2 = check ((x, info t1) :: ctx) e2 tp in
       Mk.let' tp x t1 t2

    | _ -> 
       update (is (eq tp)) (synth ctx e)

  (* synth : ctx -> 'a exp -> tp option exp *)
  and synth ctx e = 
    match shape e with 
    | App(e1, e2) -> 
       let t1 = synth ctx e1 in 
       let (tp2, tp) = arrow.get (info t1) in 
       let t2 = check ctx e2 tp2 in 
       Mk.app tp t1 t2

    | Var x ->
       let tp = lookup ctx x in
       Mk.var tp x 

    | Annot(e, tp) -> 
       let t = check ctx e (Some tp) in 
       Mk.annot (Some tp) t tp

    (* The *only* substantive change -- instead of failing when we are asked to synthesize
	   a type for a checking term, we switch to checking with None as the type argument! *)
    | _ -> check ctx e None 
end
```

This is very satisfying, because as a language designer, you can still write down the 
inference rules you want, and when you transcribe it to code, the shape of the code you
write does not change *at all*. The only difference is that the monad goes away, because
type inference never fails -- in error cases, you get a term annotated with errors. 
(I'm always happy when a monad goes away, because basic, total functions are the best!)

In a real implementation, you generally want to keep position information around, as well 
as other information such as the current context. One thing I have found useful is to 
use OCaml's row polymorphism is to keep an object in the info field, and implement things 
like typecheckers as things which *add* fields to the object there. That way, you can 
extend the information, but existing information is still accessible with a flat
field access like `(info e)#pos`. 

Having the position info plus the type and context info together has made 
it extremely easy to generate useful information for LSP queries. 

Long-term, though, I think that a better design is to annotate syntax
trees with unique ids, and store different kinds of information in
tables mapping ids to information.  The reason for this is that I have a 
hunch that many IDE services actually want to perform *queries* on your
collected information, and if it's in a tabular format, then you can use
Datalog-ish approaches to compute what you want, even if it doesn't arise
as a compositional decoration of the syntax tree. 

An example of this is when you compile pattern matching: one case
expression in the IR might correspond to many different clauses in the
source program. Another example is when you want to do things that
require computing a transitive closure, like identifying dead code (if
a binding is only used in dead code, then it iself is dead, and so on
recursively).

That said, though, you will still want to structure the actual
typechecking code using an explicit pattern abstraction like I just
did.

[All the code in this blog post is here at this gist.](https://gist.github.com/neel-krishnaswami/7241bb1b7bce4275ac9318b6cf8b53cd). Also it's basically untested, so it's surely full of bugs!

