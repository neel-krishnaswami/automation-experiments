# Unification under a mixed prefix, for first-order terms

## Grammar

t ::= a | f(t1, t2) | c | X[ρ]

Γ ::= · | Γ, a

Θ ::= · | Θ, X:[Γ] 

σ ::= · | σ, t/X

i, j, ρ ::= · | ρ, x/y 

**Convention.** Object contexts `Γ` and metavariable contexts `Θ` are assumed *duplicate-free*: each object variable name appears in `Γ` at most once, and each metavariable name appears in `Θ` at most once. Metavariable contexts `Θ` are interpreted *up to permutation of entries* — i.e. as finite maps from metavariable names to dependency contexts. Pattern judgments such as `Θ ≡ Θ', X:[Γ_X]` and `Θ ≡ Θ', X:[Γ_X], Y:[Γ_Y]` are read modulo this permutation.


## Context lookup: x ∈ Γ

—————————  InHere
x ∈ Γ, x


x ∈ Γ
—————————  InThere
x ∈ Γ, y

## Removing metavariables: Θ₀ - X ≡ Θ₁ 

———————————
Θ,X:[Γ] - X ≡ Θ


X ≠ Y   Θ₀ - X ≡ Θ₁
———————————————————————————
(Θ₀,Y:[Γ]) - X ≡ (Θ₁,Y:[Γ])


## Removing variables: Γ₀ - a ≡ Γ₁ 

———————————
Γ,a - a ≡ Γ


a ≠ b   Γ₀ - a ≡ Γ₁
—————————————————————
(Γ₀,b) - a ≡ (Γ₁,b)


1. If Γ₀ - a ≡ Γ₁ then a ∈ Γ₀
2. (Membership after removal.) If Γ₀ - a ≡ Γ₁ and b ∈ Γ₁ then b ∈ Γ₀ and b ≠ a.
3. (Swap of removals.) If Γ - a₁ ≡ Γ_1 and Γ_1 - a₂ ≡ Γ_{12} with a₁ ≠ a₂, then there exists Γ_2 such that Γ - a₂ ≡ Γ_2 and Γ_2 - a₁ ≡ Γ_{12}.


## Removing contexts: Γ - Γ' ≡ Γ'' 

—————————
Γ - · ≡ Γ


Γ₀ - a ≡ Γ₁   Γ₁ - Γ' ≡ Γ₂
——————————————————————————
Γ₀ - (Γ', a) ≡ Γ₂ 


## Subcontext: Γ ⊆ Γ'

——————  SubCtxNil
· ⊆ Γ


Γ ⊆ Γ'
——————————————  SubCtxCons
Γ, x ⊆ Γ', x


Γ ⊆ Γ'
——————————————  SubCtxSkip
Γ ⊆ Γ', x


1. Γ ⊆ Γ (reflexivity)
2. If Γ ⊆ Γ' and Γ' ⊆ Γ'' then Γ ⊆ Γ'' (transitivity)
3. If Γ ⊆ Γ' and a ∈ Γ then a ∈ Γ'
4. If Γ₀ - a ≡ Γ₁ then Γ₁ ⊆ Γ₀


## Renaming well-formedness: Γ ⊢ ρ : Γ'

——————————
Γ ⊢ · : ·


Γ₀ - a ≡ Γ₁    Γ₁ ⊢ ρ : Γ'
————————————————————————————
Γ₀ ⊢ (ρ, a/x) : Γ',x 

1. (Codomain reweakening.) If Γ ⊢ ρ : Γ' and y ∉ Γ then (Γ, y) ⊢ ρ : Γ'.
2. (Linearity inversion.) If Γ ⊢ ρ : Γ' and y ∈ Γ' with ρ(y) = b, then there exist Γ_mid and ρ_y such that Γ - b ≡ Γ_mid, Γ' - y ≡ Γ'_y, Γ_mid ⊢ ρ_y : Γ'_y, and ρ agrees with ρ_y on Γ' \ {y}.


### Renaming variables: ρ(x) = y 

(ρ, y/x)(z) = y     when x = z
(ρ, y/x)(z) = ρ(z)  when x ≠ z 

1. If Γ ⊢ ρ : Γ' and x ∈ Γ' then ρ(x) ∈ Γ 


### Identity renaming id(Γ) = ρ

id(·) = ·
id(Γ,x) = id(Γ), x/x 

1. Γ ⊢ id(Γ) : Γ 


### Composition of renamings (ρ; ρ')

ρ; · = · 
ρ; (ρ', y/x) = ((ρ; ρ'), ρ(y)/x) 

1. If Γ ⊢ ρ : Γ' and Γ' ⊢ ρ' : Γ'' then Γ ⊢ ρ;ρ' : Γ''
2. (Lookup of composition.) (ρ; ρ')(x) = ρ(ρ'(x)) whenever ρ'(x) is defined.
3. (Left identity.) If Γ ⊢ ρ : Γ' then id(Γ); ρ = ρ.
4. (Right identity.) If Γ ⊢ ρ : Γ' then ρ; id(Γ') = ρ.
5. (Associativity.) (ρ₁; ρ₂); ρ₃ = ρ₁; (ρ₂; ρ₃).

### Renaming terms: [ρ]t = t' 

[ρ]a         = ρ(a)
[ρ]f(t1, t2) = f([ρ]t1, [ρ]t2)
[ρ]c         = c 
[ρ] (X[ρ'])  = X[ρ;ρ']


1. If Θ; Γ' ⊢ t and Γ ⊢ ρ : Γ' then Θ; Γ ⊢ [ρ]t
2. If Θ; Γ ⊢ t   then [id(Γ)]t = t 
3. If Γ ⊢ ρ : Γ' and Γ' ⊢ ρ' : Γ'' and Θ; Γ'' ⊢ t then [ρ] [ρ'] t = [ρ;ρ']t 

### Inverting renamings: ρ⁻¹ = ρ'

range(·)      = ·
range(ρ, x/y) = range(ρ), x 

(·)⁻¹      = ·
(ρ, y/x)⁻¹ = ρ⁻¹, x/y

1. If Γ ⊢ ρ : Γ' then Γ' ⊢ ρ⁻¹ : range(ρ) and range(ρ) ⊆ Γ
2. (Range-recast.) If Γ ⊢ ρ : Γ' then range(ρ) ⊢ ρ : Γ'.
3. (Inverse lookup.) If Γ ⊢ ρ : Γ' and ρ(x) = a then ρ⁻¹(a) = x.
4. (Round-trip.) If Γ ⊢ ρ : Γ' then ρ⁻¹; ρ = id(Γ') and ρ; ρ⁻¹ = id(range(ρ)).


## Term well-formedness: Θ; Γ ⊢ t 

a ∈ Γ
——————————  WfVar
Θ; Γ ⊢ a 


——————————  WfCon
Θ; Γ ⊢ c 


Θ; Γ ⊢ t1  Θ; Γ ⊢ t2
——————————————————————  WfFun
Θ; Γ ⊢ f(t1, t2)


X:[Γ'] ∈ Θ   Γ ⊢ ρ : Γ'
————————————————————————  WfMeta
Θ; Γ ⊢ X[ρ]


### Strengthening 

fv(a)         = {a}
fv(f(t₁, t₂)) = fv(t₁) ∪ fv(t₂) 
fv(c)         = ∅
fv(X[ρ])      = list-to-set(range(ρ))

1. (Strengthening.) If Θ; Γ ⊢ t then there exists a duplicate-free Γ₀ ⊆ Γ whose elements equal fv(t) (as a set), and Θ; Γ₀ ⊢ t.


## Metaweakening: Θ ⊇ Θ'

——————  WkNil
· ⊇ ·


Θ ⊇ Θ'
—————————————————————  WkCons
Θ, X:[Γ] ⊇ Θ', X:[Γ]


Θ ⊇ Θ'
———————————————  WkSkip
Θ, X:[Γ] ⊇ Θ'


1. If  Θ ⊇ Θ' and Θ'; Γ ⊢ t then Θ; Γ ⊢ t
2. (Reflexivity.) Θ ⊇ Θ.
3. (Transitivity.) If Θ ⊇ Θ' and Θ' ⊇ Θ'' then Θ ⊇ Θ''.
4. (Preserves membership.) If Θ ⊇ Θ' and X:[Γ] ∈ Θ' then X:[Γ] ∈ Θ.


## Metasubstitution: Θ ⊢ σ : Θ'

———————————  SubNil
Θ ⊢ · : ·


Θ ⊢ σ : Θ'  Θ; Γ ⊢ t
———————————————————————————  SubCons
Θ ⊢ (σ, t/X) : (Θ', X:[Γ])


1. If Θ ⊇ Θ' and Θ' ⊢ σ : Θ'' then Θ ⊢ σ : Θ'' 


#### Lookup and Application

σ(X) = t 
[σ]t = t'

(σ, t/X)(Z) = t     when Z = X 
(σ, t/X)(Z) = σ(Z)  when Z ≠ X

[σ]a         = a 
[σ]c         = c
[σ]f(t1, t2) = f([σ]t1, [σ]t2)
[σ] (X[ρ])   = [ρ] (σ(X))


1. If Θ ⊢ σ : Θ' and X:[Γ] ∈ Θ', then Θ; Γ ⊢ σ(X)
2. If Θ ⊢ σ : Θ' and Θ'; Γ ⊢ t, then Θ; Γ ⊢ [σ]t
3. (σ-ρ commutation.) [σ]([ρ]t) = [ρ]([σ]t).


#### Identity

id(·)        = ·
id(Θ, X:[Γ]) = id(Θ), X[id(Γ)]/X


1. Θ ⊢ id(Θ) : Θ
2. If Θ; Γ ⊢ t then [id(Θ)]t = t
3. (Identity lookup.) If X:[Γ] ∈ Θ then id(Θ)(X) = X[id(Γ)].

#### Composition 

σ; σ' = σ'' 

σ; · = · 
σ; (σ', t/X) = (σ; σ'), [σ]t/X 

1. If Θ ⊢ σ : Θ' and Θ' ⊢ σ' : Θ'' then Θ ⊢ σ; σ' : Θ'' 
2. [σ] ([σ']t)  = [σ; σ']t
3. (Lookup of composition.) (σ; σ')(X) = [σ](σ'(X)) whenever σ'(X) is defined.
4. (Left identity.) If Θ ⊢ σ : Θ' then id(Θ); σ = σ.
5. (Right identity.) If Θ ⊢ σ : Θ' then σ; id(Θ') = σ.
6. (Associativity.) (σ₁; σ₂); σ₃ = σ₁; (σ₂; σ₃).


## Unification: Θ; Γ ⊢ t1 = t2 ↝ σ : Θ'

### Find a variable in the domain of ρ mapping to y: ρ|y ≡ ρ', y/x     ρ|y ≡ ⊥

——————————
·|y ≡ ⊥


y = z 
———————————————————
(ρ, z/x)|y ≡ ρ, z/x


y ≠ z        ρ|y ≡ ρ', y/a
————————————————————————————
(ρ, z/x)|y ≡ (ρ', z/x), y/a 


y ≠ z     ρ|y ≡ ⊥
——————————————————
(ρ, z/x)|y ≡ ⊥



#### Pushout: Γ ⊢ ρ₁ ⊔ ρ₂ = p₁ ; p₂ : Γ₃

——————————————————————— PushNilL
Γ ⊢ · ⊔ ρ₂ = ·; · : ·


——————————————————————— PushNilR
Γ ⊢ ρ₁ ⊔ · = ·; · : ·


ρ₂|y ≡ ρ'₂, y/z 
Γ ⊢ ρ₁ ⊔ ρ'₂ = i₁; i₂ : Γ' 
———————————————————————————————————————————————————— PushConsVar
Γ ⊢ (ρ₁, y/x) ⊔ ρ₂ = (i₁, x/y); (i₂, z/y) : (Γ', y)


ρ₂|y ≡ ⊥
Γ ⊢ ρ₁ ⊔ ρ₂ = p₁; p₂ : Γ' 
———————————————————————————————————————————————————— PushConsSkip 
Γ ⊢ (ρ₁, y/x) ⊔ ρ₂ = p₁; p₂ : Γ'


If Γ ⊢ ρ₁ : Γ₁ and Γ ⊢ ρ₂ : Γ₂ and Γ ⊢ ρ₁ ⊔ ρ₂ = i₁; i₂ : Γ' then 
1. Γ₁ ⊢ i₁ : Γ' and Γ₂ ⊢ i₂ : Γ' 
2. ρ₁; i₁ = ρ₂; i₂ 
3. For all Γ₁ ⊢ q₁ : Δ and Γ₂ ⊢ q₂ : Δ such that ρ₁;q₁ = ρ₂;q₂, 
   there exists a ρ' such that Γ' ⊢ ρ' : Δ and q₁ = i₁; ρ' and q₂ = i₂; ρ'
4. (Range characterization.) For x ∈ Γ₁: x ∈ range(i₁) iff ρ₁(x) ∈ range(ρ₂).
   For z ∈ Γ₂: z ∈ range(i₂) iff ρ₂(z) ∈ range(ρ₁).
5. (Term factorization.) For all Θ; Γ₁ ⊢ u₁ and Θ; Γ₂ ⊢ u₂ such that [ρ₁]u₁ = [ρ₂]u₂,
   there exists Θ; Γ' ⊢ u' such that [i₁]u' = u₁ and [i₂]u' = u₂.


#### Coequalizer: Γ ⊢ ρ₁ • ρ₂ = i : Γ'

————————————————————— CoeqNil
Γ ⊢ · • · = · : ·


Γ ⊢ ρ₁ • ρ₂ = i : Γ'
————————————————————————————————————————————————— CoeqConsOk
Γ ⊢ (ρ₁, y/x) • (ρ₂, y/x) = (i, x/y) : Γ', y


Γ ⊢ ρ₁ • ρ₂ = i : Γ'     y ≠ z 
———————————————————————————————————————————————— CoeqConsSkip
Γ ⊢ (ρ₁, y/x) • (ρ₂, z/x) = i  : Γ'



If Γ ⊢ ρ₁ : Γ'  and Γ ⊢ ρ₂ : Γ' and Γ ⊢ ρ₁ • ρ₂ = i : Γ'' then
1. Γ' ⊢ i : Γ'' 
2. ρ₁; i = ρ₂; i 
3. If Γ' ⊢ j : Δ and ρ₁;j = ρ₂;j then there is a Γ'' ⊢ ρ' : Δ such that j = i; ρ'
4. (Range characterization.) For x ∈ Γ': x ∈ range(i) iff ρ₁(x) = ρ₂(x).
5. (Term factorization.) For all Θ; Γ' ⊢ u such that [ρ₁]u = [ρ₂]u,
   there exists Θ; Γ'' ⊢ u' such that [i]u' = u.


#### The Unification Algorithm 


——————————————————————————  UnVar
Θ; Γ ⊢ a = a ↝ id(Θ) : Θ


——————————————————————————  UnCon
Θ; Γ ⊢ c = c ↝ id(Θ) : Θ


Θ; Γ ⊢ t1 = t1' ↝ σ : Θ'    Θ'; Γ ⊢ [σ]t2 = [σ]t2' ↝ σ' : Θ''
———————————————————————————————————————————————————————————————  UnFun
Θ; Γ ⊢ f(t1, t2) = f(t1', t2') ↝ σ'; σ : Θ''


Θ - X ≡ Θ' 
Z∉Θ'
Γ ⊢ ρ₁ • ρ₂ = i : Γ'
—————————————————————————————————————————————————————  UnMetaSame
Θ; Γ ⊢ X[ρ₁] = X[ρ₂] ↝ (id(Θ'), Z[i]/X) : (Θ', Z:[Γ'])


Θ ≡ Θ', X:[Γ₁], Y:[Γ₂]
Γ ⊢ ρ₁ ⊔ ρ₂ = i₁; i₂ : Γ₃
Z ∉ Θ' 
—————————————————————————————————————————————————————————————————  UnMetaDiff
Θ; Γ ⊢ X[ρ₁] = Y[ρ₂] ↝ (id(Θ'), Z[i₁]/X, Z[i₂]/Y) : (Θ', Z:[Γ₃])


Θ ≡ Θ', X:[Γ']
Γ ⊢ ρ : Γ'
t not a metavariable
Θ'; range(ρ) ⊢ t 
——————————————————————————————————————————  UnMetaTm
Θ; Γ ⊢ X[ρ] = t ↝ (id(Θ'), [ρ⁻¹]t/X) : Θ'


Θ ≡ Θ', X:[Γ']
Γ ⊢ ρ : Γ'
t not a metavariable
Θ'; range(ρ) ⊢ t 
——————————————————————————————————————————  UnTmMeta
Θ; Γ ⊢ t = X[ρ] ↝ (id(Θ'), [ρ⁻¹]t/X) : Θ'


If Θ; Γ ⊢ t1 and Θ; Γ ⊢ t2 and Θ; Γ ⊢ t1 = t2 ↝ σ: Θ' then: 
1. Θ' ⊢ σ : Θ 
2. [σ]t1 = [σ]t2 
3. for all Θ'' ⊢ σ' : Θ such that [σ']t1 = [σ']t2, 
   there exists Θ'' ⊢ σ'' : Θ' such that σ' = σ''; σ 






