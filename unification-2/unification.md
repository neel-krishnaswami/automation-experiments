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




## Renaming well-formedness: Γ ⊢ ρ : Γ'

——————————
Γ ⊢ · : ·


Γ₀ - a ≡ Γ₁    Γ₁ ⊢ ρ : Γ'
————————————————————————————
Γ₀ ⊢ (ρ, a/x) : Γ',x 



### Renaming variables: ρ(x) = y 

(ρ, y/x)(z) = y     when x = z
(ρ, y/x)(z) = ρ(z)  when x ≠ z 


### Identity renaming id(Γ) = ρ

id(·) = ·
id(Γ,x) = id(Γ), x/x 



### Composition of renamings (ρ; ρ')

ρ; · = · 
ρ; (ρ', y/x) = ((ρ; ρ'), ρ(y)/x) 


### Renaming terms: [ρ]t = t' 

[ρ]a         = ρ(a)
[ρ]f(t1, t2) = f([ρ]t1, [ρ]t2)
[ρ]c         = c 
[ρ] (X[ρ'])  = X[ρ;ρ']



### Inverting renamings: ρ⁻¹ = ρ'

range(·)      = ·
range(ρ, x/y) = range(ρ), x 

(·)⁻¹      = ·
(ρ, y/x)⁻¹ = ρ⁻¹, x/y

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



## Metaweakening: Θ ⊇ Θ'

——————  WkNil
· ⊇ ·


Θ ⊇ Θ'
—————————————————————  WkCons
Θ, X:[Γ] ⊇ Θ', X:[Γ]


Θ ⊇ Θ'
———————————————  WkSkip
Θ, X:[Γ] ⊇ Θ'




## Metasubstitution: Θ ⊢ σ : Θ'

———————————  SubNil
Θ ⊢ · : ·


Θ ⊢ σ : Θ'  Θ; Γ ⊢ t
———————————————————————————  SubCons
Θ ⊢ (σ, t/X) : (Θ', X:[Γ])




#### Lookup and Application

σ(X) = t 
[σ]t = t'

(σ, t/X)(Z) = t     when Z = X 
(σ, t/X)(Z) = σ(Z)  when Z ≠ X

[σ]a         = a 
[σ]c         = c
[σ]f(t1, t2) = f([σ]t1, [σ]t2)
[σ] (X[ρ])   = [ρ] (σ(X))




#### Identity

id(·)        = ·
id(Θ, X:[Γ]) = id(Θ), X[id(Γ)]/X



#### Composition 

σ; σ' = σ'' 

σ; · = · 
σ; (σ', t/X) = (σ; σ'), [σ]t/X 



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




#### Coequalizer: Γ ⊢ ρ₁ • ρ₂ = i : Γ'

————————————————————— CoeqNil
Γ ⊢ · • · = · : ·


Γ ⊢ ρ₁ • ρ₂ = i : Γ'
————————————————————————————————————————————————— CoeqConsOk
Γ ⊢ (ρ₁, y/x) • (ρ₂, y/x) = (i, x/y) : Γ', y


Γ ⊢ ρ₁ • ρ₂ = i : Γ'     y ≠ z 
———————————————————————————————————————————————— CoeqConsSkip
Γ ⊢ (ρ₁, y/x) • (ρ₂, z/x) = i  : Γ'





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






