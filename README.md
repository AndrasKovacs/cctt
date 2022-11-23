
## cubeval

A small implementation of a cartesian cubical type theory, designed from
group-up with performance in mind. WIP, doesn't work yet. The immediate project
goal is to get the implementation in a testable state and then port over a bunch
of existing cubical benchmarks.

Existing code was written by me (András Kovács), but Anders Mörtberg and Evan
Cavallo have provided significant design input and code review.

There are numerous examples which can't be checked in any existing cubical type
theory implementation, like the infamous original definition of Brunerie's
number. The hope is that we'll be able to check more of these in this
implementation.

I'm publishing this repo and README because people have been asking for
it. However, this repo will be a lot more interesting when it actually works. I
summarize belowthe design. I assume that readers of this README are familiar
with rules of cubical TTs.

### 1. Normalization by evaluation

In vanilla type theories, normalization-by-evaluation (NbE) is the standard
implementation technique. The point is that we need to evaluate terms during
type checking. It's basically just higher-order functional program evaluation,
plus the extra feature of handling free variables which can block computation.
The informal scheme for "deriving" NbE for a theory is the following.

1. Obtain the definition of runtime values: starting from the data type of
   syntactic terms, replace all binders with closures. A closure (in its
   simplest form) contains a syntactic term and a list of runtime values.
   For example, a syntactic `Pi Name Tm Tm`, where the name is bound in the
   second field, becomes `Pi Name Val (List Val, Tm)` in values.
2. Define evaluation, which takes as input a list of values ("environment") and
   a term, and returns a value. Evaluation is usually a standard [eval-apply](https://www.cs.tufts.edu/comp/150FP/archive/simon-peyton-jones/eval-apply-jfp.pdf)
   strategy, where we return a closure when evaluating a binder and apply closures
   in function application. The extra feature is *neutral values*: these are
   values blocked by free variables, e.g. a variable with function type applied
   to some arguments.
3. Define conversion checking, which takes a "fresh variable" and two values as
   input, and returns whether the values are convertible. The assumption is that
   the fresh variable is not free in either of the input values. We recursively
   compare the values, and when there's a closure on both sides, we apply both
   to a fresh variable and continue checking conversion of the results.

There's also *quotation*, which returns a syntactic term from a value, which
also uses fresh variable passing to go under closures. The name *normalization*
in NbE comes from this: normalization of terms can be defined as evaluation
followed by quotation. However, in a minimal type checker, normalization is not
needed, only conversion checking is.

We might have the following informal definitions and types for NbE:

- `Γ` and `Δ` are contexts, i.e. lists of types.
- `Tm Γ` is the set of syntactic terms in `Γ`, of unspecified type. I don't
  specify types for the sake of brevity. `Val Γ` is the set of runtime values
  with free variables in `Γ`.
- `Sub Γ Δ` is the set of parallel term substitutions. `σ : Sub Γ Δ` is a list
  of terms, where the number and types of terms is given by `Δ`, and each term
  may have free variables from `Γ`.
- `Env Γ Δ` is analogous to `Sub Γ Δ`, except that it's a list of values.
- `eval : Env Γ Δ → Tm Δ → Val Γ` is the evaluation function.
- `quote : Val Γ → Tm Γ` is quotation. The implicit `Γ` contains enough
  information for us to get a fresh variable. If we use de Bruijn levels, the
  length of `Γ` definitely does not occur freely in any `Val Γ`. In
  implementations we usually only pass the length info.
- `conv : Val Γ → Val Γ → Bool` is conversion checking, and once again we can
  grab fresh vars.

Again, this scheme is almost the same as standard implementation practices for
functional programming, extended with the handling of neutral values.

In particular, there is a separation of immutable program code, which never
changes during execution, and runtime values which are dynamically created and
garbage collected. This separation makes it possible to choose between different
code representations, such as bytecode, machine code or AST, while leaving
conversion checking logic essentially the same. The only operation that acts on
terms is evaluation. There is no substitution or renaming.

In cubical type theories we don't have this happy situation. Here, *interval
substitution* is an inseparable component of evaluation which seemingly cannot
be eliminated. There is no known abstract machine for cubical TTs which is
substitution-free. In this repo we also don't have such a thing.

For example, *filling operations* in CCTT (Cartesian CTT) require weakening
substitutions on interval variables. These operations may act on *arbitrary*
terms/values at evaluation time, which are not known to be closures. So it's not
enough to have closures, we need unrestricted interval substitutions too.

Runtime values don't support efficient substitution, e.g. the operation

    _[x ↦ _] : Val (Γ, x : A) → Val Γ → Val Γ

which instantiates the last variable to a value in some value. The problematic
part is the substitution of closures: here we have some `Env (Γ, x : A) Δ` and a
`Tm Δ`, so we have to traverse the `Env` and substitute each value therein.
Sadly, if done eagerly, this deeply and recursively copies every value and every
closure within a value. The main reason for the efficiency of vanilla NbE is
*implicit structure sharing* in values, and eager substitution destroys all such
sharing.

So I refine vanilla NbE for CTTs. It does have substitution for values, but the
evils of it are mitigated.

### 2. Cubical NbE

In the CCTT that I'm considering here, terms are in triple contexts:

    ψ;α;Γ ⊢ t : A

- The `ψ` part lists interval vars.
- `α` is a single cofibration; we don't need multiple entries because we can
  extend the context by conjunction.
- `Γ` lists ordinary fibrant vars.

Recalling vanilla NbE, there `Env Γ Δ` can be though of as a semantic context morphism
which interprets each variable.

Analogously, cubical NbE should take as input a semantic context morphism between
`ψ₀;α₀;Γ₀` and `ψ₁;α₁;Γ₁`. What should this be? It consists of

- An interval substitution `σ : Subᴵ ψ₀ ψ₁`.
- A cofibration implication `f : α₀ ⊢ α₁[σ]`.
- A value environment `δ : Env Γ₀ (Γ₁[σ, f])`.

So the explicit type of evaluation would be:

    eval : ∀ ψ₀ α₀ Γ₀ ψ₁ α₁ Γ₁ (σ : Subᴵ ψ₀ ψ₁)(f : α₀ ⊢ α₁[σ])(δ : Env Γ₀ (Γ₁[σ, f]))
           (t : Tm (ψ₁;α₁;Γ₁)) → Val (ψ₀;α₀;Γ₀)

This is a whole bunch of arguments (even ignoring types of terms and values),
but not all of these will be computationally relevant to us. In the implementation
we only pass the following:

    ψ₀, α₀, Γ₀, σ, δ, t

- We only pass ψ₀ as a length. This is the de Bruijn level marking the next fresh interval
  variable. We need fresh interval vars in several cubical computation rules, such as when
  we do weakening substitution.
- We need α₀ for "forcing"; we'll see this later. A faithful representation is passed.
- Γ₀ is passed as a length. No computation rules really require this, but we use it for
  *optimization*: if Γ₀ is empty, we can take some shortcuts.
- σ, δ and `t` are evidently required in evaluation.

We introduce two additional basic operations:

- `sub  : (σ : Subᴵ ψ₀ ψ₀) → Val (ψ₀;α₀;Γ₀) → Val (ψ₁;α₀[σ];Γ₀[σ])`. This is
  interval substitution. However, `sub` is guaranteed to be cheap: it doesn't do
  any deep computation. It simply stores an explicit interval substitution as
  shallowly as possible in values. There are analogous `sub` operations for
  all kinds of semantics constructs besides values.
- `force : ∀ ψ₀ α₀ Γ₀ → Val (ψ₀;α₀;Γ₀) → Val (ψ₀;α₀;Γ₀)`, where `ψ₀ α₀ Γ₀`
  denote the same arguments as before. Forcing computes a value to *head normal
  form*, by pushing interval substitutions down and potentially re-evaluating
  neutral values until we hit a rigid head. We also have forcing for every kind
  of semantic values.

We substitute by `sub`, which is always cheap. Moreover, a `sub` of an explicit
`sub` collapses to a single composed `sub`.

When we have to match on the head form of a value, we force it. Forcing
accumulates explicit `sub`-s as it hits them, so generally we have two versions
of `force` for each semantic value kind: plain forcing and forcing under an
extra `Subᴵ` parameter.

Forcing is cheap on canonical values. Here it just pushes substitutions down one layer
to expose the canonical head. On neutral values however, forcing can trigger arbitrary
computations, because neutrals are not stable under interval substitution. By applying
a substitution we can unblock coercions and compositions.

Moreover, we don't just force neutrals with respect to the action of a
substitution.  We also force them w.r.t. the α₀ cofibration. Why is this needed,
and how can neutrals even be "out of date" w.r.t. cofibrations? It's all because
of the handling of value weakening. In vanilla NbE, a value `Val Γ` can be
implicitly used in `Val (Γ,A)`. Weakening is for free, we don't need to shift
variables or do anything.

In cubical NbE, weakening is *not for free*, because a value under a cofibration
`α` could be further computed under the cofibration `α ∧ β`. But we don't
compute weakening eagerly, in fact we still do implicit weakening. We defer the
cost of weakening until forcing, where we recompute cofibrations and interval
expression under the forcing cofibration.

#### Stability annotations

We don't want to always recompute neutral values on every forcing. Instead, we
add small annotations to neutral values. These annotations can be cheaply
forced, and they tell us if the neutral value would change under the current
forcing. If it wouldn't, we just delay the forcing.

This is inspired by the paper "Normalization for Cubical Type Theory", where
each neutral is annotated by the cofibration which is true when the neutral can
be further computed. A false annotation signifies a neutral which can not be
further computed under any cofibration or interval substitution.

In my implementation, annotations are *not precise*, they are not cofibrations
but simple sets (bitmasks) of interval variables which occur in relevant
positions in a neutral. When forcing, I check whether relevant interval vars
are mapped to distinct vars by forcing. If so, then forcing has no action on
the neutral. This is a sound approximation of the precise stability predicate.

#### Closures vs. values

In semantic values, we generally use closures for binders which are never
inspected in computations rules:

- Path abstraction
- Dependent path type binder
- Ordinary lambda abstraction

We don't use closures when computation rules can "peek under" binders:

- In `coe` types.
- In partial "systems" in `hcom`, `Glue`, `glue` and `unglue`.

The reason is that peeking under closures can be expensive; it can be only
done by instantiating it with a fresh variable. Peeking at plain values only
requires forcing.

Generally speaking, this cubical NbE can be call-by-need or call-by-value in
"ordinary" reductions, and call-by-name in computation triggered by interval
substitution and weakening under cofibrations.

#### Defunctionalization

There's another critical detail, the implementation of closures. In vanilla NbE,
we generally use one of two representations, or rarely, both at the same time:

- Defunctionalization. In the simplest case, this means that a closure is always
  just a pair of an environment and a term. This is often what people mean by
  "closure". But this is a simple specific case of the more general technique of
  [defunctionalization](https://en.wikipedia.org/wiki/Defunctionalization),
  where we convert higher-order functions to a combination of first-order data
  and a generic application function.

- Metalanguage functions (higher-order abstract syntax, "HOAS"). This represents
  closures as `Val -> Val` functions.

The main advantage of HOAS is that we can write metalanguage lambdas *in situ*
to define any number of different closure types. In the most extreme case, we
can compile terms to HOAS, where every binder is represented by a potentially
different metalanguage function. These functions can be in turn compiled to
machine code.

The main disadvantage of HOAS is that we don't have access to the internal code
and data of closures, we can only call them. This pretty much settles that in
cubical evaluation *we have to use defunctionalization*, because interval
substitution has to act on closures.

Defunctionalization is most convenient when we have few different kinds of
closures, like in the vanilla NbE case, where have one kind of closure. If we
have lots of different closures, there's a distance in the implementation code
between the points where we create closures, and the place where we define the
actual application logic for each closure (the "generic apply" function). This
can make code less readable. However, I did not find this problematic at all in
CTT. In the codebase right now there are only six different closures.

### 3. Closed cubical evaluation

In the following, by "closed" I mean Γ₀ is empty in evaluation, i.e. the result
value of evaluation has no free fibrant variables. The result value may still
contain free interval variables and may also depend on a cofibration. This is
not the same "closed" as in vanilla TT, where closed means really closed.

The closed case is interesting because CTTs have *canonicity* properties for
values here. In the CTT of this repo and also in cubical Agda, we have that

- Every closed value is convertible to a canonical value.

In [`cooltt`](https://github.com/RedPRL/cooltt) and
[ABCFHL](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/syntax-and-models-of-cartesian-cubical-type-theory/01B9E98DF997F0861E4BA13A34B72A7D)
this is not the case; instead there's a weaker canonicity property, that every
closed value can be maximally eta-expanded to a system of canonical values.  The
difference comes from the ability to directly define partial values by
elimination of cofibration disjunctions.  In ABCFHL an element of `Bool` can be
defined under `i=1 ∨ i=1` as `[i=1 ↦ true, i=1 ↦ false]`, which is not
canonical, but is a partial system of canonical values. In cubical Agda a
partial `Bool` value is explicitly typed as `Partial i Bool`, so the plain
`Bool` type cannot have partial inhabitants.

If we instead define "closed" to require that the cofibration in the context is
true, then `cooltt` and ABCFHL have the usual canonicity property as well.

However, we need canonicity under arbitrary cofibrations for the optimization
that I'll shortly describe, so it makes sense to disallow unrestricted
elimination of disjunctions.

The CTT in this repo is based on ABCFHL, with two restrictions:

- We can only define partial values as "systems" in `Glue` and `hcom` primitives
- Users can't write cofibration disjunctions. Since users can only write
  disjunctions in system branches, we don't lose any expressive power by
  disallowing them, because a disjunctive system branch can be always expanded
  to two branches. In other words, `[α ∨ β ↦ t]` can be rewritten as `[α ↦ t, β
  ↦ t]`. This may cause code and work duplication, but we gain a dramatic
  simplification of cofibration representation and evaluation.

#### The optimization

First, let's look at the potential sources of expensive computation in cubical
evaluation. We only look at closed evaluation.

First, *interval substitution* can introduce arbitrarily expensive call-by-name
evaluation. But it turns out that there is only *a single* computation rule
which introduces "real" cost: the coercion rule for `Glue`. Every other instance
of interval substitution is actually an interval weakening, and neutral values
are stable under weakening. In other words, if we don't hit `coe Glue`, then
interval substitution has no asymptotic overhead! In that case, all we do is
push around weakenings during forcing with constant cost, and we never recompute
neutrals.

Second, `hcom` for *strict inductive types* is especially badly behaved. Consider
the rule for `Nat` successors:

    hcom r r' Nat [α ↦ suc t] (suc b) ≡ suc (hcom r r' Nat [α ↦ t] b)

Computing this rule requires to peek at *all components* of the system to
check that all of them are `suc`.

- Systems are the only place where we get potentially multi-dimensional objects and thus
  potential size explosions arising from cubical structure.
- `hcom` at strict inductive types is the *only place* where all components of a
  system have to be forced.
- Contrast cubical systems to sum type eliminations in vanilla TT. In the latter
  setting, closed evaluation only forces one branch of a case split.

My optimization yields a closed cubical evaluation which forces at most one
component of each system.

The idea is that we don't have to force system components in strict inductive
`hcom`, because of canonicity: if the base is `suc`, we already know by the
boundary assumptions that all system components are `suc`. We instead have the
rule

    hcom r r' Nat [α ↦ t] (suc b) ≡ suc (hcom r r' Nat [α ↦ pred t] b)

where `pred` is a metatheoretic function which peels off a `suc` from a value.
In general, we can use lazy "projection" functions from strict inductive
constructors.  For lists, we would use `head` and `tail`.

You might wonder about this rule instead in the closed case:

    hcom r r' Nat [α ↦ t] b ≡ b

This works fine. Since `b` is a numeral, all system components are the same
numeral, so `hcom` computes all the way down to `zero`. But we can't do the same
for general parameterized types. For W-types, `sup` branches with a fibrant
function so we can't shortcut through multiple constructors.

So putting everything together, in closed evaluation the only point of
significant overhead is `coe Glue`. Informally speaking, since `coe Glue`
usually comes from univalence: if we don't use univalence, there's no overhead.

In *open* evaluation though, we can't get around the `hcom` computation. As an
optimization tough, we might use *weak* inductive types instead of strict ones,
where `hcom` is a canonical element. A possible strategy: use weak types in open
evaluation, convert to strict types when we know that we only need closed
evaluation or when we specifically want to rely on strict `hcom` computation.

What about only using weak types? Unfortunately, this defeats the purpose of
many of the notorious benchmarks, including the original Brunerie number
definition. If the original Brunerie number used weak inductive integers, I'm
pretty sure that the definition wouldn't compute to a numeral.

#### Laziness vs. strictness

We can fairly freely choose between call-by-need and call-by-value. Function
application works fine with either. If we don't expect many constant functions
then call-by-value is preferable.

There is one place where laziness is essential: in system components, precisely
because of the optimization which allows us to force no more than one component.

### 4. Half-adjoint equivalences

This improvement is due to Evan Cavallo. It should not change evaluation
asymptotics at all, but it seems definitely worth to implement.

The idea is simply to use the half-adjoint definition of equivalences in `Glue`
primitives, instead of the previously used contractible-fibers definition.  See
[HoTT book](https://hott.github.io/book/hott-online-1353-g16a4bfa.pdf) Chapter 4
for details.

To give a short summary for why this makes sense: in the definition of `coe
Glue`, we use the contractibility of fibers of the partial equivalence in
the `Glue` type at one point. This gives us a center of contraction and
a contraction function to the center. However, we only apply the contraction
function to a fiber which has `refl` as path component. If we switch to
half-adjoint equivalences, the coherence component of that gives us precisely
the ability to contract such a `refl` fiber. In more detail, we use this
definition of equivalences:

    isEquiv : (A → B) → U
    isEquiv f :=
        (f⁻¹  : B → A)
      × (linv : ∀ a → a = f⁻¹ (f a))
      × (rinv : ∀ b → f (f⁻¹ b) = b)
      × (coh  : ∀ a →
                PathP i (f (linv a i) = f a) (refl (f a)) (rinv (f a)))

The coh ("coherence") component can be drawn as a square:

                             refl
                f a --------------------- f a
                 |                         |
    f (linv a i) |                         | refl
                 |                         |
           f (f⁻¹ (f a))----------------- f a
                           rinv (f a)

In `coe Glue`, we can choose something of the form `rinv (f a)` as the "center"
fiber and use `coh` to connect a `refl` fiber to it. There are more details
scattered in the notes in this repo. I will tidy them up later at some point,
and write out all rules of the CTT in a document.

Comparing half-adjoint equivalences to contractible fibers:

- `idIsEquiv` becomes trivial
- `isoToEquiv` becomes significantly smaller. This doesn't appear in computation rules but is common in user code.
- `coe Glue` becomes a bit smaller
- `coeIsEquiv` stays roughly the same size
