
## cubeval

A small implementation of a cartesian cubical type theory, designed from
group-up with performance in mind. WIP, doesn't work yet. The immediate project
goal is to get the implementation in a testable state, and then port a bunch of
existing benchmarks.

There are numerous examples which can't be checked in any existing cubical type
theory implementation, like the infamous original definition of Brunerie's
number. The hope is that we'll be able to check more of these in this implementation.

I'm publishing this repo and README because people have been asking for
it. However, this repo will be a lot more interesting when it actually works. I
summarize below the design. I assume that readers of this README already know
some cubical TT.

### Normalization by evaluation

In vanilla type theories, normalization-by-evaluation (NbE) is the standard
implementation technique. The point is that we need to evaluate terms during
type checking. It's essentially higher-order functional program evaluation,
except that free variables can appear in programs which block all computation.
The basic recipe for implementing NbE:

1. Obtain the definition of runtime values: starting from the data type of
   syntactic terms, replace all binders with closures. A closure (in its
   simplest form) contains a syntactic term and a list of runtime values.
   For example, a syntactic `Pi Name Tm Tm`, where the name is bound in the
   second field, becomes `Pi Name Val (List Val, Tm)` in values.
2. Define evaluation, which takes as input a list of values ("environment") and
   a term, and returns a value. Evaluation is usually a standard eval-apply
   strategy, where we return a closure when evaluating a binder and apply closures
   in function application. The extra feature is *neutral values*: these are
   values blocked by free variables, e.g. a variable with function type applied
   to some arguments.
3. Define conversion checking, which takes a "fresh variable" and two values as
   input, and returns whether the values are convertible. The assumption is that
   the fresh variable is not free in either of the input values. We recursively
   compare the values, and when there's a closure on both sides, we apply both
   to a fresh variable and continue conversion checking on the results.

There's also *quotation*, which return a syntactic term from a value, which also
uses fresh variable passing to go under closures. The name *normalization* in
NbE comes from this: normalization of terms can be defined as evaluation
followed by quotation. However, in a minimal type checker, normalization is not
needed, only conversion checking is.

We might have the following informal definitions and types for NbE:

- `Γ` and `Δ` are contexts, i.e. lists of types.
- `Tm Γ` is the set of syntactic terms in `Γ`, of unspecified type. I don't
  specify types for the sake of brevity. `Val Γ` is the set of runtime values
  with free variables in `Γ`.
- `Sub Γ Δ` is the set of parallel term substitutions. `σ : Sub Γ Δ` is a
  list of terms, where the number and types of terms is given by `Δ`, and
  each term may have free variables from `Γ`.
- `Env Γ Δ` is analogous to `Sub Γ Δ`, except that it's a list of values.
- `eval : Env Γ Δ → Tm Δ → Val Γ` is the evaluation function.
- `quote : Val Γ → Tm Γ` is quotation. The implicit `Γ` contains enough information
  for us to get a fresh variable. If we use de Bruijn levels, the length of `Γ` definitely
  does not occur freely in any `Val Γ`. In implementations we usually only pass the length info.
- `conv : Val Γ → Val Γ → Bool` is conversion checking, and once again we can grab fresh vars.

This scheme is almost the same as standard implementation practices for
functional programming, extended with the handling of neutral values.

In particular, there is a separation of program code, which is immutable and
never created or modified during execution, and runtime values which are
dynamically created and garbage collected. This separation makes it possible to
choose between different code representations, such as bytecode, machine code or
AST, while leaving conversion checking logic essentially the same. The only
operation that acts on terms is evaluation. There is no substitution or
renaming.

In cubical type theories we don't have this happy situation. Here, *interval
substitution* is an inseparable component of evaluation which seemingly cannot
be eliminated. There is no known abstract machine for cubical TTs which is
substitution-free. In this repo we also don't have such a thing.

For example, *filling operations* in CCTT (Cartesian CTT) require weakening
substitutions on interval variables. These operations may act on *arbitrary*
terms/values at evaluation time, which are not known to be closures. So it's not
enough to have closures, we need unrestricted interval substitutions too.

Runtime values don't support efficient substitution, e.g.

    _[x ↦ _] : Val (Γ, x : A) → Val Γ → Val Γ

which instantiates the last variable to a value in some value. The problematic
part is the substitution of closures: here we have some `Env (Γ, x : A) Δ` and a
`Tm Δ`, so we have to traverse the `Env` and substitute each value therein.
Sadly, if done eagerly, this deeply and recursively copies every value and every
closure within a value. The main reason for the efficiency of vanilla NbE is
*implicit structure sharing* in values and eager substitution destroys all such
sharing.

So I refine vanilla NbE for CTTs. It does have substitution for values, but the
evilness of it is mitigated.

### Cubical NbE

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

The last important ingredient is forcing is **stability annotations**.  We don't
want to always recompute neutral values on every forcing. Instead, we add small
annotations to neutral values. These annotations can be cheaply forced, and they
tell us if the neutral value would change under the current forcing. If it
wouldn't, we just delay the forcing.

This is inspired by the paper "Normalization for Cubical Type Theory", where
each neutral is annotated by the cofibration which is true when the neutral can
be further computed. A false annotation signifies a neutral which can not be
further computed under any cofibration or interval substitution.

In my implementation, annotations are *not precise*, they are not cofibrations
but simple sets (bitmasks) of interval variables which occur in relevant
positions in a neutral. When forcing, I check whether relevant interval vars
are mapped to distinct vars by forcing. If so, then forcing has no action on
the neutral. This is a sound approximation of the precise stability predicate.

In semantic values, we generally use closures for binders which are never
inspected in computations rules:

- Path abstraction
- Dependent path type binder
- Ordinary lambda abstraction

We don't use closures when computation rules can "peek under" binders:

- In `coe` types.
- In partial "systems" in `hcom`, `Glue`, `glue` and `unglue`.

The reason is that peeking under closures can be very expensive; it can be only
done by instantiating it with a fresh variable. Peeking at plain values is
just forcing.

Generally speaking, this cubical NbE can be call-by-need or call-by-value in
"ordinary" reductions, and call-by-name in computation triggered by interval
substitution and weakening under cofibrations.

In the following I look at considerations on laziness vs strictness and closed
vs open evaluation.

### Closed cubical evaluation
