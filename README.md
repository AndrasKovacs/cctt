
### cubeval

Investigating evaluation efficiency in cubical type theories. There will
be a prototype implementation here with benchmarks.

Currently there's no such thing, but I include here a preliminary analysis. This
is based on spending some time staring at the computation rules of cubical TTs
and some benchmark source code. Any of my feelings and expectations could be
invalidated by eventual benchmarking. I assume that the reader of this document
is familiar with CTT rules.

## Table of Contents

<!-- * [Motivation](#overview) -->
<!-- * [Installation](#installation) -->
<!-- * [Language overview](#language-overview) -->
<!-- * [Design](#design) -->
<!-- * [GHC-specific optimizations](#ghc-specific-optimizations) -->
<!-- * [Benchmarks](#benchmarks) -->

### Intro

Existing implementation of cubical type theories all have performance issues.
In many cases it could be possible, in principle, to prove things by `refl`, but
in practice it takes too long to check.

I have the following approach in this repo. I try to identify & implement a CTT
variant which is as simple as possible, supports performance optimizations and
supports enough interesting benchmarks. Having more expressive power generally
makes optimization more difficult. I start with barebones CTTs, if those can be
successfully sped up, then we can consider more expressive ones.

### What are the complications

In ordinary type theories, we can usually use environment machine evaluation
in a straightforward way. In cubical TTs, we can't really. The complications
are the following.

First, **interval substitutions**. Vanilla TTs support evaluation where no
substitution is ever required, only evaluation of terms in environments. In
CTTs,


### Picking a CTT

There are many possible variations on CTT rules and features. I pick a concrete
variation on Cartesian Cubical TT (CCTT), which seems to be the easiest to
optimize.  I will mostly compare this CCTT variation to CHM cubical type theory,
which is notable for being the basis of Cubical Agda. I shall use "CCTT" in the
following to refer to the particular flavor of CCTT that I plan to implement.

#### Metatheory

CCTT has the advantage of having a normalization proof (TOOD), while CHM does
not have one right now, and it also has some wobbly parts which could make the
normalization proof difficult (TODO).

#### Interval expressions & substitutions

In CCTT interval expressions are `0`, `1` or variables. In CHM, we additionally
have `∧`, `∨` and `~` (reversal/negation) in interval expressions. Thus, the
CCTT interval language is much simpler, and we can represent CCTT interval
substitutions more compactly. In principle, CCTT substitution can be bit-packed
and their composition can be defined using SIMD instructions. This is pretty
fun, although I doubt that it would make or break overall performance.

#### Primitives

My CCTT has `coe` and `hcom` separately. There's some potential performance
advantage to CCTT coercion in comparison to CHM `transp`. `coe` can be defined
for the simply-typed language fragment without interval substitutions, while
`transp` can't. We write `coe` as follows:

    coeⁱ r r' A t

where `Γ, i ⊢ A type`, `Γ ⊢ t : A[i↦r]` and `Γ ⊢ coeⁱ r r' A t : A[i↦r']`.
Consider coercion for non-dependent functions:

    coeⁱ r r' (A → B) t = λ x. coeⁱ r r' B (t (coeⁱ r' r A x))

Also `transp`:

    transpⁱ (A → B) t = λ x. transpⁱ B (t (transpⁱ (A[i ↦ ~i]) x))

The direction of CCTT coercion can be reversed "natively", while in `transp` we
have to reverse the `i` variable by substitution. Assuming that CCTT and CHM are
both implemented in an optimized way, this probably doesn't change the
asymptotics, but it looks like a win for CCTT in any case.

For dependent types, we can't avoid interval substitution with `coe`.  For
example:

    coeⁱ r r' ((a : A) × B a) t =
	  (coeⁱ r r' A (t.1), coeⁱ r r' (B (coeFillⁱ r r' A (t.1))))

Here, the definition of `coeFill` requires a weakening substitution.
Specification of `coeFill`:

    Γ, i ⊢ A type   Γ ⊢ t : A[i ↦ r]
    ────────────────────────────────────
    Γ, i ⊢ coeFillⁱ r r' A t : A
	Γ, i, i=r  ⊢ coeFillⁱ r r' A t ≡ t
	Γ, i, i=r' ⊢ coeFillⁱ r r' A t ≡ coeⁱ r r' A t

Definition:

    coeFill i r r' A t := coeʲ r i (A[i ↦ j]) t

where `j` is a fresh interval variable. Hence, if `i=r` then we get `coeʲ r r
(A[i ↦ j]) t ≡ t`, and if `i=r'`, then `coeʲ r r' (A[i ↦ j]) t ≡ coeⁱ r r' A t`,
so the specification is satisfied.

Substituting a fresh variable for some variable is always a
*weakening*. Weakenings are quite special, because all neutral values in CTT are
stable under weakening. More generally, *injective renamings* have the same
stability property, and we want to take advantage of this in
implementations. More on this later; let's just note for now that coercion for
the vanilla MLTT type formers can be implemented using only interval weakenings.





It's a Cartesian CTT, closest to ABCFHL. The alternative would be CHM.

- CCTT has more-developed metatheory, e.g. it has a normalization proof.
- The interval expressions and substitutions in CCTT are simpler than in CHM.




  In CCTT an interval expression is just 0, 1 or a variable, so substitutions
  can be represented very compactly and also composed efficiently. In principle,
  we can could even compose packed substitutions with SIMD instructions, but I
  doubt that this would make a decisive difference in overall performance.
- CCTT cubical primitives can be implemented with fewer interval substitutions.
  In particular, coercion for non-dependent type formers can be implemented
  without interval substitution. For instance:

      coe i:r->r' (A → B)




<!-- #### Choosing a theory -->

<!-- There are multiple cubical TTs and a bunch of feature variations. I want to -->
<!-- first pick a simple and highly streamlined configuration for implementation, -->
<!-- which is however still sufficient to host the classic benchmarks, -->
<!-- e.g. Brunerie's number. We can work out more fancy features afterwards. -->
<!-- Summarizing the features: -->

<!-- - I pick Cartesian CTT. This makes interval substitutions simpler, and more -->
<!--   amenable to compression. However, I do not actually expect that there would be -->
<!--   a notable performance difference between CCTT and De Morgan CTT solely because -->
<!--   of the difference in interval substitutions. Both in CCTT and DMCTT interval -->
<!--   substitutions are tiny compared to value substitutions (and we want to exploit -->
<!--   this!). At the end of the day, I do not see a major difference between the -->
<!--   efficiency of CCTT and DMCTT; it's just that I have to pick one. -->
<!-- - We have `hcom` and `coe` as separate primitives. -->
<!-- - I do not allow abstraction over intervals and cofibrations, unlike cooltt and -->
<!--   Agda. -->
<!-- - There are no first-class partial values. We can only write down partial values -->
<!--   in `hcom`, `Glue` and `glue`. Unlike cooltt. -->
<!-- - There are no cubical subtypes. -->
<!-- - There are no *cofibration disjunctions* in the surface syntax. The syntax for -->
<!--   partial values has a normalized structure: we have zero or more disjunctive -->
<!--   "branches" in a partial value, and in each branch the cofibration is a -->
<!--   conjunction of equations. For example, I can write `[i=0∧j=0 ↦ t₁, i=1∧j=1 ↦ -->
<!--   t₂]`, but I can't write `[i=0∨i=1 ↦ t]`. The latter can be rewritten as `[i=0 -->
<!--   ↦ t, i=1 ↦ t]`. Every potential usage of `∨` can be eliminated in this manner. -->
<!--   Now, this causes partial values to potentially increase in size. On the other hand -->
<!--   we can simplify the treatment of cofibrations by a fair margin. Now, we only -->
<!--   every work under a cofibration which is a conjunction of equations. If such a -->
<!--   cofibration is not `False`, then it can be represented as a "canonical" interval -->
<!--   substitution which maps each variable to 0, 1 or the greatest representative -->
<!--   variable of its equivalence class. Overall I do not expect that the potential -->
<!--   value duplication for unfolded partial values will make or break performance. -->
<!-- - The `∀` operation of cofibrations is quite obviously also not available in the -->
<!--   surface syntax. In the `coe` rule for `Glue`, the usage of `∀` is unfolded -->
<!--   on the fly: if `∀` yields a disjunction cofibration, we immediately rewrite -->
<!--   `[∀i.ϕ ↦ t]` to the unfolded partial value where each disjunctive case is -->
<!--   mapped to the same value. -->
<!-- - Inductive types: not yet pinned down. It would be good to have at least: -->
<!--   - parameterized single-sorted strict inductive types (with strict `coe` and -->
<!--     `hcom` reduction rules) -->
<!--   - parameterized single-sorted HITs. -->
<!--   Dropping support for parameters is possible at the cost of significant -->
<!--   boilerplate in code. -->

<!-- Overall, the above language is roughly as expressive as the latest branches of -->
<!-- `cubicaltt`. -->


<!-- #### Canonical and open evaluation -->

<!-- By **canonical evaluation** I mean evaluation in a context which contains interval -->
<!-- variables and a cofibration (as a conjunction of equations), but no ordinary -->
<!-- variables. In such contexts, we have canonicity: every value of a strict -->
<!-- inductive type is definitionally equal to a constructor. This inspires the -->
<!-- naming "canonical evaluation". In non-cubical TTs, we have canonical evaluation -->
<!-- only in empty contexts. -->

<!-- This contrasts **open evaluation** where we work under arbitrary contexts. -->

<!-- In CTTs, evaluating a closed value can depend on canonical evaluation (we may -->
<!-- need to go under interval binders) but not open evaluation. The infamous -->
<!-- explosive CTT benchmarks are all instances of canonical evaluation. -->


<!-- #### Interval substitutions -->

<!-- One crucical problem in cubical evaluation is the necessity of interval -->
<!-- substitutions. They pretty much make it impossible to implement cubical -->
<!-- evaluation with straightforward environment machines. -->
