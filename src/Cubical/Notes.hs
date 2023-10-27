
module Cubical.Notes where

import Common
import qualified Data.IVarSet as IS


-- Interval
--------------------------------------------------------------------------------

maxIVar :: IVar
maxIVar = 63
{-# inline maxIVar #-}

data I = IVar IVar | IAnd I I | IOr I I | I0 | I1
  deriving Show

-- | Unsafely flip an I which is known to be 0 or 1.
flip# :: I -> I
flip# I0 = I1
flip# I1 = I0
flip# _  = impossible
{-# inline flip# #-}


-- Cofibration
--------------------------------------------------------------------------------

-- | A clause is a set of negated vars and a set of non-negated vars.
--   Invariant (outside of SAT solving): their intersection is empty.
data Clause = Clause IS.Set IS.Set
  deriving Show

-- | List of clauses, interspersed with ivar introductions. The explicit binders
--   are needed so we can weaken Clauses by dropping clauses until some binder.
data Clauses
  = CEmpty
  | CBind Clauses IVar -- ^ Bind "IVar" number of extra ivars.
  | CClause Clauses {-# unpack #-} Clause
  deriving Show

data NCof = NCof IVar Clauses -- ^ Next fresh ivar, clauses
  deriving Show

type NCofArg = (?cof :: NCof)

-- | Conjunctive normal form of a cof. It is in tree form instead of list form, because
--   the list form can't be efficiently produced by the CNF conversion algorithm (and
--   there's no point in copying the tree-CNF in the end to get a list).

data CNF
  = CNTrue
  | CNFalse
  | CNAnd CNF CNF
  | CNClause {-# unpack #-} Clause
  deriving Show

data NeCof = NeCof {
    neCofExtended :: {-# unpack #-} NCof
  , neCofExtra    :: CNF }
  deriving Show

makeFields ''NeCof

-- | Semantic cofibration in a context.
data VCof
  = VCTrue              -- ^ Cof is true in cxt.
  | VCFalse             -- ^ Cof is false in cxt.
  | VCNe NeCof IS.Set   -- ^ Cof is neither true nor false. The IS.Set contains
                        --   the free ivars of the neutral cof.
  deriving Show

instance HasDom NCof where
  dom (NCof d _) = d

  setDom i (NCof d cls) = NCof i (go i d cls) where
    go :: IVar -> IVar -> Clauses -> Clauses
    go i d (CBind cls extra) =
      let d' = d - extra in
      if d' == i     then cls
      else if d' < i then CBind cls i
      else                go i d' cls
    go i d (CClause cls _) =
      go i d cls
    go _ _ CEmpty =
      CEmpty



{-
Plan:

1. Equality shortcut
2. CNF shortcut (x0, x1, xy)
3. CNF ¬ϕ + occurring vars
4. Sweep Γ for occurs, collect assignments (units + pure literal prop), don't build Γ
5. If ¬ϕ vars indep from Γ:
    - If ϕ UNSAT: ret False
           else : ret Neutral Γ,ϕ
   Else:
    - if Γ,¬ϕ UNSAT: return True
      else : return Neutral Γ,ϕ

SAT Γ:

- input: pre-assignment, priority vars for splitting (dependent ϕ vars)
- pick smallest priority var, or smallest occurring var otherwise
  - back and forth sweep until assignment doesn't change
    - compute occurs + assignment
    - if empty clause, CONFLICT
    - if empty Γ, SAT
  - backtrack on CONFLICT
   - reassign
   - if no more occurring vars, SAT
-}


-- Substitution
--------------------------------------------------------------------------------
