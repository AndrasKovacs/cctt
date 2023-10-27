
module Cubical.Cofibration where


import Common
import Cubical.Interval
import qualified Data.IVarSet as IS


-- | A clause is a set of negated vars and a set of non-negated vars.
--   Invariant (outside of SAT solving): their intersection is empty.
data Clause = Clause IS.Set IS.Set
  deriving Show

cnClause :: Clause -> CNF
cnClause c@(Clause xs ys)
  | IS.null (IS.intersect xs ys) = CNClause c
  | otherwise                    = CNTrue

clOr :: Clause -> Clause -> Clause
clOr (Clause xs ys) (Clause xs' ys') = Clause (xs <> xs') (ys <> ys')

clSize :: Clause -> Int
clSize (Clause xs ys) = IS.size xs + IS.size ys

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

clVars :: Clause -> IS.Set
clVars (Clause xs ys) = xs <> ys

cnVars :: CNF -> IS.Set
cnVars = \case
  CNClause c -> clVars c
  CNAnd i j  -> cnVars i <> cnVars j
  _          -> mempty

cnSize :: CNF -> Int
cnSize = \case
  CNTrue -> 1
  CNFalse -> 1
  CNAnd i j -> cnSize i + cnSize j
  CNClause _ -> 1

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

data Cof = CofEq I I


-- CNF conversion
--------------------------------------------------------------------------------

cvar0 :: IVar -> Clause
cvar0 x = Clause (IS.singleton x) mempty

cvar1 :: IVar -> Clause
cvar1 x = Clause mempty (IS.singleton x)

eqvarvar :: IVar -> IVar -> IVar -> (CNF, IVar)
eqvarvar x y d = cnand (cnClause (Clause (IS.singleton x) (IS.singleton y)))
                       (cnClause (Clause (IS.singleton y) (IS.singleton x)))
                 // d

neqvarvar :: IVar -> IVar -> IVar -> (CNF, IVar)
neqvarvar x y d = cnand (cnClause (Clause (IS.insertIVar x $ IS.singleton y) mempty))
                        (cnClause (Clause mempty (IS.insertIVar x $ IS.singleton y)))
                 // d

eqcnf :: Cof -> IVar -> (CNF, IVar)
eqcnf (CofEq I0       I0      ) d = (CNTrue // d)
eqcnf (CofEq I0       I1      ) d = (CNFalse // d)
eqcnf (CofEq I0       (IVar x)) d = (CNClause (cvar0 x) // d)
eqcnf (CofEq I0       j       ) d = goNegCnf j d
eqcnf (CofEq I1       I0      ) d = (CNFalse // d)
eqcnf (CofEq I1       I1      ) d = (CNTrue // d)
eqcnf (CofEq I1       (IVar x)) d = (CNClause (cvar1 x) // d)
eqcnf (CofEq I1       j       ) d = goCnf j d
eqcnf (CofEq (IVar x) I0      ) d = (CNClause (cvar0 x) // d)
eqcnf (CofEq (IVar x) I1      ) d = (CNClause (cvar1 x) // d)
eqcnf (CofEq (IVar x) (IVar y)) d = if x == y then CNTrue // d else eqvarvar x y d
eqcnf (CofEq i        j       ) d = cnand' (cnor' (goNegCnf i) (goCnf j))
                                           (cnor' (goCnf i) (goNegCnf j)) d

neqcnf :: Cof -> IVar -> (CNF, IVar)
neqcnf (CofEq I0       I0      ) d = (CNFalse // d)
neqcnf (CofEq I0       I1      ) d = (CNTrue // d)
neqcnf (CofEq I0       (IVar x)) d = (CNClause (cvar1 x) // d)
neqcnf (CofEq I0       j       ) d = goCnf j d
neqcnf (CofEq I1       I0      ) d = (CNTrue // d)
neqcnf (CofEq I1       I1      ) d = (CNFalse // d)
neqcnf (CofEq I1       (IVar x)) d = (CNClause (cvar0 x) // d)
neqcnf (CofEq I1       j       ) d = goNegCnf j d
neqcnf (CofEq (IVar x) I0      ) d = (CNClause (cvar1 x) // d)
neqcnf (CofEq (IVar x) I1      ) d = (CNClause (cvar0 x) // d)
neqcnf (CofEq (IVar x) (IVar y)) d = if x == y then CNFalse // d else neqvarvar x y d
neqcnf (CofEq i        j       ) d = cnand' (cnor' (goCnf i) (goCnf j))
                                            (cnor' (goNegCnf i) (goNegCnf j)) d


cnand :: CNF -> CNF -> CNF
cnand CNTrue  j       = j
cnand CNFalse _       = CNFalse
cnand i       CNTrue  = i
cnand _       CNFalse = CNFalse
cnand i       j       = CNAnd i j

cnand' :: (IVar -> (CNF, IVar)) -> (IVar -> (CNF, IVar)) -> (IVar -> (CNF, IVar))
cnand' i j d = case i d of
  (i, d) -> case j d of
    (j, d) -> cnand i j // d

cnor' :: (IVar -> (CNF, IVar)) -> (IVar -> (CNF, IVar)) -> (IVar -> (CNF, IVar))
cnor' i j d = case i d of
  (i, d) -> case j d of
    (j, d) -> cnor i j d

-- distribute (_∨ cl) over a CNF
distribOr :: CNF -> Clause -> CNF
distribOr i cl = case i of
  CNTrue      -> impossible
  CNFalse     -> impossible
  CNClause c  -> cnClause (clOr c cl)
  CNAnd c1 c2 -> cnand (distribOr c1 cl) (distribOr c2 cl)

cnor :: CNF -> CNF -> IVar -> (CNF, IVar)
cnor CNTrue        _           d = CNTrue // d
cnor CNFalse       j           d = j // d
cnor _             CNTrue      d = CNTrue // d
cnor i             CNFalse     d = i // d

-- Note: we distribute single clauses regardless of size!
-- could blow up
cnor (CNClause c) j            d = distribOr j c // d
cnor i            (CNClause c) d = distribOr i c // d
cnor i            j            d = cnand (distribOr i (cvar1 d)) (distribOr j (cvar0 d))
                                   // d + 1

goCnf :: I -> IVar -> (CNF, IVar)
goCnf i d = case i of
  I0     -> CNFalse // d
  I1     -> CNTrue  // d
  IVar x -> CNClause (cvar1 x) // d
  IAnd i j -> case goCnf i d of
    (i, d) -> case goCnf j d of
      (j, d) -> cnand i j // d
  IOr i j -> case goCnf i d of
    (i, d) -> case goCnf j d of
      (j, d) -> cnor i j d

goNegCnf :: I -> IVar -> (CNF, IVar)
goNegCnf i d = case i of
  I0     -> CNTrue  // d
  I1     -> CNFalse // d
  IVar x -> CNClause (cvar0 x) // d
  IAnd i j -> case goNegCnf i d of
    (i, d) -> case goNegCnf j d of
      (j, d) -> cnor i j d
  IOr i j -> case goNegCnf i d of
    (i, d) -> case goNegCnf j d of
      (j, d) -> cnand i j // d

-- I conversion
--------------------------------------------------------------------------------

sat :: NCofArg => (CNF, IVar) -> Bool
sat (!c, !d) = _

conjClauses :: IVar -> Clauses -> IVar -> CNF -> Clauses
conjClauses d cls d' i = _

conjNCof :: NCof -> (CNF, IVar) -> NCof
conjNCof (NCof d cls) (!c, !d') = NCof d' _

eq :: NCofArg => I -> I -> VCof
eq i j = case neqcnf (CofEq i j) (dom ?cof) of
  (CNTrue , _) -> VCFalse
  (CNFalse, _) -> VCTrue
  neq          -> if sat neq then
                    let eq@(!eqcn, !eqd) = eqcnf (CofEq i j) (dom ?cof)
                    in if sat eq then
                      VCNe (NeCof (conjNCof ?cof eq) _) (cnVars eqcn)
                    else
                      VCFalse
                  else
                    VCTrue

  -- case eqcnf (CofEq i j) (dom ?cof) of
  -- (CNTrue, _ )   -> Eq
  -- (CNFalse, _)   -> Neq
  -- (eq     , eqd) -> case neqcnf (CofEq i j) (dom ?cof

{-
Plan:

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





-- import Common
-- import Cubical.Interval
-- import Cubical.Substitution
-- import Statistics (bumpMaxIVar)

-- import qualified Data.IVarSet as IS

-- ----------------------------------------------------------------------------------------------------

-- data Cof = CEq I I deriving Show
-- data NeCof = NCEq I I deriving Show

-- -- | Substitution which maps each ivar to its smallest
-- --   representative ivar in the equivalence class.
-- data NCof = NCof IVar IList

-- type NCofArg = (?cof :: NCof)

-- data NeCof' = NeCof' {
--     neCof'Extended :: NCof
--   , neCof'Extra    :: {-# unpack #-} NeCof}

-- -- TODO: unbox
-- data VCof
--   = VCTrue
--   | VCFalse
--   | VCNe {-# unpack #-} NeCof' IS.Set

-- makeFields ''NeCof'

-- instance HasDom NCof where
--   dom (NCof d is) = d; {-# inline dom #-}
--   setDom i (NCof d is) = NCof i (dropIList (d - i) is); {-# inline setDom #-}

-- instance Show NCof where
--   show nc = "[" ++ go nc "" ++ "]" where
--     sep = \case ILNil -> id
--                 _     -> (" | "++)
--     go (NCof d is) = case is of
--       ILNil         -> id
--       ILDef is i    -> go (NCof (d - 1) is).sep is.((show (d - 1)++" = "++show i)++)

-- instance Show NeCof' where
--   show (NeCof' c c') = show (c, c')

-- deriving instance Show VCof

-- instance Lift NCof where
--   lift (NCof d is) = runIO (bumpMaxIVar d >> (pure $! (NCof (d + 1) (ILDef is (IVar d)))))
--   -- lift (NCof d is) = NCof (d + 1) (ILDef is (IVar d))
--   {-# inline lift #-}

-- lookupNCof :: IVar -> NCof -> I
-- lookupNCof i (NCof d is) = lookupIList (d - i - 1) is
-- {-# inline lookupNCof #-}

-- appNCof :: NCof -> I -> I
-- appNCof ncof i = matchIVar i (\i -> lookupNCof i ncof) i
-- {-# inline appNCof #-}

-- orient :: (IVar, IVar) -> (IVar, IVar)
-- orient (i, j) | i < j = (i, j)
--               | True  = (j, i)

-- solve :: NCof -> IVar -> I -> NCof
-- solve (NCof d is) i j = NCof d (go d is i j) where
--   go d is i j = case is of
--     ILNil -> impossible
--     ILDef is i' | d - 1 == i   -> ILDef is j
--                 | i' == IVar i -> ILDef (go (d - 1) is i j) j
--                 | True         -> ILDef (go (d - 1) is i j) i'

-- -- | Equate forced I-s.
-- eq# :: NCofArg => I -> I -> VCof
-- eq# i j = case (i, j) of
--   (i, j) | i == j  -> VCTrue
--   (IVar i, IVar j) -> case orient (i, j) of
--                         (i', j') -> VCNe (NeCof' (solve ?cof j' (IVar i')) (NCEq (IVar i) (IVar j)))
--                                          (IS.insert i $ IS.insert j mempty)
--   (IVar i, j     ) -> VCNe (NeCof' (solve ?cof i j) (NCEq (IVar i) j)) (IS.insert i mempty)
--   (i     , IVar j) -> VCNe (NeCof' (solve ?cof j i) (NCEq (IVar j) i)) (IS.insert j mempty)
--   _                -> VCFalse

-- eq :: NCofArg => I -> I -> VCof
-- eq i j = eq# (appNCof ?cof i) (appNCof ?cof j)
-- {-# inline eq #-}

-- evalI :: NCofArg => SubArg => I -> I
-- evalI i = appNCof ?cof (sub i)
-- {-# inline evalI #-}

-- eqS :: SubArg => NCofArg => I -> I -> VCof
-- eqS i j = eq# (evalI i) (evalI j)
-- {-# inline eqS #-}

-- -- | Extend with a forced neutral NeCof. Error if non-neutral.
-- conjNeCof :: NCofArg => NeCof -> NCof
-- conjNeCof = \case
--   NCEq i j    -> case (i, j) of
--     (i     , j     ) | i == j -> impossible
--     (IVar i, IVar j)          -> case orient (i, j) of (i, j) -> solve ?cof j (IVar i)
--     (IVar i, j     )          -> solve ?cof i j
--     (i     , IVar j)          -> solve ?cof j i
--     _                         -> impossible

-- assumeNeCof :: NeCof -> (NCofArg => a) -> (NCofArg => a)
-- assumeNeCof nc act = let ?cof = conjNeCof nc in act
-- {-# inline assumeNeCof #-}

-- idNCof :: IVar -> NCof
-- idNCof i = NCof i (go 0 ILNil) where
--   go j acc | i == j = acc
--   go j acc = go (j + 1) (ILDef acc (IVar j))

-- emptyNCof :: NCof
-- emptyNCof = NCof 0 ILNil

-- ----------------------------------------------------------------------------------------------------

-- appNCofToSub :: NCof -> Sub -> Sub
-- appNCofToSub nc (Sub d c is) = Sub d c (go nc is) where
--   go nc ILNil        = ILNil
--   go nc (ILDef is i) = ILDef (go nc is) (appNCof nc i)

-- wkSub :: NCofArg => Sub -> Sub
-- wkSub s = setDom (dom ?cof) s
-- {-# inline wkSub #-}

-- ----------------------------------------------------------------------------------------------------

-- evalCof :: NCofArg => SubArg => Cof -> VCof
-- evalCof (CEq i j) = eqS i j
-- {-# inline evalCof #-}

-- ----------------------------------------------------------------------------------------------------

-- isUnblocked :: NCofArg => IS.Set -> Bool
-- isUnblocked is =
--   IS.foldrAccum
--     (\x hyp (!varset, !cof) ->
--        matchIVar (lookupNCof x cof)
--          (\x -> IS.member x varset || hyp (IS.insert x varset // cof))
--          True)
--     (mempty, ?cof)
--     False
--     is

-- isUnblockedS :: SubArg => NCofArg => IS.Set -> Bool
-- isUnblockedS is = IS.foldrAccum
--   (\x hyp (!varset, !sub, !cof) ->
--      matchIVar (lookupSub x sub)
--        (\x -> matchIVar (lookupNCof x cof)
--          (\x -> IS.member x varset || hyp ((,,) $$! IS.insert x varset $$! sub $$! cof))
--          True)
--        True)
--   (mempty, ?sub, ?cof)
--   False
--   is

-- insertI :: NCofArg => I -> IS.Set -> IS.Set
-- insertI i s = IS.insertI (appNCof ?cof i) s
-- {-# inline insertI #-}

-- neCofVars :: NeCof -> IS.Set
-- neCofVars (NCEq i j) = IS.insertI i $ IS.insertI j mempty
-- {-# inline neCofVars #-}
