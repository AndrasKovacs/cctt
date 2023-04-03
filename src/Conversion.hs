
module Conversion where

import Common
import CoreTypes
import Core
import Interval


-- Note: neutral inputs (NeSys, Ne, NeSysHCom) are assumed to be forced
--       other things are not!
-- Also: neutral inputs may have different types!
----------------------------------------------------------------------------------------------------

class Conv a where
  conv :: NCofArg => DomArg => a -> a -> Bool

instance Conv Val where
  conv t t' = case frc t // frc t' of

    -- rigid match
    (VNe n _        , VNe n' _          ) -> conv n n'
    (VGlueTy a sys  , VGlueTy a' sys'   ) -> conv a a' && conv (fst sys) (fst sys')
    (VPi a b        , VPi a' b'         ) -> conv a a' && conv b b'
    (VLam t         , VLam t'           ) -> conv t t'
    (VPath a t u    , VPath a' t' u'    ) -> conv a a' && conv t t' && conv u u'
    (VPLam _ _ t    , VPLam _ _ t'      ) -> conv t t'
    (VSg a b        , VSg a' b'         ) -> b^.name == b'^.name && conv a a' && conv b b'
    (VWrap x a      , VWrap x' a'       ) -> x == x' && conv a a'
    (VPair _ t u    , VPair _ t' u'     ) -> conv t t' && conv u u'
    (VU             , VU                ) -> True
    (VLine a        , VLine a'          ) -> conv a a'
    (VLLam t        , VLLam t'          ) -> conv t t'
    (VTyCon x ts    , VTyCon x' ts'     ) -> x == x' && conv ts ts'
    (VDCon _ i sp   , VDCon _ i' sp'    ) -> i == i' && conv sp sp'

    -- We keep track of evaluation contexts for holes.
    -- This prevents spurious conversions between holes.
    (VHole _ p s e  , VHole _ p' s' e'  ) -> p == p' && conv s s' && conv e e'

    -- eta
    (VLam t         , t'                ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (t              , VLam t'           ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (VPair x t u    , t'                ) -> conv t (proj1 x t') && conv u (proj2 x t')
    (t              , VPair x t' u'     ) -> conv (proj1 x t) t' && conv (proj2 x t) u'
    (VPLam l r t    , t'                ) -> freshI \(IVar -> i) -> conv (t ∙ i) (papp l r t' i)
    (t              , VPLam l r t'      ) -> freshI \(IVar -> i) -> conv (papp l r t i) (t' ∙ i)
    (VLLam t        , t'                ) -> freshI \(IVar -> i) -> conv (t ∙ i) (lapp t' i)
    (t              , VLLam t'          ) -> freshI \(IVar -> i) -> conv (lapp t i) (t' ∙ i)
    (VPack x t      , t'                ) -> conv t (unpack x t')
    (t              , VPack x t'        ) -> conv (unpack x t) t'

    (VSub{}         , _                 ) -> impossible
    (_              , VSub{}            ) -> impossible
    _                                     -> False

instance Conv Ne where

  conv t t' = case unSubNe t // unSubNe t' of
    (NLocalVar x   , NLocalVar x'      ) -> x == x'
    (NDontRecurse x, NDontRecurse x'   ) -> x == x'
    (NApp t u      , NApp t' u'        ) -> conv t t' && conv u u'
    (NPApp p t u r , NPApp p' t' u' r' ) -> conv p p' && conv r r'
    (NProj1 n _    , NProj1 n' _       ) -> conv n n'
    (NProj2 n _    , NProj2 n' _       ) -> conv n n'
    (NLApp t i     , NLApp t' i'       ) -> conv t t' && conv i i'

    (NCoe r1 r2 a t, NCoe r1' r2' a' t') ->
      conv r1 r1' && conv r2 r2' && conv a a' && conv t t'

    (NHCom r1 r2 a sys t, NHCom r1' r2' a' sys' t') ->
      conv r1 r1' && conv r2 r2' && conv a a' && conv sys sys' && conv t t'

    -- the types of the "a"-s can be different Glue-s a priori, that's
    -- why we first convert sys-es. Neutrals of different types can
    -- be converted, and then the type equality is part of the output,
    -- but the "a" here aren't neutrals!
    (NUnglue a sys    , NUnglue a' sys'      ) -> conv sys sys' && conv a a'


    (NCase t b cs     , NCase t' b' cs'      ) -> conv t t' && conv b b' && convCases cs cs'
    (NGlue b sys fib  , NGlue b' sys' fib'   ) -> conv b b' && conv sys sys' && conv fib fib'

    -- Glue eta
    -- A bit ugly that we put "mempty"-s there, and potentially dodgy, but the only
    -- way conversion checking can succeed here is when the VNe-s are immediately consumed.
    (NGlue b sys fib  , t'                   ) -> conv b (VNe (NUnglue t' sys) mempty)
    (t                , NGlue b' sys' fib'   ) -> conv (VNe (NUnglue t sys') mempty) b'

    (NSub{} , _      ) -> impossible
    (t      , NSub{} ) -> impossible
    _                  -> False

convCases' :: NCofArg => DomArg => RecurseArg => Sub -> Env -> Cases -> Sub -> Env -> Cases -> Bool
convCases' sub env cs sub' env' cs' = case (cs, cs') of
  (CSNil            , CSNil             ) -> True
  (CSCons _ xs t cs , CSCons _ _  t' cs') ->
    (let (env , dom) = pushVars env  xs
         (env', _  ) = pushVars env' xs in
     let ?dom = dom in
     let v  = (let ?env = env ; ?sub = sub  in eval t ) in
     let v' = (let ?env = env'; ?sub = sub' in eval t') in
     conv v v')
    &&
    convCases' sub env cs sub' env' cs'
  _ ->
    impossible

convCases :: NCofArg => DomArg => EvalClosure Cases -> EvalClosure Cases -> Bool
convCases (EC sub env _ cs) (EC sub' env' _ cs') =
  let ?recurse = DontRecurse in convCases' sub env cs sub' env' cs'

instance Conv NeCof where
  conv c c' = case (c, c') of
    (NCEq i j   , NCEq i' j'   ) -> conv i i' && conv j j'
    (NCAnd c1 c2, NCAnd c1' c2') -> conv c1 c1' && conv c2 c2'
    _                            -> False

instance Conv VDSpine where
  conv sp sp' = case (sp, sp') of
    (VDNil         , VDNil           ) -> True
    (VDCons t sp   , VDCons t' sp'   ) -> conv t t' && conv sp sp'
    _                                  -> impossible

instance Conv a => Conv [a] where
  conv as as' = case (as, as') of
    ([], [])       -> True
    (a:as, a':as') -> conv a a' && conv as as'
    _              -> False
  {-# inline conv #-}

instance Conv (BindI Val) where
  conv t t' = freshI \(IVar -> i) -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}

instance Conv (BindILazy Val) where
  conv t t' = freshI \(IVar -> i) -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}

instance Conv a => Conv (BindCofLazy a) where
  conv t t' = conv (t^.binds) (t'^.binds)
           && assumeCof (t^.binds) (conv (t^.body) (t'^.body))
  {-# inline conv #-}

instance Conv a => Conv (BindCof a) where
  conv t t' = conv (t^.binds) (t'^.binds)
           && assumeCof (t^.binds) (conv (t^.body) (t'^.body))
  {-# inline conv #-}

instance Conv I where
  conv r r' = frc r == frc r'; {-# inline conv #-}

instance Conv Sub where
  conv s s' = frc s == frc s'; {-# inline conv #-}

instance Conv NeSys where
  conv t t' = case (t, t') of
    (NSEmpty      , NSEmpty        ) -> True
    (NSCons t sys , NSCons t' sys' ) -> conv t t' && conv sys sys'
    _                                -> False

instance Conv NeSysHCom where
  conv t t' = case (t, t') of
    (NSHEmpty      , NSHEmpty        ) -> True
    (NSHCons t sys , NSHCons t' sys' ) -> conv t t' && conv sys sys'
    _                                  -> False

instance Conv NamedClosure where
  conv t t' = fresh \x -> conv (t ∙ x) (t' ∙ x); {-# inline conv #-}

instance Conv NamedIClosure where
  conv t t' = freshI \(IVar -> i) -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}

instance Conv NeCof' where
  conv (NeCof' _ c) (NeCof' _ c') = conv c c'
  {-# inline conv #-}

instance Conv Env where
  conv e e' = case (e, e') of
    (ENil     , ENil       ) -> True
    (EDef e t , EDef e' t' ) -> conv e e' && conv t t'
    _                        -> False
