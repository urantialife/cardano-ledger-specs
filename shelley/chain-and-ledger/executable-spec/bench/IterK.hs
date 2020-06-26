{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies  #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators, DataKinds,  KindSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE BangPatterns #-}


-- Iteration with Continuations

module IterK where

import Debug.Trace
-- import Data.Array
import Data.List(sort,nub)
import qualified Data.Map.Strict as Map
import Data.Map.Internal(Map(..),link,link2)
-- import Utils.Containers.Internal.PtrEquality (ptrEq)
import Data.Map.Internal.Debug(showTree)
import Shelley.Spec.Ledger.Core(Bimap(..),bimapFromList, bimapEmpty)
import qualified Shelley.Spec.Ledger.Core as Core
import qualified Control.Monad as CM
import qualified Control.Applicative as AP

import qualified Data.Set as Set
import Collect
import SetAlgebra

-- ====================================================
{-
instance Semigroup (Bimap k v) where
   (<>) x y = error ("NO Bimap merge yet")
instance Monoid (Bimap k v) where
   mempty = bimapEmpty

instance Semigroup (Pair k v) where
   Fail <> x = x
   x <> Fail = x
   x <> y = x

instance Monoid (Pair k v) where
   mempty = Fail
   mappend = (<>)

-- These are not the only instances. We Probably need a more general approach
-- Perhaps expose the "ans" type as a Parameter of (collect ans t)

instance Semigroup Int where
  (<>) = (+)

instance Monoid Int where
  mempty = 0
  mappend = (<>)

instance Semigroup Bool where
  (<>) = (&&)

instance Monoid Bool where
  mempty = False
  mappend = (<>)
-}
-- ==================================================================
-- One type that can be iterated over (in order) and hence collected
-- Of course the iteration is trivial as there are only 0 or 1 pairs.

chars::String
chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdeghijklmnopqrstuvwxyz0123456789"

nchars :: Int
nchars = length chars

-- ==========================================================================
-- Data.Map.Strict is another example, let's build a few things to test with

m0 :: Map.Map Int Char
m0 = Map.fromList [(1,'a'),(2,'z'),(4,'g')]

m1 :: Map.Map Int Char
m1 = Map.fromList [ (n,chars !! n) | n <- [0..length chars -1]]

m2 :: Map.Map Int Char
m2 = Map.fromList [ (57+n,chars !! n) | n <- [0..length chars -1]]

mN :: Int -> Int -> Map.Map Int Char
mN start size  = Map.fromList [ (n,chars !! (n `mod` nchars)) | n <- [start..start+size]]

-- | Some really big Maps, with very small overlap.

m5,m6 :: Map.Map Int Char
m5 = mN 1 10000000
m6 = mN 9999995 10000000

b0::Bimap Int Char
b0 = bimapFromList [(1,'a'),(2,'z'),(4,'g')]


-- ======================================================================================
-- A binary type constructor can act as an iterator, collecting the pairs in the type,
-- if it supports the following operations: `nxt` and `lub`
-- If it iterates over items in increasing order, and can skip over many items
-- using `lub` in sub-linear time, it can make things really fast. Many collections
-- support lub: Balanced binary trees, Arrays (using binary search), Tries, etc.

instance Iter Pair where
  nxt (Two k v) = Collect(\ ans f -> f (k,v,Fail) ans)
  nxt (One k) = Collect(\ ans f ->  f (k,(),Fail) ans)
  nxt Fail = Collect(\ ans f -> ans)
  lub key (Two k v) = Collect(\ ans f -> if k<=key then f (k,v,Fail) ans else ans)
  lub key (One k) = Collect(\ ans f -> if k<=key then f(k,(),Fail) ans else ans)
  lub key Fail = Collect(\ ans f -> ans)
  x `element` (Two k v) = when (x==k)
  x `element` (One k) = when (x==k)
  x `element` Fail = when False
  haskey k (One a) = k==a
  haskey k (Two a b) = k==a
  haskey k Fail = False
  addpair k v (Two a b) = if k==a then Two a v else Fail
  addpair k v (One a) = if k==a then Two a v else Fail
  addpair k v Fail = Two k v
  removekey key (Two a b) = if key==a then Fail else (Two a b)
  removekey key (One a) = if key==a then Fail else (One a)
  removekey key Fail = Fail
  empty Fail = True
  empty _ = False


instance Iter Sett where
  x `element` (Sett m) =  when (Set.member x m)
  nxt (Sett m) = Collect (\ ans f -> if Set.null m then ans else let (k,nextm) = Set.deleteFindMin m in f (k,(),Sett nextm) ans)
  lub key (Sett m) =
      Collect (\ ans f -> if Set.null m
                             then ans
                             else case Set.splitMember key m of   -- NOTE in Log time, we skip over all those tuples in _left
                                     (_left,True,right) -> f (key,(),Sett right) ans
                                     (_left,False,right) -> if Set.null right
                                                        then ans
                                                        else let (k,nextm) = Set.deleteFindMin right in f (k,(),Sett  nextm) ans)
  addpair key unit (Sett m) = Sett(Set.insert key m)
  haskey key (Sett m) = Set.member key m
  empty (Sett x) = Set.null x
  removekey k (Sett m) = Sett(Set.delete k m)


instance Iter Map.Map where
  x `element` m =  when (Map.member x m)
  nxt m = Collect (\ ans f ->
     case Map.minViewWithKey m of
        Nothing -> ans
        Just((k,v),nextm) -> f (k,v,nextm) ans)
  lub key m = Collect (\ ans f ->
     -- mygo key m ans (\ v nextm -> f (key,v,nextm) ans) (\ nextm -> let ((k,v),m3) = Map.deleteFindMin nextm in f (k,v,m3) ans))
     case Map.splitLookup key m of                  -- NOTE in Log time, we skip over all those tuples in _left
       (_left,Just v,right) -> f (key,v,right) ans
       (_left,Nothing,Tip) -> ans
       (_left,Nothing,right) -> f (k,v,m3) ans
           where ((k,v),m3) = Map.deleteFindMin right)
  haskey x m = case Map.lookup x m of Just _ -> True; Nothing -> False
  addpair = Map.insertWith (\x _y -> x)
  removekey k m = Map.delete k m
  empty = Map.null

-- ==================================
leftpart:: Bimap k v -> Map.Map k v
leftpart(MkBimap left right) = left

rightpart:: Bimap k v -> Map.Map v k
rightpart(MkBimap left right) = right

instance Iter Bimap where
  x `element` m =  when (Map.member x (leftpart m))
  nxt m = Collect (\ ans f ->
     case Map.minViewWithKey (leftpart m) of
        Nothing -> ans
        Just((k,v),nextm) -> f (k,v,MkBimap nextm (rightpart m)) ans)
  lub key m = Collect (\ ans f ->
     case Map.splitLookup key (leftpart m) of           -- NOTE in Log time, we skip over all those tuples in _left
       (_left,Just v,right) -> f (key,v,MkBimap right (rightpart m)) ans
       (_left,Nothing,Tip) -> ans
       (_left,Nothing,right) -> f (k,v,MkBimap m3 (rightpart m)) ans
           where ((k,v),m3) = Map.deleteFindMin right)
  haskey x m = case Map.lookup x (leftpart m) of Just _ -> True; Nothing -> False
  addpair = undefined -- Core.addpair
  removekey key m = error("removekey for Bimap requires (Ord val) as well as (Ord key)")
  empty (MkBimap f g) = empty f


-- ==============================================================
-- Combining Type (Iter f) types to new ones



andLoop :: (Ord a, Iter f1, Iter f2) =>
            (f1 a b1 -> f2 a b2 -> c) ->
            (a, b1, f1 a b1) ->
            (a, b2, f2 a b2) ->
            Collect (a, (b1, b2), c)
andLoop combine (ftrip@(k1,v1,f1)) (gtrip@(k2,v2,g2)) =
   case compare k1 k2 of
      EQ -> one (k1,(v1,v2),combine f1 g2)
      LT -> do { ftrip' <- lub k2 f1; andLoop combine ftrip' gtrip  }
      GT -> do { gtrip' <- lub k1 g2; andLoop combine ftrip gtrip' }

instance Iter And2 where
   nxt (And2x f g) =
      do { triple1 <- nxt f; triple2 <- nxt g; andLoop And2x triple1 triple2 }
   lub  key (And2x f g) =
      do { triple1 <- lub key f; triple2 <- lub key g; andLoop And2x triple1 triple2 }
   element k (And2x f g) = do { k `element` f; k `element` g; one () }
   haskey k (And2x f g) = haskey k f && haskey k g
   addpair k v (And2x f g) = And2x (addpair k (fst v) f) (addpair k (snd v) g)
   removekey k (And2x f g) = And2x (removekey k f) g
   empty (And2x f g) = empty f  ||  empty g

-- =============================================================================


orAction :: (Iter f, Iter g, Ord k) =>
            (forall h b . Iter h => h k b -> Collect(k,b,h k b)) ->
            f k v -> g k v ->
            Collect (k, [v], Or2 k [v])
orAction next f g | empty g =
   do (k1,v1,h1) <- next f
      one (k1,[v1],Or2x h1 g)
orAction next f g | empty f =
   do (k1,v1,h1) <- next g
      one (k1,[v1],Or2x f h1)
orAction next f g =
   do (ftrip@(k1,v1,f1)) <- next f
      (gtrip@(k2,v2,g2)) <- next g
      case compare k1 k2 of
         EQ -> one (k1,[v1,v2],Or2x f1 g2)
         LT -> one (k1,[v1],Or2x f1 g)
         GT -> one (k2,[v2],Or2x f g2)

instance Iter Or2 where
   nxt (Or2x f g) = orAction nxt f g
   lub key (Or2x f g) = orAction (lub key) f g
   haskey k (Or2x f g) = haskey k f ||  haskey k g
   element k (Or2x f g) = when (not ( isempty (element k f) && isempty(element k g)))
   addpair k xs (Or2x f g) = Or2x (foldr accum f xs) g  where accum v ans = addpair k v ans
   removekey k (Or2x f g) = Or2x (removekey k f) (removekey k g)
   empty (Or2x f g) = empty f &&  empty g


-- ================================================================

guardAction :: (Iter f, Ord k) =>
            (forall h b . Iter h => h k b -> Collect(k,b,h k b)) ->
            (k -> v -> Bool) ->
            f k v ->
            Collect (k, v, Guard k v)
guardAction next p f = do { triple <- next f; loop triple }
   where loop (k,v,f') = if (p k v) then one (k,v,Guardx f' p) else do { triple <- nxt f'; loop triple}

instance Iter Guard where
   nxt (Guardx f p) = guardAction nxt p f
   lub key (Guardx f p) = guardAction (lub key) p f
   element x (Guardx f p)  = do { (y,v,f') <- lub x f; when (x==y && p x v) }
   haskey key f = nonempty(element key f)
   addpair k v (old@(Guardx f p)) = if (p k v) then Guardx (addpair k v f) p else old
   empty (Guardx f p) = empty f
   removekey key (Guardx f p) = Guardx (removekey key f) p


-- =================================================================

projAction :: (Iter f, Ord k) =>
            (forall h b . Iter h => h k b -> Collect(k,b,h k b)) ->
            (k -> v -> u) ->
            f k v ->
            Collect (k, u, Project k u)
projAction next p f = do { triple <- next f; loop triple }
   where loop (k,v,f') = one (k,p k v,Projectx f' p)

instance Iter Project where
   nxt (Projectx f p) = projAction nxt p f
   lub key (Projectx f p) = projAction (lub key) p f
   element x (Projectx f p) = element x f
   haskey key (Projectx f p) = haskey key f
   addpair k v (Projectx f p) = error ("can't add a (key,value) pair to a projection view.")
   empty (Projectx f p) = empty f
   removekey key (Projectx f p) = Projectx (removekey key f) p

-- ================================================================

data Diff k v where
   Diffx :: (Ord k,Iter f,Iter g) => f k v -> g k u -> Diff k v

diffAction:: (Iter f, Iter g, Ord k) => (k,u,f k u) -> g k v -> Collect (k,u,Diff k u)
diffAction (t1@(k1,u1,f1)) g = do
   (t2@(k2,u2,g2)) <- lub k1 g
   case compare k1 k2 of
      EQ -> do { tup <- nxt f1; diffAction tup g2 }
      LT -> one (k1,u1,Diffx f1 g)
      GT -> one (k1,u1,Diffx f1 g)

instance Iter Diff where
   nxt (Diffx f g) = do { trip <- nxt f; diffAction trip g }
   lub key (Diffx f g) = do { trip <- lub key f; diffAction trip g}
   element key diff = when (haskey key diff)
   haskey key (Diffx f g) = haskey key f && (not (haskey key g))
   addpair k v (Diffx f g) = Diffx (addpair k v f) (removekey k g)
   removekey key (Diffx f g) = Diffx (removekey key f) g
   empty (Diffx f g) = error ("empty for Diff is (f `iskeysubset` g)")

-- =================================================================
-- An iterator over a single  Iter f => (f k v)
-- This is going to be Linear in time, better to use domEq when we can take advantage of fast matching

lifo :: Iter f => f k v -> Collect (k,v)
lifo x = do { (k,v,x2) <- nxt x; front (k,v) (lifo x2) }

fifo :: Iter f => f k v -> Collect (k,v)
fifo x = do { (k,v,x2) <- nxt x; rear (fifo x2) (k,v)}

-- ==================================================================
-- Now we make an iterator that collects triples, on the intersection
-- of the domain of the two Iter types 'f' and 'g'. An answer of (k,b,c) means that
-- (k,b) is in m::f k a, and (k,c) is in n::g k c. All the other possible triples
-- are skipped over.  This is an instance of a thing called a "Generic Join"
-- See https://arxiv.org/pdf/1310.3314.pdf  or  http://personales.dcc.uchile.cl/~pbarcelo/ngo.pdf
-- The number of tuples it touches is proportional to the size of the output (modulo log factors).
-- It's cost is unrelated to the size of its inputs (modulo log factors)

(⨝) ::  (Ord k,Iter f,Iter g) =>  f k b -> g k c -> Collect (k,b,c)
(⨝) = domEq

domEq:: (Ord k,Iter f,Iter g) =>  f k b -> g k c -> Collect (k,b,c)
domEq m n = do
    triplem <- nxt m
    triplen <- nxt n
    let loop (mt@(k1,b,nextm)) (nt@(k2,c,nextn)) =
          case compare k1 k2 of
            EQ -> front (k1,b,c) (domEq nextm nextn)
            LT -> do { mt' <- lub k2 nextm; loop mt' nt }
            GT -> do { nt' <- lub k1 nextn; loop mt nt' }
    loop triplem triplen

-- This version is really slow as it visits every tuple in both Types.

domEqSlow:: (Ord k,Iter f, Iter g) =>  f k b -> g k c -> Collect (k,b,c)
domEqSlow m n = do
    triplem <- nxt m
    triplen <- nxt n
    let loop (mt@(k1,b,nextm)) (nt@(k2,c,nextn)) =
          case compare k1 k2 of
            EQ -> front (k1,b,c) (domEqSlow nextm nextn)
            LT -> do { mt' <- nxt nextm; loop mt' nt }
            GT -> do { nt' <- nxt nextn; loop mt nt' }
    loop triplem triplen

-- ===========================================================================================
{-  Compare the run times and the memory allocation difference between domEq and domEqSlow
    where m5 and m6 have 10,000,000 pairs, and an intersection size of 7

*IterK> domEq m5 m6
(10000001,'b','b')
(10000000,'a','a')
(9999999,'Z','Z')
(9999998,'Y','Y')
(9999997,'X','X')
(9999996,'W','W')
(9999995,'V','V')

(0.01 secs, 250,160 bytes)

*IterK> domEqSlow m5 m6
(10000001,'b','b')
(10000000,'a','a')
(9999999,'Z','Z')
(9999998,'Y','Y')
(9999997,'X','X')
(9999996,'W','W')
(9999995,'V','V')

(10.67 secs, 18,391,871,488 bytes)
-}

-- ==============================================================================================
-- Consider one of transactions that needs to compute the following.
-- ((dom stkcreds) ◁ delegs) ▷ (dom stpools)
-- We could express this in datalog as follows
-- ans(x,y) <- skcreds(x,z) and delegs(x,y) and stpools(y,w)
-- Or if collections: stkcreds, delegs, and stpools were lists of pairs as a comprehension
-- [ (x,y) | (x,z) <- skcreds, (x',y) <- delegs, x==x', (y',w) <- stpools, y=y' ]
-- This runs in time and space proportional to: size(dom skcreds) + size(dom delegs) + size(dom stpools) (perhaps even worse)
-- Or if  stkcreds, delegs, and stpools were Data.Map, we could use the Collection monad.
-- Even better, this will run in time and space proportional to: size((dom skcreds) ∩ (dom delegs))
-- See the example with timing above.

foo skcreds delegs stpools = materialize Map $
  do (x,z,y) <- skcreds ⨝ delegs
     y `element` stpools
     one (x,y)

-- Even better,  stkcreds, delegs, and stpools can be any binary type construtors in the Iter class.

foo :: (Iter s, Iter d, Iter p, Ord a, Ord b1) =>
       s a b2 ->
       d a b1 ->
       p b1 b3 ->
       Map a b1

-- =====================================================================================
-- Some times we need to write our own version of functions over Map.Map that
-- do not appear in the library

-- A version of withoutKeys where both parts are Map.Map

noKeys :: Ord k => Map k a -> Map k b -> Map k a
noKeys Tip _ = Tip
noKeys m Tip = m
noKeys m (Bin _ k _ ls rs) = case Map.split k m of
  (lm, rm) -> link2 lm' rm'     -- We know `k` is not in either `lm` or `rm`
     where !lm' = noKeys lm ls
           !rm' = noKeys rm rs
{-# INLINABLE noKeys #-}

-- ===============================================================================================
-- Exp is a typed Symbol representation of queries we may ask. It allows us to introspect a query
-- The strategy is to
-- 1) Define Exp so all queries can be represented.
-- 2) Define smart constructors that "parse" the surface syntax, and build a typed Exp
-- 3) Write an evaluate function. eval:: Exp t -> t
-- 4) "eval" can introspect the code and apply efficient domain and type specific translations
-- 5) Use the (Iter f) class to evaluate some Exp that can benefit from its efficient nature.


-- ============================================================================================
-- | In order to build typed Exp, we need to know what Basic types of Maps and Sets are supported.


-- | Given a BaseRep we can materialize a (Collect k v) which has no intrinsic type.

materialize :: (Ord k,Ord v) => BaseRep f k v -> Collect (k,v) -> f k v
materialize Map x = runCollect x Map.empty (\ (k,v) ans -> Map.insert k v ans)
materialize Set x = Sett (runCollect x Set.empty (\ (k,_) ans -> Set.insert k ans))
materialize Bimap x = runCollect x  bimapEmpty (\ (k,v) ans -> Core.addpair k v ans)
materialize Pair x = runCollect x Fail (\ (k,v) _ignore -> Two k v)
materialize other x = error ("Can't materialize compound (Iter f) type: "++show other++". Choose some other BaseRep.")


-- ===============================================================================================
-- The eval function. Here are some sample of optimizations we incorporate
--  x  ∈ (dom y)            haskey
--  x  ∉ (dom y)            not . haskey
-- x ∪ (singleton y)        addpair
-- (Set.singleton x) ⋪ y    removekey
-- x ⋫ (Set.singleton y)    easy on Bimap  remove val
-- (dom x) ⊆ (dom y)
-- ===============================================================================================

data Code k v where
  Data:: (Ord k,Iter f) => f k v -> Code k v
  Act:: (Ord k) => Collect (k,v) -> Code k v

compile:: Exp (f k v) -> Code k v
compile (Base rep relation) = Data relation

compile (Dom (Base Set rel)) = Data rel
compile (Dom (Singleton k v)) = Data (Sett (Set.singleton k))
compile (Dom (SetSingleton k)) = Data (Sett (Set.singleton k))
compile (Dom x) = case compile x of
  Data xcode -> Data (Projectx xcode (\ _ y -> ()))
  Act comp -> Act $ do { (k,v) <- comp; one (k,()) }

compile (Rng (Base Set rel)) = Data (Sett (Set.singleton ()))
compile (Rng (Singleton k v)) = Data (Sett (Set.singleton v))
compile (Rng (SetSingleton k)) = Data (Sett (Set.singleton ()))
compile (Rng x) =
   case compile x of  -- This is going to be expensive, last gasp fallback
      Data xcode -> Act $ do { (k,v) <- lifo xcode; one (v,())}
      Act comp -> Act $ do { (k,v) <- comp; one (v,())}
compile (DRestrict set rel) = case (compile set, compile rel) of
   (Data setd, Data reld) -> Data (Projectx (And2x setd reld) (\ k (u,v) -> v))
   (Act comp, Data reld) -> Data (Projectx (And2x setd reld) (\ k (u,v) -> v))
      where setd = materialize Set comp
   (Act setc, Act relc) -> Act $ do { (x,u) <- setc; (y,v) <- relc; when (x==y); one (y,v) }
   (Data setd,Act relc) -> Act $ do { (x,u) <- lifo setd; (y,v) <- relc; when (x==y); one (y,v) }
compile (DExclude set rel) = case (compile set,compile rel) of
   -- (Data setd, Data reld) ->
    (Data setd,Act relc) -> Act $ do { (x,u) <- lifo setd; (y,v) <- relc; when (not(x==y)); one (y,v) }


compile other = error "No compile yet"


eval:: Exp t -> t
eval (Base rep relation) = relation

eval (Dom (Base Set rel)) = rel
eval (Dom (Singleton k v)) = Sett (Set.singleton k)
eval (Dom (SetSingleton k)) = Sett (Set.singleton k)

eval (Rng (Base Set rel)) = Sett (Set.singleton ())
eval (Rng (Singleton k v)) = Sett (Set.singleton v)
eval (Rng (SetSingleton k)) = Sett (Set.singleton ())

eval (DRestrict (Base Set x1) (Base rep x2)) = materialize rep $ do { (x,y,z) <- x1 `domEq` x2; one (x,z) }
eval (DRestrict (Dom (Base _ x1)) (Base rep x2)) = materialize rep $ do { (x,y,z) <- x1 `domEq` x2; one (x,z) }
eval (DRestrict (SetSingleton k) (Base rep x2)) = materialize rep $  do { (x,y,z) <- (One k) `domEq` x2; one (x,z) }
eval (DRestrict (Dom (Singleton k _)) (Base rep x2)) = materialize rep $  do { (x,y,z) <- (One k) `domEq` x2; one (x,z) }
eval (DRestrict (Rng (Singleton _ v)) (Base rep x2)) = materialize rep $  do { (x,y,z) <- (One v) `domEq` x2; one (x,z) }

eval (DExclude (Base Set (Sett x1)) (Base Map x2)) =  Map.withoutKeys x2 x1
eval (DExclude (Dom (Base Map x1)) (Base Map x2)) = noKeys x2 x1
eval (DExclude (SetSingleton k) (Base Bimap x)) = Core.removekey k x
eval (DExclude (Dom (Singleton k _)) (Base Bimap x)) = Core.removekey k x
eval (DExclude (Rng (Singleton _ v)) (Base Bimap x)) = Core.removekey v x

eval (RExclude (Base Bimap x) (SetSingleton k)) = Core.removeval k x
eval (RExclude (Base Bimap x) (Dom (Singleton k v))) = Core.removeval k x
eval (RExclude (Base Bimap x) (Rng (Singleton k v))) = Core.removeval v x
eval (RExclude (Base rep lhs) y) =
   materialize rep $ do { (a,b) <- lifo lhs; (c,_) <- lifo rhs; when (not(b==c)); one (a,b)} where rhs = eval y

eval (RRestrict (DRestrict (Dom (Base r1 stkcreds)) (Base r2 delegs)) (Dom (Base r3 stpools))) =
   materialize r2 $ do { (x,z,y) <- stkcreds `domEq` delegs; y `element` stpools; one (x,y)}
eval (RRestrict (Base rep lhs) y) =
   materialize rep $ do { (a,b) <- lifo lhs; (c,_) <- lifo rhs; when ((b==c)); one (a,b)} where rhs = eval y

eval (Elem k (Dom (Base rep x))) = haskey k x
eval (Elem k (Base rep rel)) = haskey k rel
eval (Elem k (Dom (Singleton key v))) = k==key
eval (Elem k (Rng (Singleton _ key))) = k==key
eval (Elem k (SetSingleton key)) = k==key

eval (NotElem k (Dom (Base rep x))) = not $ haskey k x
eval (NotElem k (Base rep rel)) = not $ haskey k rel
eval (NotElem k (Dom (Singleton key v))) = not $ k==key
eval (NotElem k (Rng (Singleton _ key))) = not $ k==key
eval (NotElem k (SetSingleton key)) = not $ k==key

eval (UnionLeft (Base rep x) (Singleton k v)) = addpair k v x
eval (UnionRight (Base rep x) (Singleton k v)) = addpair k v x   --TODO MIght not have the right parity
eval (UnionPlus (Base Map x) (Base Map y)) = Map.unionWith (+) x y

eval (Singleton k v) = Two k v
eval (SetSingleton k) = Sett (Set.singleton k)

eval other = error ("Can't eval: "++show other++" yet.")


-- =========================================================
-- Some examples of Exp and tests

ex1 :: Exp Bool
ex1 = 5 ∈ (dom m1)

ex2 :: Exp Bool
ex2 = 70 ∈ (dom m1)

ex3 :: Exp (Map Int Char)
ex3 = m0 ∪ (singleton 3 'b')

ex4,ex5,ex6 :: Exp(Map Int Char)
ex4 = (setSingleton 2) ⋪ m0
ex5 = dom(singleton 2 'z') ⋪ m0
ex6 = rng(singleton 'z' 2) ⋪ m0

ex7::Exp Bool
ex7 = 70 ∉ (dom m1)

tests :: [Bool]
tests = [ eval ex1==True
        , eval ex2==False
        , eval ex3 == Map.fromList [(1,'a'),(2,'z'),(3,'b'),(4,'g')]
        , eval ex4 == Map.fromList [(1,'a'),(4,'g')]
        , eval ex5 == Map.fromList [(1,'a'),(4,'g')]
        , eval ex6 == Map.fromList [(1,'a'),(4,'g')]
        , eval ex7 == True
        ]


-- ==================================================================
-- Show instances
