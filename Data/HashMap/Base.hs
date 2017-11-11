{-@ LIQUID "--prune-unsorted" @-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns, DeriveDataTypeable, MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-full-laziness -funbox-strict-fields #-}

module Data.HashMap.Base
    (
      Tree(..)
    , HashMap(..)
    , Leaf(..)

      -- * Construction
    , empty
    , singleton

      -- * Basic interface
    , null
    , size
    , member
    , lookup
    , lookupDefault
    , (!)
    , insert
    , insertWith
    , unsafeInsert
    , delete
    , adjust
    , update
    , alter

      -- * Combine
      -- ** Union
    , union
    , unionWith
    , unionWithKey
    , unions

      -- * Transformations
    , map
    , mapWithKey
    , traverseWithKey

      -- * Difference and intersection
    , difference
    , differenceWith
    , intersection
    , intersectionWith
    , intersectionWithKey

      -- * Folds
    , foldl'
    , foldlWithKey'
    , foldr
    , foldrWithKey

      -- * Filter
    , mapMaybe
    , mapMaybeWithKey
    , filter
    , filterWithKey

      -- * Conversions
    , keys
    , elems

      -- ** Lists
    , toList
    , fromList
    , fromListWith

      -- Internals used by the strict version
    , Hash
    , Bitmap
    , bitmapIndexedOrFull
    , collision
    , hash
    , mask
    , index
    , bitsPerSubkey
    , fullNodeMask
    , sparseIndex
    , two
    , unionArrayBy
    , unionArrayByInternal
    , update16
    , update16M
    , update16With'
    , update16WithInternal'
    , updateOrConcatWith
    , updateOrConcatWithKey
    , filterMapAuxInternal
    , equalKeys
    ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>), Applicative(pure))
import Data.Monoid (Monoid(mempty, mappend))
import Data.Traversable (Traversable(..))
import Data.Word (Word)
#endif
#if __GLASGOW_HASKELL__ >= 711
import Data.Semigroup (Semigroup((<>)))
#endif
import Control.DeepSeq (NFData(rnf))
import Control.Monad.ST (ST)
import Data.Bits ((.&.), (.|.), complement, popCount)
import Data.Data hiding (Typeable)
import qualified Data.Foldable as Foldable
import qualified Data.List as L
import GHC.Exts ((==#), build, isTrue#, reallyUnsafePtrEquality#)
import Prelude hiding (filter, foldr, lookup, map, null, pred)
import Text.Read hiding (step)

import qualified Data.HashMap.Array as A
import qualified Data.Hashable as H
import Data.Hashable (Hashable)
-- LIQUID import qualified Data.Hashable.Lifted as H
import Data.HashMap.Unsafe (runST)
import Data.HashMap.UnsafeShift (unsafeShiftL, unsafeShiftR)
import Data.HashMap.List (isPermutationBy, unorderedCompare)
-- LIQUID import Data.Maybe (isJust)
import Data.Typeable (Typeable)

import GHC.Exts (isTrue#)
import qualified GHC.Exts as Exts

#if MIN_VERSION_base(4,9,0)
import Data.Functor.Classes
#endif

#if MIN_VERSION_hashable(1,2,5)
import qualified Data.Hashable.Lifted as H
#endif

-- | A set of values.  A set cannot contain duplicate values.
------------------------------------------------------------------------

-- | Convenience function.  Compute a hash value for the given value.
hash :: H.Hashable a => a -> Hash
hash = fromIntegral . H.hash

data Leaf k v = L !k v
  deriving Eq

instance (NFData k, NFData v) => NFData (Leaf k v) where
    rnf (L k v) = rnf k `seq` rnf v

-- Invariant: The length of the 1st argument to 'Full' is
-- 2^bitsPerSubkey

{-@ data Tree [tlen] k v
         = Empty
         | BitmapIndexed (bmp :: !Bitmap)
                         (arr :: !(A.Array (Tree k v)))
         | Leaf (h :: !Hash)
                (l :: (Leaf k v))
         | Full (arr :: !(A.Array (Tree k v)))
         | Collision (h :: !Hash)
                     (arr :: !(A.Array (Leaf k v)))
  @-}

{-@ invariant {v:Tree k v | (tlen v) >= 0} @-}

{-@ measure tlen @-}
tlen :: Tree k v -> A.Size
tlen t = A.Size (go t 0)
  where
    go Empty                !n = n
    go (Leaf _ _)            n = n + 1
    go (BitmapIndexed _ ary) n = A.foldl' (flip go) n ary
    go (Full ary)            n = A.foldl' (flip go) n ary
    go (Collision _ ary)     n = n + A.length ary

-- | A map from keys to values.  A map cannot contain duplicate keys;
-- each key can map to at most one value.
data Tree k v
    = Empty
    | BitmapIndexed !Bitmap !(A.Array (Tree k v))
    | Leaf !Hash !(Leaf k v)
    | Full !(A.Array (Tree k v))
    | Collision !Hash !(A.Array (Leaf k v))
      deriving Typeable

type role Tree nominal representational

{-@ data HashMap [hlen] k v = HashMap A.Size (Tree k v) @-}

{-@ invariant {v:HashMap k v | (hlen v) >= 0} @-}

{-@ measure hlen @-}
hlen :: HashMap k v -> A.Size
hlen (HashMap _ t) = tlen t

-- | A wrapper over 'Tree'. The 'Int' field represent the hashmap's
-- size.
data HashMap k v = HashMap {-# UNPACK #-} !A.Size !(Tree k v)
  deriving Typeable

instance (NFData k, NFData v) => NFData (Tree k v) where
    rnf Empty                 = ()
    rnf (BitmapIndexed _ ary) = rnf ary
    rnf (Leaf _ l)            = rnf l
    rnf (Full ary)            = rnf ary
    rnf (Collision _ ary)     = rnf ary

instance (NFData k, NFData v) => NFData (HashMap k v) where
    rnf (HashMap !_ m) = rnf m

instance Functor (HashMap k) where
    fmap = map

instance Foldable.Foldable (HashMap k) where
    foldr f = foldrWithKey (const f)

#if __GLASGOW_HASKELL__ >= 711
instance (Eq k, Hashable k) => Semigroup (HashMap k v) where
  (<>) = union
  {-# INLINE (<>) #-}
#endif

instance (Eq k, Hashable k) => Monoid (HashMap k v) where
  mempty = empty
  {-# INLINE mempty #-}
#if __GLASGOW_HASKELL__ >= 711
  mappend = (<>)
#else
  mappend = union
#endif
  {-# INLINE mappend #-}

instance (Data k, Data v, Eq k, Hashable k) => Data (HashMap k v) where
    gfoldl f z hw   = z fromList `f` toList hw
    toConstr _     = fromListConstr
    gunfold k z c  = case constrIndex c of
        1 -> k (z fromList)
        _ -> error "gunfold"
    dataTypeOf _   = hashMapDataType
    dataCast2 f    = gcast2 f

fromListConstr :: Constr
fromListConstr = mkConstr hashMapDataType "fromList" [] Prefix

hashMapDataType :: DataType
hashMapDataType = mkDataType "Data.HashMap.Base.HashMap" [fromListConstr]

type Hash   = Word
type Bitmap = Word
type Shift  = Int

#if MIN_VERSION_base(4,9,0)
instance Show2 HashMap where
    liftShowsPrec2 spk slk spv slv d m =
        showsUnaryWith (liftShowsPrec sp sl) "fromList" d (toList m)
      where
        sp = liftShowsPrec2 spk slk spv slv
        sl = liftShowList2 spk slk spv slv

instance Show k => Show1 (HashMap k) where
    liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Eq k, Hashable k, Read k) => Read1 (HashMap k) where
    liftReadsPrec rp rl = readsData $
        readsUnaryWith (liftReadsPrec rp' rl') "fromList" fromList
      where
        rp' = liftReadsPrec rp rl
        rl' = liftReadList rp rl
#endif

instance (Eq k, Hashable k, Read k, Read e) => Read (HashMap k e) where
    readPrec = parens $ prec 10 $ do
      Ident "fromList" <- lexP
      xs <- readPrec
      return (fromList xs)

    readListPrec = readListPrecDefault

instance (Show k, Show v) => Show (HashMap k v) where
    showsPrec d m = showParen (d > 10) $
      showString "fromList " . shows (toList m)

instance Traversable (HashMap k) where
    traverse f = traverseWithKey (const f)

#if MIN_VERSION_base(4,9,0)
instance Eq2 HashMap where
    liftEq2 = equal

instance Eq k => Eq1 (HashMap k) where
    liftEq = equal (==)
#endif

instance (Eq k, Eq v) => Eq (HashMap k v) where
    (==) = equal (==) (==)

equal :: (k -> k' -> Bool) -> (v -> v' -> Bool)
      -> HashMap k v -> HashMap k' v' -> Bool
equal eqk eqv (HashMap s1 t1) (HashMap s2 t2) =
    (s1 == s2) && go (toList' t1 []) (toList' t2 [])
  where
    -- If the two trees are the same, then their lists of 'Leaf's and
    -- 'Collision's read from left to right should be the same (modulo the
    -- order of elements in 'Collision').

    go (Leaf k1 l1 : tl1) (Leaf k2 l2 : tl2)
      | k1 == k2 &&
        leafEq l1 l2
      = go tl1 tl2
    go (Collision k1 ary1 : tl1) (Collision k2 ary2 : tl2)
      | k1 == k2 &&
        A.length ary1 == A.length ary2 &&
        isPermutationBy leafEq (A.toList ary1) (A.toList ary2)
      = go tl1 tl2
    go [] [] = True
    go _  _  = False

    leafEq (L k v) (L k' v') = eqk k k' && eqv v v'

#if MIN_VERSION_base(4,9,0)
instance Ord2 HashMap where
    liftCompare2 = cmp

instance Ord k => Ord1 (HashMap k) where
    liftCompare = cmp compare
#endif

-- | The order is total.
--
-- /Note:/ Because the hash is not guaranteed to be stable across library
-- versions, OSes, or architectures, neither is an actual order of elements in
-- 'HashMap' or a result of `compare`.
instance (Ord k, Ord v) => Ord (HashMap k v) where
    compare = cmp compare compare

cmp :: (k -> k' -> Ordering) -> (v -> v' -> Ordering)
    -> HashMap k v -> HashMap k' v' -> Ordering
cmp cmpk cmpv (HashMap _ t1) (HashMap _ t2) =
    go (toList' t1 []) (toList' t2 [])
  where
    go (Leaf k1 l1 : tl1) (Leaf k2 l2 : tl2)
      = compare k1 k2 `mappend`
        leafCompare l1 l2 `mappend`
        go tl1 tl2
    go (Collision k1 ary1 : tl1) (Collision k2 ary2 : tl2)
      = compare k1 k2 `mappend`
        compare (A.length ary1) (A.length ary2) `mappend`
        unorderedCompare leafCompare (A.toList ary1) (A.toList ary2) `mappend`
        go tl1 tl2
    go (Leaf _ _ : _) (Collision _ _ : _) = LT
    go (Collision _ _ : _) (Leaf _ _ : _) = GT
    go [] [] = EQ
    go [] _  = LT
    go _  [] = GT
    go _ _ = error "cmp: Should never happend, toList' includes non Leaf / Collision"

    leafCompare (L k v) (L k' v') = cmpk k k' `mappend` cmpv v v'

-- Same as 'equal' but doesn't compare the values.
equalKeys :: (k -> k' -> Bool) -> HashMap k v -> HashMap k' v' -> Bool
equalKeys eq (HashMap s1 t1) (HashMap s2 t2) =
    (s1 == s2) && go (toList' t1 []) (toList' t2 [])
  where
    go (Leaf k1 l1 : tl1) (Leaf k2 l2 : tl2)
      | k1 == k2 && leafEq l1 l2
      = go tl1 tl2
    go (Collision k1 ary1 : tl1) (Collision k2 ary2 : tl2)
      | k1 == k2 && A.length ary1 == A.length ary2 &&
        isPermutationBy leafEq (A.toList ary1) (A.toList ary2)
      = go tl1 tl2
    go [] [] = True
    go _  _  = False

    leafEq (L k _) (L k' _) = eq k k'

#if MIN_VERSION_hashable(1,2,5)
instance H.Hashable2 HashMap where
    liftHashWithSalt2 hk hv salt (HashMap _ hm) = go salt (toList' hm [])
      where
        -- go :: Int -> [Tree k v] -> Int
        go s [] = s
        go s (Leaf _ l : tl)
          = s `hashLeafWithSalt` l `go` tl
        -- For collisions we hashmix hash value
        -- and then array of values' hashes sorted
        go s (Collision h a : tl)
          = (s `H.hashWithSalt` h) `hashCollisionWithSalt` a `go` tl
        go s (_ : tl) = s `go` tl

        -- hashLeafWithSalt :: Int -> Leaf k v -> Int
        hashLeafWithSalt s (L k v) = (s `hk` k) `hv` v

        -- hashCollisionWithSalt :: Int -> A.Array (Leaf k v) -> Int
        hashCollisionWithSalt s
          = L.foldl' H.hashWithSalt s . arrayHashesSorted s

        -- arrayHashesSorted :: Int -> A.Array (Leaf k v) -> [Int]
        arrayHashesSorted s = L.sort . L.map (hashLeafWithSalt s) . A.toList

instance (Hashable k) => H.Hashable1 (HashMap k) where
    liftHashWithSalt = H.liftHashWithSalt2 H.hashWithSalt
#endif

instance (Hashable k, Hashable v) => Hashable (HashMap k v) where
    hashWithSalt salt (HashMap _ hm) = go salt (toList' hm [])
      where
        go :: Int -> [Tree k v] -> Int
        go s [] = s
        go s (Leaf _ l : tl)
          = s `hashLeafWithSalt` l `go` tl
        -- For collisions we hashmix hash value
        -- and then array of values' hashes sorted
        go s (Collision h a : tl)
          = (s `H.hashWithSalt` h) `hashCollisionWithSalt` a `go` tl
        go s (_ : tl) = s `go` tl

        hashLeafWithSalt :: Int -> Leaf k v -> Int
        hashLeafWithSalt s (L k v) = s `H.hashWithSalt` k `H.hashWithSalt` v

        hashCollisionWithSalt :: Int -> A.Array (Leaf k v) -> Int
        hashCollisionWithSalt s
          = L.foldl' H.hashWithSalt s . arrayHashesSorted s

        arrayHashesSorted :: Int -> A.Array (Leaf k v) -> [Int]
        arrayHashesSorted s = L.sort . L.map (hashLeafWithSalt s) . A.toList

  -- Helper to get 'Leaf's and 'Collision's as a list.
toList' :: Tree k v -> [Tree k v] -> [Tree k v]
toList' (BitmapIndexed _ ary) a = A.foldr toList' a ary
toList' (Full ary)            a = A.foldr toList' a ary
toList' l@(Leaf _ _)          a = l : a
toList' c@(Collision _ _)     a = c : a
toList' Empty                 a = a

-- Helper function to detect 'Leaf's and 'Collision's.
isLeafOrCollision :: Tree k v -> Bool
isLeafOrCollision (Leaf _ _)      = True
isLeafOrCollision (Collision _ _) = True
isLeafOrCollision _               = False

------------------------------------------------------------------------
-- * Construction

-- | /O(1)/ Construct an empty map.
{-@ empty :: {h : HashMap k v | hlen h = 0} @-}
empty :: HashMap k v
empty = HashMap 0 Empty

{-@ singleton :: key:k -> val:v -> {h : HashMap k v | hlen h = 1} @-}
-- | /O(1)/ Construct a map with a single element.
singleton :: (Hashable k) => k -> v -> HashMap k v
singleton k v = HashMap 1 (Leaf (hash k) (L k v))

------------------------------------------------------------------------
-- * Basic interface

-- | /O(1)/ Return 'True' if this map is empty, 'False' otherwise.
null :: HashMap k v -> Bool
null (HashMap _ Empty) = True
null _                 = False

{-@ invariant {v:HashMap k v | hlen v = size v} @-}

-- | /O(1)/ Return the number of key-value mappings in this map.
{-@ size :: h:HashMap k v -> {n:Nat | n = hlen h} @-}
size :: HashMap k v -> Int
size (HashMap sz _) = A.unSize sz

-- | /O(log n)/ Return 'True' if the specified key is present in the
-- map, 'False' otherwise.
member :: (Eq k, Hashable k) => k -> HashMap k a -> Bool
member k m = case lookup k m of
    Nothing -> False
    Just _  -> True
{-# INLINABLE member #-}

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or 'Nothing' if this map contains no mapping for the key.
lookup :: (Eq k, Hashable k) => k -> HashMap k v -> Maybe v
lookup k0 (HashMap _ m0) = go h0 k0 0 m0
  where
    h0 = hash k0
    go !_ !_ !_ Empty = Nothing
    go h k _ (Leaf hx (L kx x))
        | h == hx && k == kx = Just x  -- TODO: Split test in two
        | otherwise          = Nothing
    go h k s (BitmapIndexed b v)
        | b .&. m == 0 = Nothing
        | otherwise    = go h k (s+bitsPerSubkey) (A.index v (sparseIndex b m))
      where m = mask h s
    go h k s (Full v) = go h k (s+bitsPerSubkey) (A.index v (index h s))
    go h k _ (Collision hx v)
        | h == hx   = lookupInArray k v
        | otherwise = Nothing
{-# INLINABLE lookup #-}

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or the default value if this map contains no mapping for the key.
lookupDefault :: (Eq k, Hashable k)
              => v          -- ^ Default value to return.
              -> k -> HashMap k v -> v
lookupDefault def k t = case lookup k t of
    Just v -> v
    _      -> def
{-# INLINABLE lookupDefault #-}

-- | /O(log n)/ Return the value to which the specified key is mapped.
-- Calls 'error' if this map contains no mapping for the key.
(!) :: (Eq k, Hashable k) => HashMap k v -> k -> v
(!) m k = case lookup k m of
    Just v  -> v
    Nothing -> error "Data.HashMap.Base.(!): key not found"
{-# INLINABLE (!) #-}

infixl 9 !

-- | Create a 'Collision' value with two 'Leaf' values.
{-@ collision :: h:Hash -> l:Leaf k v -> {t : Tree k v | tlen t = 2} @-}
collision :: Hash -> Leaf k v -> Leaf k v -> Tree k v
collision h e1 e2 =
    let v = A.run $ do mary <- A.new 2 e1
                       A.write mary 1 e2
                       return mary
    in Collision h v
{-# INLINE collision #-}

-- | Create a 'BitmapIndexed' or 'Full' node.
{-@ bitmapIndexedOrFull :: bmp:Bitmap
                        -> arr:A.Array (Tree k v)
                        -> {v:Tree k v | tlen v = A.foldr (+) 0 (A.map tlen arr)}
@-}
bitmapIndexedOrFull :: Bitmap -> A.Array (Tree k v) -> Tree k v
bitmapIndexedOrFull b ary
    | b == fullNodeMask = Full ary
    | otherwise         = BitmapIndexed b ary
{-# INLINE bitmapIndexedOrFull #-}

-- | /O(log n)/ Associate the specified value with the specified
-- key in this map.  If this map previously contained a mapping for
-- the key, the old value is replaced.
{-@ insert :: (Eq k, Hashable k)
           => key:k
           -> val:v
           -> h:HashMap k v
           -> {h:HashMap k v | size h = if member k h then hlen h else 1 + hlen h}
@-}
insert :: (Eq k, Hashable k) => k -> v -> HashMap k v -> HashMap k v
insert k0 v0 (HashMap sz m0) =
    let A.Sized diff m0' = insertInternal k0 v0 m0
    in HashMap (sz + diff) m0'
{-# INLINE insert #-}

-- | /O(log n)/ Associate the specified value with the specified
-- key in this map.  If this map previously contained a mapping for
-- the key, the old value is replaced. Returns a tuple containing the
-- hashmap's change in size, and the hashmap after the insertion.
insertInternal :: (Eq k, Hashable k) => k -> v -> Tree k v -> A.Sized (Tree k v)
insertInternal k0 v0 m0 = go h0 k0 v0 0 m0
  where
    h0 = hash k0
    go !h !k x !_ Empty = A.Sized 1 (Leaf h (L k x))
    go h k x s t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then if x `ptrEq` y
                         then A.Sized 0 t
                         else A.Sized 0 (Leaf h (L k x))
                    else A.Sized 1 (collision h l (L k x))
        | otherwise = A.Sized 1 (runST (two s h k x hy ky y))
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 =
            let !ary' = A.insert ary i $! Leaf h (L k x)
            in A.Sized 1 (bitmapIndexedOrFull (b .|. m) ary')
        | otherwise =
            let !st  = A.index ary i
                A.Sized sz st' = go h k x (s+bitsPerSubkey) st
            in if st' `ptrEq` st
               then A.Sized sz t
               else A.Sized sz (BitmapIndexed b (A.update ary i st'))
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) =
        let !st  = A.index ary i
            A.Sized sz st' = go h k x (s+bitsPerSubkey) st
        in if st' `ptrEq` st
            then A.Sized sz t
            else A.Sized sz (Full (update16 ary i st'))
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   =
            let !start = A.length v
                !newV = updateOrSnocWith const k x v
                !end = A.length newV
            in A.Sized (A.Size (end - start)) (Collision h newV)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE insertInternal #-}

{-@ unsafeInsert :: (Eq k, Hashable k)
                 => key:k
                 -> val:v
                 -> h:HashMap k v
                 -> {h:HashMap k v | size h = if member k h then hlen h else 1 + hlen h}
@-}
-- | In-place update version of insert
unsafeInsert :: (Eq k, Hashable k) => k -> v -> HashMap k v -> HashMap k v
unsafeInsert k0 v0 (HashMap sz m0) =
    let A.Sized diff m0' = unsafeInsertInternal k0 v0 m0
    in HashMap (diff + sz) m0'
{-# INLINABLE unsafeInsert #-}

-- | In-place update version of insert. Returns a tuple with the
-- HashMap's change in size and the hashmap itself.
unsafeInsertInternal :: (Eq k, Hashable k) => k -> v -> Tree k v -> A.Sized (Tree k v)
unsafeInsertInternal k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go !h !k x !_ Empty = return $! A.Sized 1 (Leaf h (L k x))
    go h k x s t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then if x `ptrEq` y
                         then return $! A.Sized 0 t
                         else return $! A.Sized 0 (Leaf h (L k x))
                    else return $! A.Sized 1 (collision h l (L k x))
        | otherwise = A.Sized 1 <$> two s h k x hy ky y
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertM ary i $! Leaf h (L k x)
            return $! A.Sized 1 (bitmapIndexedOrFull (b .|. m) ary')
        | otherwise = do
            st <- A.indexM ary i
            A.Sized sz st' <- go h k x (s+bitsPerSubkey) st
            A.unsafeUpdateM ary i st'
            return (A.Sized sz t)
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) = do
        st <- A.indexM ary i
        A.Sized sz st' <- go h k x (s+bitsPerSubkey) st
        A.unsafeUpdateM ary i st'
        return (A.Sized sz t)
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   =
            let !start = A.length v
                !newV = updateOrSnocWith const k x v
                !end = A.length newV
            in return $! A.Sized (A.Size (end - start)) (Collision h newV)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE unsafeInsertInternal #-}

-- | Create a map from two key-value pairs which hashes don't collide.
{-@ two :: sh:Shift
        -> hs:Hash
        -> key:k
        -> val:v
        -> hs':Hash
        -> key':k
        -> val':v
        -> {st:ST s (Tree k v) | tlen (runST st) = 2
@-}
two :: Shift -> Hash -> k -> v -> Hash -> k -> v -> ST s (Tree k v)
two = go
  where
    go s h1 k1 v1 h2 k2 v2
        | bp1 == bp2 = do
            st <- go (s+bitsPerSubkey) h1 k1 v1 h2 k2 v2
            ary <- A.singletonM st
            return $! BitmapIndexed bp1 ary
        | otherwise  = do
            mary <- A.new 2 $ Leaf h1 (L k1 v1)
            A.write mary idx2 $ Leaf h2 (L k2 v2)
            ary <- A.unsafeFreeze mary
            return $! BitmapIndexed (bp1 .|. bp2) ary
      where
        bp1  = mask h1 s
        bp2  = mask h2 s
        idx2 | index h1 s < index h2 s = 1
             | otherwise               = 0
{-# INLINE two #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.  Example:
--
-- > insertWith f k v map
-- >   where f new old = new + old
{-@ insertWith :: (Eq k, Hashable k)
               => fun:(v -> v -> v)
               -> key:k
               -> val:v
               -> h:HashMap k v
               -> {h':HashMap k v | size h' = if member k h then hlen h else 1 + hlen h}
@-}
insertWith :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> HashMap k v
            -> HashMap k v
insertWith f k0 v0 (HashMap sz m0) =
    let A.Sized diff m0' = insertWithInternal f k0 v0 m0
    in HashMap (diff + sz) m0'
{-# INLINABLE insertWith #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.
-- Returns a tuple where the first component is the
-- difference in size between the old and new hashmaps, and the second
-- is the new hashmap.
-- Example:
--
-- > insertWithInternal f k v map
-- >   where f new old = new + old
insertWithInternal :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> Tree k v
            -> A.Sized (Tree k v)
insertWithInternal f k0 v0 m0 = go h0 k0 v0 0 m0
  where
    h0 = hash k0
    go !h !k x !_ Empty = A.Sized 1 (Leaf h (L k x))
    go h k x s (Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then A.Sized 0 (Leaf h (L k (f x y)))
                    else A.Sized 1 (collision h l (L k x))
        | otherwise = A.Sized 1 (runST (two s h k x hy ky y))
    go h k x s (BitmapIndexed b ary)
        | b .&. m == 0 =
            let ary' = A.insert ary i $! Leaf h (L k x)
            in A.Sized 1 (bitmapIndexedOrFull (b .|. m) ary')
        | otherwise =
            let st           = A.index ary i
                A.Sized sz st' = go h k x (s+bitsPerSubkey) st
                ary'         = A.update ary i $! st'
            in A.Sized sz (BitmapIndexed b ary')
      where m = mask h s
            i = sparseIndex b m
    go h k x s (Full ary) =
        let st           = A.index ary i
            A.Sized sz st' = go h k x (s+bitsPerSubkey) st
            ary'         = update16 ary i $! st'
        in A.Sized sz (Full ary')
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   =
            let !start = A.length v
                !newV  = updateOrSnocWith f k x v
                !end   = A.length newV
            in A.Sized (A.Size (end - start)) (Collision h newV)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE insertWithInternal #-}

-- | In-place update version of insertWith
{-@ unsafeInsertWith :: (Eq k, Hashable k)
                     => fun:(v -> v -> v)
                     -> key:k
                     -> val:v
                     -> h:HashMap k v
                     -> {h:HashMap k v | size h = if member k h then hlen h else 1 + hlen h}
@-}
unsafeInsertWith :: forall k v . (Eq k, Hashable k)
                 => (v -> v -> v) -> k -> v -> HashMap k v
                 -> HashMap k v
unsafeInsertWith f k0 v0 (HashMap sz m0) =
    let A.Sized diff m0' = unsafeInsertWithInternal f k0 v0 m0
    in HashMap (diff + sz) m0'
{-# INLINABLE unsafeInsertWith #-}

-- | In-place update version of insertWithInternal
unsafeInsertWithInternal :: forall k v. (Eq k, Hashable k)
                 => (v -> v -> v) -> k -> v -> Tree k v
                 -> A.Sized (Tree k v)
unsafeInsertWithInternal f k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go :: Hash -> k -> v -> Shift -> Tree k v -> ST s (A.Sized (Tree k v))
    go !h !k x !_ Empty = return $! A.Sized 1 (Leaf h (L k x))
    go h k x s (Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then return $! A.Sized 0 (Leaf h (L k (f x y)))
                    else return $! A.Sized 1 (collision h l (L k x))
        | otherwise = do
              twoHm <- two s h k x hy ky y
              return $! A.Sized 1 twoHm
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertM ary i $! Leaf h (L k x)
            return $! A.Sized 1 (bitmapIndexedOrFull (b .|. m) ary')
        | otherwise = do
            st <- A.indexM ary i
            A.Sized sz st' <- go h k x (s+bitsPerSubkey) st
            A.unsafeUpdateM ary i st'
            return (A.Sized sz t)
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) = do
        st <- A.indexM ary i
        A.Sized sz st' <- go h k x (s+bitsPerSubkey) st
        A.unsafeUpdateM ary i st'
        return (A.Sized sz t)
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   =
            let !start = A.length v
                !newV = updateOrSnocWith f k x v
                !end = A.length newV
            in return $! A.Sized (A.Size (end - start)) (Collision h newV)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE unsafeInsertWithInternal #-}

-- | /O(log n)/ Remove the mapping for the specified key from this map
-- if present.
{-@ delete :: (Eq k, Hashable k)
           => key:k
           -> h:HashMap k v
           -> {h:HashMap k v | size h = if member k h then hlen h - 1 else hlen h}
@-}
delete :: (Eq k, Hashable k) => k -> HashMap k v -> HashMap k v
delete k0 (HashMap sz m0) =
    let A.Sized diff m0' = deleteInternal k0 m0
    in HashMap (sz + diff) m0'
{-# INLINABLE delete #-}

-- | /O(log n)/ Remove the mapping for the specified key from this map
-- if present. Returns a tuple with the hashmap's change in size and the
-- hashmap after the deletion.
deleteInternal :: (Eq k, Hashable k) => k -> Tree k v -> A.Sized (Tree k v)
deleteInternal k0 m0 = go h0 k0 0 m0
  where
    h0 = hash k0
    go !_ !_ !_ Empty = A.Sized 0 Empty
    go h k _ t@(Leaf hy (L ky _))
        | hy == h && ky == k = A.Sized (-1) Empty
        | otherwise          = A.Sized 0 t
    go h k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = A.Sized 0 t
        | otherwise =
            let !st = A.index ary i
                A.Sized sz st' = go h k (s+bitsPerSubkey) st
            in A.Sized sz $! if st' `ptrEq` st
                then t
                else case st' of
                Empty | A.length ary == 1 -> Empty
                      | A.length ary == 2 ->
                          case (i, A.index ary 0, A.index ary 1) of
                          (0, _, l) | isLeafOrCollision l -> l
                          (1, l, _) | isLeafOrCollision l -> l
                          _                               -> bIndexed
                      | otherwise -> bIndexed
                    where
                      bIndexed = BitmapIndexed (b .&. complement m) (A.delete ary i)
                l | isLeafOrCollision l && A.length ary == 1 -> l
                _ -> BitmapIndexed b (A.update ary i st')
      where m = mask h s
            i = sparseIndex b m
    go h k s t@(Full ary) =
        let !st   = A.index ary i
            A.Sized sz st' = go h k (s+bitsPerSubkey) st
        in A.Sized sz $! if st' `ptrEq` st
            then t
            else case st' of
            Empty ->
                let ary' = A.delete ary i
                    bm   = fullNodeMask .&. complement (1 `unsafeShiftL` i)
                in BitmapIndexed bm ary'
            _ -> Full (A.update ary i st')
      where i = index h s
    go h k _ t@(Collision hy v)
        | h == hy = case indexOf k v of
            Just i
                | A.length v == 2 ->
                    A.Sized (-1) $! if i == 0
                    then Leaf h (A.index v 1)
                    else Leaf h (A.index v 0)
                | otherwise -> A.Sized (-1) (Collision h (A.delete v i))
            Nothing -> A.Sized 0 t
        | otherwise = A.Sized 0 t
{-# INLINABLE deleteInternal #-}

-- | /O(log n)/ Adjust the value tied to a given key in this map only
-- if it is present. Otherwise, leave the map alone.
adjust :: (Eq k, Hashable k) => (v -> v) -> k -> HashMap k v -> HashMap k v
adjust f k0 (HashMap sz m0) = HashMap sz (go h0 k0 0 m0)
  where
    h0 = hash k0
    go !_ !_ !_ Empty = Empty
    go h k _ t@(Leaf hy (L ky y))
        | hy == h && ky == k = Leaf h (L k (f y))
        | otherwise          = t
    go h k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise = let st   = A.index ary i
                          st'  = go h k (s+bitsPerSubkey) st
                          ary' = A.update ary i $! st'
                      in BitmapIndexed b ary'
      where m = mask h s
            i = sparseIndex b m
    go h k s (Full ary) =
        let i    = index h s
            st   = A.index ary i
            st'  = go h k (s+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in Full ary'
    go h k _ t@(Collision hy v)
        | h == hy   = Collision h (updateWith f k v)
        | otherwise = t
{-# INLINABLE adjust #-}

-- | /O(log n)/  The expression (@'update' f k map@) updates the value @x@ at @k@,
-- (if it is in the map). If (f k x) is @'Nothing', the element is deleted.
-- If it is (@'Just' y), the key k is bound to the new value y.
{-@ update :: (Eq k, Hashable k)
           => fun:(a -> Maybe a)
           -> key:k
           -> h:HashMap k a
           -> {h:HashMap k a | size h = if isJust (f (lookup k h)) then 1 + hlen h else hlen h}
@-}
update :: (Eq k, Hashable k) => (a -> Maybe a) -> k -> HashMap k a -> HashMap k a
update f = alter (>>= f)
{-# INLINABLE update #-}

-- | /O(log n)/  The expression (@'alter' f k map@) alters the value @x@ at @k@, or
-- absence thereof. @alter@ can be used to insert, delete, or update a value in a
-- map. In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
{-@ alter :: (Eq k, Hashable k)
          => fun:(a -> Maybe a)
          -> key:k
          -> h:HashMap k a
          -> {h:HashMap k a | size h = if isJust (f (lookup k h)) then 1 + hlen h else hlen h}
@-}
alter
    :: (Eq k, Hashable k)
    => (Maybe v -> Maybe v)
    -> k
    -> HashMap k v
    -> HashMap k v
alter f k m =
  case f (lookup k m) of
    Nothing -> delete k m
    Just v  -> insert k v m
{-# INLINABLE alter #-}

------------------------------------------------------------------------
-- * Combine

-- | /O(n+m)/ The union of two maps. If a key occurs in both maps, the
-- mapping from the first will be the mapping in the result.
{-@ union :: (Eq k, Hashable k)
          => h1:HashMap k v
          -> h2:HashMap k v
          -> {h:HashMap k a | size h = hlen h1 + hlen h2 - hlen (intersection h1 h2)}
@-}
union :: (Eq k, Hashable k) => HashMap k v -> HashMap k v -> HashMap k v
union = unionWith const
{-# INLINABLE union #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
{-@ unionWith :: (Eq k, Hashable k)
              => fun:(v -> v -> v)
              -> h1:HashMap k v
              -> h2:HashMap k v
              -> {h:HashMap k a | size h = hlen h1 + hlen h2 - hlen (intersection h1 h2)}
@-}
unionWith :: (Eq k, Hashable k) => (v -> v -> v) -> HashMap k v -> HashMap k v
          -> HashMap k v
unionWith f = unionWithKey (const f)
{-# INLINE unionWith #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
{-@ unionWithKey :: (Eq k, Hashable k)
                 => h1:HashMap k v
                 -> h2:HashMap k v
                 -> {h:HashMap k a | size h = hlen h1 + hlen h2 - hlen (intersection h1 h2)}
@-}
unionWithKey
    :: (Eq k, Hashable k)
    => (k -> v -> v -> v)
    -> HashMap k v
    -> HashMap k v
    -> HashMap k v
unionWithKey f (HashMap sz m) hw =
    let A.Sized diff m' = unionWithKeyInternal f m hw
    in HashMap (diff + sz) m'
{-# INLINE unionWithKey #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
-- Returns a tuple where the first component is how many elements were added
-- to the first hashmap and the second is the union hashmap itself.
unionWithKeyInternal
    :: forall k v . (Eq k, Hashable k)
    => (k -> v -> v -> v)
    -> Tree k v
    -> HashMap k v
    -> A.Sized (Tree k v)
unionWithKeyInternal f hm1 (HashMap siz hm2) = go 0 siz hm1 hm2
  where
    go :: Int                -- ^ Bitmask accumulator
       -> A.Size             -- ^ Size accumulator.
                             -- Counts down from the second hashmap's size.
       -> Tree k v
       -> Tree k v
       -> A.Sized (Tree k v)
    -- empty vs. anything
    go !_ !sz t1 Empty = A.Sized sz t1
    go _ !sz Empty t2 = A.Sized sz t2
    -- leaf vs. leaf
    go s !sz t1@(Leaf h1 l1@(L k1 v1)) t2@(Leaf h2 l2@(L k2 v2))
        | h1 == h2  = if k1 == k2
                      then A.Sized (sz - 1) (Leaf h1 (L k1 (f k1 v1 v2)))
                      else A.Sized sz (collision h1 l1 l2)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    go s !sz t1@(Leaf h1 (L k1 v1)) t2@(Collision h2 ls2)
        | h1 == h2  =
            let !start = A.length ls2
                !newV = updateOrSnocWithKey f k1 v1 ls2
                !end = A.length newV
            in A.Sized (sz + A.Size (end - start - 1)) (Collision h1 newV)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    go s !sz t1@(Collision h1 ls1) t2@(Leaf h2 (L k2 v2))
        | h1 == h2  =
            let !start = A.length ls1
                !newV = updateOrSnocWithKey (flip . f) k2 v2 ls1
                !end = A.length newV
            in A.Sized (sz + A.Size (end - start - 1)) (Collision h1 newV)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    go s !sz t1@(Collision h1 ls1) t2@(Collision h2 ls2)
        | h1 == h2  =
            let !start = A.length ls1
                !newV = updateOrConcatWithKey f ls1 ls2
                !end = A.length newV
            in A.Sized (sz + A.Size (end - start - A.length ls2)) (Collision h1 newV)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    -- branch vs. branch
    go s !sz (BitmapIndexed b1 ary1) (BitmapIndexed b2 ary2) =
        let b'         = b1 .|. b2
            A.RunRes dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     b1
                                     b2
                                     ary1
                                     ary2
        in A.Sized dsz (bitmapIndexedOrFull b' ary')
    go s !sz (BitmapIndexed b1 ary1) (Full ary2) =
        let A.RunRes dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     b1
                                     fullNodeMask
                                     ary1
                                     ary2
        in A.Sized dsz (Full ary')
    go s !sz (Full ary1) (BitmapIndexed b2 ary2) =
        let A.RunRes dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     fullNodeMask
                                     b2
                                     ary1
                                     ary2
        in A.Sized dsz (Full ary')
    go s !sz (Full ary1) (Full ary2) =
        let A.RunRes dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     fullNodeMask
                                     fullNodeMask
                                     ary1
                                     ary2
        in A.Sized dsz (Full ary')
    -- leaf vs. branch
    go s !sz (BitmapIndexed b1 ary1) t2
        | b1 .&. m2 == 0 = let ary' = A.insert ary1 i t2
                               b'   = b1 .|. m2
                           in A.Sized sz (bitmapIndexedOrFull b' ary')
        | otherwise      = let A.RunRes dsz ary' =
                                   A.updateWithInternal' ary1 i $ \st1 ->
                                       go (s+bitsPerSubkey) sz st1 t2
                           in A.Sized dsz (BitmapIndexed b1 ary')
        where
          h2 = leafHashCode t2
          m2 = mask h2 s
          i = sparseIndex b1 m2
    go s !sz t1 (BitmapIndexed b2 ary2)
        | b2 .&. m1 == 0 = let ary' = A.insert ary2 i $! t1
                               b'   = b2 .|. m1
                           in A.Sized sz (bitmapIndexedOrFull b' ary')
        | otherwise      = let A.RunRes dsz ary'=
                                   A.updateWithInternal' ary2 i $ \st2 ->
                                       go (s+bitsPerSubkey) sz t1 st2
                           in A.Sized dsz (BitmapIndexed b2 ary')
      where
        h1 = leafHashCode t1
        m1 = mask h1 s
        i = sparseIndex b2 m1
    go s !sz (Full ary1) t2 =
        let h2              = leafHashCode t2
            i               = index h2 s
            A.RunRes dsz ary' =
                update16WithInternal' ary1 i $ \st1 ->
                    go (s+bitsPerSubkey) sz st1 t2
        in A.Sized dsz (Full ary')
    go s !sz t1 (Full ary2) =
        let h1              = leafHashCode t1
            i               = index h1 s
            A.RunRes dsz ary' =
                update16WithInternal' ary2 i $ \st2 ->
                    go (s+bitsPerSubkey) sz t1 st2
        in A.Sized dsz (Full ary')

    leafHashCode (Leaf h _) = h
    leafHashCode (Collision h _) = h
    leafHashCode _ = error "leafHashCode"

    goDifferentHash s sz h1 h2 t1 t2
        | m1 == m2  = let A.Sized dsz hm = go (s+bitsPerSubkey) sz t1 t2
                      in A.Sized dsz (BitmapIndexed m1 (A.singleton hm))
        | m1 <  m2  = A.Sized sz (BitmapIndexed (m1 .|. m2) (A.pair t1 t2))
        | otherwise = A.Sized sz (BitmapIndexed (m1 .|. m2) (A.pair t2 t1))
      where
        m1 = mask h1 s
        m2 = mask h2 s
{-# INLINE unionWithKeyInternal #-}

-- | Strict in the result of @f@.
unionArrayBy :: (a -> a -> a) -> Bitmap -> Bitmap -> A.Array a -> A.Array a
             -> A.Array a
unionArrayBy f b1 b2 ary1 ary2 = A.run $ do
    let b' = b1 .|. b2
    mary <- A.new_ (popCount b')
    -- iterate over nonzero bits of b1 .|. b2
    -- it would be nice if we could shift m by more than 1 each time
    let ba = b1 .&. b2
        go !i !i1 !i2 !m
            | m > b'        = return ()
            | b' .&. m == 0 = go i i1 i2 (m `unsafeShiftL` 1)
            | ba .&. m /= 0 = do
                A.write mary i $! f (A.index ary1 i1) (A.index ary2 i2)
                go (i+1) (i1+1) (i2+1) (m `unsafeShiftL` 1)
            | b1 .&. m /= 0 = do
                A.write mary i =<< A.indexM ary1 i1
                go (i+1) (i1+1) (i2  ) (m `unsafeShiftL` 1)
            | otherwise     = do
                A.write mary i =<< A.indexM ary2 i2
                go (i+1) (i1  ) (i2+1) (m `unsafeShiftL` 1)
    go 0 0 0 (b' .&. negate b') -- XXX: b' must be non-zero
    return mary
    -- TODO: For the case where b1 .&. b2 == b1, i.e. when one is a
    -- subset of the other, we could use a slightly simpler algorithm,
    -- where we copy one array, and then update.
{-# INLINE unionArrayBy #-}

-- | Strict in the result of @f@.
unionArrayByInternal
    :: A.Size
    -> (A.Size -> a -> a -> A.Sized a)
    -> Bitmap
    -> Bitmap
    -> A.Array a
    -> A.Array a
    -> A.RunResA a
unionArrayByInternal siz f b1 b2 ary1 ary2 = A.runInternal $ do
    let b' = b1 .|. b2
    mary <- A.new_ (popCount b')
    -- iterate over nonzero bits of b1 .|. b2
    -- it would be nice if we could shift m by more than 1 each time
    let ba = b1 .&. b2
        go !sz !i !i1 !i2 !m
            | m > b'        = return sz
            | b' .&. m == 0 = go sz i i1 i2 (m `unsafeShiftL` 1)
            | ba .&. m /= 0 = do
                let A.Sized dsz hm = f sz (A.index ary1 i1) (A.index ary2 i2)
                A.write mary i hm
                go dsz (i+1) (i1+1) (i2+1) (m `unsafeShiftL` 1)
            | b1 .&. m /= 0 = do
                A.write mary i =<< A.indexM ary1 i1
                go sz (i+1) (i1+1) (i2  ) (m `unsafeShiftL` 1)
            | otherwise     = do
                A.write mary i =<< A.indexM ary2 i2
                go sz (i+1) (i1  ) (i2+1) (m `unsafeShiftL` 1)
    d <- go siz 0 0 0 (b' .&. negate b') -- XXX: b' must be non-zero
    return (A.RunRes d mary)
    -- TODO: For the case where b1 .&. b2 == b1, i.e. when one is a
    -- subset of the other, we could use a slightly simpler algorithm,
    -- where we copy one array, and then update.
{-# INLINE unionArrayByInternal #-}

-- TODO: Figure out the time complexity of 'unions'.

-- | Construct a set containing all elements from a list of sets.
unions :: (Eq k, Hashable k) => [HashMap k v] -> HashMap k v
unions = L.foldl' union empty
{-# INLINE unions #-}

------------------------------------------------------------------------
-- * Transformations

-- | /O(n)/ Transform this map by applying a function to every value.
mapWithKey :: (k -> v1 -> v2) -> HashMap k v1 -> HashMap k v2
mapWithKey f (HashMap sz m) = HashMap sz (go m)
  where
    go Empty = Empty
    go (Leaf h (L k v)) = Leaf h $ L k (f k v)
    go (BitmapIndexed b ary) = BitmapIndexed b $ A.map' go ary
    go (Full ary) = Full $ A.map' go ary
    go (Collision h ary) = Collision h $
                           A.map' (\ (L k v) -> L k (f k v)) ary
{-# INLINE mapWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value.
map :: (v1 -> v2) -> HashMap k v1 -> HashMap k v2
map f = mapWithKey (const f)
{-# INLINE map #-}

-- TODO: We should be able to use mutation to create the new
-- 'Tree'.

-- | /O(n)/ Transform this map by accumulating an Applicative result
-- from every value.
traverseWithKey :: Applicative f => (k -> v1 -> f v2) -> HashMap k v1
                -> f (HashMap k v2)
traverseWithKey f (HashMap sz m) = HashMap sz <$> go m
  where
    go Empty                 = pure Empty
    go (Leaf h (L k v))      = Leaf h . L k <$> f k v
    go (BitmapIndexed b ary) = BitmapIndexed b <$> A.traverse go ary
    go (Full ary)            = Full <$> A.traverse go ary
    go (Collision h ary)     =
        Collision h <$> A.traverse (\ (L k v) -> L k <$> f k v) ary
{-# INLINE traverseWithKey #-}

------------------------------------------------------------------------
-- * Difference and intersection

-- | /O(n*log m)/ Difference of two maps. Return elements of the first map
-- not existing in the second.
{-@ difference :: (Eq k, Hashable k)
               => h1:HashMap k v
               -> h2:HashMap k w
               -> {h:HashMap k v | size h = hlen h - hlen (intersection h1 h2)}
@-}
difference :: (Eq k, Hashable k) => HashMap k v -> HashMap k w -> HashMap k v
difference a b= foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Nothing -> insert k v m
                 _       -> m
{-# INLINABLE difference #-}

-- | /O(n*log m)/ Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the values of these keys.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
{-@ differenceWith :: (Eq k, Hashable k)
                   => h1:HashMap k v
                   -> h2:HashMap k w
                   -> {h:HashMap k v | size h = hlen h - hlen (intersection h1 h2)}
@-}

differenceWith
    :: (Eq k, Hashable k)
    => (v -> w -> Maybe v)
    -> HashMap k v
    -> HashMap k w
    -> HashMap k v
differenceWith f a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Nothing -> insert k v m
                 Just w  -> maybe m (\y -> insert k y m) (f v w)
{-# INLINABLE differenceWith #-}

-- | /O(n*log m)/ Intersection of two maps. Return elements of the first
-- map for keys existing in the second.
{-@ intersection :: (Eq k, Hashable k)
                 => h1:HashMap k v
                 -> h2:HashMap k w
                 -> {h:HashMap k v | size h = (len . filter (member h1) . keys) h2}
@-}
intersection :: (Eq k, Hashable k) => HashMap k v -> HashMap k w -> HashMap k v
intersection a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just _ -> insert k v m
                 _      -> m
{-# INLINABLE intersection #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
{-@ intersectionWith :: (Eq k, Hashable k)
                     => fun: (v -> w -> u)
                     -> h1:HashMap k v
                     -> h2:HashMap k w
                     -> {h:HashMap k u | size h = (len . filter (member h1) . keys) h2}
@-}
intersectionWith :: (Eq k, Hashable k) => (v1 -> v2 -> v3) -> HashMap k v1
                 -> HashMap k v2 -> HashMap k v3
intersectionWith f a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just w -> insert k (f v w) m
                 _      -> m
{-# INLINABLE intersectionWith #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
{-@ intersectionWithKey :: (Eq k, Hashable k)
                        => fun: (v -> w -> u)
                        -> h1:HashMap k v
                        -> h2:HashMap k w
                        -> {h:HashMap k u | size h = (len . filter (member h1) . keys) h2}
@-}
intersectionWithKey :: (Eq k, Hashable k) => (k -> v1 -> v2 -> v3)
                    -> HashMap k v1 -> HashMap k v2 -> HashMap k v3
intersectionWithKey f a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just w -> insert k (f k v w) m
                 _      -> m
{-# INLINABLE intersectionWithKey #-}

------------------------------------------------------------------------
-- * Folds

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before before using the result in the next
-- application.  This function is strict in the starting value.
foldl' :: (a -> v -> a) -> a -> HashMap k v -> a
foldl' f = foldlWithKey' (\ z _ v -> f z v)
{-# INLINE foldl' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before before using the result in the next
-- application.  This function is strict in the starting value.
foldlWithKey' :: (a -> k -> v -> a) -> a -> HashMap k v -> a
foldlWithKey' f acc (HashMap _ m) = go acc m
  where
    go !z Empty                = z
    go z (Leaf _ (L k v))      = f z k v
    go z (BitmapIndexed _ ary) = A.foldl' go z ary
    go z (Full ary)            = A.foldl' go z ary
    go z (Collision _ ary)     = A.foldl' (\ z' (L k v) -> f z' k v) z ary
{-# INLINE foldlWithKey' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldr :: (v -> a -> a) -> a -> HashMap k v -> a
foldr f = foldrWithKey (const f)
{-# INLINE foldr #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldrWithKey :: (k -> v -> a -> a) -> a -> HashMap k v -> a
foldrWithKey f a (HashMap _ m) = go a m
  where
    go z Empty                 = z
    go z (Leaf _ (L k v))      = f k v z
    go z (BitmapIndexed _ ary) = A.foldr (flip go) z ary
    go z (Full ary)            = A.foldr (flip go) z ary
    go z (Collision _ ary)     = A.foldr (\ (L k v) z' -> f k v z') z ary
{-# INLINE foldrWithKey #-}

------------------------------------------------------------------------
-- * Filter

-- | Create a new array of the @n@ first elements of @mary@.
trim :: A.MArray s a -> Int -> ST s (A.Array a)
trim mary n = do
    mary2 <- A.new_ n
    A.copyM mary 0 mary2 0 n
    A.unsafeFreeze mary2
{-# INLINE trim #-}

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybeWithKey :: (k -> v1 -> Maybe v2) -> HashMap k v1 -> HashMap k v2
mapMaybeWithKey f (HashMap _ m) = HashMap size' m'
  where onLeaf (Leaf h (L k v)) | Just v' <- f k v = Just (Leaf h (L k v'))
        onLeaf _ = Nothing

        onColl (L k v) | Just v' <- f k v = Just (L k v')
                       | otherwise = Nothing

        A.Sized size' m' = filterMapAuxInternal onLeaf onColl m
{-# INLINE mapMaybeWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybe :: (v1 -> Maybe v2) -> HashMap k v1 -> HashMap k v2
mapMaybe f = mapMaybeWithKey (const f)
{-# INLINE mapMaybe #-}

-- | /O(n)/ Filter this map by retaining only elements satisfying a
-- predicate.
filterWithKey :: forall k v. (k -> v -> Bool) -> HashMap k v -> HashMap k v
filterWithKey pred (HashMap _ m) = HashMap size' m'
  where onLeaf t@(Leaf _ (L k v)) | pred k v = Just t
        onLeaf _ = Nothing

        onColl el@(L k v) | pred k v = Just el
        onColl _ = Nothing

        A.Sized size' m' = filterMapAuxInternal onLeaf onColl m
{-# INLINE filterWithKey #-}

-- | Common implementation for 'filterWithKey' and 'mapMaybeWithKey',
-- allowing the former and latter to reuse terms.
-- Returns the result hashmap's size, and the hashmap itself.
filterMapAuxInternal :: forall k v1 v2
              . (Tree k v1 -> Maybe (Tree k v2))
             -> (Leaf k v1 -> Maybe (Leaf k v2))
             -> Tree k v1
             -> A.Sized (Tree k v2)
filterMapAuxInternal onLeaf onColl = go 0
  where
    go !sz Empty = A.Sized sz Empty
    go !sz t@Leaf{}
        | Just t' <- onLeaf t = A.Sized (sz + 1) t'
        | otherwise = A.Sized sz Empty
    go !sz (BitmapIndexed b ary) = filterA sz ary b
    go !sz (Full ary) = filterA sz ary fullNodeMask
    go !sz (Collision h ary) = filterC sz ary h

    filterA sze ary0 b0 =
        let !n = A.length ary0
        in runST $ do
            mary <- A.new_ n
            step ary0 mary b0 0 0 1 n sze
      where
        step :: A.Array (Tree k v1) -> A.MArray s (Tree k v2)
             -> Bitmap -> Int -> Int -> Bitmap -> Int -> A.Size
             -> ST s (A.Sized (Tree k v2))
        step !ary !mary !b i !j !bi n !siz
            | i >= n = case j of
                0 -> return $! A.Sized siz Empty
                1 -> do
                    ch <- A.read mary 0
                    case ch of
                      t | isLeafOrCollision t -> return $! A.Sized siz t
                      _                       -> A.Sized siz . BitmapIndexed b <$> trim mary 1
                _ -> do
                    ary2 <- trim mary j
                    return . A.Sized siz $! if j == maxChildren
                                       then Full ary2
                                       else BitmapIndexed b ary2
            | bi .&. b == 0 = step ary mary b i j (bi `unsafeShiftL` 1) n siz
            | otherwise = case go siz (A.index ary i) of
                A.Sized dsz Empty -> step ary mary (b .&. complement bi) (i+1) j
                                (bi `unsafeShiftL` 1) n dsz
                A.Sized dsz t     -> do A.write mary j t
                                        step ary mary b (i+1) (j+1)
                                            (bi `unsafeShiftL` 1) n dsz

    filterC siz ary0 h =
        let !n = A.length ary0
        in runST $ do
            mary <- A.new_ n
            step ary0 mary 0 0 n siz
      where
        step :: A.Array (Leaf k v1) -> A.MArray s (Leaf k v2)
             -> Int -> Int -> Int -> A.Size
             -> ST s (A.Sized (Tree k v2))
        step !ary !mary i !j n !sze
            | i >= n    = case j of
                0 -> return (A.Sized sze Empty)
                1 -> do l <- A.read mary 0
                        return . A.Sized sze $! Leaf h l
                _ | i == j -> do ary2 <- A.unsafeFreeze mary
                                 return . A.Sized sze $! Collision h ary2
                  | otherwise -> do ary2 <- trim mary j
                                    return  . A.Sized sze $! Collision h ary2
            | Just el <- onColl (A.index ary i)
                = A.write mary j el >> step ary mary (i+1) (j+1) n (sze + 1)
            | otherwise = step ary mary (i+1) j n sze
{-# INLINE filterMapAuxInternal #-}

-- | /O(n)/ Filter this map by retaining only elements which values
-- satisfy a predicate.
filter :: (v -> Bool) -> HashMap k v -> HashMap k v
filter p = filterWithKey (\_ v -> p v)
{-# INLINE filter #-}

------------------------------------------------------------------------
-- * Conversions

-- TODO: Improve fusion rules by modelled them after the Prelude ones
-- on lists.

-- | /O(n)/ Return a list of this map's keys.  The list is produced
-- lazily.
keys :: HashMap k v -> [k]
keys = L.map fst . toList
{-# INLINE keys #-}

-- | /O(n)/ Return a list of this map's values.  The list is produced
-- lazily.
elems :: HashMap k v -> [v]
elems = L.map snd . toList
{-# INLINE elems #-}

------------------------------------------------------------------------
-- ** Lists

-- | /O(n)/ Return a list of this map's elements.  The list is
-- produced lazily. The order of its elements is unspecified.
toList :: HashMap k v -> [(k, v)]
toList t = build (\ c z -> foldrWithKey (curry c) z t)
{-# INLINE toList #-}

-- | /O(n)/ Construct a map with the supplied mappings.  If the list
-- contains duplicate mappings, the later mappings take precedence.
fromList :: (Eq k, Hashable k) => [(k, v)] -> HashMap k v
fromList = L.foldl' (\ m (k, v) -> unsafeInsert k v m) empty
{-# INLINABLE fromList #-}

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function to merge duplicate entries.
fromListWith :: (Eq k, Hashable k) => (v -> v -> v) -> [(k, v)] -> HashMap k v
fromListWith f = L.foldl' (\ m (k, v) -> unsafeInsertWith f k v m) empty
{-# INLINE fromListWith #-}

------------------------------------------------------------------------
-- Array operations

-- | /O(n)/ Lookup the value associated with the given key in this
-- array.  Returns 'Nothing' if the key wasn't found.
lookupInArray :: Eq k => k -> A.Array (Leaf k v) -> Maybe v
lookupInArray k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = Nothing
        | otherwise = case A.index ary i of
            (L kx v)
                | k == kx   -> Just v
                | otherwise -> go k ary (i+1) n
{-# INLINABLE lookupInArray #-}

-- | /O(n)/ Lookup the value associated with the given key in this
-- array.  Returns 'Nothing' if the key wasn't found.
indexOf :: Eq k => k -> A.Array (Leaf k v) -> Maybe Int
indexOf k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = Nothing
        | otherwise = case A.index ary i of
            (L kx _)
                | k == kx   -> Just i
                | otherwise -> go k ary (i+1) n
{-# INLINABLE indexOf #-}

updateWith :: Eq k => (v -> v) -> k -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateWith f k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = ary
        | otherwise = case A.index ary i of
            (L kx y) | k == kx   -> A.update ary i (L k (f y))
                     | otherwise -> go k ary (i+1) n
{-# INLINABLE updateWith #-}

updateOrSnocWith :: Eq k => (v -> v -> v) -> k -> v -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
updateOrSnocWith f = updateOrSnocWithKey (const f)
{-# INLINABLE updateOrSnocWith #-}

updateOrSnocWithKey :: Eq k => (k -> v -> v -> v) -> k -> v -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
updateOrSnocWithKey f k0 v0 ary0 = go k0 v0 ary0 0 (A.length ary0)
  where
    go !k v !ary !i !n
        | i >= n = A.run $ do
            -- Not found, append to the end.
            mary <- A.new_ (n + 1)
            A.copy ary 0 mary 0 n
            A.write mary n (L k v)
            return mary
        | otherwise = case A.index ary i of
            (L kx y) | k == kx   -> A.update ary i (L k (f k v y))
                     | otherwise -> go k v ary (i+1) n
{-# INLINABLE updateOrSnocWithKey #-}

updateOrConcatWith :: Eq k => (v -> v -> v) -> A.Array (Leaf k v) -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateOrConcatWith f = updateOrConcatWithKey (const f)
{-# INLINABLE updateOrConcatWith #-}

updateOrConcatWithKey :: Eq k => (k -> v -> v -> v) -> A.Array (Leaf k v) -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateOrConcatWithKey f ary1 ary2 = A.run $ do
    -- first: look up the position of each element of ary2 in ary1
    let indices = A.map (\(L k _) -> indexOf k ary1) ary2
    -- that tells us how large the overlap is:
    -- count number of Nothing constructors
    let nOnly2 = A.foldl' (\n -> maybe (n+1) (const n)) 0 indices
    let n1 = A.length ary1
    let n2 = A.length ary2
    -- copy over all elements from ary1
    mary <- A.new_ (n1 + nOnly2)
    A.copy ary1 0 mary 0 n1
    -- append or update all elements from ary2
    let go !iEnd !i2
          | i2 >= n2 = return ()
          | otherwise = case A.index indices i2 of
               Just i1 -> do -- key occurs in both arrays, store combination in position i1
                             L k v1 <- A.indexM ary1 i1
                             L _ v2 <- A.indexM ary2 i2
                             A.write mary i1 (L k (f k v1 v2))
                             go iEnd (i2+1)
               Nothing -> do -- key is only in ary2, append to end
                             A.write mary iEnd =<< A.indexM ary2 i2
                             go (iEnd+1) (i2+1)
    go n1 0
    return mary
{-# INLINABLE updateOrConcatWithKey #-}

------------------------------------------------------------------------
-- Manually unrolled loops

-- | /O(n)/ Update the element at the given position in this array.
update16 :: A.Array e -> Int -> e -> A.Array e
update16 ary idx b = runST (update16M ary idx b)
{-# INLINE update16 #-}

-- | /O(n)/ Update the element at the given position in this array.
update16M :: A.Array e -> Int -> e -> ST s (A.Array e)
update16M ary idx b = do
    mary <- clone16 ary
    A.write mary idx b
    A.unsafeFreeze mary
{-# INLINE update16M #-}

-- | /O(n)/ Update the element at the given position in this array, by applying a function to it.
update16With' :: A.Array e -> Int -> (e -> e) -> A.Array e
update16With' ary idx f = update16 ary idx $! f (A.index ary idx)
{-# INLINE update16With' #-}

-- | /O(n)/ Update the element at the given position in this array, by applying a function to it.
update16WithInternal' :: A.Array e -> Int -> (e -> A.Sized e) -> A.RunResA e
update16WithInternal' ary idx f =
    let A.Sized s x = f $! A.index ary idx
    in A.RunRes s (update16 ary idx x)
{-# INLINE update16WithInternal' #-}

-- | Unsafely clone an array of 16 elements.  The length of the input
-- array is not checked.
clone16 :: A.Array e -> ST s (A.MArray s e)
clone16 ary =
    A.thaw ary 0 16

------------------------------------------------------------------------
-- Bit twiddling

bitsPerSubkey :: Int
bitsPerSubkey = 4

maxChildren :: Int
maxChildren = fromIntegral $ 1 `unsafeShiftL` bitsPerSubkey

subkeyMask :: Bitmap
subkeyMask = 1 `unsafeShiftL` bitsPerSubkey - 1

sparseIndex :: Bitmap -> Bitmap -> Int
sparseIndex b m = popCount (b .&. (m - 1))

mask :: Word -> Shift -> Bitmap
mask w s = 1 `unsafeShiftL` index w s
{-# INLINE mask #-}

-- | Mask out the 'bitsPerSubkey' bits used for indexing at this level
-- of the tree.
index :: Hash -> Shift -> Int
index w s = fromIntegral $ (unsafeShiftR w s) .&. subkeyMask
{-# INLINE index #-}

-- | A bitmask with the 'bitsPerSubkey' least significant bits set.
fullNodeMask :: Bitmap
fullNodeMask = complement (complement 0 `unsafeShiftL` maxChildren)
{-# INLINE fullNodeMask #-}

-- | Check if the two arguments are the same value.  N.B. This
-- function might give false negatives (due to GC moving objects.)
ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y ==# 1#)
{-# INLINE ptrEq #-}

------------------------------------------------------------------------
-- IsList instance
instance (Eq k, Hashable k) => Exts.IsList (HashMap k v) where
    type Item (HashMap k v) = (k, v)
    fromList = fromList
    toList   = toList
