{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes      #-}

-- | Infrastructure for working with indexed sets
module Cardano.Wallet.Kernel.DB.Util.IxSet (
    -- * Primary keys
    HasPrimKey(..)
  , OrdByPrimKey -- opaque
    -- * Wrapper around IxSet
  , IndicesOf
  , IxSet
  , Indexable
    -- * Building 'Indexable' instances
  , ixFun
  , ixList
    -- * Queries
  , getEQ
  , member
  , size
  , null
  , getOne
  , toMap
    -- * Construction
  , fromList
  , singleton
  , omap
  , otraverse
  , foldl'
  , emptyIxSet
    -- * Destruction
  , toList
  ) where

import qualified Prelude
import           Universum hiding (Foldable, foldl', null, toList)

import qualified Control.Lens as Lens
import           Data.Coerce (coerce)
import           Data.Foldable (Foldable)
import qualified Data.Foldable
import qualified Data.IxSet.Typed as IxSet
import qualified Data.Map.Strict as Map
import           Data.SafeCopy (SafeCopy (..))
import qualified Data.Set as Set
import qualified Data.Traversable

-- Imports needed for the various instances
import           Formatting (bprint, build)
import qualified Formatting.Buildable
import           Pos.Core.Util.LogSafe (BuildableSafe, SecureLog, buildSafeList,
                     getSecureLog, secure)
import           Serokell.Util (listJsonIndent)
import           Test.QuickCheck (Arbitrary (..))

{-# ANN module ("HLint: ignore Unnecessary hiding" :: Text) #-}

{-------------------------------------------------------------------------------
  Primary keys
-------------------------------------------------------------------------------}

-- | Type equipped with a primary key
--
-- The key assumption is that such types can be compared for equality and
-- sorted using their primary key only.
class Ord (PrimKey a) => HasPrimKey a where
  type PrimKey a :: *
  primKey :: a -> PrimKey a

-- | Newtype wrapper around a type that uses the type's primary key for
-- equality and ordering comparisons.
--
-- Unfortunately we cannot keep this type entirely internally, since we need
-- it in 'Indexable' instances. TODO: Is that fixable?
newtype OrdByPrimKey a = WrapOrdByPrimKey { unwrapOrdByPrimKey :: a }

instance HasPrimKey a => Eq (OrdByPrimKey a) where
  (==) = (==) `on` (primKey . unwrapOrdByPrimKey)

instance HasPrimKey a => Ord (OrdByPrimKey a) where
  compare = compare `on` (primKey . unwrapOrdByPrimKey)

instance Buildable a => Buildable (OrdByPrimKey a) where
    build (WrapOrdByPrimKey o) = bprint build o

{-------------------------------------------------------------------------------
  Wrap IxSet
-------------------------------------------------------------------------------}

-- | Static set of indices per type
type family IndicesOf (a :: *) :: [*]

-- | Wrapper around IxSet
--
-- This is an 'IxSet' with a fixed set of indices ('IndicesOf') as well as
-- a primary key.
--
-- NOTE: This module is intended as a replacement for an import of "Data.IxSet",
-- so we use the same names as "Data.IxSet" uses.
newtype IxSet a = WrapIxSet {
      unwrapIxSet :: IxSet.IxSet (PrimKey a ': IndicesOf a) (OrdByPrimKey a)
    }

instance Show a => Show (IxSet a) where
    show = show . toList

-- | Evidence that the specified indices are in fact available
type Indexable a = IxSet.Indexable (PrimKey a ': IndicesOf a) (OrdByPrimKey a)

-- | Evidence that something is an index
type IsIndexOf ix a = IxSet.IsIndexOf ix (PrimKey a ': IndicesOf a)

{-------------------------------------------------------------------------------
  Safecopy
-------------------------------------------------------------------------------}

instance SafeCopy a => SafeCopy (IxSet a) where
  getCopy = error "getCopy for IxSet wrapper"
  putCopy = error "putCopy for IxSet wrapper"

{-------------------------------------------------------------------------------
  Building 'Indexable' instances
-------------------------------------------------------------------------------}

ixFun :: Ord ix => (a -> [ix]) -> IxSet.Ix ix (OrdByPrimKey a)
ixFun f = IxSet.ixFun (f . unwrapOrdByPrimKey)

ixList :: ( HasPrimKey a
          , IxSet.MkIxList ixs (PrimKey a : ixs) (OrdByPrimKey a) r
          )
       => r
ixList = IxSet.ixList (ixFun ((:[]) . primKey))

{-------------------------------------------------------------------------------
  Lens instances for the primary key
-------------------------------------------------------------------------------}

type instance Lens.Index   (IxSet a) = PrimKey a
type instance Lens.IxValue (IxSet a) = a

instance (HasPrimKey a, Indexable a) => Lens.Ixed (IxSet a) where
  ix pk f (WrapIxSet s) =
      case IxSet.getOne (IxSet.getEQ pk s) of
        Nothing -> pure $ WrapIxSet s
        Just a  -> upd <$> f (unwrapOrdByPrimKey a)
    where
      upd :: a -> IxSet a
      upd a = WrapIxSet $ IxSet.updateIx pk (WrapOrdByPrimKey a) s

instance (HasPrimKey a, Indexable a) => Lens.At (IxSet a) where
  at pk f (WrapIxSet s) =
      upd <$> f (unwrapOrdByPrimKey <$> IxSet.getOne (IxSet.getEQ pk s))
    where
      upd :: Maybe a -> IxSet a
      upd Nothing  = WrapIxSet $ IxSet.deleteIx pk                      s
      upd (Just a) = WrapIxSet $ IxSet.updateIx pk (WrapOrdByPrimKey a) s

{-------------------------------------------------------------------------------
  Queries
-------------------------------------------------------------------------------}

getEQ :: (Indexable a, IsIndexOf ix a) => ix -> IxSet a -> IxSet a
getEQ ix = WrapIxSet . IxSet.getEQ ix . unwrapIxSet

member :: (HasPrimKey a, Indexable a) => PrimKey a -> IxSet a -> Bool
member pk = isJust . view (Lens.at pk)

size :: IxSet a -> Int
size = IxSet.size . unwrapIxSet

-- | Whether or not this 'IxSet' contains no elements.
null :: IxSet a -> Bool
null = IxSet.null . unwrapIxSet

-- | Safely returns the 'head' of this 'IxSet', but only if it is a singleton
-- one, i.e. only if it has @exactly@ one element in it. Usually this is
-- used in tandem with 'getEQ' to witness the existence of exactly one element
-- in the set indexed by a particular index.
getOne :: HasPrimKey a => IxSet a -> Maybe a
getOne = fmap coerce . IxSet.getOne . unwrapIxSet

-- | Project out the underlying set
--
-- Use with caution! This loses all the indices, potentially losing all the
-- benefits that 'IxSet' provides.
toMap :: HasPrimKey a => IxSet a -> Map (PrimKey a) a
toMap = Map.mapKeysMonotonic (primKey . unwrapOrdByPrimKey)
      . Map.fromSet unwrapOrdByPrimKey
      . IxSet.toSet
      . unwrapIxSet

{-------------------------------------------------------------------------------
  Construction
-------------------------------------------------------------------------------}

-- | Construct 'IxSet' from a list
fromList :: Indexable a => [a] -> IxSet a
fromList = WrapIxSet . IxSet.fromList . coerce

-- | Construct 'IxSet' from a single element
singleton :: Indexable a => a -> IxSet a
singleton = fromList . (:[])

-- | Monomorphic map over an 'IxSet'
--
-- Since we assume that the primary keys never change, we do not need to
-- build the set itself. However, we do need to rebuild the indices.
omap :: forall a. Indexable a => (a -> a) -> IxSet a -> IxSet a
omap f =
      WrapIxSet
    . IxSet.fromSet
    . Set.mapMonotonic (coerce f)
    . IxSet.toSet
    . unwrapIxSet

-- | Monomorphic traversal over an 'IxSet'
--
-- NOTE: This rebuilds the entire 'IxSet'. Potentially expensive.
otraverse :: (Applicative f, Indexable a)
          => (a -> f a) -> IxSet a -> f (IxSet a)
otraverse f = fmap fromList . Data.Traversable.traverse f . toList

emptyIxSet :: forall a.
              Indexable a
           => IxSet a
emptyIxSet = WrapIxSet IxSet.empty

-- | Strict left fold over an 'IxSet'.
foldl' :: (acc -> a -> acc)
       -> acc
       -> IxSet a
       -> acc
foldl' f initialValue (WrapIxSet nativeSet) =
    Data.Foldable.foldl' (\acc (WrapOrdByPrimKey a) -> f acc a)
                         initialValue
                         nativeSet

-- | Right fold
foldrIxSet :: (a -> acc -> acc)
           -> acc
           -> IxSet a
           -> acc
foldrIxSet f initialValue (WrapIxSet nativeSet) =
    Data.Foldable.foldr (\(WrapOrdByPrimKey a) acc -> f a acc)
                        initialValue
                        nativeSet

instance Foldable IxSet where
    foldr = foldrIxSet

{-------------------------------------------------------------------------------
  Destruction
-------------------------------------------------------------------------------}

-- | Converts the 'IxSet' back into a plain list. You need to use this function
-- with care as unwrapping the 'IxSet' means losing the performance advantages
-- of using it in the first place.
-- You probably want to use this function only at application boundaries, i.e.
-- before the data gets consumed by the web handlers.
toList :: IxSet a -> [a]
toList = coerce . IxSet.toList . unwrapIxSet

{-------------------------------------------------------------------------------
  Other miscellanea instances for IxSet
-------------------------------------------------------------------------------}

instance (Indexable a, Arbitrary a) => Arbitrary (IxSet a) where
    arbitrary = fromList <$> arbitrary

instance Buildable a => Buildable (IxSet a) where
    build = bprint (listJsonIndent 4) . toList

instance BuildableSafe a => Buildable (SecureLog (IxSet a)) where
    build = bprint (buildSafeList secure) . toList . getSecureLog
