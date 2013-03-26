{-# LANGUAGE ConstraintKinds, DataKinds, TypeFamilies, MultiParamTypeClasses, TypeOperators, PolyKinds, UndecidableInstances, FlexibleInstances, ScopedTypeVariables #-}
module Coerce where

import qualified Data.Typeable as T (typeOf, mkTyCon3)
import Data.Rank1Typeable
import GHC.Prim
import Unsafe.Coerce

{-|

  This module allows ground representations (Data.Rank1Typeable) of
  polymorphic functions to be safely coerced into actually polymorphic
  functions. This is done by explicitly controlling polymorphism:

  Let's take the Prelude.replicate function as an example:
  replicate :: Int -> a -> [a]

  A ground representation of this type would be
  replicate' :: G Int -> ANY -> G1 [] ANY

  This can be safely coerced back into the original type:
  replicate = coerceAny replicate'

  Note that we need to tag every already ground type with
  G/G1/GK. Internally this allows us to avoid using
  OverlappingInstances. Here are a few examples on how to use these
  tags:
  
  | Original type    | Shorthand rep.              | General rep.                | Alternative rep.     |
  |------------------+-----------------------------+-----------------------------+----------------------|
  | Int              | G Int                       | GK Int '[]                  | -                    |
  | Maybe a          | G1 Maybe ANY                | GK Maybe '[ANY]             | -                    |
  | Either Error Int | G2 Either (G Error) (G Int) | GK Either '[G Error, G Int] | G (Either Error Int) |
  | Free Maybe a     | -                           | -                           | G1 (Free Maybe) ANY  |

  The first argument to these tags must always be a ground type
  constructor, and the arguments to the constructor are treated the same
  as the original type.

  The reason why the last example doesn't work in general is because
  Free has a kind (* -> *) -> * -> * which is not allowed. However (Free Maybe)
  has kind * -> *, which is why we have an alternative representation
  for it. The only types that truly cannot be represented are ones where
  the first argument to Free is left polymorphic (e.g. Free f Int).

  Question: What if I have StateT :: (* -> (* -> *) -> * -> *) and I
  have a ground monad, but want to keep the state type polymorphic?
  Answer: Well, you're out of luck, you'd need to create an alias
  newtype which flips those arguments. Bloeh. Or extend this module to
  handle your specific needs. Double bloeh.

  Interlude: To see why we need these tags consider the "ground" type
  replicate'' :: a -> ANY -> G1 [] ANY

  Internally there is no way to tell whether 'a' is going to be
  intantiated into ANY or some other type. We could use
  -XOverlappingInstances as well to disallow this type, but we want to
  avoid that extension.

  On the other hand consider
  replicate''' :: G a -> ANY -> G1 [] ANY

  This still works, because although 'a' is left
  "Haskell-polymorphic", we know it will be a ground type that we want
  to get back after the coercion.

  Limitations:

  * Only polymorphic types of kind * can be coerced.
    - There is possibly a way to extend this to other kinds but I can't
      make up a proper use case for it.
  * Monomorpic types that may take polymorphic arguments may only be
      of kind *, (* -> *), (* -> * -> *) etc. and must be tagged with
      GK. This can be manually extended to handle other kinds, however I
      don't think there is a generic solution for all kinds.
    - Basically the problem is kind-safely extracting the base type
      constructor (e.g. Maybe in (Maybe Int)) to be used in the equality
      constraints generated. We'd need a kind-level function to accurately
      describe the different arity type constructors that we want to
      extract.
    - Right now we exploit this limitation and the equality constraint
      generated for e.g. Either =?= f will be (Either () () ~ f () ())
      instead of (Either ~ f).
    - Note that the above means that if we have a type constructor
      TyCon :: (* -> *) -> * -> * then we cannot write
      (GK TyCon [G Maybe(?), G Char]), however we CAN write
      (GK (TyCon Maybe) [G Char]) which will behave as expected.

  Question: Why would anyone need this?
  Answer: In general you want such a coercion if your program needs a
  ground representation of polymorphic types and you want to recover the
  original polymorphism later. For example you may want to existentially
  hide functions and later dynamicallly cast them back. If you want to
  store polymorphic functions you need such a representation.

  Question: Ok. Let's say I want to store replicate. How would I go
  about it?
  

|-}

class CoerceAny f g where
    coerceAny :: f -> g

instance (PolyOf f g) => CoerceAny f g where
    -- | coerces a ground represented polymorphic function back into a polymorphic one
    coerceAny = unsafeCoerce

newtype GK f l = GK { unGK :: AppArgs f l }

instance (Typeable (AppArgs f l)) => Typeable (GK f l) where
    typeOf _ = let tyCon = T.mkTyCon3 "rank1dynamic-coerce" "Data.Rank1Typeable.Coerce" "GK"
                   appTyRep = typeOf (undefined :: AppArgs f l)
               in  underlyingTypeRep $ mkTyConApp tyCon [appTyRep]

type G (a :: *)                = GK a '[]
type G1 (a :: * -> *) b        = GK a '[b]
type G2 (a :: * -> * -> *) b c = GK a '[b, c]

data Nat = Zer | Suc Nat

-- carry
data C k

type family AppArgs (f :: k) (as :: [*]) :: *
type instance AppArgs f '[] = f
type instance AppArgs f (a ': as) = AppArgs (f a) as

type family Hey a :: Constraint
type instance Hey (a -> b) = Show a

type family Concat (fss :: [[k]]) :: [k]
type instance Concat '[] = '[]
type instance Concat ('[] ': fss) = Concat fss
type instance Concat ((f ': fs) ': fss) = f ': Concat (fs ': fss)

type family CollectTys (f :: *) (g :: *) :: [(*, *)]
type instance CollectTys (a -> b) (c -> d) = Concat [(CollectTys a c), (CollectTys b d)]
type instance CollectTys (TypVar n) a = '[ '(TypVar n, a) ]
type instance CollectTys (GK tc ts) a = '(C (AppArgs tc (Replicate () (Length ts))), ReplaceUnit a (Length ts)) ': Concat (CollectArgTys ts (GetTyArgs a (Length ts) '[]))

type family ReplaceUnit (f :: k) (n :: Nat) :: k
type instance ReplaceUnit f Zer = f
type instance ReplaceUnit (f a) (Suc n) = ReplaceUnit f n ()

type family Replicate a (n :: Nat) :: [*]
type instance Replicate a Zer = '[]
type instance Replicate a (Suc n) = a ': Replicate a n

type family CollectArgTys (fs :: [*]) (gs :: [*]) :: [[(*, *)]]
type instance CollectArgTys '[] '[] = '[]
type instance CollectArgTys (f ': fs) (g ': gs) = CollectTys f g ': CollectArgTys fs gs

type family GetTyArgs (f :: k) (n :: Nat) (acc :: [*]) :: [*]
type instance GetTyArgs (f k) (Suc n) acc = (GetTyArgs f n (k ': acc))
type instance GetTyArgs f Zer acc = acc

type family Length (l :: [k]) :: Nat
type instance Length '[] = Zer
type instance Length (a ': as) = Suc (Length as)

type family CreateConstraints (tys :: [(*, *)]) :: Constraint
type instance CreateConstraints '[] = ()
type instance CreateConstraints ('(TypVar n, a) ': tys) = (PolyConstraints n a tys, CreateConstraints (TakeAll n tys))
type instance CreateConstraints ('(C tc, a) ': tys) = (tc ~ a, CreateConstraints tys)

type family If (b :: Bool) (t :: k) (e :: k) :: k
type instance If True t e = t
type instance If False t e = e

type family NatEq n m :: Bool
type instance NatEq Zero Zero = True
type instance NatEq (Succ n) Zero = False
type instance NatEq Zero (Succ n) = False
type instance NatEq (Succ n) (Succ m) = NatEq n m

type family PolyConstraints n a (tys :: [(*, *)]) :: Constraint
type instance PolyConstraints n a '[] = ()
type instance PolyConstraints n a ('(TypVar m, b) ': tys) = (If (NatEq n m) (a ~ b) (), PolyConstraints n a tys)
type instance PolyConstraints n a ('(C tc, ty) ': tys) = PolyConstraints n a tys

type family TakeAll n (tys :: [(*, *)]) :: [(*, *)]
type instance TakeAll n '[] = '[]
type instance TakeAll n ('(TypVar m, b) ': tys) = If (NatEq n m) (TakeAll n tys) ('(TypVar m, b) ': TakeAll n tys)
type instance TakeAll n ('(C tc, a) ': tys) = ('(C tc, a) ': TakeAll n tys)

class (CreateConstraints (CollectTys f g)) => PolyOf f g
instance (CreateConstraints (CollectTys f g)) => PolyOf f g

-- replicate' :: G Int -> ANY -> G1 [] ANY
-- replicate' (GK 0) _ = GK []
-- replicate' (GK n) a = GK $ a : unGK (replicate' (GK (n - 1)) a)

-- hah :: Int -> a -> [a]
-- hah = coerceAny replicate'
