******************************************************************************
**********                                                          **********
**********     Category.lhs --- categorical gizmos                  **********
**********                                                          **********
******************************************************************************

> module Category where


******************************************************************************
Favourite function spaces
******************************************************************************

> type BinOp x = x -> x -> x



******************************************************************************
Unpack
******************************************************************************

> class Unpack s t | s -> t where
>   un :: s -> t
>   nu :: t -> s

Unpack is my way of specify standard coercions. Usually, s is a newtype,
packaging t to indicate some specific purpose to which t's are being put.



******************************************************************************
Id, Comp, K, Cross, Endo
******************************************************************************

> newtype Id x = Id x deriving (Show,Eq)

> instance Unpack (Id x) x where
>   un (Id x) = x
>   nu = Id


> newtype Comp f g x = Comp (f (g x))

> instance Unpack (Comp f g x) (f (g x)) where
>   un (Comp x) = x
>   nu = Comp


> newtype K s t = K s deriving (Show,Eq)

> instance Unpack (K s t) s where
>   un (K x) = x
>   nu = K


> infixr 5 :*:
> data Cross f g x = f x :*: g x deriving Show


> newtype Endo x = Endo (x -> x)

> instance Unpack (Endo x) (x -> x) where
>   un (Endo f) = f
>   nu = Endo

> newtype Odne x = Odne (x -> x)

> instance Unpack (Odne x) (x -> x) where
>   un (Odne f) = f
>   nu = Odne


******************************************************************************
Fun
******************************************************************************

A type constructor is Fun if it can be pushed through ->.

> infixl 9 <$>
> class Fun f where
>   eta :: x -> f x
>   (<$>) :: f (s -> t) -> f s -> f t

Useful special cases

> infixl 9 </>
> (</>) :: Fun f => f s -> f t -> f s
> fs </> ft = eta const <$> fs <$> ft

> infixl 9 <\>
> (<\>) :: Fun f => f s -> f t -> f t
> fs <\> ft = eta (const id) <$> fs <$> ft

> funMap :: Fun f => (s -> t) -> f s -> f t
> funMap f = (eta f <$>)


> instance Fun Id where
>   eta = nu
>   Id f <$> Id s = Id (f s)

> instance (Fun f,Fun g) => Fun (Comp f g) where
>   eta = Comp . eta . eta
>   Comp fgh <$> Comp fgx = Comp (funMap (<$>) fgh <$> fgx)

> instance (Fun f,Fun g) => Fun (Cross f g) where
>   eta x = eta x :*: eta x
>   (f :*: g) <$> (x :*: y) = f <$> x :*: g <$> y



******************************************************************************
Funnel
******************************************************************************

This type-level operation computes the lifting of a function through a Fun f.

> class Fun f => Funnel f s t | f s -> t, s t -> f, f t -> s where
>   fun :: s -> t
>   funnel :: f s -> t

> instance Funnel f t u => Funnel f (s -> t) (f s -> u) where
>   fun g = funnel (eta g)
>   funnel fg fx = funnel (fg <$> fx)

Every datatype should be given a base Funnel instance. Here's a handy
emacs function to generate it!

(defun base-funnel (data) (insert (concat "\n\n"
"> instance Fun f => Funnel f " data " (f " data") where\n"
">   fun    = eta\n"
">   funnel = id\n"
)))

(base-funnel "(Id x)")

> instance Fun f => Funnel f (Id x) (f (Id x)) where
>   fun    = eta
>   funnel = id


(base-funnel "(Comp g h x)")

> instance Fun f => Funnel f (Comp g h x) (f (Comp g h x)) where
>   fun    = eta
>   funnel = id


(base-funnel "(K s t)")

> instance Fun f => Funnel f (K s t) (f (K s t)) where
>   fun    = eta
>   funnel = id


(base-funnel "(Cross g h x)")

> instance Fun f => Funnel f (Cross g h x) (f (Cross g h x)) where
>   fun    = eta
>   funnel = id


(base-funnel "(Endo x)")

> instance Fun f => Funnel f (Endo x) (f (Endo x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(Odne x)")

> instance Fun f => Funnel f (Odne x) (f (Odne x)) where
>   fun    = eta
>   funnel = id



******************************************************************************
Functorial
******************************************************************************

> infixl 9 <^>
> class Functorial g where
>   (<^>) :: Fun f => (s -> f t) -> g s -> f (g t)

> infixl 9 <^^>
> (<^^>) :: (Fun f,Functorial g,Functorial h) =>
>            (s -> f t) -> g (h s) -> f (g (h t))
> f <^^> ghs = (f <^>) <^> ghs

> up :: Functorial g => (s -> t) -> g s -> g t
> up g gs = un ((Id . g) <^> gs)

> up2 :: (Functorial h,Functorial g) => (s -> t) -> g (h s) -> g (h t)
> up2 = up . up

We can write <^> by the usual method, but using fun to lift the constructors.
Lists, for example:

> instance Functorial [] where
>   g <^> []       = fun []
>   g <^> (x : xs) = fun (:) (g x) (g <^> xs)

> instance Functorial (K s) where
>   g <^> K x = fun (K x)

> instance Functorial Id where
>   g <^> Id x = fun Id (g x)

> instance (Functorial g,Functorial h) => Functorial (Comp g h) where
>   g <^> Comp x = fun Comp (g <^^> x)

> instance (Functorial g,Functorial h) => Functorial (Cross g h) where
>   g <^> (x :*: y) = eta (:*:) <$> (g <^> x) <$> (g <^> y)

   g <^> (x :*: y) = fun (:*:) (g <^> x) (g <^> y) -- ditto


******************************************************************************
Products
******************************************************************************

> infixl 9 <$$>
> (<$$>) :: (s1 -> t1,s2 -> t2) -> (s1,s2) -> (t1,t2)
> (f,g) <$$> (x,y) = (f x,g y)

> delta :: x -> (x,x)
> delta x = (x,x)



******************************************************************************
Monoidal
******************************************************************************

> infixr 5 <+>
> class Monoidal x where
>   m0 :: x
>   (<+>) :: BinOp x

> instance Monoidal t => Monoidal (s -> t) where
>   m0 = const m0
>   (f <+> g) x = f x <+> g x

> to :: s -> (s -> t) -> t
> to a f = f a

> instance Monoidal s => Fun (K s) where
>   eta _ = K m0
>   K x <$> K y = K (x <+> y)

> infixl 9 <!>

> (<!>) :: (Functorial g,Monoidal s) => (x -> s) -> g x -> s
> f <!> gx = un ((K . f) <^> gx)

> instance Monoidal (Endo x) where
>   m0 = Endo id
>   Endo f <+> Endo g = Endo (f . g)

> action :: Functorial g => (x -> y -> y) -> g x -> y -> y
> action f gx = un ((Endo . f) <!> gx)

> instance Monoidal (Odne x) where
>   m0 = Odne id
>   Odne f <+> Odne g = Odne (g . f)

> noitca :: Functorial g => (y -> x -> y) -> y -> g x -> y
> noitca f y gx = un ((Odne . flip f) <!> gx) y

> when :: Monoidal s => Bool -> s -> s
> when False = m0
> when True  = id

> instance Monoidal () where
>   m0 = ()
>   _ <+> _ = ()

> instance Monoidal [x] where
>   m0 = []
>   (<+>) = (++)

> instance (Monoidal x,Monoidal y) => Monoidal (x,y) where
>   m0 = (m0,m0)
>   (x1,y1) <+> (x2,y2) = (x1 <+> x2,y1 <+> y2)

> instance Monoidal Int where
>   m0 = 0
>   (<+>) = (+)

> instance (Monoidal (f x),Monoidal (g x)) => Monoidal (Cross f g x) where
>   m0 = m0 :*: m0
>   (x1 :*: y1) <+> (x2 :*: y2) = (x1 <+> x2) :*: (y1 <+> y2)


******************************************************************************
Funnels for standard datatypes
******************************************************************************

(base-funnel "()")

> instance Fun f => Funnel f () (f ()) where
>   fun    = eta
>   funnel = id


(base-funnel "Bool")

> instance Fun f => Funnel f Bool (f Bool) where
>   fun    = eta
>   funnel = id


(base-funnel "(x,y)")

> instance Fun f => Funnel f (x,y) (f (x,y)) where
>   fun    = eta
>   funnel = id


(base-funnel "[x]")

> instance Fun f => Funnel f [x] (f [x]) where
>   fun    = eta
>   funnel = id


(base-funnel "(Maybe x)")

> instance Fun f => Funnel f (Maybe x) (f (Maybe x)) where
>   fun    = eta
>   funnel = id


(base-funnel "(Either x y)")

> instance Fun f => Funnel f (Either x y) (f (Either x y)) where
>   fun    = eta
>   funnel = id


(base-funnel "Int")

> instance Fun f => Funnel f Int (f Int) where
>   fun    = eta
>   funnel = id


(base-funnel "Char")

> instance Fun f => Funnel f Char (f Char) where
>   fun    = eta
>   funnel = id


