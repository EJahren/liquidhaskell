module Foo where

-- THIS SHOULD BE UNSAFE......
{-@ cmp' :: forall < p :: xx:b -> c -> Prop
                  , q :: yy:a -> b -> Prop>.
     (x:b -> c) -> g:(x:a -> b) -> y:a -> 
      exists[z:b].c<p z>
 @-}


cmp' :: (b -> c) -> (a -> b) -> a -> c
cmp' f g x = f (g x)





{-@ cmp :: forall < p :: xx:b -> c -> Prop
                  , q :: yy:a -> b -> Prop>.
     (x:b -> c<p x>) -> g:(x:a -> b<q x>) -> y:a -> 
      exists[z:b<q y>].c<p z>
 @-}


cmp :: (b -> c) -> (a -> b) -> a -> c
cmp f g x = f (g x)




{-@ foo :: forall < p :: xx:a -> a -> Prop
                 , q :: yy:a -> a -> Prop>.
     (x:a -> a<p x>) -> g:(x:a -> a<q x>) -> y:a -> 
      exists[z:a<q y>].a<p z>
 @-}


foo :: (a -> a) -> (a -> a) -> a -> a
foo f g x =
  let s1 = g x in 
  let s2 = g x in if bar () then f s2 else f s1

bar _ = 9==0
