module Ruitenburg where

import qualified Prelude


__ :: any
__ = Prelude.error "Logical or arity value used"

data Nat =
   O
 | S Nat deriving Prelude.Show

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons y l' -> S (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p0 -> S (plus p0 m)}

mult :: Nat -> Nat -> Nat
mult n m =
  case n of {
   O -> O;
   S p0 -> plus m (mult p0 m)}

minus :: Nat -> Nat -> Nat
minus n m =
  case n of {
   O -> n;
   S k ->
    case m of {
     O -> n;
     S l -> minus k l}}

max :: Nat -> Nat -> Nat
max n m =
  case n of {
   O -> m;
   S n' ->
    case m of {
     O -> n;
     S m' -> S (max n' m')}}

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
in_dec h a l =
  list_rec Right (\a0 l0 iHl ->
    let {s = h a0 a} in
    case s of {
     Left -> Left;
     Right -> iHl}) l

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

eq_nat_dec :: Nat -> Nat -> Sumbool
eq_nat_dec n =
  nat_rec (\m ->
    case m of {
     O -> Left;
     S m0 -> Right}) (\n0 iHn m ->
    case m of {
     O -> Right;
     S m0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (iHn m0)}) n

data Form =
   Var Nat
 | Imp Form Form
 | And Form Form
 | Or Form Form
 | Tt
 | Ff

form_rect :: (Nat -> a1) -> (Form -> a1 -> Form -> a1 -> a1) -> (Form -> a1
             -> Form -> a1 -> a1) -> (Form -> a1 -> Form -> a1 -> a1) -> a1
             -> a1 -> Form -> a1
form_rect f f0 f1 f2 f3 f4 f5 =
  case f5 of {
   Var n -> f n;
   Imp f6 f7 ->
    f0 f6 (form_rect f f0 f1 f2 f3 f4 f6) f7 (form_rect f f0 f1 f2 f3 f4 f7);
   And f6 f7 ->
    f1 f6 (form_rect f f0 f1 f2 f3 f4 f6) f7 (form_rect f f0 f1 f2 f3 f4 f7);
   Or f6 f7 ->
    f2 f6 (form_rect f f0 f1 f2 f3 f4 f6) f7 (form_rect f f0 f1 f2 f3 f4 f7);
   Tt -> f3;
   Ff -> f4}

form_rec :: (Nat -> a1) -> (Form -> a1 -> Form -> a1 -> a1) -> (Form -> a1 ->
            Form -> a1 -> a1) -> (Form -> a1 -> Form -> a1 -> a1) -> a1 -> a1
            -> Form -> a1
form_rec =
  form_rect

dceq_v :: Nat -> Nat -> Sumbool
dceq_v n =
  nat_rec (\n0 ->
    case n0 of {
     O -> Left;
     S n1 -> Right}) (\n0 iHn n1 ->
    case n1 of {
     O -> Right;
     S n2 -> iHn n2}) n

dceq_f :: Form -> Form -> Sumbool
dceq_f a =
  form_rec (\n b ->
    case b of {
     Var n0 -> dceq_v n n0;
     _ -> Right}) (\a1 iHA1 a2 iHA2 b ->
    case b of {
     Imp b1 b2 ->
      let {s = iHA1 b1} in
      case s of {
       Left -> iHA2 b2;
       Right -> Right};
     _ -> Right}) (\a1 iHA1 a2 iHA2 b ->
    case b of {
     And b1 b2 ->
      let {s = iHA1 b1} in
      case s of {
       Left -> iHA2 b2;
       Right -> Right};
     _ -> Right}) (\a1 iHA1 a2 iHA2 b ->
    case b of {
     Or b1 b2 ->
      let {s = iHA1 b1} in
      case s of {
       Left -> iHA2 b2;
       Right -> Right};
     _ -> Right}) (\b ->
    case b of {
     Tt -> Left;
     _ -> Right}) (\b ->
    case b of {
     Ff -> Left;
     _ -> Right}) a

p :: Form
p =
  Var O

q :: Form
q =
  Var (S O)

r :: Form
r =
  Var (S (S O))

sub :: (Nat -> Form) -> Form -> Form
sub s a =
  case a of {
   Var i -> s i;
   Imp a0 b -> Imp (sub s a0) (sub s b);
   And a0 b -> And (sub s a0) (sub s b);
   Or a0 b -> Or (sub s a0) (sub s b);
   x -> x}

s_n :: Nat -> Form -> Nat -> Form
s_n n a m =
  case eq_nat_dec n m of {
   Left -> a;
   Right -> Var m}

s_p :: Form -> Nat -> Form
s_p =
  s_n O

dup_rem :: (List Form) -> List Form
dup_rem g =
  case g of {
   Nil -> Nil;
   Cons a g' ->
    case in_dec dceq_f a g' of {
     Left -> dup_rem g';
     Right -> Cons a (dup_rem g')}}

mb_red :: Form -> List Form
mb_red a =
  case a of {
   Var i -> Cons (sub (s_p Tt) (Var i)) (Cons Tt Nil);
   Imp b c -> Cons (sub (s_p Tt) (Imp b c)) (app (mb_red b) (mb_red c));
   And b c -> app (mb_red b) (mb_red c);
   Or b c -> app (mb_red b) (mb_red c);
   _ -> Cons Tt Nil}

exform1 :: Form
exform1 =
  And (Imp q (Imp p r)) (Imp (Imp p r) (Or p r))

t_optimize :: Form -> Form
t_optimize a =
  case a of {
   Imp b c ->
    case b of {
     Tt -> t_optimize c;
     _ ->
      case c of {
       Tt -> Tt;
       _ -> Imp (t_optimize b) (t_optimize c)}};
   And b c ->
    case b of {
     Tt ->
      case c of {
       Tt -> t_optimize b;
       _ -> t_optimize c};
     _ ->
      case c of {
       Tt -> t_optimize b;
       _ -> And (t_optimize b) (t_optimize c)}};
   Or b c ->
    case b of {
     Tt -> Tt;
     _ ->
      case c of {
       Tt -> Tt;
       _ -> Or (t_optimize b) (t_optimize c)}};
   _ -> a}

frm_dep :: Form -> Nat
frm_dep a =
  case a of {
   Imp b c -> plus (max (frm_dep b) (frm_dep c)) (S O);
   And b c -> plus (max (frm_dep b) (frm_dep c)) (S O);
   Or b c -> plus (max (frm_dep b) (frm_dep c)) (S O);
   _ -> O}

iterator :: Nat -> (a1 -> a1) -> a1 -> a1
iterator n x x0 =
  case n of {
   O -> x x0;
   S n' -> x (iterator n' x x0)}

optimized_bound_param :: Form -> Nat -> List Form
optimized_bound_param a n =
  dup_rem (map (iterator n t_optimize) (mb_red a))

optimized_bound :: Form -> List Form
optimized_bound a =
  optimized_bound_param a (frm_dep a)

frm_len :: Form -> Nat
frm_len a =
  case a of {
   Imp b c -> plus (plus (frm_len b) (frm_len c)) (S O);
   And b c -> plus (plus (frm_len b) (frm_len c)) (S O);
   Or b c -> plus (plus (frm_len b) (frm_len c)) (S O);
   _ -> S O}

p_occ :: Form -> Nat
p_occ a =
  case a of {
   Var n ->
    case n of {
     O -> S O;
     S n' -> O};
   Imp b c -> plus (p_occ b) (p_occ c);
   And b c -> plus (p_occ b) (p_occ c);
   Or b c -> plus (p_occ b) (p_occ c);
   _ -> O}

length_of_f_p :: Form -> Nat -> Prod Nat Nat
length_of_f_p a n =
  case n of {
   O -> Pair (S O) (S O);
   S n' ->
    case length_of_f_p a n' of {
     Pair l o ->
      let {pA = p_occ a} in
      Pair (minus (plus (mult pA l) (frm_len a)) pA) (mult pA o)}}

optimized_cycle :: Form -> Prod (Prod (Prod Nat (List Form)) Nat) Nat
optimized_cycle a =
  let {b = optimized_bound a} in
  let {m = length b} in
  case length_of_f_p a (plus (mult (S (S O)) m) (S (S O))) of {
   Pair len occ -> Pair (Pair (Pair m b) (plus (mult (S (S O)) m) (S (S O))))
    len}

cycle_formula_length :: Form -> Nat
cycle_formula_length a =
  let {b = optimized_bound a} in
  let {m = length b} in
  case length_of_f_p a (plus (mult (S (S O)) m) (S (S O))) of {
   Pair len x -> len}

