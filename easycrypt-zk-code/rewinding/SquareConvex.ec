require import Distr.
require import List.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete.
require import RealFun RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.

section.

op square (x : real) : real = x ^ 2.


(* basics *)
local lemma iji : forall d, 0%r <= d => d <= 1%r => d - 1%r <= 0%r.
move => d p1 p2. smt(). qed.

local lemma iyi : forall d a, d <= 0%r => a >= 0%r  => d * a <= 0%r.
move => d p1 p2. smt(). qed.

local lemma sq_lemma1p : forall (a b : real), (a + b)^2 = a^2 + 2%r*a*b + b^2.
by smt(@Real). qed.

local lemma sq_lemma1m : forall (a b : real), (a - b)^2 = a^2 - 2%r*a*b + b^2.
by smt(@Real). qed.

local lemma sq_lemma2 : forall (a b : real), (a * b)^2 = a^2 * b^2.
by smt(@Real). qed.

local lemma sq_lemma5 : 1%r ^ 2 = 1%r.
by smt(@Real). qed.

local lemma sq_lemma6 : forall (a b c : real) , a - (b - c) = a - b + c.
smt(). qed.

local lemma sq_lemma7 : forall (a b c : real) , a + (b - c) = a + b - c.
by smt(). qed.

local lemma sq_lemma8 : forall (a b c : real), a * (b * c) = a * b * c.
by smt(). qed.

local lemma sq_lemma9 : forall (a b c : real) , a + (b + c) = a + b + c.
by smt(). qed.

local lemma sq_lemma10 : forall (a b c d : real), a * (b -c + d) = a*b -a*c + a *d .
by smt(). qed.

local lemma sq_lemma11 : forall (a : real), a * a = a^2.
by smt(@Real). qed.

local lemma sq_lemma3 : forall (a b c : real), (a - b) * c = a*c - b * c.
by smt(). qed.

local lemma sq_lemma3' : forall (c a b : real), c * (a - b) = a*c - b * c.
by smt(). qed.

local lemma sq_lemma4 : forall (a b c : real), (a + b) * c = a*c + b * c.
by smt(). qed.

local lemma sq_lemma4' : forall (a b c : real), c * (a + b) = a*c + b * c.
by smt(). qed.

local lemma sq_lemmapos : forall (a : real), a^2 >= 0%r. 
smt(@Real). qed.
    
(* smt(@Real sq_lemma4' sq_lemma4 sq_lemma3 sq_lemma3' sq_lemma11 sq_lemma10 sq_lemma9 sq_lemma8 sq_lemma7 sq_lemma6 sq_lemma5 sq_lemma2 sq_lemma1p sq_lemma1m) *)
lemma square_convex : forall (a b : real), convex square a b.
move => a b.
simplify convex. move => d p1.
simplify square.
pose z := (1%r - d).
have : z <= 1%r.
smt().
move => zp.
have s1 : (d * a + z * b) ^ 2 = (d * a)^2 
          + 2%r * (d * a) * (z * b) + (z * b)^2. smt(sq_lemma1p sq_lemma1m). rewrite s1.
have s2 : (d * a)^2  + 2%r * (d * a) * (z * b) + (z * b)^2 
          = d^2 * a^2  + 2%r * (d * a) * (z * b) + z^2 * b^2. 
smt (sq_lemma2). rewrite s2.
have  eqts : d ^ 2 * a ^ 2 + 2%r * (d * a) * (z * b) 
            + z ^ 2 * b ^ 2 - d * a ^ 2 - z * b ^ 2 <= 0%r.
have ze : z = 1%r - d. smt(). rewrite ze.
rewrite (sq_lemma1m (1%r) d).
simplify.
rewrite (sq_lemma3 1%r d (b ^ 2)).
simplify.
rewrite (sq_lemma3 1%r d b). simplify.
rewrite sq_lemma5.
rewrite (sq_lemma4 (1%r - 2%r * d) (d^2) (b^2)). simplify.          
rewrite (sq_lemma3' (2%r * (d * a)) b  (d *b)).
rewrite (sq_lemma3 1%r ((2%r) * d) (b^2)).
simplify.
rewrite (sq_lemma6 ((d ^ 2) * a ^ 2 + (b * (2%r * (d * a)) 
          - d * b * (2%r * (d * a))) + (b ^ 2 - 2%r * d * b ^ 2 + d ^ 2 * b ^ 2) 
          - d * a ^ 2) (b ^ 2) (d * b ^ 2)).
rewrite (sq_lemma7 (d ^ 2 * a ^ 2) (b * (2%r * (d * a))) 
                   (d * b * (2%r * (d * a)))). 
rewrite (sq_lemma8 2%r d a).
rewrite (sq_lemma8 (d*b) (2%r * d) a).
rewrite (sq_lemma8 (d*b) 2%r d).
rewrite (sq_lemma8 b (2%r * d) a).
rewrite (sq_lemma8 b 2%r d).
rewrite (sq_lemma9 (d ^ 2 * a ^ 2 + b * 2%r * d * a - d * b * 2%r * d * a) 
                   (b ^ 2 - 2%r * d * b ^ 2) (d ^ 2 * b ^ 2)).
rewrite (sq_lemma7 (d ^ 2 * a ^ 2 + b * 2%r * d * a - d * b * 2%r * d * a) 
           (b ^ 2)  (2%r * d * b ^ 2)).
have me : d ^ 2 * a ^ 2 + b * 2%r * d * a - d * b * 2%r * d * a 
           + b ^ 2 - 2%r * d * b ^ 2 + d ^ 2 * b ^ 2 - d * a ^ 2 - b ^ 2 
           + d * b ^ 2 
            = d ^ 2 * a ^ 2 + b * 2%r * d * a 
              - d * b * 2%r * d * a - 2%r * d * b ^ 2 
              + d ^ 2 * b ^ 2 - d * a ^ 2 + d * b ^ 2.
smt (sq_lemma1p sq_lemma1m sq_lemma2 sq_lemma3 sq_lemma3' 
     sq_lemma4 sq_lemma4' sq_lemma5 sq_lemma6 sq_lemma7 
     sq_lemma8 sq_lemma9).
rewrite me.
have me2 : d ^ 2 * a ^ 2 + b * 2%r * d * a - d * b * 2%r * d * a 
           - 2%r * d * b ^ 2 +
             d ^ 2 * b ^ 2 - d * a ^ 2 + d * b ^ 2 
          = d ^ 2 * a ^ 2 + b * 2%r * d * a - d * b * 2%r * d * a 
            - d * b ^ 2 + d ^ 2 * b ^ 2 - d * a ^ 2.
smt().
rewrite me2.
have me3 : d * (d - 1%r) * (a - b)^2 = d ^ 2 * a ^ 2 
               + b * 2%r * d * a - d * b * 2%r * d * a - d * b ^ 2 
               + d ^ 2 * b ^ 2 - d * a ^ 2.
rewrite (sq_lemma1m a b).
rewrite (sq_lemma3' d d 1%r).
rewrite (sq_lemma10 (d * d - 1%r * d) (a ^ 2) (2%r * a * b) (b ^ 2)). simplify.
rewrite (sq_lemma3 (d * d) d (a ^2)). rewrite (sq_lemma3 (d * d) d (b ^2)).
rewrite (sq_lemma3 (d * d) d (2%r * a * b)).
rewrite (sq_lemma11 d).
rewrite (sq_lemma6 (d ^ 2 * a ^ 2 - d * a ^ 2) (d ^ 2 * (2%r * a * b)) 
                   (d * (2%r * a * b))).
rewrite (sq_lemma7 (d ^ 2 * a ^ 2 - d * a ^ 2 - d ^ 2 * (2%r * a * b) 
                     + d * (2%r * a * b)) (d ^ 2 * b ^ 2) (d * b ^ 2)).
have : d ^ 2 * (2%r * a * b)  =  d * b * 2%r * d * a. 
rewrite - (sq_lemma11 d). smt().
move => q. rewrite q.
have : d * (2%r * a * b) =  b * 2%r * d * a. smt().
move => qq. rewrite qq. smt().
rewrite - me3.  
have : d * (d - 1%r) * (a - b) ^ 2 = (d - 1%r) * (d * (a - b) ^ 2). smt().
move => wo. rewrite wo.
have ko : (d-1%r) <= 0%r. clear me me2 me3  wo ze s2 s1 zp. smt().
have ok : ((a - b) ^ 2) >= 0%r. smt(sq_lemmapos).
have okk : (d * (a - b) ^ 2) >= 0%r. smt().
smt(). smt().
qed.


end section.
