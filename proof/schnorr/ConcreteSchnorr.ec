require import AllCore Distr DInterval List Int IntDiv.
require  GroupNew.

require Ring_ops_spec.
clone import Ring_ops_spec as ROS.
import Zp.

require AbstractSchnorr.
clone import AbstractSchnorr as SP
  with 
    type G.group <- Zp.zp,
    op G.( * ) <- Zp.( * ),
    op G.e <- Zp.one,
    op G.inv <- Zp.inv,
    op G.elems <-Zp.DZmodP.Support.enum.
   


module MyImpl = {
 proc commit(h : zp, w : int) : zp * int = {
   var r, q : int;
   var a : zp;    
   r <$ duniform (range 0 P); (*       (q,r) <@ rsample(P);*)
   a <@ ASpecFp.expm(G.g,r); (* a <- (generator ^ r) % P; *)    
   return (a, r);
  } 
}.


lemma commit_same : 
  equiv [  SchnorrPK.commit ~ MyImpl.commit 
   :   arg.`1{1} = arg.`1{2}
   /\  GP.ZModE.Sub.val arg.`2{1} = arg.`2{2} 
     ==> res.`1{1} = res.`1{2}
      /\  GP.ZModE.Sub.val res.`2{1} = res.`2{2} 
    ].
proc. 
inline ASpecFp.expm. wp.  simplify.
rnd GP.ZModE.Sub.val (oget \o GP.ZModE.Sub.insub) .
skip. progress. 
have -> :  (GP.ZModE.Sub.val ((\o) oget GP.ZModE.Sub.insub rR))
 = rR.  
rewrite /(\o).
rewrite - Core.oget_omap_some. 
have rint : (0 <= rR && rR < G.order).
have ->: G.order = p. smt. 
smt (@Distr @DInterval @List). auto. auto.
smt(GP.ZModE.Sub.insubP).
rewrite GP.ZModE.Sub.insubT.
have ->: G.order = p. smt. 
smt (@Distr @DInterval @List). auto. auto.
(* smt (@Distr @DInterval). auto. *)
rewrite duniform1E. 
have ->: rR \in range 0 P = true. smt(@List @Distr). simplify.
rewrite FD.dt1E. smt. 
have : 0 <= GP.ZModE.Sub.val rL < P. smt.
smt(@Distr @DInterval @List).
rewrite /(\o).
rewrite GP.ZModE.Sub.valK. auto.
rewrite /GP.(^). rewrite /asint.
 rewrite /G.(^).
have :  ((GP.ZModE.Sub.val rL)%GP.ZModE.Sub < 0)%Int = false. 
smt.
move => q. rewrite q. simplify. 
rewrite /(^). rewrite /asint.
have prop : forall (n : int),  0 <= n => forall (x : zp), 
  (G.(^+ ) x  n) =
inzp (Ring.IntID.(^) (Sub.val x)  n) .
apply intind.  
progress. smt.
progress. 
rewrite  G.exppS. auto. rewrite H5.
rewrite  Ring.IntID.exprSr. auto. 
rewrite inzpM. 
rewrite asintK. 
auto.
apply prop. smt.
qed.
