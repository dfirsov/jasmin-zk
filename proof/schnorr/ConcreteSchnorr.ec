require import AllCore Distr DInterval List Int IntDiv.
require  GroupNew.

require import JModel JBigNum.

require import Array32 Array64 Array128.

require Ring_ops_spec.
clone import Ring_ops_spec as ROS.
 (* with type Zp.zp <- W64.t Array32.t. *)
import Zp.


require AbstractSchnorr.
clone import AbstractSchnorr as SP
  with 
    type G.group <- Zp.zp,
    op G.( * ) <- Zp.( * ),
    op G.e <- Zp.one,
    op G.inv <- Zp.inv,
    op G.elems <-Zp.DZmodP.Support.enum,
    type GP.exp <- R,
    op GP.ZModE.Sub.val <= W64xN.valR.



module MyImpl = {
 proc commit(h : zp, w : R) : zp * R = {
   var r, q : int;
   var a : zp;    
   r <@ ASpecFp.rsample(P);
   a <@ ASpecFp.expm(G.g,r);
   return (a, W64xN.R.bn_ofint r);
  } 
}.



lemma commit_same : 
  equiv [ SchnorrPK.commit ~ MyImpl.commit 
          : ={arg}  ==> ={res} ].
proc. 
inline *. wp.  simplify. sp.
rnd GP.ZModE.Sub.val (oget \o GP.ZModE.Sub.insub) .
skip. progress. 
have -> :  (GP.ZModE.Sub.val ((\o) oget GP.ZModE.Sub.insub r0R))
 = r0R.  
rewrite /(\o).
rewrite - Core.oget_omap_some. 
have rint : (0 <= r0R && r0R < G.order).
have ->: G.order = p. smt. 
smt (@Distr @DInterval @List). auto. auto.
smt(GP.ZModE.Sub.insubP).
rewrite GP.ZModE.Sub.insubT.
have ->: G.order = p. smt. 
smt (@Distr @DInterval @List). auto. auto.
rewrite duniform1E. 
have ->: r0R \in range 0 P = true. smt(@List @Distr). simplify.
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
rewrite /val. 
rewrite   W64xN.R.bnK.
auto.
qed.

module type SProver = {
 proc commit(h : zp, w : R) : zp * R
}.

module type PDistinguisher(P:SProver) = {
  proc run() : bool
}.

lemma p_indist : forall (D <: PDistinguisher) &m,  
  Pr[ D(SchnorrPK).run()@&m : res ]
  =  Pr[ D(MyImpl).run()@&m : res ].
proof. progress.
byequiv. 
proc*.
call (_:true).
conseq commit_same. progress.
smt(). skip. smt(). auto. auto.
qed.


  
