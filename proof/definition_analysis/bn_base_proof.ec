require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

require import JBigNum.



abstract theory BN_base.

op nlimbs : int.
axiom gt0_nlimbs: 0 < nlimbs.

clone import BN with
  op nlimbs <- nlimbs
  proof gt0_nlimbs by exact gt0_nlimbs.

(*
  extracted code from 'bn_base.jinc' with:
  - 'nlimbs' turned a parameter;
  - 'W64.t ArrayXX.t' turned 'BN.t'
  - 'XX' in code turned 'nlimbs'
  - removed parameterisation wrt 'SC:Systemcall_t"
  - '__bn_rng" is "idealized"                 *  - 'bn_sample" is "idealized semantics of __bn_rsample"                 *)
module M = {
  proc __bn_load (a:W64.t) : BN.t = {
    var aux: int;
    
    var x:BN.t;
    var i:int;
    var t:W64.t;
    x <- witness;
    i <- 0;
    while (i < nlimbs) {
      t <- (loadW64 Glob.mem (W64.to_uint (a + (W64.of_int (8 * i)))));
      x.[i] <- t;
      i <- i + 1;
    }
    return (x);
  }
  
  proc __bn_store (a:W64.t, b:BN.t) : unit = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      t <- b.[i];
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (a + (W64.of_int (8 * i)))) (t);
      i <- i + 1;
    }
    return ();
  }
  
  proc __bn_eq_zf (a:BN.t, b:BN.t) : bool = {
    var aux: int;
    
    var zf:bool;
    var acc:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    acc <- (W64.of_int 0);
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      t <- (t `^` b.[i]);
      acc <- (acc `|` t);
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 acc acc;
    return (zf);
  }
  
  proc __bn_eq (a:BN.t, b:BN.t) : W64.t = {
    
    var res_0:W64.t;
    var zf:bool;
    var are_equal:W64.t;
    
    zf <@ __bn_eq_zf (a, b);
    res_0 <- (W64.of_int 0);
    are_equal <- (W64.of_int 1);
    res_0 <- (zf ? are_equal : res_0);
    return (res_0);
  }
  
  proc _bn_eq (a:BN.t, b:BN.t) : W64.t = {
    
    var r:W64.t;
    
    r <@ __bn_eq (a, b);
    return (r);
  }
  
  proc _bn_eq_ (_a:BN.t, _b:BN.t) : W64.t = {
    
    var r:W64.t;
    var a:BN.t;
    var b:BN.t;
    a <- witness;
    b <- witness;
    a <- _a;
    b <- _b;
    r <@ _bn_eq (a, b);
    r <- r;
    return (r);
  }
  
  proc __bn_test0_zf (a:BN.t) : bool = {
    var aux: int;
    
    var zf:bool;
    var acc:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    acc <- a.[0];
    i <- 1;
    while (i < nlimbs) {
      acc <- (acc `|` a.[i]);
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 acc acc;
    return (zf);
  }
  
  proc __bn_test0 (a:BN.t) : W64.t = {
    
    var res_0:W64.t;
    var is_zero:W64.t;
    var zf:bool;
    
    res_0 <- (W64.of_int 0);
    is_zero <- (W64.of_int 1);
    zf <@ __bn_test0_zf (a);
    res_0 <- (zf ? is_zero : res_0);
    return (res_0);
  }
  
  proc _bn_test0 (a:BN.t) : W64.t = {
    
    var r:W64.t;
    
    r <@ __bn_test0 (a);
    return (r);
  }
  
  proc __bn_copy (a:BN.t) : BN.t = {
    var aux: int;
    
    var r:BN.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc __bn_copy2 (a:BN.t, r:BN.t) : BN.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc __bn_cmov (cond:bool, a:BN.t, b:BN.t) : 
  BN.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      t <- (cond ? b.[i] : t);
      a.[i] <- t;
      i <- i + 1;
    }
    return (a);
  }
  
  proc __bn_set0 (a:BN.t) : BN.t = {
    var aux: int;
    
    var t:W64.t;
    var i:int;
    
    t <- (W64.of_int 0);
    i <- 0;
    while (i < nlimbs) {
      a.[i] <- t;
      i <- i + 1;
    }
    return (a);
  }
  
  proc __bn_add1c (a:BN.t, b:W64.t) : bool * BN.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    (aux, aux_0) <- adc_64 a.[0] b false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < nlimbs) {
      (aux, aux_0) <- adc_64 a.[i] (W64.of_int 0) cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc __bn_addc (a:BN.t, b:BN.t) : bool *
                                                          BN.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    t <- b.[0];
    (aux, aux_0) <- adc_64 a.[0] t false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < nlimbs) {
      t <- b.[i];
      (aux, aux_0) <- adc_64 a.[i] t cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc _bn_addc (a:BN.t, b:BN.t) : bool *
                                                         BN.t = {
    
    var cf:bool;
    
    (cf, a) <@ __bn_addc (a, b);
    return (cf, a);
  }
  
  proc __bn_subc (a:BN.t, b:BN.t) : bool *
                                                          BN.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    t <- b.[0];
    (aux, aux_0) <- sbb_64 a.[0] t false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < nlimbs) {
      t <- b.[i];
      (aux, aux_0) <- sbb_64 a.[i] t cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc _bn_subc (a:BN.t, b:BN.t) : bool *
                                                         BN.t = {
    
    var cf:bool;
    
    (cf, a) <@ __bn_subc (a, b);
    return (cf, a);
  }
  
  proc __bn_lt_cf (a:BN.t, b:BN.t) : bool = {
    var aux: int;

    var cf:bool;
    var t:W64.t;
    var i:int;

    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] false;
    i <- 1;
    while (i < nlimbs) {
      t <- a.[i];
      (cf, t) <- sbb_64 t b.[i] cf;
      i <- i + 1;
    }
    return (cf);
  }
  
  (* idealised version of randombytes *)
  proc __bn_rnd (a:BN.t) : BN.t = {
    a <$ BN.bn_rnd;
    return a;
  }
  
  (* idealised version of rsample *)
  proc bn_sample_bnd (a:BN.t, bnd: BN.t) : BN.t = {
    var i;
    i <$ [0..bn bnd - 1];
    a <- bn_ofint i;
    return a;
  }
  
  proc __bn_rsample (a:BN.t, bnd:BN.t) : BN.t = {
    
    var cf:bool;
    
    a <@ __bn_rnd (a);
    cf <@ __bn_lt_cf (a, bnd);
    while ((! cf)) {
      a <@ __bn_rnd (a);
      cf <@ __bn_lt_cf (a, bnd);
    }
    return (a);
  }
}.

(** LOSSLESS lemmas *)
lemma __bn_load_ll: islossless M.__bn_load.
proof.
proc; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_store_ll: islossless M.__bn_store.
proof.
proc; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_eq_zf_ll: islossless M.__bn_eq_zf.
proof.
proc; wp; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_eq_ll: islossless M.__bn_eq.
proof. by proc; wp; call __bn_eq_zf_ll. qed.

lemma _bn_eq_ll: islossless M._bn_eq.
proof. by proc; call __bn_eq_ll. qed.

lemma _bn_eq__ll: islossless M._bn_eq_.
proof. by proc; wp; call _bn_eq_ll; auto. qed.

lemma __bn_test0_zf_ll: islossless M.__bn_test0_zf.
proof.
proc; wp; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_test0_ll: islossless M.__bn_test0.
proof. by proc; wp; call __bn_test0_zf_ll; auto. qed.

lemma _bn_test0_ll: islossless M._bn_test0.
proof. by proc; call __bn_test0_ll. qed.

lemma __bn_copy_ll: islossless M.__bn_copy.
proof.
proc; wp; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_copy2_ll: islossless M.__bn_copy2.
proof.
proc; wp; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_cmov_ll: islossless M.__bn_cmov.
proof.
proc; wp; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_set0_ll: islossless M.__bn_set0.
proof.
proc; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_add1c_ll: islossless M.__bn_add1c.
proof.
proc; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_addc_ll: islossless M.__bn_addc.
proof.
proc; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma _bn_addc_ll: islossless M._bn_addc.
proof. by proc; call __bn_addc_ll. qed.

lemma __bn_subc_ll: islossless M.__bn_subc.
proof.
proc; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma __bn_lt_cf_ll: islossless M.__bn_lt_cf.
proof.
proc; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => />; smt(gt0_nlimbs).
qed.

lemma _bn_subc_ll: islossless M._bn_subc.
proof. by proc; call __bn_subc_ll. qed.

(* Correctness lemmas *)

hoare __bn_eq_zf_h _a _b:
 M.__bn_eq_zf: a=_a /\ b=_b ==> res =  (_a=_b).
proof.
proc; simplify. 
wp; while ( #pre /\ 0 <= i <= nlimbs /\ ((acc = W64.zero) <=> (bnk i a = bnk i b))).
 wp; skip => /> &hr Hi1 Hi2 [HL HR] Hi3.
 split; first smt().
 split.
  rewrite orw_eq0 xorw_eq0; move => [E1 E2].
  by rewrite !bnkS 1..2:/# /= E2 (HL E1) /#.
 move => /(bnkS_eq _ _ _ Hi1) [E1 E2].
 by rewrite orw_eq0 (HR E2) E1.
wp; skip => />; split; first smt(gt0_nlimbs bnk0).
move=> acc i ???; rewrite (_:i=nlimbs) 1:/#.
move=> [H1 H2].
rewrite /AND_64 /rflags_of_bwop_w /flags_w /rflags_of_bwop /ZF_of /=.
by case: (acc = W64.zero) => C; smt(bn_inj).
qed.

phoare __bn_eq_zf_ph _a _b:
 [M.__bn_eq_zf: a=_a /\ b=_b ==> res = (_a=_b)] = 1%r.
proof. by conseq __bn_eq_zf_ll (__bn_eq_zf_h _a _b). qed.

hoare __bn_eq_h _a _b:
 M.__bn_eq: a=_a /\ b=_b ==> to_uint res =  b2i (_a=_b).
proof.
proc; wp; call (__bn_eq_zf_h _a _b); skip => />.
by case: (_a=_b) => C /#.
qed.

phoare __bn_eq_ph _a _b:
 [M.__bn_eq: a=_a /\ b=_b ==> to_uint res =  b2i (_a=_b)] = 1%r.
proof. by conseq __bn_eq_ll (__bn_eq_h _a _b). qed.

hoare _bn_eq_h _a _b:
 M._bn_eq: a=_a /\ b=_b ==> to_uint res = b2i (_a=_b).
proof. by proc; ecall (__bn_eq_h a b). qed.

phoare _bn_eq_ph _a _b:
 [M._bn_eq: a=_a /\ b=_b ==> to_uint res = b2i (_a=_b)] = 1%r.
proof. by conseq _bn_eq_ll (_bn_eq_h _a _b). qed.
 
hoare _bn_eq__h a b:
 M._bn_eq_: _a=a /\ _b=b ==> to_uint res = b2i (a=b).
proof. by proc; wp; ecall (_bn_eq_h a b); auto. qed.
 
phoare _bn_eq__ph a b:
 [M._bn_eq_: _a=a /\ _b=b ==> to_uint res = b2i (a=b) ] = 1%r.
proof. by conseq _bn_eq__ll (_bn_eq__h a b). qed.

hoare __bn_test0_zf_h _a:
 M.__bn_test0_zf: a=_a ==> res = (bn _a=0).
proof.
proc.
wp; while ( #pre /\ 0 <= i <= nlimbs /\ ((acc = W64.zero) <=> (bnk i a = 0))).
 wp; skip; progress; first 2 smt().
  move: H3; rewrite orw_eq0 => [[E1 E2]].
  by rewrite bnkS 1:/# /= E2 to_uint0 /= -H1 E1.
 move: (bnkS_eq0 _ _ H H3) => {H3} [H31 H32].
 by rewrite orw_eq0 H1 H32 /= to_uint_eq /#.
wp; skip => />; progress.
   smt(gt0_nlimbs).
  by rewrite bnk1 /= H to_uint0.
 by move: H; rewrite bnk1 /= to_uint_eq /=.
move: H2; rewrite (_:i0=nlimbs) 1:/# => <-.
by rewrite /AND_64 /#.
qed.

phoare __bn_test0_zf_ph _a:
 [M.__bn_test0_zf: a=_a ==> res = (bn _a=0)] = 1%r.
proof. by conseq __bn_test0_zf_ll (__bn_test0_zf_h _a). qed.

hoare __bn_test0_h _a:
 M.__bn_test0: a=_a ==> to_uint res = b2i (bn _a=0).
proof.
proc; wp; call (__bn_test0_zf_h _a); auto => />.
case (bnk nlimbs _a = 0) => _; smt().
qed.

phoare __bn_test0_ph _a:
 [M.__bn_test0: a=_a ==> to_uint res = b2i (bn _a=0)] = 1%r.
proof. by conseq __bn_test0_ll (__bn_test0_h _a). qed.

hoare _bn_test0_h _a:
 M._bn_test0: a=_a ==> to_uint res = b2i (bn _a=0).
proof. by proc; ecall (__bn_test0_h a). qed.
 
phoare _bn_test0_ph _a:
 [M._bn_test0: a=_a ==> to_uint res = b2i (bn _a=0)] = 1%r.
proof. by conseq _bn_test0_ll (_bn_test0_h _a). qed.

hoare __bn_copy_h _a:
 M.__bn_copy: a=_a ==> res = _a.
proof.
proc; while (0 <= i <= nlimbs /\ _a = a /\ (forall j, 0 <= j < i => r.[j] = _a.[j])).
 by wp; skip; progress; [smt() | smt() | rewrite get_setE => /#]. 
wp; skip; progress; first 2 smt(gt0_nlimbs).  
by rewrite tP /#.
qed.

phoare __bn_copy_ph _a:
 [M.__bn_copy: a=_a ==> res = _a] = 1%r.
proof. by conseq __bn_copy_ll (__bn_copy_h _a). qed.

hoare __bn_copy2_h _a:
 M.__bn_copy2: a=_a ==> res = _a.
proof.
proc; while (0 <= i <= nlimbs /\ _a = a /\ (forall j, 0 <= j < i => r.[j] = _a.[j])).
 by wp; skip; progress; [smt() | smt() | rewrite get_setE => /#]. 
wp; skip; progress; first 2 smt(gt0_nlimbs).  
by rewrite tP /#.
qed.

phoare __bn_copy2_ph _a:
 [M.__bn_copy2: a=_a ==> res = _a] = 1%r.
proof. by conseq __bn_copy2_ll (__bn_copy2_h _a). qed.

hoare __bn_cmov_h _cond _a _b:
 M.__bn_cmov: cond=_cond /\ a=_a /\ b=_b
              ==> res = if _cond then _b else _a.
proof.
proc => //=. 
while (0 <= i <= nlimbs /\ _cond = cond /\ _b = b /\
       (forall j, i <= j < nlimbs => a.[j] = _a.[j]) /\
       forall j, 0 <= j < i => a.[j] = if _cond then _b.[j] else _a.[j]).
 wp; skip => /> &hr *; split; first smt().
 split.
  move=> j Hj1 Hj2; rewrite get_setE 1:/#.
  by rewrite ifF 1:/# /#.
 by move=> j Hj1 Hj2; rewrite get_setE 1:/# /#.
wp; skip => />. split; first smt(gt0_nlimbs).
move=> a i ???; rewrite (:i=nlimbs) 1:/# => H1 H2.
by rewrite tP /#.
qed.

phoare __bn_cmov_ph _cond _a _b:
 [M.__bn_cmov: cond=_cond /\ a=_a /\ b=_b
              ==> res = if _cond then _b else _a] = 1%r.
proof. by conseq __bn_cmov_ll (__bn_cmov_h _cond _a _b). qed.

hoare __bn_set0_h:
 M.__bn_set0 : true ==> bn res = 0.
proof.
proc.
while (bnk i a = 0 /\ 0 <= i <= nlimbs /\ to_uint t = 0).
 auto => /> *.
 by rewrite bnkS 1:/# /= get_setE 1:/# bnk_setO /#.
by auto => /> &m; smt(bnk0 gt0_nlimbs).
qed.

phoare __bn_set0_ph:
 [M.__bn_set0 : true ==> bn res = 0] = 1%r.
proof. by conseq __bn_set0_ll __bn_set0_h. qed.

(* bnk with carry *)
op bnk_withcarry k (x: bool * t): int =
 b2i x.`1 * W64.modulus ^ k + bnk k x.`2. 

abbrev bn_withcarry x = bnk_withcarry nlimbs x.

op bnk_addc k cf (a:t) x = 
 ((addc a.[k] x cf).`1, a.[k <- (addc a.[k] x cf).`2]).

op to_uint_withcarry (cw:bool*W64.t) =
 W64.to_uint cw.`2 + b2i cw.`1 * W64.modulus.

lemma to_uint_withcarry_addc x y cf:
 to_uint_withcarry (W64.addc x y cf)
 = to_uint x + to_uint y + b2i cf.
proof.
move: (W64.addcP x y cf) => /=.
by rewrite /to_uint_withcarry mulrC addcE /=.
qed.

lemma bnk_withcarryS k cf a x:
 0 <= k < nlimbs =>
 bnk_withcarry (k+1) (bnk_addc k cf a x)
 = (to_uint a.[k] + to_uint x) * W64.modulus ^ k
   + bnk_withcarry k (cf,a).
proof.
move=> Hk; rewrite /bnk_withcarry /bnk_addc /= bnkS 1:/# addcE /= bnk_setO 1:/# get_setE 1:/# /=.
move: (W64.addcP a.[k] x cf); rewrite addcE /= => E.
rewrite exprS 1:/#; ring E.
qed.

hoare __bn_add1c_h _a _b:
 M.__bn_add1c :
 a=_a /\ b=_b
 ==> bn_withcarry res = bn _a + to_uint _b.
proof.
have Hlimbs:= gt0_nlimbs; proc; simplify.
while (1 <= i <= nlimbs /\ _b = b /\
       (forall j, i <= j < nlimbs => a.[j] = _a.[j]) /\
       bnk_withcarry i (cf, a) = bnk i _a + to_uint b).
 wp; skip => &hr [[[Hi1 Hi2]]] /> Ha H Hc.
 split; [smt() | split].
  by move=> j Hj1 Hj2; rewrite get_setE 1:/# ifF /#.
 rewrite -/(bnk_addc i{hr} cf{hr} a{hr} W64.zero).
 rewrite bnk_withcarryS 1:/# bnkS 1:/# /=. 
 by rewrite -addzA -H /#.
auto => />; split.
 split; first smt().
 split.
  by move=> j Hj1 Hj2; rewrite get_setE /#.
 rewrite -/(bnk_addc 0 false _a _b).
 rewrite {1}(:1=0+1) 1:/# bnk_withcarryS 1:/# expr0 bnk1 /=.
 by rewrite /bnk_withcarry /= b2i0 bnk0 /=.
by move=> a cf i ??? _; rewrite (:i=nlimbs) 1:/#.
qed.

(*
get_setE 1:/# bnk_setO 1:/# /=.
print addcE.
  by rewrite addcE !bn_carryS /= 1:/# carryE /carry_add /= bn_digitS // to_uint0 /=.
 rewrite !bnkS /= 1..2:/# get_setE 1:/# /= bnk_setO 1:/# H1.
 by rewrite addcP' !exprS 1:/# carryE addcE /carry_add /=; ring.
wp; skip => /> .
split.
 split; first by smt().
 split.
  by rewrite (_: 1 = 0 + 1) // bn_carryS // bn_carry0 bn_digit0 carryE addcE /= /carry_add.
 rewrite (_: 1 = 0 + 1) // !bnkS //= !bnk0 //= get_setE 1:/# //=.
 by rewrite addcP' addcE carryE /carry_add /=.
move => j dd Hj1 Hj2 Hj3 Hwsize; split.
 by rewrite (_ : j = nlimbs) 1:/# bn_carryE 1:/# bn_modulusE bn_digit.
move: Hwsize; rewrite (_:j = nlimbs) 1:/# => ->.
have Hwsize:= W64.ge0_size.
pose X:= (bn_carry _ _ _ _); case: X; rewrite /X => {X} H.
 rewrite b2i1 -(modzMDr (-1)) bn_modulusE /= modz_small.
  rewrite ger0_norm; first smt(expr_gt0).
  have ->/=: bnk nlimbs aa + to_uint bb + b2i cc + (-1) * W64.modulus ^ nlimbs = bnk nlimbs aa + to_uint bb + b2i cc + -1 * W64.modulus ^ nlimbs by smt().
  apply mod_sub.
  - by smt(expr_gt0).
  - by move: bnk_cmp; smt().
  - split => *; first smt(to_uint_cmp).
    by move: to_uint_cmp ler_eexpr; smt().
  - by move: H; rewrite bn_carryE 1:/# bn_digit /#.
 by smt().
rewrite b2i0 bn_modulusE -exprM /=.
move: H; rewrite /X bn_carryE 1:/# => H.
rewrite modz_small // ger0_norm; first smt(expr_gt0).
split => *; first move: to_uint_cmp bnk_cmp; smt().
by rewrite exprM; rewrite bn_digit -ltzNge in H.

qed.
*)

phoare __bn_add1c_ph _a _b:
 [ M.__bn_add1c :
   a=_a /\ b=_b
   ==> bn_withcarry res = bn _a + to_uint _b] = 1%r.
proof. by conseq __bn_add1c_ll (__bn_add1c_h _a _b). qed.

hoare __bn_addc_h _a _b:
 M.__bn_addc : 
 a=_a /\ b=_b ==> bn_withcarry res = bn _a + bn _b.
proof.
have Hlimbs:= gt0_nlimbs; proc; simplify.
while (1 <= i <= nlimbs /\ _b = b /\
       (forall j, i <= j < nlimbs => a.[j] = _a.[j]) /\
       bnk_withcarry i (cf, a) = bnk i _a + bnk i _b).
 wp; skip => &hr [[[Hi1 Hi2]]] /> Ha H Hc.
 split; [smt() | split].
  by move=> j Hj1 Hj2; rewrite get_setE 1:/# ifF /#.
 rewrite -/(bnk_addc i{hr} cf{hr} a{hr} b{hr}.[i{hr}]).
 rewrite bnk_withcarryS 1:/# !bnkS 1..2:/# /=.
 rewrite Ha 1:/#. 
 by ring H.
auto => />; split.
 split; first smt().
 split.
  by move=> j Hj1 Hj2; rewrite get_setE /#.
 rewrite -/(bnk_addc 0 false _a _b.[0]).
 rewrite {1}(:1=0+1) 1:/# bnk_withcarryS 1:/# expr0 !bnk1 /=.
 by rewrite /bnk_withcarry /= b2i0 bnk0 /=.
by move=> a cf i ??? _; rewrite (:i=nlimbs) 1:/#.
qed.

phoare __bn_addc_ph _a _b:
 [ M.__bn_addc : 
   a=_a /\ b=_b 
   ==> bn_withcarry res = bn _a + bn _b] = 1%r.
proof. by conseq __bn_addc_ll (__bn_addc_h _a _b). qed.

hoare _bn_addc_h _a _b:
 M._bn_addc : 
 a=_a /\ b=_b
 ==> bn_withcarry res = bn _a + bn _b.
proof. by proc; ecall (__bn_addc_h a b). qed.

phoare _bn_addc_ph _a _b:
 [ M._bn_addc : 
   a=_a /\ b=_b 
   ==> bn_withcarry res = bn _a + bn _b] = 1%r.
proof. by conseq _bn_addc_ll (_bn_addc_h _a _b). qed.

(* bn with borrow *)
op bnk_withborrow k (x: bool * t): int =
 bnk k x.`2 - b2i x.`1 * W64.modulus ^ k.

abbrev bn_withborrow x = bnk_withborrow nlimbs x.
(*
op bnb (x: bool * t): int = bn x.`2 - b2i x.`1 * bn_modulus. 
*)
op bnk_subc k cf (a:t) x = 
 ((subc a.[k] x cf).`1, a.[k <- (subc a.[k] x cf).`2]).

op to_uint_withborrow (cw:bool*W64.t) =
 W64.to_uint cw.`2 - b2i cw.`1 * W64.modulus.

lemma to_uint_withborrow_subc x y cf:
 to_uint_withborrow (W64.subc x y cf)
 = to_uint x - (to_uint y + b2i cf).
proof.
move: (W64.subcP x y cf) => /=.
by rewrite /to_uint_withborrow mulrC subcE /=.
qed.

lemma bnk_withborrowS k cf a x:
 0 <= k < nlimbs =>
 bnk_withborrow (k+1) (bnk_subc k cf a x)
 = (to_uint a.[k] - to_uint x) * W64.modulus ^ k
   + bnk_withborrow k (cf,a).
proof.
move=> Hk; rewrite /bnk_withborrow /bnk_subc /= bnkS 1:/# subcE /= bnk_setO 1:/# get_setE 1:/# /=.
move: (W64.subcP a.[k] x cf); rewrite subcE /= => E.
rewrite exprS 1:/#; ring E.
qed.


hoare __bn_subc_h _a _b:
 M.__bn_subc :
 a=_a /\ b=_b 
 ==> bn_withborrow res = bn _a - bn _b.
proof.
have Hlimbs:= gt0_nlimbs; proc; simplify.
while (1 <= i <= nlimbs /\ _b = b /\
       (forall j, i <= j < nlimbs => a.[j] = _a.[j]) /\
       bnk_withborrow i (cf, a) = bnk i _a - bnk i _b).
 wp; skip => &hr [[[Hi1 Hi2]]] /> Ha H Hc.
 split; [smt() | split].
  by move=> j Hj1 Hj2; rewrite get_setE 1:/# ifF /#.
 rewrite -/(bnk_subc i{hr} cf{hr} a{hr} b{hr}.[i{hr}]).
 rewrite bnk_withborrowS 1:/# !bnkS 1..2:/# /=.
 rewrite Ha 1:/#. 
 by ring H.
auto => />; split.
 split; first smt().
 split.
  by move=> j Hj1 Hj2; rewrite get_setE /#.
 rewrite -/(bnk_subc 0 false _a _b.[0]).
 rewrite {1}(:1=0+1) 1:/# bnk_withborrowS 1:/# expr0 !bnk1 /=.
 by rewrite /bnk_withborrow /= b2i0 bnk0 /=.
by move=> a cf i ??? _; rewrite (:i=nlimbs) 1:/#.
qed.

phoare __bn_subc_ph _a _b:
 [ M.__bn_subc :
   a=_a /\ b=_b 
   ==> bn_withborrow res = bn _a - bn _b] = 1%r.
proof. by conseq __bn_subc_ll (__bn_subc_h _a _b). qed.

hoare __bn_lt_cf_h _a _b:
 M.__bn_lt_cf : a=_a /\ b=_b ==> res = bn _a < bn _b.
proof.
have Hlimbs:= gt0_nlimbs; proc; simplify.
while (1 <= i <= nlimbs /\ _a = a /\ _b = b /\
       cf = (bnk i _a < bnk i _b)).
 wp; skip => &hr [[[Hi1 _]]] /> Hi.
 split; [smt() |].
 rewrite subcE /borrow_sub /=.
 rewrite (bnk_ltb i{hr} a{hr} b{hr} false _) 1:/#.
 case: (bnk i{hr} a{hr} < bnk i{hr} b{hr}) => C.
  by rewrite b2i1 b2i0 C /= ltzS StdOrder.IntOrder.ler_eqVlt to_uint_eq /#.
 by rewrite b2i0 /#.
auto => />; split.
 split; first smt().
 by rewrite subcE /borrow_sub b2i0 /= !bnk1.
by move=> i ???; rewrite (:i=nlimbs) 1:/#.
qed.

phoare __bn_lt_cf_ph _a _b:
 [M.__bn_lt_cf : a=_a /\ b=_b ==> res = bn _a < bn _b] = 1%r.
proof. by conseq __bn_lt_cf_ll (__bn_lt_cf_h _a _b). qed.


(* REJECTION SAMPLING *)

phoare __bn_rnd_ph _res:
 [ M.__bn_rnd :
   true ==> res = _res ] = (mu1 bn_rnd _res).
proof. by proc; rnd; skip => />. qed.

phoare bn_sample_bnd_ph _bnd _res:
 [ M.bn_sample_bnd :
   bnd=_bnd ==> res = _res ] = (mu1 (bn_rnd_bnd bnd) _res).
proof. 
proc; wp; rnd; skip => />. 
by rewrite dmap1E /pred1 /(\o) /=.
qed.

require import DInterval Dexcepted.
clone import WhileSampling as RS
 with type input = unit,
      type t = BN.t,
      op dt i = bn_rnd.

equiv __bn_rsample_eq:
 M.__bn_rsample ~ M.bn_sample_bnd :
 ={bnd} ==> ={res}.
proof.
exlim bnd{2} => _bnd.
case: (bn _bnd = 0) => Hbnd.
 bypr res{1} res{2} => //.
 move=> &1 &2 _a [Hbnd1 Hbnd2].
 pose P:= Pr[M.bn_sample_bnd(_, _) @ &2 : res = _].
 have ->: P = 0%r.
  rewrite /P; byphoare (: bnd=bnd{2} ==> _) => //; hoare.
  by proc; auto => /> i; rewrite supp_dinter; smt(bnk_cmp).
 byphoare (: bnd=_bnd ==> _) => //.
  hoare; proc; while(bnd=_bnd /\ cf = bnk nlimbs a < bnk nlimbs _bnd).
   ecall (__bn_lt_cf_h a bnd).
   by inline*; auto => /> &m.
  ecall (__bn_lt_cf_h a bnd).
  inline*; auto => &m -> a Ha r; rewrite Hbnd.
  smt(bnk_cmp).
 smt().
transitivity
 RS.SampleW.sample
 (bnd{1}=_bnd /\ i{2}=tt /\ test{2}=fun _ n =>! bn n < bn _bnd
  ==> ={res})
 (bnd{2}=_bnd /\ i{1}=tt /\ test{1}=fun _ n =>! bn n < bn _bnd
  ==> ={res}) => //=.
+ move=> &1 &2 [E E2].
  by exists (tt,fun _ n => !bn n < bn _bnd) => /#.
+ proc; simplify; inline SampleWi.sample.
  wp; while (#pre /\ test0{2}=test{2} /\ a{1}=r0{2} /\
             (!cf{1})=(test0 i0 r0){2}).
   ecall {1} (__bn_lt_cf_ph a{1} bnd{1}).
   by inline*; auto => />.
  ecall {1} (__bn_lt_cf_ph a{1} bnd{1}).
  by inline*; auto => &1 &2 /=.
transitivity RS.SampleE.sample
 (={i,test} /\ i{2}=tt /\ test{2}=fun _ n =>! bn n < bn _bnd
  ==> ={res})
 (bnd{2}=_bnd /\ i{1}=tt /\ test{1}=fun _ n =>! bn n < bn _bnd
  ==> ={res}) => //=.
+ move=> &1 &2 [E2 E].
  by exists (tt,fun _ n => !bn n < bn _bnd) => /#.
+ symmetry; conseq RS.sampleE_sampleW.
   by move => /> &1 &2 -> _ /=; apply bn_rnd_ll.
  by move=> />.
proc; simplify.
rnd : 0 *0; skip => /> &1; split.
 move=> a; rewrite supp_dmap => [[i />]].
 rewrite supp_dinter => Hi.
 rewrite !dmap1E /pred1 /(\o) /=.
 rewrite bn_rnd_excepted dmapE.
 apply mu_eq_support.
 by move=> x; rewrite supp_dinter /(\o) /=.
move => H1 r /=.
rewrite supp_dmap => [[a />]].
rewrite supp_dexcepted /= => [[HA HB]].
rewrite supp_dmap; exists (bn a); split.
 by rewrite supp_dinter; smt(bnk_cmp).
by rewrite bnK.
qed.

phoare __bn_rsample_ph _bnd _res:
 [ M.__bn_rsample :
   bnd=_bnd ==> res = _res ] = (mu1 (bn_rnd_bnd bnd) _res).
proof.
conseq __bn_rsample_eq (bn_sample_bnd_ph _bnd _res) => /> &1.
by exists (bnd{1},bnd{1}); smt().
qed.

lemma bn_sample_bnd_ll:
 phoare [ M.bn_sample_bnd : 0 < bn bnd ==> true ] = 1%r.
proof.
proc; simplify; auto => /> &m Hbnd.
by rewrite weight_dinter /#.
qed.

lemma __bn_rsample_ll:
 phoare [ M.__bn_rsample : 0 < bn bnd ==> true ] = 1%r.
proof.
conseq __bn_rsample_eq bn_sample_bnd_ll => //=.
by move=> /> &1 Hbnd; exists (witness, bnd{1}) => /#.
qed.




from Jasmin require import JLeakage.

module Mleak = {
  var leakages : leakages_t

  proc __bn_load (a:W64.t) : BN.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var x:BN.t;
    var i:int;
    var t:W64.t;
    x <- witness;
    leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < nlimbs) {
      leakages <- LeakAddr([(W64.to_uint (a + (W64.of_int (8 * i))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (a + (W64.of_int (8 * i)))));
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      x.[i] <- aux_0;
      i <- i + 1;
    }
    return (x);
  }
  
  proc __bn_store (a:W64.t, b:BN.t) : unit = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- b.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([(W64.to_uint (a + (W64.of_int (8 * i))))]) :: leakages;
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (a + (W64.of_int (8 * i)))) (aux_0);
      i <- i + 1;
    }
    return ();
  }
  
  proc __bn_eq_zf (a:BN.t, b:BN.t) : bool = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: int;
    var aux: W64.t;
    
    var zf:bool;
    var acc:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    acc <- aux;
    leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      t <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (t `^` b.[i]);
      t <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (acc `|` t);
      acc <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux) <- AND_64 acc acc;
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
    zf <- aux_1;
     _4 <- aux;
    return (zf);
  }
  
  proc __bn_eq (a:BN.t, b:BN.t) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var res_0:W64.t;
    var zf:bool;
    var are_equal:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ __bn_eq_zf (a, b);
    zf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    res_0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    are_equal <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (zf ? are_equal : res_0);
    res_0 <- aux_0;
    return (res_0);
  }
  
  proc _bn_eq (a:BN.t, b:BN.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ __bn_eq (a, b);
    r <- aux;
    return (r);
  }
  
  proc _bn_eq_ (_a:BN.t, _b:BN.t) : W64.t = {
    var aux_0: W64.t;
    var aux: BN.t;
    
    var r:W64.t;
    var a:BN.t;
    var b:BN.t;
    a <- witness;
    b <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- _a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- _b;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ _bn_eq (a, b);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- r;
    r <- aux_0;
    return (r);
  }
  
  proc __bn_test0_zf (a:BN.t) : bool = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: int;
    var aux: W64.t;
    
    var zf:bool;
    var acc:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    acc <- aux;
    leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (acc `|` a.[i]);
      acc <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux) <- AND_64 acc acc;
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
    zf <- aux_1;
     _4 <- aux;
    return (zf);
  }
  
  proc __bn_test0 (a:BN.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var res_0:W64.t;
    var is_zero:W64.t;
    var zf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    is_zero <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ __bn_test0_zf (a);
    zf <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zf ? is_zero : res_0);
    res_0 <- aux;
    return (res_0);
  }
  
  proc _bn_test0 (a:BN.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ __bn_test0 (a);
    r <- aux;
    return (r);
  }
  
  proc __bn_copy (a:BN.t) : BN.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:BN.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc __bn_copy2 (a:BN.t, r:BN.t) : BN.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc __bn_cmov (cond:bool, a:BN.t, b:BN.t) : 
  BN.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (cond ? b.[i] : t);
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc __bn_set0 (a:BN.t) : BN.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var t:W64.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    t <- aux;
    leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < nlimbs) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- t;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux;
      i <- i + 1;
    }
    return (a);
  }
  
  proc __bn_add1c (a:BN.t, b:W64.t) : bool * BN.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    leakages <- LeakAddr([0]) :: leakages;
    (aux, aux_0) <- adc_64 a.[0] b false;
    cf <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux_0;
    leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      (aux, aux_0) <- adc_64 a.[i] (W64.of_int 0) cf;
      cf <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc __bn_addc (a:BN.t, b:BN.t) : bool *
                                                          BN.t = {
    var aux_0: bool;
    var aux_1: int;
    var aux: W64.t;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- b.[0];
    t <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- adc_64 a.[0] t false;
    cf <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- b.[i];
      t <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_0, aux) <- adc_64 a.[i] t cf;
      cf <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc _bn_addc (a:BN.t, b:BN.t) : bool *
                                                         BN.t = {
    var aux: bool;
    var aux_0: BN.t;
    
    var cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ __bn_addc (a, b);
    cf <- aux;
    a <- aux_0;
    return (cf, a);
  }
  
  proc __bn_subc (a:BN.t, b:BN.t) : bool *
                                                          BN.t = {
    var aux_0: bool;
    var aux_1: int;
    var aux: W64.t;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- b.[0];
    t <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- sbb_64 a.[0] t false;
    cf <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- b.[i];
      t <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_0, aux) <- sbb_64 a.[i] t cf;
      cf <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc __bn_lt_cf (a:BN.t, b:BN.t) : bool = {
    var aux_0: bool;
    var aux_1: int;
    var aux: W64.t;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    t <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- sbb_64 t b.[0] false;
    cf <- aux_0;
    t <- aux;
    leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < nlimbs) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      t <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_0, aux) <- sbb_64 t b.[i] cf;
      cf <- aux_0;
      t <- aux;
      i <- i + 1;
    }
    return (cf);
  }
  
  proc _bn_subc (a:BN.t, b:BN.t) : bool *
                                                         BN.t = {
    var aux: bool;
    var aux_0: BN.t;
    
    var cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ __bn_subc (a, b);
    cf <- aux;
    a <- aux_0;
    return (cf, a);
  }
  
  proc __bn_rnd (a:BN.t) : BN.t = {
    leakages <- LeakAddr([]) :: leakages;
    a <$ BN.bn_rnd;
    return a;
  }
  
  proc __bn_rsample (a:BN.t, bnd:BN.t) : BN.t = {
    var aux_0: bool;
    var aux: BN.t;
    
    var cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ __bn_rnd (a);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ __bn_lt_cf (a, bnd);
    cf <- aux_0;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    while ((! cf)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <@ __bn_rnd (a);
      a <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ __bn_lt_cf (a, bnd);
      cf <- aux_0;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    }
    return (a);
  }
}.

(** M vs. Mleak *)
equiv __bn_load_proj:
 M.__bn_load ~ Mleak.__bn_load : ={arg, Glob.mem} ==> ={res}
 by sim.

equiv __bn_store_proj:
 M.__bn_store ~ Mleak.__bn_store : ={arg, Glob.mem} ==> ={res, Glob.mem}
 by sim.

equiv __bn_eq_zf_proj:
 M.__bn_eq_zf ~ Mleak.__bn_eq_zf : ={arg} ==> ={res}
 by sim.

equiv __bn_eq_proj:
 M.__bn_eq ~ Mleak.__bn_eq : ={arg} ==> ={res}
 by sim.

equiv _bn_eq_proj:
 M._bn_eq ~ Mleak._bn_eq : ={arg} ==> ={res}
 by sim.

equiv _bn_eq__proj:
 M._bn_eq_ ~ Mleak._bn_eq_ : ={arg} ==> ={res}
 by sim.

equiv __bn_test0_zf_proj:
 M.__bn_test0_zf ~ Mleak.__bn_test0_zf : ={arg} ==> ={res}
 by sim.

equiv __bn_test0_proj:
 M.__bn_test0 ~ Mleak.__bn_test0 : ={arg} ==> ={res}
 by sim.

equiv _bn_test0_proj:
 M._bn_test0 ~ Mleak._bn_test0 : ={arg} ==> ={res}
 by sim.

equiv __bn_copy_proj:
 M.__bn_copy ~ Mleak.__bn_copy : ={arg} ==> ={res}
 by sim.

equiv __bn_copy2_proj:
 M.__bn_copy2 ~ Mleak.__bn_copy2 : ={arg} ==> ={res}
 by sim.

equiv __bn_cmov_proj:
 M.__bn_cmov ~ Mleak.__bn_cmov : ={arg} ==> ={res}
 by sim.

equiv __bn_set0_proj:
 M.__bn_set0 ~ Mleak.__bn_set0 : ={arg} ==> ={res}
 by sim.

equiv __bn_add1c_proj:
 M.__bn_add1c ~ Mleak.__bn_add1c : ={arg} ==> ={res}
 by sim.

equiv __bn_addc_proj:
 M.__bn_addc ~ Mleak.__bn_addc : ={arg} ==> ={res}
 by sim.

equiv _bn_addc_proj:
 M._bn_addc ~ Mleak._bn_addc : ={arg} ==> ={res}
 by sim.

equiv __bn_subc_proj:
 M.__bn_subc ~ Mleak.__bn_subc : ={arg} ==> ={res}
 by sim.

equiv _bn_subc_proj:
 M._bn_subc ~ Mleak._bn_subc : ={arg} ==> ={res}
 by sim.

equiv __bn_lt_cf_proj:
 M.__bn_lt_cf ~ Mleak.__bn_lt_cf : ={arg} ==> ={res}
 by sim.

equiv __bn_rnd_proj:
 M.__bn_rnd ~ Mleak.__bn_rnd : ={arg} ==> ={res}
 by sim.

equiv __bn_rsample_proj:
 M.__bn_rsample ~ Mleak.__bn_rsample : ={arg} ==> ={res}
 by sim.


(* ct property *)

equiv __bn_load_ct:
 Mleak.__bn_load ~ Mleak.__bn_load : 
  ={a, Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_store_ct:
 Mleak.__bn_store ~ Mleak.__bn_store : 
  ={a, Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_eq_zf_ct:
 Mleak.__bn_eq_zf ~ Mleak.__bn_eq_zf : 
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_eq_ct:
 Mleak.__bn_eq ~ Mleak.__bn_eq :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof.
proc; wp.
by call __bn_eq_zf_ct; auto => />.
qed.

equiv _bn_eq_ct:
 Mleak._bn_eq ~ Mleak._bn_eq :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. 
proc; wp.
by call __bn_eq_ct; auto => />.
qed.

equiv _bn_eq__ct:
 Mleak._bn_eq_ ~ Mleak._bn_eq_ :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. 
proc; wp.
by call _bn_eq_ct; auto => />.
qed.

equiv __bn_test0_zf_ct:
 Mleak.__bn_test0_zf ~ Mleak.__bn_test0_zf :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_test0_ct:
 Mleak.__bn_test0 ~ Mleak.__bn_test0 :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof.
proc; wp.
by call __bn_test0_zf_ct; auto => />.
qed.

equiv _bn_test0_ct:
 Mleak._bn_test0 ~ Mleak._bn_test0 :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof.
proc; wp.
by call __bn_test0_ct; auto => />.
qed.

equiv __bn_copy_ct:
 Mleak.__bn_copy ~ Mleak.__bn_copy :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_copy2_ct:
 Mleak.__bn_copy2 ~ Mleak.__bn_copy2 :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_cmov_ct:
 Mleak.__bn_cmov ~ Mleak.__bn_cmov :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_set0_ct:
 Mleak.__bn_set0 ~ Mleak.__bn_set0 :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_add1c_ct:
 Mleak.__bn_add1c ~ Mleak.__bn_add1c :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_addc_ct:
 Mleak.__bn_addc ~ Mleak.__bn_addc :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv _bn_addc_ct:
 Mleak._bn_addc ~ Mleak._bn_addc :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof.
proc; wp.
by call __bn_addc_ct; auto => />.
qed.

equiv __bn_subc_ct:
 Mleak.__bn_subc ~ Mleak.__bn_subc :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv _bn_subc_ct:
 Mleak._bn_subc ~ Mleak._bn_subc :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof.
proc; wp.
by call __bn_subc_ct; auto => />.
qed.

equiv __bn_lt_cf_ct:
 Mleak.__bn_lt_cf ~ Mleak.__bn_lt_cf :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_rnd_ct:
 Mleak.__bn_rnd ~ Mleak.__bn_rnd :
  ={Mleak.leakages} ==> ={Mleak.leakages}.
proof. by proc; sim. qed.

equiv __bn_rsample_ct:
 Mleak.__bn_rsample ~ Mleak.__bn_rsample :
  ={bnd, Mleak.leakages} ==> ={Mleak.leakages}.
proof.
proc; wp.
while (={bnd, cf, Mleak.leakages}).
 wp; call (: ={arg,Mleak.leakages} ==> ={res, Mleak.leakages}); first by sim.
 by inline*; auto => /> *.
wp; call (: ={arg,Mleak.leakages} ==> ={res, Mleak.leakages}); first by sim.
by inline*; auto => /> *.
qed.


(**
  * Leakage-freeness for probabilistic programs
  * ===========================================
  *
  * The following development illustrates the
  * proof of Leakage-freeness for the rejection
  * sampling procedure [__bn_rsample]. It relies
  * on the definitions and lemmas formalised in
  * [PRHL_Defs], presented on paper ...
***)
require import PRHL_Defs.

(** The following theories instantiate the
 abstract developments for individual procedures.*)
theory LF_bn_lt.
clone import LF_Meta as Meta
 with type pin_t <- unit, (*  *)
      type sin_t <- BN.t*BN.t, (* a, b *)
      type out_t <- bool. (* res *)

module JI = {
 proc main(pin: unit, sin: BN.t*BN.t) : bool = {
  var r;
  r <@ M.__bn_lt_cf(sin.`1,sin.`2);
  return r;
 }
}.

lemma stateless_JI &m x: (glob JI){m} = x
 by done.

module JR = {
 proc main(pin: unit, sin: BN.t*BN.t) : bool = {
  var r;
  r <@ Mleak.__bn_lt_cf(sin.`1,sin.`2);
  return r;
 }
 proc mainG(pin: unit, sin: BN.t*BN.t) : bool * leakages_t = {
  var r;
  r <@ Mleak.__bn_lt_cf(sin.`1,sin.`2);
  return (r, Mleak.leakages);
 }
}.

lemma proj_JR_JI:
 equiv [ JR.main ~ JI.main
       : ={pin, sin} ==> ={res} ]
 by sim.

lemma globJR:
 equiv [ JR.main ~ JR.mainG
       : ={pin,sin,glob JR}
         ==> ={glob JR} /\ res{2} = (res{1},glob JR){2} ].
proof.
proc*; inline JR.main JR.mainG.
wp; call (: ={arg,glob JR} ==> ={res,glob JR}) => //.
 by proc; sim.
by auto.
qed.

lemma prMuE P pin sin &m:
 Pr[ JR.main(pin,sin) @ &m : P (res,glob JR)]
 = RealSeries.sum (fun (x:_*_) => Pr [JR.main(pin,sin) @ &m : P (res,glob JR) /\ res=x.`1 /\ (glob JR)=x.`2]).
proof.
have ->: Pr[JR.main(pin, sin) @ &m : P (res,glob JR)]
  = Pr[JR.mainG(pin, sin) @ &m : P res].
 byequiv => //.
 by conseq globJR => /> // /#.
rewrite Pr [muE].
apply RealSeries.eq_sum; move => [r l].
rewrite eq_sym.
by byequiv globJR => /> /#.
qed.

end LF_bn_lt.

lemma GenLF_bn_lt:
 equiv[ LF_bn_lt.Meta.RSim(LF_bn_lt.JI, LF_bn_lt.JR).main ~ LF_bn_lt.Meta.SimR(LF_bn_lt.JI, LF_bn_lt.JR).main :
  ={pin, sin, glob LF_bn_lt.JR} ==> ={res, glob LF_bn_lt.JR}].
proof.
apply (LF_bn_lt.Meta.CT_det_GenLF LF_bn_lt.JR LF_bn_lt.JI).
+ by apply LF_bn_lt.stateless_JI.
+ by apply LF_bn_lt.proj_JR_JI.
+ by apply LF_bn_lt.prMuE.
+ by proc; call __bn_lt_cf_ct; auto => />.
exists (fun _ (x:_*_) => bn x.`1 < bn x.`2) => ? [a b].
by proc; ecall (__bn_lt_cf_h a b); auto.
qed.

lemma LF_bn_lt:
 equiv[ LF_bn_lt.JR.main ~ LF_bn_lt.Meta.SimR(LF_bn_lt.JI, LF_bn_lt.JR).main :
  ={pin, sin, glob LF_bn_lt.JR} ==> ={res, glob LF_bn_lt.JR}].
proof.
apply (LF_bn_lt.Meta.ll_LF LF_bn_lt.JR LF_bn_lt.JI _ _ _ _ GenLF_bn_lt).
+ by apply LF_bn_lt.stateless_JI.
+ by apply LF_bn_lt.proj_JR_JI.
+ by apply LF_bn_lt.prMuE.
by proc; call __bn_lt_cf_ll.
qed.


theory LF_bn_rnd.

clone import LF_Meta as Meta
 with type pin_t <- unit, (*  *)
      type sin_t <- BN.t, (* a *)
      type out_t <- BN.t. (* res *)

module JI = {
 proc main(pin: unit, sin: BN.t) : BN.t = {
  var r;
  r <@ M.__bn_rnd(sin);
  return r;
 }
}.

lemma stateless_JI &m x: (glob JI){m} = x
 by done.

module JR = {
 proc main(pin: unit, sin: BN.t) : BN.t = {
  var r;
  r <@ Mleak.__bn_rnd(sin);
  return r;
 }
 proc mainG(pin: unit, sin: BN.t) : BN.t * leakages_t = {
  var r;
  r <@ Mleak.__bn_rnd(sin);
  return (r, Mleak.leakages);
 }
}.

lemma proj_JR_JI:
 equiv [ JR.main ~ JI.main
       : ={pin, sin} ==> ={res} ]
 by sim.

lemma globJR:
 equiv [ JR.main ~ JR.mainG
       : ={pin,sin,glob JR}
         ==> ={glob JR} /\ res{2} = (res{1},glob JR){2} ].
proof.
proc*; inline JR.main JR.mainG.
wp; call (: ={arg,glob JR} ==> ={res,glob JR}) => //.
 by proc; sim.
by auto.
qed.

lemma prMuE P pin sin &m:
 Pr[ JR.main(pin,sin) @ &m : P (res,glob JR)]
 = RealSeries.sum (fun (x:_*_) => Pr [JR.main(pin,sin) @ &m : P (res,glob JR) /\ res=x.`1 /\ (glob JR)=x.`2]).
proof.
have ->: Pr[JR.main(pin, sin) @ &m : P (res,glob JR)]
  = Pr[JR.mainG(pin, sin) @ &m : P res].
 byequiv => //.
 by conseq globJR => /> // /#.
rewrite Pr [muE].
apply RealSeries.eq_sum; move => [r l].
rewrite eq_sym.
by byequiv globJR => /> /#.
qed.

end LF_bn_rnd.

lemma GenLF_bn_rnd:
 equiv[ LF_bn_rnd.Meta.RSim(LF_bn_rnd.JI, LF_bn_rnd.JR).main ~ LF_bn_rnd.Meta.SimR(LF_bn_rnd.JI, LF_bn_rnd.JR).main :
  ={pin, sin, glob LF_bn_rnd.JR} ==> ={res, glob LF_bn_rnd.JR}].
proof. by proc; inline*; auto. qed.

lemma LF_bn_rnd:
 equiv[ LF_bn_rnd.JR.main ~ LF_bn_rnd.Meta.SimR(LF_bn_rnd.JI, LF_bn_rnd.JR).main :
  ={pin, sin, glob LF_bn_rnd.JR} ==> ={res, glob LF_bn_rnd.JR}].
proof.
apply (LF_bn_rnd.Meta.ll_LF LF_bn_rnd.JR LF_bn_rnd.JI _ _ _ _ GenLF_bn_rnd). 
+ by apply LF_bn_rnd.stateless_JI.
+ by apply LF_bn_rnd.proj_JR_JI.
+ by apply LF_bn_rnd.prMuE.
by proc; islossless; smt(bn_rnd_ll).
qed.




theory LF_bn_rsample.

clone import LF_Meta as Meta
 with type pin_t <- BN.t, (* bnd *)
      type sin_t <- BN.t, (* a *)
      type out_t <- BN.t. (* res *)

module JI = {
 proc main(pin : BN.t, sin: BN.t) : BN.t = {
  var r;
  r <@ M.__bn_rsample(sin,pin);
  return r;
 }
}.

lemma stateless_JI &m x: (glob JI){m} = x
 by done.

module JR = {
 proc main(pin : BN.t, sin: BN.t) : BN.t = {
  var r;
  r <@ Mleak.__bn_rsample(sin,pin);
  return r;
 }
 proc mainG(pin : BN.t, sin: BN.t) : BN.t * leakages_t = {
  var r;
  r <@ Mleak.__bn_rsample(sin,pin);
  return (r, Mleak.leakages);
 }
}.

lemma proj_JR_JI:
 equiv [ JR.main ~ JI.main
       : ={pin, sin} ==> ={res} ]
 by sim.

lemma globJR:
 equiv [ JR.main ~ JR.mainG
       : ={pin,sin,glob JR}
         ==> ={glob JR} /\ res{2} = (res{1},glob JR){2} ].
proof.
proc*; inline JR.main JR.mainG.
wp; call (: ={arg,glob JR} ==> ={res,glob JR}) => //.
 by proc; sim.
by auto.
qed.

lemma prMuE P pin sin &m:
 Pr[ JR.main(pin,sin) @ &m : P (res,glob JR)]
 = RealSeries.sum (fun (x:_*_) => Pr [JR.main(pin,sin) @ &m : P (res,glob JR) /\ res=x.`1 /\ (glob JR)=x.`2]).
proof.
have ->: Pr[JR.main(pin, sin) @ &m : P (res,glob JR)]
  = Pr[JR.mainG(pin, sin) @ &m : P res].
 byequiv => //.
 by conseq globJR => /> // /#.
rewrite Pr [muE].
apply RealSeries.eq_sum; move => [r l].
rewrite eq_sym.
by byequiv globJR => /> /#.
qed.

end LF_bn_rsample.


(**
  * PROOF OF LEAKAGE-FREENESS FOR __bn_rsample
***)

(* Auxiliary theory for decoupling the sampling from leaked events *)
abstract theory SampleEventSwap.

type in_t.
type out_t.

require import DBool DProd.
import Biased.

module SampleEvent = {
 proc sample(i: in_t, d: in_t -> out_t distr, P: in_t -> out_t -> bool): out_t * bool = {
  var b, x;
  x <$ d i;
  b <- P i x;
  return (x, b);
 }
 proc sampleEv(i: in_t, d: in_t -> out_t distr, P: in_t -> out_t -> bool): out_t * bool = {
  var b, x;
  b <$ dbiased (mu (d i) (P i));
  x <$ if b then dcond (d i) (P i) else dcond (d i) (predC (P i));
  return (x, b);
 }
}.


clone DLetSampling as LS with
 type t <- bool,
 type u <- out_t.

equiv sample_sampleEv:
 SampleEvent.sample ~ SampleEvent.sampleEv:
 ={i, d, P} /\ is_lossless (d i){2} 
 ==> ={res}.
proof.
proc; simplify; wp.
case: ((mu (d i) (P i)){2}=0%r).
 seq 0 1: (#pre /\ !b{2}).
  rnd{2}; auto => /> &m Hll Hb; split; first by apply dbiased_ll.
  by move=> _ b; rewrite Hb dbiased0 supp_dunit.
 rnd; auto => /> &m Hll Hb0 Hb; split.
  move=> xR; rewrite dcond_supp; move=> [Hx1 Hx2].
  by rewrite dcond1E Hx2 /= mu_not Hll Hb0 /=.
 move => H xL Hx; split.
  by rewrite dcond_supp Hx /predC /=; apply (eq0_mu (d{m} i{m}) (P{m} i{m})).
 by rewrite dcond_supp Hx /predC /= /#.
case: ((mu (d i) (P i)){2}=1%r).
 seq 0 1: (#pre /\ b{2}).
  rnd{2}; auto => /> &m Hll _ Hb; split; first by apply dbiased_ll.
  by move=> _ b; rewrite Hb dbiased1 supp_dunit.
 rnd; auto => /> &m Hll _ Hb1 Hb; split.
  move=> xR; rewrite dcond_supp; move=> [Hx1 Hx2].
  by rewrite dcond1E Hx2 Hb1.
 move => _ xL Hx; split.
  rewrite dcond_supp Hx /=. 
  apply (mu_in_weight (P{m} i{m}) (d{m} i{m})) => //.
  by rewrite Hb1 Hll.
 by rewrite dcond_supp Hx /#.
transitivity{1} { x <@ LS.SampleDLet.sample(dbiased (mu (d i) (P i)), fun b=> if b then dcond (d i) (P i) else dcond (d i) (predC (P i))); }
 (={i,d,P} /\ is_lossless (d i){2} /\ 0%r < (mu (d i) (P i)){2} < 1%r
  ==> ={x,i,d,P} /\ is_lossless (d i){2} /\ 0%r < (mu (d i) (P i)){2} < 1%r)
 (={i,d,P} /\ is_lossless (d i){2} /\ 0%r < (mu (d i) (P i)){2} < 1%r ==> ={x} /\ P{1} i{1} x{1}=b{2}) => //.
  by move=> /> &m Hll Hbias1 Hbias2; exists P{m} d{m} i{m}; smt(mu_bounded).
 inline*; auto => /> &m Hll Hbias1 Hbias2; split.
  move=> xR.
  by rewrite -marginal_sampling_pred //.
 move => H xL HxL.
 rewrite supp_dlet.
 case: (P{m} i{m} xL) => bL.
  exists true => /=.
  rewrite supp_dbiased 1:/#.
  by rewrite dcond_supp.
 exists false => /=.
 rewrite supp_dbiased 1:/#.
 by rewrite dcond_supp.
transitivity{1} { x <@ LS.SampleDep.sample(dbiased (mu (d i) (P i)), fun b=> if b then dcond (d i) (P i) else dcond (d i) (predC (P i))); }
 (={i,d,P} /\ 0%r < (mu (d i) (P i)){2} < 1%r ==> ={x,i,d,P} /\ 0%r < (mu (d i) (P i)){2} < 1%r)
 (={i,d,P} /\ 0%r < (mu (d i) (P i)){2} < 1%r ==> ={x} /\ P{1} i{1} x{1}=b{2}) => //.
  by move=> /> &m Hll Hbias1 Hbias2; exists P{m} d{m} i{m}; auto.
 by symmetry; call LS.SampleDepDLet => //=.
inline*; auto => /> &m Hbias1 Hbias2 b Hb xL.
by case: (b) => Cb; rewrite dcond_supp /#.
qed.

end SampleEventSwap.



(** Auxiliary theory to perform the eager/lazy sampling on the rejection loop *)
abstract theory RejectionLoop.

type t.

op dt: t distr.
op p : t -> t -> bool.
(* workaround to get a lossless distribution on the underlying RO (required in EC's
 PROM.ec library *)
op t0: t.
op p_ll bnd x = bnd=t0 \/ p bnd x.

axiom dt_ll: is_lossless dt.
axiom t0_ll: 0%r < mu1 dt t0.
axiom p_t0E: p t0=pred0.
axiom p_t0P bnd: bnd <> t0 => p bnd t0.
axiom dtPN_ll bnd: 0%r < mu dt (predC (p bnd)).

lemma dcondP_ll bnd b:
 is_lossless (if b then dcond dt (p_ll bnd) else dcond dt (predC (p bnd))).
proof.
case: (b) => ?.
 rewrite /p_ll dcond_ll.
 case: (bnd=t0) => E /=; first smt(dt_ll).
 apply (StdOrder.RealOrder.ltr_le_trans (mu1 dt t0) _ _ t0_ll).
 apply mu_le => x _ @/pred1 /= ->.
 by apply p_t0P.
rewrite dcond_ll; exact dtPN_ll.
qed.

lemma p_llE bnd:
 bnd <> t0 => p_ll bnd = p bnd by smt().

module type AdvLoop = {
  proc loop_init(b: bool): unit
  proc loop_body(b: bool): unit
}.

require import DBool.
import Biased.

module RejLoop(L:AdvLoop) = {
  proc loopEager (bnd: t) = {
    var x, b;
    b <$ dbiased (mu dt (p bnd));
    x <$ if b then dcond dt (p bnd)
              else dcond dt (predC (p bnd));
    L.loop_init(b);
    while (! b) {
      b <$ dbiased (mu dt (p bnd));
      x <$ if b then dcond dt (p bnd)
                else dcond dt (predC (p bnd));
      L.loop_body(b);
    }
    return x;
  }
  proc loopLazy (bnd: t) = {
    var x, b;
    b <$ dbiased (mu dt (p bnd));
    L.loop_init(b);
    while (!b) {
      b <$ dbiased (mu dt (p bnd));
      L.loop_body(b);
    }
    x <$ dcond dt (p bnd);
    return x;
  }
}.


require import PROM SmtMap.

clone import PROM.FullRO as ROx with
    type in_t    <- t*bool,
    type out_t   <- t, 
    type d_in_t  <- t,
    type d_out_t <- t,
    op   dout    <- fun y:_*_=> if y.`2
                            then dcond dt (p_ll y.`1)
                            else dcond dt (predC (p y.`1))
  proof *.

module RejLoop_D (L:AdvLoop) (O: RO) = {
 proc distinguish(bnd): t = {
  var b, x;
  b <$ dbiased (mu dt (p bnd));
  O.sample((bnd,b));
  L.loop_init(b);
  while (!b) {
    O.rem((bnd,b));
    b <$ dbiased (mu dt (p bnd));
    O.sample((bnd,b));
    L.loop_body(b);
  }
  x <@ O.get((bnd,b));
  return x;
 }
}.

section.

declare module L <: AdvLoop {+Mleak}.

module RejLoopD = RejLoop_D(L).

lemma pr_loopEager_t0 &m:
 Pr[RejLoop(L).loopEager(t0) @ &m : true] = 0%r.
proof.
byphoare (:arg=t0 ==> _) => //.
proc; hoare.
while (!b /\ bnd=t0) => //.
 call (:true).
 auto => /> &1 b b'.
 by rewrite p_t0E mu0 dbiased0 supp_dunit => -> /=.
call (:true); auto => /> b.
by rewrite p_t0E mu0 dbiased0 supp_dunit => -> /=.
qed.

lemma pr_loopLazy_t0 &m:
 Pr[RejLoop(L).loopLazy(t0) @ &m : true] = 0%r.
proof.
byphoare (:arg=t0 ==> _) => //.
proc; hoare.
seq 3: (bnd=t0).
 while (!b /\ bnd=t0) => //.
  call (:true).
  auto => /> &1 b b'.
  by rewrite p_t0E mu0 dbiased0 supp_dunit => -> /=.
 call (:true); auto => /> b.
 by rewrite p_t0E mu0 dbiased0 supp_dunit => -> /=.
by auto => /> x; rewrite p_t0E dcond_supp /pred0 /=.
qed.

equiv rejloop_t0_eq:
 RejLoop(L).loopEager ~ RejLoop(L).loopLazy
 : ={bnd} /\ bnd{2}=t0 ==> ={res, glob L}.
proof.
bypr (res,glob L){1} (res,glob L){2} => //.
move=> /> &1 &2 [r l] -> ->.
have ->: Pr[RejLoop(L).loopEager(t0) @ &1 : (res, (glob L)) = (r, l)] = 0%r.
 by rewrite -(pr_loopEager_t0 &1); smt(mu_le pr_loopEager_t0).
by rewrite eq_sym -(pr_loopLazy_t0 &1); smt(mu_le pr_loopLazy_t0).
qed.

equiv rejloop_eq:
 RejLoop(L).loopEager ~ RejLoop(L).loopLazy
 : ={bnd, glob L} ==> ={res, glob L}.
proof.
proc*; case: (bnd{2}=t0).
 by call rejloop_t0_eq => //.
have ?:= dcondP_ll.
transitivity{1}
 { RO.init();
   r <@ RejLoopD(RO).distinguish(bnd); }
 ( ={bnd,glob L} /\ bnd{2} <> t0 ==> ={r, glob L} )
 ( ={bnd,glob L} /\ bnd{2} <> t0 ==> ={r, glob L} ) => //.
+ by move=> /> &2 H; exists (glob L){2} bnd{2} => />.
+ inline RejLoop(L).loopEager RejLoopD(RO).distinguish.
  inline RO.sample RO.get RO.init.
  seq 4 8: (={bnd0, b, glob L} /\ bnd0{2} <> t0 /\ RO.m{2}=empty.[(bnd0{2},b{2}) <- x{1}]).
   swap {2} 1 5.
   seq 3 5: (={bnd0, b, glob L} /\ bnd0{2} <> t0 /\ x{1}=r1{2} /\ x3{2}=(bnd0{2},b{2})).
    by rnd; wp; rnd; auto => /> &2 Hbnd b Hb; split; move => y; rewrite !p_llE //.
   rcondt {2} 2.
    by move=> &m; auto => /> *; apply mem_empty.
   by call (: true); auto => />.
  seq 1 1: (b{2} /\ #pre).
   while (#pre).
    seq 0 1: (!b{2} /\ ={bnd0, b, glob L} /\ bnd0{2} <> t0 /\ RO.m{2}=empty).
     inline*; auto => /> &1 &2 *.
     rewrite /rem set_valE empty_valE /= -(tomapK empty); congr.
     by rewrite empty_valE /#.
    seq 2 4: (#[2:]pre /\ x{1}=r2{2} /\ x4{2}=(bnd0{2},b{2})).
     by rnd; wp; rnd; auto => /> *; split; move => y; rewrite !p_llE //.
    rcondt {2} 1.
     by move=> &m; auto => /> *; apply mem_empty.
    by call (: true); auto => /> *.
   done.
  rcondf {2} 3.
   by move=> &m; auto => /> *; smt(mem_set). 
  wp; rnd{2}; auto => /> &1 &2 *; split => *.
   smt().
  by rewrite get_setE.
transitivity{1}
 { LRO.init();
   r <@ RejLoopD(LRO).distinguish(bnd); }
 ( ={bnd, glob L} /\ bnd{2} <> t0 ==> ={r, glob L} )
 ( ={bnd, glob L} /\ bnd{2} <> t0 ==> ={r, glob L} ) => //.
+ by move=> /> &2 *; exists (glob L){2} bnd{2} => />.
+ call (FullEager.RO_LRO_D RejLoopD) => />.
   move=> /> xb.
   by case: (xb) => ? /#.
  by inline*; auto => />.
inline RejLoop(L).loopLazy RejLoopD(LRO).distinguish.
inline LRO.sample LRO.get LRO.init.
seq 6 4: (={bnd0, b, glob L} /\ bnd0{2} <> t0 /\ RO.m{1}=empty /\ b{2}).
 while (={bnd0, b, glob L} /\ bnd0{2} <> t0 /\ RO.m{1}=empty).
  inline *; call (: true); auto => /> &2.
  smt(rem_id mem_empty).
 by wp; call (: true); auto => /> *.
rcondt {1} 3.
 by move=> &m; auto => />; smt(mem_empty).
by auto => /> &2 Hb *; smt(p_llE get_setE).
qed.

end section.

print rejloop_eq.

end RejectionLoop.

(** Instantiation of abstract theories *)
clone import SampleEventSwap as EvSwap
 with type in_t <- BN.t,
      type out_t <- BN.t.

clone import RejectionLoop as RSloop
 with type t <- BN.t,
      op p <- fun bnd x => bn x < bn bnd,
      op t0 <- bn_ofint 0,
      op dt <- bn_rnd
 proof dt_ll by exact bn_rnd_ll
 proof t0_ll by smt(bn_rnd1E bn_modulusE StdOrder.IntOrder.expr_gt0)
 proof p_t0E by (move => *; rewrite bn_ofintK mod0z; smt(bnk_cmp))
 proof *.
realize p_t0P.
move=> bnd Hbnd; rewrite bn_ofintK modz_small 1:bn_modulusE /=.
 smt(StdOrder.IntOrder.expr_gt0).
have ?: bn bnd <> 0 by smt(bnK).
smt(bnk_cmp).
qed.
realize dtPN_ll.
move=> bnd.
apply (StdOrder.RealOrder.ltr_le_trans (mu1 bn_rnd bnd)).
 rewrite bn_rnd1E. smt.
by apply mu_le => x _ @/predC @/pred1 /= -> /#.
qed.


module RSampleLoop = {
  proc loop_init(b: bool): unit = {
    var r1, _r1;
    Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    r1 <@ LF_bn_rnd.JR.main(tt, witness);
    Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    _r1 <@ LF_bn_lt.JR.main(tt, (witness, witness));
    Mleak.leakages <- LeakCond (!b) :: LeakAddr [] :: Mleak.leakages;
  }
  proc loop_body(b: bool): unit = {
    var r1, _r1;
    Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    r1 <@ LF_bn_rnd.JR.main(tt, witness);
    Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    _r1 <@ LF_bn_lt.JR.main(tt, (witness, witness));
    Mleak.leakages <- LeakCond (!b) :: LeakAddr [] :: Mleak.leakages;
  }
}.

(** Main result establishes the Coupled-Composition property
 (CC, in the PRHL_Defs terminology) for the rejection sampling.
 The strategy  is the following:
   1) exploit the CT property (more precisely,
  its simpler formulation for procedures for which
  divergence is determined by public  inputs -- CT')
  of the called procedures (__bn_rnd and __bn_lt_cf)
  in order to decouple the generation of leakage in
  those functions from the relevant data;
   2) decouple the leaked event from the generated
  number (abstract theory EventSwap)
   3) rearrange the samplings on the rejection loop
  (Eager/Lazy sampling reasoning, based on the abstract
  theory RejectionLoop).

 In the between, a lot of boilerplate is needed
 to fit the formalization on the abstract setting
 of leakage-free definitions and related
 meta-properties (PRHL_Defs.ec), as well
 as instantiations required from the abstract
 theories.                                  *)
lemma CC_bn_rsample:
 equiv[ LF_bn_rsample.JR.main ~ LF_bn_rsample.Meta.CC(LF_bn_rsample.JI, LF_bn_rsample.JR).main :
  ={pin, sin, glob LF_bn_rsample.JR} ==> ={res, glob LF_bn_rsample.JR}].
proof.
proc*; simplify.
inline LF_bn_rsample.Meta.CC(LF_bn_rsample.JI, LF_bn_rsample.JR).main.
inline LF_bn_rsample.JR.main LF_bn_rsample.JI.main Mleak.__bn_rsample.

transitivity {1}
 { bnd <- pin;
   a <- sin;
   Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
   a <@ LF_bn_rnd.JR.main(tt,a);
   Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
   cf <@ LF_bn_lt.JR.main(tt, (a,bnd));
   Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
   while (!cf) {
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     a <@ LF_bn_rnd.JR.main(tt,a);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     cf <@ LF_bn_lt.JR.main(tt, (a,bnd));
     Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
   }
   r <- a;
 }
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages} )
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages} ) => //.
+ move=> /> &2 /#.
+ inline LF_bn_rnd.JR.main LF_bn_lt.JR.main.
  wp; while(#pre /\ ={a,cf,bnd}).
   wp; call(: ={Mleak.leakages}); first by sim.
   by inline*; auto => />.
  wp; call(: ={Mleak.leakages}); first by sim.
  by inline*; auto => />.

transitivity {1}
 { bnd <- pin;
   a <- sin;
   Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
   a <@ LF_bn_rnd.Meta.SimR(LF_bn_rnd.JI, LF_bn_rnd.JR).main(tt,a, witness);
   Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
   cf <@ LF_bn_lt.Meta.SimR(LF_bn_lt.JI, LF_bn_lt.JR).main(tt, (a,bnd), (witness, witness));
   Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
   while (!cf) {
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     a <@ LF_bn_rnd.Meta.SimR(LF_bn_rnd.JI, LF_bn_rnd.JR).main(tt,a, witness);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     cf <@ LF_bn_lt.Meta.SimR(LF_bn_lt.JI, LF_bn_lt.JR).main(tt, (a,bnd), (witness, witness));
     Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
   }
   r <- a;
 }
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages} )
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages} ) => //.
+ move=> /> &2 /#.
+ wp; while(#pre /\ ={a,cf,bnd}).
   wp; call LF_bn_lt.
   by wp; call LF_bn_rnd; auto => />.
  wp; call LF_bn_lt.
  by wp; call LF_bn_rnd; auto => />.
inline LF_bn_rnd.Meta.SimR(LF_bn_rnd.JI, LF_bn_rnd.JR).main.
inline LF_bn_lt.Meta.SimR(LF_bn_lt.JI, LF_bn_lt.JR).main.
swap {1} [4..5] -1.
swap {1} [8..9] -3.
swap {1} [11..12] -4.
swap {1} [15..16] -6.

transitivity {1}
 { bnd <- pin;
   a <- sin;
   (a, cf) <@ SampleEvent.sample(bnd, (fun _ => bn_rnd), fun bnd x => bn x < bn bnd);
   Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
   r1 <@ LF_bn_rnd.JR.main(tt, witness);
   Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
   _r1 <@ LF_bn_lt.JR.main(tt, (witness,witness));
   Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
   while (!cf) {
     (a, cf) <@ SampleEvent.sample(bnd, (fun _ => bn_rnd), fun bnd x => bn x < bn bnd);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     r1 <@ LF_bn_rnd.JR.main(tt, witness);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     _r1 <@ LF_bn_lt.JR.main(tt, (witness,witness));
     Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
   }
   r <- a;
 }
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages} )
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages} ) => //.
+ move=> /> &2 /#.
+ wp; while(#pre /\ ={a,cf,bnd}).
   inline SampleEvent.sample.
   swap {1} [2..3] -1.
   swap {1} [6..7] -3.
   swap {1} [9..10] -4.
   swap {1} [13..14] -6.
   wp; call(: ={Mleak.leakages}); first by sim.
   wp; call(: ={Mleak.leakages}); first by sim.
   inline LF_bn_lt.JI.main.
   wp; ecall {1} (__bn_lt_cf_ph sin5.`1{1} sin5.`2{1}).
   by inline*; auto => /> *.
  wp; call(: ={Mleak.leakages}); first by sim.
  wp; call(: ={Mleak.leakages}); first by sim.
  inline LF_bn_lt.JI.main.
  wp; ecall {1} (__bn_lt_cf_ph sin5.`1{1} sin5.`2{1}).
  by inline*; auto => /> *.

transitivity {1}
 { bnd <- pin;
   a <- sin;
   (a, cf) <@ SampleEvent.sampleEv(bnd, (fun _ => bn_rnd), fun bnd x => bn x < bn bnd);
   Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
   r1 <@ LF_bn_rnd.JR.main(tt, witness);
   Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
   _r1 <@ LF_bn_lt.JR.main(tt, (witness,witness));
   Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
   while (!cf) {
     (a, cf) <@ SampleEvent.sampleEv(bnd, (fun _ => bn_rnd), fun bnd x => bn x < bn bnd);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     r1 <@ LF_bn_rnd.JR.main(tt, witness);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     _r1 <@ LF_bn_lt.JR.main(tt, (witness,witness));
     Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
   }
   r <- a;
 }
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages} )
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages} ) => //.
+ move=> /> &2 /#.
+ wp; while(#pre /\ ={a,cf,bnd}).
   wp; call(: ={Mleak.leakages}); first by sim.
   wp; call(: ={Mleak.leakages}); first by sim.
   wp; call EvSwap.sample_sampleEv.
   by auto => />; smt(bn_rnd_ll).
  wp; call(: ={Mleak.leakages}); first by sim.
  wp; call(: ={Mleak.leakages}); first by sim.
  wp; call EvSwap.sample_sampleEv.
  by auto => />; smt(bn_rnd_ll).

transitivity {1}
 { r <@ RSloop.RejLoop(RSampleLoop).loopEager(pin); }
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages})
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages}) => //.
+ by move=> /> &2; exists Mleak.leakages{2} pin{2} sin{2} => />.
+ inline RejLoop(RSampleLoop).loopEager.
  inline SampleEvent.sampleEv.
  inline RSampleLoop.loop_init RSampleLoop.loop_body.
  wp; while (={Mleak.leakages} /\ (cf,a,bnd){1}=(b,x,bnd0){2}).
   wp; call(: ={Mleak.leakages}); first by sim.
   wp; call(: ={Mleak.leakages}); first by sim.
   by auto.
  wp; call(: ={Mleak.leakages}); first by sim.
  wp; call(: ={Mleak.leakages}); first by sim.
  by auto.

transitivity {1}
 { r <@ RSloop.RejLoop(RSampleLoop).loopLazy(pin); }
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages})
 ( ={pin, sin, Mleak.leakages} ==> ={r, Mleak.leakages}) => //.
+ by move=> /> &2; exists Mleak.leakages{2} pin{2} sin{2} => />.
+ call (rejloop_eq RSampleLoop); auto => />.

inline RejLoop(RSampleLoop).loopLazy.
inline RSampleLoop.loop_init RSampleLoop.loop_body.
seq 9 18: (={Mleak.leakages} /\ bnd0{1}=pin2{2}).
 transitivity {1}
  { bnd0 <- pin;
    (a, b) <@ SampleEvent.sampleEv(bnd0, (fun _ => bn_rnd), fun bnd x => bn x < bn bnd);
    Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    r10 <@ LF_bn_rnd.JR.main(tt, witness);
    Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    _r10 <@ LF_bn_lt.JR.main(tt, (witness, witness));
    Mleak.leakages <- LeakCond (!b) :: LeakAddr [] :: Mleak.leakages;
    while (!b) {
     (a, b) <@ SampleEvent.sampleEv(bnd0, (fun _ => bn_rnd), fun bnd x => bn x < bn bnd);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     r10 <@ LF_bn_rnd.JR.main(tt, witness);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     _r10 <@ LF_bn_lt.JR.main(tt, (witness, witness));
     Mleak.leakages <- LeakCond (!b) :: LeakAddr [] :: Mleak.leakages;
    }
   }
   ( ={pin, sin, Mleak.leakages} ==> ={Mleak.leakages} /\ bnd0{1} = pin{2} )
   ( ={pin, sin, Mleak.leakages} ==> ={pin, Mleak.leakages} /\ pin2{2} = pin{2} ) => //.
 + by move => /> &2; exists Mleak.leakages{2} pin{2} sin{2} => //.
 + inline SampleEvent.sampleEv.
   while(#pre /\ ={b,bnd0} /\ bnd0{2} = pin{2}).
    wp; call(: ={Mleak.leakages}); first by sim.
    wp; call(: ={Mleak.leakages}); first by sim.
    by wp; rnd{2}; auto => /> &2 b b'; smt(dbiased_dcond_ll bn_rnd_ll).
   wp; call(: ={Mleak.leakages}); first by sim.
   wp; call(: ={Mleak.leakages}); first by sim.
   by wp; rnd{2}; auto => /> &2 b b';  smt(dbiased_dcond_ll bn_rnd_ll).

 transitivity {1}
  { bnd0 <- pin;
    (a, b) <@ SampleEvent.sample(bnd0, (fun _ => bn_rnd), fun bnd x => bn x < bn bnd);
    Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    r10 <@ LF_bn_rnd.JR.main(tt, witness);
    Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    _r10 <@ LF_bn_lt.JR.main(tt, (witness, witness));
    Mleak.leakages <- LeakCond (!b) :: LeakAddr [] :: Mleak.leakages;
    while (!b) {
     (a, b) <@ SampleEvent.sample(bnd0, (fun _ => bn_rnd), fun bnd x => bn x < bn bnd);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     r10 <@ LF_bn_rnd.JR.main(tt, witness);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     _r10 <@ LF_bn_lt.JR.main(tt, (witness, witness));
     Mleak.leakages <- LeakCond (!b) :: LeakAddr [] :: Mleak.leakages;
    }
   }
   ( ={pin, sin, Mleak.leakages} ==> ={pin, Mleak.leakages} /\ bnd0{1} = pin{2} )
   ( ={pin, sin, Mleak.leakages} ==> ={pin, Mleak.leakages} /\ pin2{2}=pin{2} ) => //.
 + by move => /> &2; exists Mleak.leakages{2} pin{2} sin{2} => //.
 + symmetry. 
   while(#pre /\ ={b,bnd0} /\ bnd0{2} = pin{2}).
    wp; call(: ={Mleak.leakages}); first by sim.
    wp; call(: ={Mleak.leakages}); first by sim.
    wp; call EvSwap.sample_sampleEv.
    auto => />; smt(bn_rnd_ll).
   wp; call(: ={Mleak.leakages}); first by sim.
   wp; call(: ={Mleak.leakages}); first by sim.
   wp; call EvSwap.sample_sampleEv.
   by auto => />; smt(bn_rnd_ll).
 inline SampleEvent.sample.
 transitivity {2}
  { Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    a <@ LF_bn_rnd.JR.main(tt,sin);
    Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
    cf <@ LF_bn_lt.JR.main(tt, (a,pin));
    Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
    while (!cf) {
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     a <@ LF_bn_rnd.JR.main(tt,sin);
     Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
     cf <@ LF_bn_lt.JR.main(tt, (a,pin));
     Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
    }
   }
   ( ={pin, sin, Mleak.leakages} ==> ={pin, Mleak.leakages} /\ bnd0{1} = pin{2} )
   ( ={pin, sin, Mleak.leakages} ==> ={pin, Mleak.leakages} /\ pin2{2} = pin{2} ) => //.
 + by move => /> &2; exists Mleak.leakages{2} pin{2} sin{2} => //.
 + transitivity {2}
    { Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
      a <@ LF_bn_rnd.Meta.SimR(LF_bn_rnd.JI, LF_bn_rnd.JR).main(tt,sin,witness);
      Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
      cf <@ LF_bn_lt.Meta.SimR(LF_bn_lt.JI, LF_bn_lt.JR).main(tt, (a,pin), (witness,witness));
      Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
      while (!cf) {
       Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
       a <@ LF_bn_rnd.Meta.SimR(LF_bn_rnd.JI, LF_bn_rnd.JR).main(tt,sin,witness);
       Mleak.leakages <- LeakAddr [] :: Mleak.leakages;
       cf <@ LF_bn_lt.Meta.SimR(LF_bn_lt.JI, LF_bn_lt.JR).main(tt, (a,pin), (witness,witness));
       Mleak.leakages <- LeakCond (!cf) :: LeakAddr [] :: Mleak.leakages;
      }
     }
     ( ={pin, sin, Mleak.leakages} ==> ={pin, Mleak.leakages} /\ bnd0{1} = pin{2} )
     ( ={pin, sin, Mleak.leakages} ==> ={pin, Mleak.leakages} ) => //.
   - by move => /> &2; exists Mleak.leakages{2} pin{2} sin{2} => //.
   - inline LF_bn_rnd.Meta.SimR LF_bn_lt.Meta.SimR.
     inline LF_bn_rnd.JI.main LF_bn_lt.JI.main.
     while ((b,bnd0){1}=(cf,pin){2} /\ ={Mleak.leakages} ).
      swap {2} [7..10] -3.
      swap {2} [16..20] -2.
      swap {2} [12..18] -3.
      swap {2} 1 14.
      wp; call(: ={Mleak.leakages}); first by sim.
      wp; call(: ={Mleak.leakages}); first by sim.
      wp; ecall {2} (__bn_lt_cf_ph sin10{2}.`1 sin10{2}.`2).
      by inline*; auto => />.
     swap {2} [6..10] -2.
     swap {2} [16..20] -2.
     swap {2} [12..18] -3.
     swap {2} 1 14.
     wp; call(: ={Mleak.leakages}); first by sim.
     wp; call(: ={Mleak.leakages}); first by sim.
     wp; ecall {2} (__bn_lt_cf_ph sin8{2}.`1 sin8{2}.`2).
     by inline*; auto => /> *.
   symmetry.
   while (#pre /\ ={cf}).
    wp; call LF_bn_lt.
    by wp; call LF_bn_rnd; auto.
   wp; call LF_bn_lt.
   by wp; call LF_bn_rnd; auto.
 inline LF_bn_rnd.JR.main LF_bn_lt.JR.main.
 wp; while(#pre /\ ={a,cf} /\ bnd{2}=pin{2}).
  wp; call(: ={Mleak.leakages}); first by sim.
  by inline*; auto => />.
 wp; call(: ={Mleak.leakages}); first by sim.
 by inline*; auto => />.
wp.
transitivity {2}
 { r2 <@ M.bn_sample_bnd(sin2,pin2); }
 ( ={Mleak.leakages} /\ bnd0{1} = pin2{2} ==> x{1} = r2{2} /\ ={Mleak.leakages} )
 ( ={pin2,Mleak.leakages} ==> ={r2, Mleak.leakages}) => //.
+ by move=> /> &2; exists Mleak.leakages{2} pin2{2}.
+ inline*; wp.
  rnd (bnk nlimbs) bn_ofint.
  auto => /> &2; split.
   move=> x; rewrite supp_dinter => Hx.
   rewrite bn_ofintK modz_small; smt(bnk_cmp).
  move => H1; split.
   move=> x; rewrite supp_dinter => Hx.
   rewrite -bn_rnd_bndE /bn_rnd_bnd dmap1E.
   apply mu_eq_support => y.
   rewrite supp_dinter => Hy.
   rewrite /pred1 /(\o) /= eq_iff => *; split => // E.
   rewrite (:y=y%%bn_modulus) 1:modz_small //; first smt(bnk_cmp). 
   rewrite (:x=x%%bn_modulus) 1:modz_small //; first smt(bnk_cmp). 
   by rewrite -!bn_ofintK E.
  move=> H2 x; rewrite dcond_supp /= => [[H3 H4]].
  rewrite supp_dinter; smt(bnk_cmp bnK).

by symmetry; call __bn_rsample_eq; auto => />.
qed.

(** The actual CT property follows from a generic
 property formalised in PRHL_Defs.        *)
lemma LF_bn_rsample:
 equiv[  LF_bn_rsample.Meta.RSim(LF_bn_rsample.JI, LF_bn_rsample.JR).main ~  LF_bn_rsample.Meta.SimR(LF_bn_rsample.JI, LF_bn_rsample.JR).main :
  ={pin, sin, glob LF_bn_rsample.JR} ==> ={res, glob LF_bn_rsample.JR}].
proof.
apply (LF_bn_rsample.Meta.pinll_CT_CC_GenLF LF_bn_rsample.JR LF_bn_rsample.JI).
+ by apply LF_bn_rsample.stateless_JI.
+ by apply LF_bn_rsample.proj_JR_JI.
+ by apply LF_bn_rsample.prMuE.
+ exists (fun bnd => bn bnd <> 0) => /> _bnd.
  case: (bn _bnd=0) => C /=; proc; simplify.
   hoare; inline M.__bn_rsample.
   wp; while(bnd=_bnd /\ cf = bnk nlimbs a < bnk nlimbs _bnd).
    ecall (__bn_lt_cf_h a bnd).
    by inline*; auto => /> &m.
   ecall (__bn_lt_cf_h a bnd).
   by inline*; auto => &m -> a Ha r;  smt(bnk_cmp).
  call (__bn_rsample_ll); auto => />.
  smt(bnk_cmp).
split.
 proc.
 by ecall (__bn_rsample_ct).
by apply CC_bn_rsample.
qed.


end BN_base.

