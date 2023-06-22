require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

require import Array1 Array32 Array64 Array128 Array256.
require import WArray1 WArray256 WArray512 WArray1024.

abbrev bn_glob_ex_s = Array32.of_list witness [W64.of_int 7171969242160550925;
W64.of_int 8804781220001203743; W64.of_int (-3852246319478611008);
W64.of_int 1472392515548218179; W64.of_int 4948236216193327450;
W64.of_int 1031462267516433719; W64.of_int 4797027940007565550;
W64.of_int (-1682256399589077742); W64.of_int 5584558119897651268;
W64.of_int (-6253712209809932799); W64.of_int 4105145217697908108;
W64.of_int (-1148259354985652029); W64.of_int (-4443658867146326380);
W64.of_int 967507600631665215; W64.of_int 6159932005602028579;
W64.of_int (-814539739404175588); W64.of_int (-980757567606559144);
W64.of_int 8949836227897206741; W64.of_int (-1604416682951394759);
W64.of_int (-5645039729267063231); W64.of_int 1566856634118248884;
W64.of_int (-6991906000357751854); W64.of_int (-5931331373579755333);
W64.of_int (-6708708076048021469); W64.of_int 6509515618992112762;
W64.of_int 4087076476951562775; W64.of_int 2349864693353382499;
W64.of_int (-2868704435141431438); W64.of_int (-3021890234342134307);
W64.of_int 3385351981655818438; W64.of_int 1357657197262854114;
W64.of_int (-8487259051711355513)].


abbrev bn_glob_ex_w = Array32.of_list witness [W64.of_int (-2367036620189524078);
W64.of_int (-8550541620283116894); W64.of_int (-8712229529929690384);
W64.of_int 2720597558662080082; W64.of_int 5422305391744666469;
W64.of_int 6284856943141827897; W64.of_int 3571931755504819832;
W64.of_int 8898582908871733242; W64.of_int 1704218965307655612;
W64.of_int (-4490832905749386442); W64.of_int 1075360349327866006;
W64.of_int (-2791609107180202942); W64.of_int (-4956848034916094035);
W64.of_int 9091884461783532811; W64.of_int (-3607414202186932578);
W64.of_int 2391092563947328990; W64.of_int 8841078175838623648;
W64.of_int 8090086859770744697; W64.of_int (-9119420935069824008);
W64.of_int (-3086993898298106202); W64.of_int 174800848911598037;
W64.of_int (-8825346821280398995); W64.of_int (-8195586540728346178);
W64.of_int (-7769074457614894293); W64.of_int 6940916673274726784;
W64.of_int (-1739713119161693699); W64.of_int (-2449711050333163937);
W64.of_int 1915269043270820409; W64.of_int 1075662976884682063;
W64.of_int 4605192895173857279; W64.of_int (-4722177852026614603);
W64.of_int 7741315053003204029].


abbrev bn_glob_bq = Array64.of_list witness [W64.of_int (-8150875838653436726);
W64.of_int 2368294145691358254; W64.of_int (-3726409782083245059);
W64.of_int 2984881376514770213; W64.of_int 1686921512324286912;
W64.of_int 4231997920348793745; W64.of_int (-9095004901848826975);
W64.of_int (-3056963286448315638); W64.of_int 9010269563805845161;
W64.of_int 9099069857497600575; W64.of_int 6313057817749168983;
W64.of_int 2462308226731011450; W64.of_int (-1456385659703587384);
W64.of_int (-3557744342647638325); W64.of_int (-2337379951638244041);
W64.of_int 5844012461544371476; W64.of_int (-8543074259021303467);
W64.of_int 3744825669284545269; W64.of_int 2140999566259290734;
W64.of_int (-771355228120257871); W64.of_int 975876959296885154;
W64.of_int (-5180221891154462855); W64.of_int (-6274721099243124874);
W64.of_int (-7956831732515365580); W64.of_int (-6268905739573351909);
W64.of_int 3248212512580043719; W64.of_int 7202372270146058191;
W64.of_int (-3918248722746680157); W64.of_int 5599696932383583266;
W64.of_int (-8212422787780664529); W64.of_int 7917410315110611862;
W64.of_int 0; W64.of_int 2; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0].


abbrev bn_glob_bp = Array64.of_list witness [W64.of_int 5147934117528057444;
W64.of_int (-8039224964009096681); W64.of_int (-1863204891041622530);
W64.of_int 1492440688257385106; W64.of_int (-8379911280692632352);
W64.of_int (-7107373076680378936); W64.of_int 4675869585930362320;
W64.of_int (-1528481643224157819); W64.of_int (-4718237254951853228);
W64.of_int (-4673837108105975521); W64.of_int 3156528908874584491;
W64.of_int 1231154113365505725; W64.of_int (-728192829851793692);
W64.of_int (-1778872171323819163); W64.of_int 8054682061035653787;
W64.of_int (-6301365806082590070); W64.of_int (-4271537129510651734);
W64.of_int 1872412834642272634; W64.of_int (-8152872253725130441);
W64.of_int 8837694422794646872; W64.of_int (-8735433557206333231);
W64.of_int 6633261091277544380; W64.of_int 6086011487233213371;
W64.of_int (-3978415866257682790); W64.of_int (-3134452869786675955);
W64.of_int (-7599265780564753949); W64.of_int (-5622185901781746713);
W64.of_int 7264247675481435729; W64.of_int (-6423523570662984175);
W64.of_int 5117160642964443543; W64.of_int 3958705157555305931; W64.of_int 0;
W64.of_int 1; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0].


abbrev bn_glob_g = Array32.of_list witness [W64.of_int 2; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].


abbrev bn_glob_q = Array32.of_list witness [W64.of_int 9223372036854775807;
W64.of_int 772727070833136948; W64.of_int (-8437191483358117240);
W64.of_int 2074651716276106610; W64.of_int (-1218815256681510004);
W64.of_int (-2674382847595894428); W64.of_int (-3633347368985571001);
W64.of_int (-1022533074756877567); W64.of_int 1821757877029398301;
W64.of_int 8699325022722592958; W64.of_int (-5510687788852425726);
W64.of_int (-3500822466873570506); W64.of_int 1022732366008985949;
W64.of_int (-4489333936743131445); W64.of_int 3786154909252085679;
W64.of_int (-3716274418890380851); W64.of_int (-2233716848964018302);
W64.of_int 2635787932944969118; W64.of_int (-2931964266147377165);
W64.of_int (-640577683343487022); W64.of_int (-8791116239691621386);
W64.of_int 8801759307383961269; W64.of_int (-989988470549168285);
W64.of_int (-6345401765425782494); W64.of_int (-7487932334278211045);
W64.of_int (-591505533540949619); W64.of_int 2928751791759295086;
W64.of_int 73710516992331153; W64.of_int (-7745866984806160838);
W64.of_int 7089564414062235240; W64.of_int (-1979352578777652966);
W64.of_int 9223372036854775807].


abbrev bn_glob_p = Array32.of_list witness [W64.of_int (-1);
W64.of_int 1545454141666273896; W64.of_int 1572361106993317136;
W64.of_int 4149303432552213221; W64.of_int (-2437630513363020008);
W64.of_int (-5348765695191788855); W64.of_int (-7266694737971142001);
W64.of_int (-2045066149513755133); W64.of_int 3643515754058796603;
W64.of_int (-1048094028264365700); W64.of_int 7425368496004700164;
W64.of_int (-7001644933747141011); W64.of_int 2045464732017971899;
W64.of_int (-8978667873486262890); W64.of_int 7572309818504171359;
W64.of_int (-7432548837780761702); W64.of_int (-4467433697928036603);
W64.of_int 5271575865889938237; W64.of_int (-5863928532294754330);
W64.of_int (-1281155366686974043); W64.of_int 864511594326308845;
W64.of_int (-843225458941629077); W64.of_int (-1979976941098336570);
W64.of_int 5755940542857986629; W64.of_int 3470879405153129527;
W64.of_int (-1183011067081899237); W64.of_int 5857503583518590173;
W64.of_int 147421033984662306; W64.of_int 2955010104097229940;
W64.of_int (-4267615245585081135); W64.of_int (-3958705157555305932);
W64.of_int (-1)].


module type Syscall_t = {
  proc randombytes_1(_:W8.t Array1.t) : W8.t Array1.t
  proc randombytes_256(_:W8.t Array256.t) : W8.t Array256.t
}.

module Syscall : Syscall_t = {
  proc randombytes_1(a:W8.t Array1.t) : W8.t Array1.t = {
    a <$ dmap WArray1.darray
         (fun a => Array1.init (fun i => WArray1.get8 a i));
    return a;
  }
  
  proc randombytes_256(a:W8.t Array256.t) : W8.t Array256.t = {
    a <$ dmap WArray256.darray
         (fun a => Array256.init (fun i => WArray256.get8 a i));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc bn_subc (a:W64.t Array32.t, b:W64.t Array32.t) : bool *
                                                        W64.t Array32.t = {
    var aux: int;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    x1 <- a.[0];
    x2 <- b.[0];
    (cf, x1) <- sbb_64 x1 x2 false;
    a.[0] <- x1;
    i <- 1;
    while (i < 32) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- sbb_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_copy (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var r:W64.t Array32.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    i <- 0;
    while (i < 32) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_cmov (cond:bool, a:W64.t Array32.t, b:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    var r1:W64.t;
    var r2:W64.t;
    
    i <- 0;
    while (i < 32) {
      r1 <- a.[i];
      r2 <- b.[i];
      r1 <- (cond ? r2 : r1);
      a.[i] <- r1;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_set0 (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 32) {
      a.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_set1 (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    
    a.[0] <- (W64.of_int 1);
    i <- 1;
    while (i < 32) {
      a.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bn_addc (a:W64.t Array32.t, b:W64.t Array32.t) : bool *
                                                        W64.t Array32.t = {
    var aux: int;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    x1 <- a.[0];
    x2 <- b.[0];
    (cf, x1) <- adc_64 x1 x2 false;
    a.[0] <- x1;
    i <- 1;
    while (i < 32) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- adc_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc mul1 (a:W64.t, b:W64.t Array32.t) : W64.t * bool * bool *
                                           W64.t Array64.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array64.t;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, _zero) <- set0_64 ;
    x1 <- a;
    x2 <- b.[0];
    (x1, x2) <- MULX_64 x1 x2;
    r.[1] <- x1;
    r.[0] <- x2;
    i <- 1;
    while (i < 32) {
      x1 <- a;
      x2 <- b.[i];
      (x1, x2) <- MULX_64 x1 x2;
      r.[(i + 1)] <- x1;
      lo <- x2;
      x1 <- r.[i];
      x2 <- lo;
      (cf, x1) <- ADCX_64 x1 x2 cf;
      r.[i] <- x1;
      i <- i + 1;
    }
    x1 <- r.[32];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[32] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc mul1acc (k:W64.t, a:W64.t, b:W64.t Array32.t, r:W64.t Array64.t,
                _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                   W64.t Array64.t = {
    var aux: int;
    
    var kk:int;
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    kk <- (W64.to_uint k);
    aux <- (32 - 1);
    i <- 0;
    while (i < aux) {
      x1 <- a;
      x2 <- b.[i];
      (x1, x2) <- MULX_64 x1 x2;
      hi <- x1;
      lo <- x2;
      x1 <- r.[(kk + i)];
      (of_0, x1) <- ADOX_64 x1 lo of_0;
      r.[(kk + i)] <- x1;
      x1 <- r.[((kk + i) + 1)];
      (cf, x1) <- ADCX_64 x1 hi cf;
      r.[((kk + i) + 1)] <- x1;
      i <- i + 1;
    }
    x1 <- a;
    x2 <- b.[(32 - 1)];
    (x1, x2) <- MULX_64 x1 x2;
    r.[(32 + kk)] <- x1;
    lo <- x2;
    x1 <- r.[((32 + kk) - 1)];
    (of_0, x1) <- ADOX_64 x1 lo of_0;
    r.[((32 + kk) - 1)] <- x1;
    x1 <- r.[(32 + kk)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[(32 + kk)] <- x1;
    x1 <- r.[(32 + kk)];
    (of_0, x1) <- ADOX_64 x1 _zero of_0;
    r.[(32 + kk)] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc bn_muln (a:W64.t Array32.t, b:W64.t Array32.t) : W64.t * bool * bool *
                                                        W64.t Array64.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array64.t;
    var ai:W64.t;
    var rp:W64.t Array64.t;
    var bp:W64.t Array32.t;
    var i:int;
    var z:W64.t;
    bp <- witness;
    r <- witness;
    rp <- witness;
    ai <- a.[0];
    (_zero, of_0, cf, r) <@ mul1 (ai, b);
    rp <- r;
    bp <- b;
    i <- 1;
    while (i < 32) {
      ai <- a.[i];
      z <- (W64.of_int i);
      (_zero, of_0, cf, rp) <@ mul1acc (z, ai, bp, rp, _zero, of_0, cf);
      i <- i + 1;
    }
    r <- rp;
    return (_zero, of_0, cf, r);
  }
  
  proc dbn_subc (a:W64.t Array64.t, b:W64.t Array64.t) : bool *
                                                         W64.t Array64.t = {
    var aux: int;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    x1 <- a.[0];
    x2 <- b.[0];
    (cf, x1) <- sbb_64 x1 x2 false;
    a.[0] <- x1;
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- sbb_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc dbn_copy (a:W64.t Array64.t) : W64.t Array64.t = {
    var aux: int;
    
    var r:W64.t Array64.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    aux <- (32 * 2);
    i <- 0;
    while (i < aux) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc dbn_cmov (cond:bool, a:W64.t Array64.t, b:W64.t Array64.t) : W64.t Array64.t = {
    var aux: int;
    
    var i:int;
    var r1:W64.t;
    var r2:W64.t;
    
    aux <- (32 * 2);
    i <- 0;
    while (i < aux) {
      r1 <- a.[i];
      r2 <- b.[i];
      r1 <- (cond ? r2 : r1);
      a.[i] <- r1;
      i <- i + 1;
    }
    return (a);
  }
  
  proc dbn_addc (a:W64.t Array64.t, b:W64.t Array64.t) : bool *
                                                         W64.t Array64.t = {
    var aux: int;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    x1 <- a.[0];
    x2 <- b.[0];
    (cf, x1) <- adc_64 x1 x2 false;
    a.[0] <- x1;
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- adc_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc dmul1 (a:W64.t, b:W64.t Array64.t) : W64.t * bool * bool *
                                            W64.t Array128.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array128.t;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, _zero) <- set0_64 ;
    x1 <- a;
    x2 <- b.[0];
    (x1, x2) <- MULX_64 x1 x2;
    r.[1] <- x1;
    r.[0] <- x2;
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      x1 <- a;
      x2 <- b.[i];
      (x1, x2) <- MULX_64 x1 x2;
      r.[(i + 1)] <- x1;
      lo <- x2;
      x1 <- r.[i];
      x2 <- lo;
      (cf, x1) <- ADCX_64 x1 x2 cf;
      r.[i] <- x1;
      i <- i + 1;
    }
    x1 <- r.[(32 * 2)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[(32 * 2)] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc dmul1acc (k:W64.t, a:W64.t, b:W64.t Array64.t, r:W64.t Array128.t,
                 _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                    W64.t Array128.t = {
    var aux: int;
    
    var kk:int;
    var x1:W64.t;
    var i:int;
    var x2:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    kk <- (W64.to_uint k);
    aux <- ((32 * 2) - 1);
    i <- 0;
    while (i < aux) {
      x1 <- a;
      x2 <- b.[i];
      (x1, x2) <- MULX_64 x1 x2;
      hi <- x1;
      lo <- x2;
      x1 <- r.[(kk + i)];
      (of_0, x1) <- ADOX_64 x1 lo of_0;
      r.[(kk + i)] <- x1;
      x1 <- r.[((kk + i) + 1)];
      (cf, x1) <- ADCX_64 x1 hi cf;
      r.[((kk + i) + 1)] <- x1;
      i <- i + 1;
    }
    x1 <- a;
    x2 <- b.[((32 * 2) - 1)];
    (x1, x2) <- MULX_64 x1 x2;
    r.[((32 * 2) + kk)] <- x1;
    lo <- x2;
    x1 <- r.[(((32 * 2) + kk) - 1)];
    (of_0, x1) <- ADOX_64 x1 lo of_0;
    r.[(((32 * 2) + kk) - 1)] <- x1;
    x1 <- r.[((32 * 2) + kk)];
    (cf, x1) <- ADCX_64 x1 _zero cf;
    r.[((32 * 2) + kk)] <- x1;
    x1 <- r.[((32 * 2) + kk)];
    (of_0, x1) <- ADOX_64 x1 _zero of_0;
    r.[((32 * 2) + kk)] <- x1;
    return (_zero, of_0, cf, r);
  }
  
  proc dbn_muln (a:W64.t Array64.t, b:W64.t Array64.t) : W64.t * bool *
                                                         bool *
                                                         W64.t Array128.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array128.t;
    var ai:W64.t;
    var rp:W64.t Array128.t;
    var bp:W64.t Array64.t;
    var i:int;
    var z:W64.t;
    bp <- witness;
    r <- witness;
    rp <- witness;
    ai <- a.[0];
    (_zero, of_0, cf, r) <@ dmul1 (ai, b);
    rp <- r;
    bp <- b;
    aux <- (32 * 2);
    i <- 1;
    while (i < aux) {
      ai <- a.[i];
      z <- (W64.of_int i);
      (_zero, of_0, cf, rp) <@ dmul1acc (z, ai, bp, rp, _zero, of_0, cf);
      i <- i + 1;
    }
    r <- rp;
    return (_zero, of_0, cf, r);
  }
  
  proc ith_bit64 (k:W64.t, ctr:W64.t) : W64.t = {
    
    var bit:W64.t;
    var p:W64.t;
    
    bit <- k;
    p <- ctr;
    p <- (p `&` (W64.of_int 63));
    bit <- (bit `>>` (truncateu8 p));
    bit <- (bit `&` (W64.of_int 1));
    return (bit);
  }
  
  proc ith_bit (kk:W64.t Array32.t, ctr:W64.t) : W64.t = {
    
    var bit:W64.t;
    var ctr2:W64.t;
    var ctr3:W64.t;
    var c1:W64.t;
    var c2:W64.t;
    var r:W64.t;
    
    ctr2 <- ctr;
    ctr3 <- ctr;
    c1 <- (ctr2 `>>` (W8.of_int 6));
    c2 <- (ctr3 `&` (W64.of_int 63));
    r <- kk.[(W64.to_uint c1)];
    bit <@ ith_bit64 (r, c2);
    return (bit);
  }
  
  proc swapr (x:W64.t Array32.t, y:W64.t Array32.t, swap_0:W64.t) : W64.t Array32.t *
                                                                    W64.t Array32.t = {
    var aux: int;
    
    var mask:W64.t;
    var i:int;
    var tmp1:W64.t;
    var tmp2:W64.t;
    
    mask <- (swap_0 * (W64.of_int 18446744073709551615));
    i <- 0;
    while (i < 32) {
      tmp1 <- x.[i];
      tmp1 <- (tmp1 `^` y.[i]);
      tmp1 <- (tmp1 `&` mask);
      x.[i] <- (x.[i] `^` tmp1);
      tmp2 <- y.[i];
      tmp2 <- (tmp2 `^` tmp1);
      y.[i] <- tmp2;
      i <- i + 1;
    }
    return (x, y);
  }
  
  proc sn_cmov (cond:bool, a:W64.t, b:W64.t) : W64.t = {
    
    var r1:W64.t;
    var r2:W64.t;
    
    r1 <- a;
    r2 <- b;
    r1 <- (cond ? r2 : r1);
    a <- r1;
    return (a);
  }
  
  proc bn_eq (a:W64.t Array32.t, b:W64.t Array32.t) : W64.t = {
    var aux: int;
    
    var output:W64.t;
    var result:W64.t;
    var i:int;
    var c1:W64.t;
    var c2:W64.t;
    var cf:bool;
    
    result <- (W64.of_int 0);
    i <- 0;
    while (i < 32) {
      c1 <- a.[i];
      c2 <- b.[i];
      c1 <- (c1 `^` c2);
      result <- (result `|` c1);
      i <- i + 1;
    }
    cf <- (result = (W64.of_int 0));
    c1 <- (W64.of_int 0);
    c2 <- (W64.of_int 1);
    output <@ sn_cmov (cf, c1, c2);
    return (output);
  }
  
  proc cminusP (p:W64.t Array32.t, x:W64.t Array32.t) : W64.t Array32.t = {
    
    var z:W64.t Array32.t;
    var cf:bool;
    z <- witness;
    z <@ bn_copy (x);
    (cf, z) <@ bn_subc (z, p);
    x <@ bn_cmov (cf, z, x);
    return (x);
  }
  
  proc dcminusP (p:W64.t Array64.t, x:W64.t Array64.t) : W64.t Array64.t = {
    
    var z:W64.t Array64.t;
    var _z:W64.t Array64.t;
    var _p:W64.t Array64.t;
    var cf:bool;
    _p <- witness;
    _z <- witness;
    z <- witness;
    z <@ dbn_copy (x);
    _z <- z;
    _p <- p;
    (cf, z) <@ dbn_subc (_z, _p);
    x <@ dbn_cmov (cf, z, x);
    return (x);
  }
  
  proc daddm (p:W64.t Array64.t, a:W64.t Array64.t, b:W64.t Array64.t) : 
  W64.t Array64.t = {
    
    var _a:W64.t Array64.t;
    var _b:W64.t Array64.t;
    var  _0:bool;
    _a <- witness;
    _b <- witness;
    _a <- a;
    _b <- b;
    ( _0, a) <@ dbn_addc (_a, _b);
    a <@ dcminusP (p, a);
    return (a);
  }
  
  proc bn_expand (x:W64.t Array32.t) : W64.t Array64.t = {
    var aux: int;
    
    var r:W64.t Array64.t;
    var i:int;
    r <- witness;
    i <- 0;
    while (i < 32) {
      r.[i] <- x.[i];
      i <- i + 1;
    }
    aux <- (32 * 2);
    i <- 32;
    while (i < aux) {
      r.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_addm2 (p:W64.t Array32.t, a:W64.t Array32.t, b:W64.t Array32.t) : 
  W64.t Array32.t = {
    
    var  _0:bool;
    
    ( _0, a) <@ bn_addc (a, b);
    a <@ cminusP (p, a);
    return (a);
  }
  
  proc bn_shrink (x:W64.t Array64.t) : W64.t Array32.t = {
    var aux: int;
    
    var r:W64.t Array32.t;
    var i:int;
    r <- witness;
    i <- 0;
    while (i < 32) {
      r.[i] <- x.[i];
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_addm (p:W64.t Array32.t, a:W64.t Array32.t, b:W64.t Array32.t) : 
  W64.t Array32.t = {
    
    var d:W64.t Array32.t;
    var aa:W64.t Array64.t;
    var bb:W64.t Array64.t;
    var pp:W64.t Array64.t;
    var cc:W64.t Array64.t;
    aa <- witness;
    bb <- witness;
    cc <- witness;
    d <- witness;
    pp <- witness;
    aa <@ bn_expand (a);
    bb <@ bn_expand (b);
    pp <@ bn_expand (p);
    cc <@ daddm (pp, aa, bb);
    d <@ bn_shrink (cc);
    return (d);
  }
  
  proc div2 (x:W64.t Array128.t, k:int) : W64.t Array64.t = {
    var aux: int;
    
    var r:W64.t Array64.t;
    var i:int;
    r <- witness;
    aux <- k;
    i <- 0;
    while (i < aux) {
      r.[i] <- x.[((32 * 2) + i)];
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_breduce (r:W64.t Array64.t, a:W64.t Array64.t, p:W64.t Array32.t) : 
  W64.t Array32.t = {
    
    var res_0:W64.t Array32.t;
    var _a:W64.t Array64.t;
    var xr:W64.t Array128.t;
    var xrf:W64.t Array64.t;
    var xrfd:W64.t Array32.t;
    var _b:W64.t Array32.t;
    var xrfn:W64.t Array64.t;
    var _xrfn:W64.t Array64.t;
    var t:W64.t Array64.t;
    var pp:W64.t Array64.t;
    var  _0:W64.t;
    var  _1:bool;
    var  _2:bool;
    var  _3:W64.t;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    _a <- witness;
    _b <- witness;
    _xrfn <- witness;
    pp <- witness;
    res_0 <- witness;
    t <- witness;
    xr <- witness;
    xrf <- witness;
    xrfd <- witness;
    xrfn <- witness;
    _a <- a;
    ( _0,  _1,  _2, xr) <@ dbn_muln (_a, r);
    xrf <@ div2 (xr, (2 * 32));
    xrfd <@ bn_shrink (xrf);
    _b <- xrfd;
    ( _3,  _4,  _5, xrfn) <@ bn_muln (_b, p);
    _a <- a;
    _xrfn <- xrfn;
    ( _6, t) <@ dbn_subc (_a, _xrfn);
    pp <@ bn_expand (p);
    t <@ dcminusP (pp, t);
    res_0 <@ bn_shrink (t);
    return (res_0);
  }
  
  proc bn_breduce_small (r:W64.t Array64.t, a:W64.t Array32.t,
                         p:W64.t Array32.t) : W64.t Array32.t = {
    
    var res_0:W64.t Array32.t;
    var aa:W64.t Array64.t;
    aa <- witness;
    res_0 <- witness;
    aa <@ bn_expand (a);
    res_0 <@ bn_breduce (r, aa, p);
    return (res_0);
  }
  
  proc bn_mulm (r:W64.t Array64.t, p:W64.t Array32.t, a:W64.t Array32.t,
                b:W64.t Array32.t) : W64.t Array32.t = {
    
    var _a:W64.t Array32.t;
    var _b:W64.t Array32.t;
    var _of:bool;
    var _cf:bool;
    var c:W64.t Array64.t;
    var  _0:W64.t;
    _a <- witness;
    _b <- witness;
    c <- witness;
    _a <- a;
    _b <- b;
    ( _0, _of, _cf, c) <@ bn_muln (_a, _b);
    a <@ bn_breduce (r, c, p);
    return (a);
  }
  
  proc bn_expm (r:W64.t Array64.t, m:W64.t Array32.t, x:W64.t Array32.t,
                n:W64.t Array32.t) : W64.t Array32.t = {
    
    var x1:W64.t Array32.t;
    var x2:W64.t Array32.t;
    var x11:W64.t Array32.t;
    var i:W64.t;
    var b:W64.t;
    x1 <- witness;
    x11 <- witness;
    x2 <- witness;
    x1 <@ bn_set1 (x1);
    x2 <@ bn_copy (x);
    x11 <@ bn_copy (x1);
    i <- (W64.of_int (32 * 64));
    b <- (W64.of_int 0);
    
    while (((W64.of_int 0) \ult i)) {
      i <- (i - (W64.of_int 1));
      b <@ ith_bit (n, i);
      (x1, x2) <@ swapr (x1, x2, b);
      x11 <@ bn_copy (x1);
      x1 <@ bn_mulm (r, m, x1, x1);
      x2 <@ bn_mulm (r, m, x11, x2);
      (x1, x2) <@ swapr (x1, x2, b);
    }
    return (x1);
  }
  
  proc bn_rsample (byte_z:W64.t Array32.t) : int * W64.t Array32.t = {
    var aux: W8.t Array256.t;
    
    var i:int;
    var byte_p:W64.t Array32.t;
    var cf:bool;
    var _byte_p:W64.t Array32.t;
    var byte_q:W64.t Array32.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    _byte_p <- witness;
    byte_p <- witness;
    byte_q <- witness;
    i <- 0;
    byte_p <@ bn_set0 (byte_p);
    ( _0, cf,  _1,  _2,  _3,  _4) <- set0_64 ;
    
    while ((! cf)) {
      _byte_p <- byte_p;
      aux <@ SC.randombytes_256 ((Array256.init (fun i_0 => get8
                                 (WArray256.init64 (fun i_0 => _byte_p.[i_0]))
                                 i_0)));
      byte_p <-
      (Array32.init (fun i_0 => get64
      (WArray256.init8 (fun i_0 => aux.[i_0])) i_0));
      byte_q <@ bn_copy (byte_p);
      (cf, byte_q) <@ bn_subc (byte_q, byte_z);
      i <- (i + 1);
    }
    return (i, byte_p);
  }
  
  proc random_bit () : W8.t = {
    
    var r:W8.t;
    var byte_p:W8.t Array1.t;
    var _byte_p:W8.t Array1.t;
    _byte_p <- witness;
    byte_p <- witness;
    _byte_p <- byte_p;
    byte_p <@ SC.randombytes_1 (_byte_p);
    r <- byte_p.[0];
    r <- (r `&` (W8.of_int 1));
    return (r);
  }
  
  proc random_bit_naive () : W8.t = {
    
    var r:W8.t;
    var byte_p:W8.t Array1.t;
    var _byte_p:W8.t Array1.t;
    _byte_p <- witness;
    byte_p <- witness;
    _byte_p <- byte_p;
    byte_p <@ SC.randombytes_1 (_byte_p);
    if ((byte_p.[0] \ult (W8.of_int 128))) {
      r <- (W8.of_int 0);
    } else {
      r <- (W8.of_int 1);
    }
    return (r);
  }
  
  proc uniform_binary_choice (a:W64.t Array32.t, b:W64.t Array32.t) : 
  W64.t Array32.t = {
    
    var r:W8.t;
    var cond:bool;
    
    r <@ random_bit ();
    cond <- (r = (W8.of_int 0));
    a <@ bn_cmov (cond, b, a);
    return (a);
  }
  
  proc commitment_indexed () : int * W64.t Array32.t * W64.t Array32.t = {
    
    var i:int;
    var commitment_0:W64.t Array32.t;
    var secret_power:W64.t Array32.t;
    var exp_order:W64.t Array32.t;
    var group_order:W64.t Array32.t;
    var group_generator:W64.t Array32.t;
    var barrett_parameter:W64.t Array64.t;
    barrett_parameter <- witness;
    commitment_0 <- witness;
    exp_order <- witness;
    group_generator <- witness;
    group_order <- witness;
    secret_power <- witness;
    exp_order <- bn_glob_q;
    group_order <- bn_glob_p;
    group_generator <- bn_glob_g;
    barrett_parameter <- bn_glob_bp;
    (i, secret_power) <@ bn_rsample (exp_order);
    commitment_0 <@ bn_expm (barrett_parameter, group_order, group_generator,
    secret_power);
    return (i, commitment_0, secret_power);
  }
  
  proc commitment () : W64.t Array32.t * W64.t Array32.t = {
    
    var commitment_0:W64.t Array32.t;
    var secret_power:W64.t Array32.t;
    var exp_order:W64.t Array32.t;
    var group_order:W64.t Array32.t;
    var group_generator:W64.t Array32.t;
    var barrett_parameter:W64.t Array64.t;
    var  _0:int;
    barrett_parameter <- witness;
    commitment_0 <- witness;
    exp_order <- witness;
    group_generator <- witness;
    group_order <- witness;
    secret_power <- witness;
    exp_order <- bn_glob_q;
    group_order <- bn_glob_p;
    group_generator <- bn_glob_g;
    barrett_parameter <- bn_glob_bp;
    ( _0, secret_power) <@ bn_rsample (exp_order);
    commitment_0 <@ bn_expm (barrett_parameter, group_order, group_generator,
    secret_power);
    return (commitment_0, secret_power);
  }
  
  proc check_challenge (challenge_0:W64.t Array32.t) : W64.t Array32.t = {
    
    var value_zero:W64.t Array32.t;
    var value_one:W64.t Array32.t;
    var eq1:W64.t;
    var eq2:W64.t;
    var cond:bool;
    value_one <- witness;
    value_zero <- witness;
    value_zero <@ bn_set0 (value_zero);
    value_one <@ bn_set1 (value_one);
    eq1 <@ bn_eq (challenge_0, value_zero);
    eq2 <@ bn_eq (challenge_0, value_one);
    eq1 <- (eq1 `|` eq2);
    cond <- (eq1 = (W64.of_int 0));
    challenge_0 <@ bn_cmov (cond, challenge_0, value_zero);
    return (challenge_0);
  }
  
  proc response (witness0:W64.t Array32.t, secret_power:W64.t Array32.t,
                 challenge_0:W64.t Array32.t) : W64.t Array32.t = {
    
    var response_0:W64.t Array32.t;
    var exp_order:W64.t Array32.t;
    var exp_barrett:W64.t Array64.t;
    var product:W64.t Array32.t;
    exp_barrett <- witness;
    exp_order <- witness;
    product <- witness;
    response_0 <- witness;
    exp_order <- bn_glob_q;
    exp_barrett <- bn_glob_bq;
    challenge_0 <@ bn_breduce_small (exp_barrett, challenge_0, exp_order);
    secret_power <@ bn_breduce_small (exp_barrett, secret_power, exp_order);
    witness0 <@ bn_breduce_small (exp_barrett, witness0, exp_order);
    challenge_0 <@ check_challenge (challenge_0);
    product <@ bn_mulm (exp_barrett, exp_order, challenge_0, witness0);
    response_0 <@ bn_addm (exp_order, secret_power, product);
    return (response_0);
  }
  
  proc challenge () : W64.t Array32.t = {
    
    var challenge_0:W64.t Array32.t;
    var value_zero:W64.t Array32.t;
    var value_one:W64.t Array32.t;
    challenge_0 <- witness;
    value_one <- witness;
    value_zero <- witness;
    value_zero <@ bn_set0 (value_zero);
    value_one <@ bn_set1 (value_one);
    challenge_0 <@ uniform_binary_choice (value_zero, value_one);
    return (challenge_0);
  }
  
  proc verify (statement:W64.t Array32.t, commitment_0:W64.t Array32.t,
               challenge_0:W64.t Array32.t, response_0:W64.t Array32.t) : 
  W64.t = {
    
    var result1:W64.t;
    var exp_order:W64.t Array32.t;
    var exp_barrett:W64.t Array64.t;
    var group_order:W64.t Array32.t;
    var group_barrett:W64.t Array64.t;
    var group_generator:W64.t Array32.t;
    var exp_order2:W64.t Array32.t;
    var tmp:W64.t Array32.t;
    var v1:W64.t Array32.t;
    var v2:W64.t Array32.t;
    var v3:W64.t Array32.t;
    var v4:W64.t Array32.t;
    var result2:W64.t;
    exp_barrett <- witness;
    exp_order <- witness;
    exp_order2 <- witness;
    group_barrett <- witness;
    group_generator <- witness;
    group_order <- witness;
    tmp <- witness;
    v1 <- witness;
    v2 <- witness;
    v3 <- witness;
    v4 <- witness;
    exp_order <- bn_glob_q;
    exp_barrett <- bn_glob_bq;
    group_order <- bn_glob_p;
    group_barrett <- bn_glob_bp;
    group_generator <- bn_glob_g;
    exp_order2 <@ bn_copy (exp_order);
    statement <@ bn_breduce_small (group_barrett, statement, group_order);
    commitment_0 <@ bn_breduce_small (group_barrett, commitment_0,
    group_order);
    challenge_0 <@ bn_breduce_small (exp_barrett, challenge_0, exp_order);
    response_0 <@ bn_breduce_small (exp_barrett, response_0, exp_order);
    tmp <@ bn_expm (group_barrett, group_order, statement, challenge_0);
    v1 <@ bn_mulm (group_barrett, group_order, commitment_0, tmp);
    v2 <@ bn_expm (group_barrett, group_order, group_generator, response_0);
    result1 <@ bn_eq (v1, v2);
    v3 <@ bn_expm (group_barrett, group_order, statement, exp_order2);
    v4 <@ bn_set1 (v4);
    result2 <@ bn_eq (v3, v4);
    result1 <- (result1 `&` result2);
    return (result1);
  }
}.

