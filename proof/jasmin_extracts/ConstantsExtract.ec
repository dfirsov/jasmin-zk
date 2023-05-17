require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

require import Array32 Array64.
require import WArray256 WArray512.



module M = {
  proc bn_set_p (p:W64.t Array32.t) : W64.t Array32.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 18446744073709551615);
    p.[0] <- tmp;
    tmp <- (W64.of_int 1545454141666273896);
    p.[1] <- tmp;
    tmp <- (W64.of_int 1572361106993317136);
    p.[2] <- tmp;
    tmp <- (W64.of_int 4149303432552213221);
    p.[3] <- tmp;
    tmp <- (W64.of_int 16009113560346531608);
    p.[4] <- tmp;
    tmp <- (W64.of_int 13097978378517762761);
    p.[5] <- tmp;
    tmp <- (W64.of_int 11180049335738409615);
    p.[6] <- tmp;
    tmp <- (W64.of_int 16401677924195796483);
    p.[7] <- tmp;
    tmp <- (W64.of_int 3643515754058796603);
    p.[8] <- tmp;
    tmp <- (W64.of_int 17398650045445185916);
    p.[9] <- tmp;
    tmp <- (W64.of_int 7425368496004700164);
    p.[10] <- tmp;
    tmp <- (W64.of_int 11445099139962410605);
    p.[11] <- tmp;
    tmp <- (W64.of_int 2045464732017971899);
    p.[12] <- tmp;
    tmp <- (W64.of_int 9468076200223288726);
    p.[13] <- tmp;
    tmp <- (W64.of_int 7572309818504171359);
    p.[14] <- tmp;
    tmp <- (W64.of_int 11014195235928789914);
    p.[15] <- tmp;
    tmp <- (W64.of_int 13979310375781515013);
    p.[16] <- tmp;
    tmp <- (W64.of_int 5271575865889938237);
    p.[17] <- tmp;
    tmp <- (W64.of_int 12582815541414797286);
    p.[18] <- tmp;
    tmp <- (W64.of_int 17165588707022577573);
    p.[19] <- tmp;
    tmp <- (W64.of_int 864511594326308845);
    p.[20] <- tmp;
    tmp <- (W64.of_int 17603518614767922539);
    p.[21] <- tmp;
    tmp <- (W64.of_int 16466767132611215046);
    p.[22] <- tmp;
    tmp <- (W64.of_int 5755940542857986629);
    p.[23] <- tmp;
    tmp <- (W64.of_int 3470879405153129527);
    p.[24] <- tmp;
    tmp <- (W64.of_int 17263733006627652379);
    p.[25] <- tmp;
    tmp <- (W64.of_int 5857503583518590173);
    p.[26] <- tmp;
    tmp <- (W64.of_int 147421033984662306);
    p.[27] <- tmp;
    tmp <- (W64.of_int 2955010104097229940);
    p.[28] <- tmp;
    tmp <- (W64.of_int 14179128828124470481);
    p.[29] <- tmp;
    tmp <- (W64.of_int 14488038916154245684);
    p.[30] <- tmp;
    tmp <- (W64.of_int 18446744073709551615);
    p.[31] <- tmp;
    return (p);
  }
  
  proc bn_set_q (q:W64.t Array32.t) : W64.t Array32.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 9223372036854775807);
    q.[0] <- tmp;
    tmp <- (W64.of_int 772727070833136948);
    q.[1] <- tmp;
    tmp <- (W64.of_int 10009552590351434376);
    q.[2] <- tmp;
    tmp <- (W64.of_int 2074651716276106610);
    q.[3] <- tmp;
    tmp <- (W64.of_int 17227928817028041612);
    q.[4] <- tmp;
    tmp <- (W64.of_int 15772361226113657188);
    q.[5] <- tmp;
    tmp <- (W64.of_int 14813396704723980615);
    q.[6] <- tmp;
    tmp <- (W64.of_int 17424210998952674049);
    q.[7] <- tmp;
    tmp <- (W64.of_int 1821757877029398301);
    q.[8] <- tmp;
    tmp <- (W64.of_int 8699325022722592958);
    q.[9] <- tmp;
    tmp <- (W64.of_int 12936056284857125890);
    q.[10] <- tmp;
    tmp <- (W64.of_int 14945921606835981110);
    q.[11] <- tmp;
    tmp <- (W64.of_int 1022732366008985949);
    q.[12] <- tmp;
    tmp <- (W64.of_int 13957410136966420171);
    q.[13] <- tmp;
    tmp <- (W64.of_int 3786154909252085679);
    q.[14] <- tmp;
    tmp <- (W64.of_int 14730469654819170765);
    q.[15] <- tmp;
    tmp <- (W64.of_int 16213027224745533314);
    q.[16] <- tmp;
    tmp <- (W64.of_int 2635787932944969118);
    q.[17] <- tmp;
    tmp <- (W64.of_int 15514779807562174451);
    q.[18] <- tmp;
    tmp <- (W64.of_int 17806166390366064594);
    q.[19] <- tmp;
    tmp <- (W64.of_int 9655627834017930230);
    q.[20] <- tmp;
    tmp <- (W64.of_int 8801759307383961269);
    q.[21] <- tmp;
    tmp <- (W64.of_int 17456755603160383331);
    q.[22] <- tmp;
    tmp <- (W64.of_int 12101342308283769122);
    q.[23] <- tmp;
    tmp <- (W64.of_int 10958811739431340571);
    q.[24] <- tmp;
    tmp <- (W64.of_int 17855238540168601997);
    q.[25] <- tmp;
    tmp <- (W64.of_int 2928751791759295086);
    q.[26] <- tmp;
    tmp <- (W64.of_int 73710516992331153);
    q.[27] <- tmp;
    tmp <- (W64.of_int 10700877088903390778);
    q.[28] <- tmp;
    tmp <- (W64.of_int 7089564414062235240);
    q.[29] <- tmp;
    tmp <- (W64.of_int 16467391494931898650);
    q.[30] <- tmp;
    tmp <- (W64.of_int 9223372036854775807);
    q.[31] <- tmp;
    return (q);
  }
  
  proc bn_set_g (g:W64.t Array32.t) : W64.t Array32.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 2);
    g.[0] <- tmp;
    tmp <- (W64.of_int 0);
    g.[1] <- tmp;
    tmp <- (W64.of_int 0);
    g.[2] <- tmp;
    tmp <- (W64.of_int 0);
    g.[3] <- tmp;
    tmp <- (W64.of_int 0);
    g.[4] <- tmp;
    tmp <- (W64.of_int 0);
    g.[5] <- tmp;
    tmp <- (W64.of_int 0);
    g.[6] <- tmp;
    tmp <- (W64.of_int 0);
    g.[7] <- tmp;
    tmp <- (W64.of_int 0);
    g.[8] <- tmp;
    tmp <- (W64.of_int 0);
    g.[9] <- tmp;
    tmp <- (W64.of_int 0);
    g.[10] <- tmp;
    tmp <- (W64.of_int 0);
    g.[11] <- tmp;
    tmp <- (W64.of_int 0);
    g.[12] <- tmp;
    tmp <- (W64.of_int 0);
    g.[13] <- tmp;
    tmp <- (W64.of_int 0);
    g.[14] <- tmp;
    tmp <- (W64.of_int 0);
    g.[15] <- tmp;
    tmp <- (W64.of_int 0);
    g.[16] <- tmp;
    tmp <- (W64.of_int 0);
    g.[17] <- tmp;
    tmp <- (W64.of_int 0);
    g.[18] <- tmp;
    tmp <- (W64.of_int 0);
    g.[19] <- tmp;
    tmp <- (W64.of_int 0);
    g.[20] <- tmp;
    tmp <- (W64.of_int 0);
    g.[21] <- tmp;
    tmp <- (W64.of_int 0);
    g.[22] <- tmp;
    tmp <- (W64.of_int 0);
    g.[23] <- tmp;
    tmp <- (W64.of_int 0);
    g.[24] <- tmp;
    tmp <- (W64.of_int 0);
    g.[25] <- tmp;
    tmp <- (W64.of_int 0);
    g.[26] <- tmp;
    tmp <- (W64.of_int 0);
    g.[27] <- tmp;
    tmp <- (W64.of_int 0);
    g.[28] <- tmp;
    tmp <- (W64.of_int 0);
    g.[29] <- tmp;
    tmp <- (W64.of_int 0);
    g.[30] <- tmp;
    tmp <- (W64.of_int 0);
    g.[31] <- tmp;
    return (g);
  }
  
  proc bn_set_bp (bp:W64.t Array64.t) : W64.t Array64.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 5147934117528057444);
    bp.[0] <- tmp;
    tmp <- (W64.of_int 10407519109700454935);
    bp.[1] <- tmp;
    tmp <- (W64.of_int 16583539182667929086);
    bp.[2] <- tmp;
    tmp <- (W64.of_int 1492440688257385106);
    bp.[3] <- tmp;
    tmp <- (W64.of_int 10066832793016919264);
    bp.[4] <- tmp;
    tmp <- (W64.of_int 11339370997029172680);
    bp.[5] <- tmp;
    tmp <- (W64.of_int 4675869585930362320);
    bp.[6] <- tmp;
    tmp <- (W64.of_int 16918262430485393797);
    bp.[7] <- tmp;
    tmp <- (W64.of_int 13728506818757698388);
    bp.[8] <- tmp;
    tmp <- (W64.of_int 13772906965603576095);
    bp.[9] <- tmp;
    tmp <- (W64.of_int 3156528908874584491);
    bp.[10] <- tmp;
    tmp <- (W64.of_int 1231154113365505725);
    bp.[11] <- tmp;
    tmp <- (W64.of_int 17718551243857757924);
    bp.[12] <- tmp;
    tmp <- (W64.of_int 16667871902385732453);
    bp.[13] <- tmp;
    tmp <- (W64.of_int 8054682061035653787);
    bp.[14] <- tmp;
    tmp <- (W64.of_int 12145378267626961546);
    bp.[15] <- tmp;
    tmp <- (W64.of_int 14175206944198899882);
    bp.[16] <- tmp;
    tmp <- (W64.of_int 1872412834642272634);
    bp.[17] <- tmp;
    tmp <- (W64.of_int 10293871819984421175);
    bp.[18] <- tmp;
    tmp <- (W64.of_int 8837694422794646872);
    bp.[19] <- tmp;
    tmp <- (W64.of_int 9711310516503218385);
    bp.[20] <- tmp;
    tmp <- (W64.of_int 6633261091277544380);
    bp.[21] <- tmp;
    tmp <- (W64.of_int 6086011487233213371);
    bp.[22] <- tmp;
    tmp <- (W64.of_int 14468328207451868826);
    bp.[23] <- tmp;
    tmp <- (W64.of_int 15312291203922875661);
    bp.[24] <- tmp;
    tmp <- (W64.of_int 10847478293144797667);
    bp.[25] <- tmp;
    tmp <- (W64.of_int 12824558171927804903);
    bp.[26] <- tmp;
    tmp <- (W64.of_int 7264247675481435729);
    bp.[27] <- tmp;
    tmp <- (W64.of_int 12023220503046567441);
    bp.[28] <- tmp;
    tmp <- (W64.of_int 5117160642964443543);
    bp.[29] <- tmp;
    tmp <- (W64.of_int 3958705157555305931);
    bp.[30] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[31] <- tmp;
    tmp <- (W64.of_int 1);
    bp.[32] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[33] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[34] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[35] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[36] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[37] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[38] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[39] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[40] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[41] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[42] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[43] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[44] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[45] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[46] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[47] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[48] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[49] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[50] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[51] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[52] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[53] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[54] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[55] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[56] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[57] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[58] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[59] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[60] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[61] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[62] <- tmp;
    tmp <- (W64.of_int 0);
    bp.[63] <- tmp;
    return (bp);
  }
  
  proc bn_set_bq (bq:W64.t Array64.t) : W64.t Array64.t = {
    
    var tmp:W64.t;
    
    tmp <- (W64.of_int 10295868235056114890);
    bq.[0] <- tmp;
    tmp <- (W64.of_int 2368294145691358254);
    bq.[1] <- tmp;
    tmp <- (W64.of_int 14720334291626306557);
    bq.[2] <- tmp;
    tmp <- (W64.of_int 2984881376514770213);
    bq.[3] <- tmp;
    tmp <- (W64.of_int 1686921512324286912);
    bq.[4] <- tmp;
    tmp <- (W64.of_int 4231997920348793745);
    bq.[5] <- tmp;
    tmp <- (W64.of_int 9351739171860724641);
    bq.[6] <- tmp;
    tmp <- (W64.of_int 15389780787261235978);
    bq.[7] <- tmp;
    tmp <- (W64.of_int 9010269563805845161);
    bq.[8] <- tmp;
    tmp <- (W64.of_int 9099069857497600575);
    bq.[9] <- tmp;
    tmp <- (W64.of_int 6313057817749168983);
    bq.[10] <- tmp;
    tmp <- (W64.of_int 2462308226731011450);
    bq.[11] <- tmp;
    tmp <- (W64.of_int 16990358414005964232);
    bq.[12] <- tmp;
    tmp <- (W64.of_int 14888999731061913291);
    bq.[13] <- tmp;
    tmp <- (W64.of_int 16109364122071307575);
    bq.[14] <- tmp;
    tmp <- (W64.of_int 5844012461544371476);
    bq.[15] <- tmp;
    tmp <- (W64.of_int 9903669814688248149);
    bq.[16] <- tmp;
    tmp <- (W64.of_int 3744825669284545269);
    bq.[17] <- tmp;
    tmp <- (W64.of_int 2140999566259290734);
    bq.[18] <- tmp;
    tmp <- (W64.of_int 17675388845589293745);
    bq.[19] <- tmp;
    tmp <- (W64.of_int 975876959296885154);
    bq.[20] <- tmp;
    tmp <- (W64.of_int 13266522182555088761);
    bq.[21] <- tmp;
    tmp <- (W64.of_int 12172022974466426742);
    bq.[22] <- tmp;
    tmp <- (W64.of_int 10489912341194186036);
    bq.[23] <- tmp;
    tmp <- (W64.of_int 12177838334136199707);
    bq.[24] <- tmp;
    tmp <- (W64.of_int 3248212512580043719);
    bq.[25] <- tmp;
    tmp <- (W64.of_int 7202372270146058191);
    bq.[26] <- tmp;
    tmp <- (W64.of_int 14528495350962871459);
    bq.[27] <- tmp;
    tmp <- (W64.of_int 5599696932383583266);
    bq.[28] <- tmp;
    tmp <- (W64.of_int 10234321285928887087);
    bq.[29] <- tmp;
    tmp <- (W64.of_int 7917410315110611862);
    bq.[30] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[31] <- tmp;
    tmp <- (W64.of_int 2);
    bq.[32] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[33] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[34] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[35] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[36] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[37] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[38] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[39] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[40] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[41] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[42] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[43] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[44] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[45] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[46] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[47] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[48] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[49] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[50] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[51] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[52] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[53] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[54] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[55] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[56] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[57] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[58] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[59] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[60] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[61] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[62] <- tmp;
    tmp <- (W64.of_int 0);
    bq.[63] <- tmp;
    return (bq);
  }
}.

