(* This file is autogenerated by constants.py *)

require import AllCore Int.
from Jasmin require JModel JBigNum.
require import Ring_ops_spec.
require W64_SchnorrExtract.

module M = W64_SchnorrExtract.M(W64_SchnorrExtract.Syscall).


op p : int = 32317006071311007300338913926423828248817941241140239112842009751400741706634354222619689417363569347117901737909704191754605873209195028853758986185622153212175412514901774520270235796078236248884246189477587641105928646099411723245426622522193230540919037680524235519125679715870117001058055877651038861847280257976054903569732561526167081339361799541336476559160368317896729073178384589680639671900977202194168647225871031411336429319536193471636533209717077448227988588565369208645296636077250268955505928362751121174096972998068410554359584866583291642136218231078990999448652468262416972035911852507045361090559.
        
lemma bn_set_p_correct : phoare[ M.bn_set_p : true ==> W64xN.valR res = p ] = 1%r.
proof.
proc.
wp.
skip.
have H: 32 = 31 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 31 = 30 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 30 = 29 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 29 = 28 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 28 = 27 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 27 = 26 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 26 = 25 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 25 = 24 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 24 = 23 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 23 = 22 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 22 = 21 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 21 = 20 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 20 = 19 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 19 = 18 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 18 = 17 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 17 = 16 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 16 = 15 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 15 = 14 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 14 = 13 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 13 = 12 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 12 = 11 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 11 = 10 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 10 = 9 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 9 = 8 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 8 = 7 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 7 = 6 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 6 = 5 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 5 = 4 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 4 = 3 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 3 = 2 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 2 = 1 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 1 = 0 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
rewrite W64xN.R.bnk0 /p.
trivial.
qed.

op q : int = 16158503035655503650169456963211914124408970620570119556421004875700370853317177111309844708681784673558950868954852095877302936604597514426879493092811076606087706257450887260135117898039118124442123094738793820552964323049705861622713311261096615270459518840262117759562839857935058500529027938825519430923640128988027451784866280763083540669680899770668238279580184158948364536589192294840319835950488601097084323612935515705668214659768096735818266604858538724113994294282684604322648318038625134477752964181375560587048486499034205277179792433291645821068109115539495499724326234131208486017955926253522680545279.
        
lemma bn_set_q_correct : phoare[ M.bn_set_q : true ==> W64xN.valR res = q ] = 1%r.
proof.
proc.
wp.
skip.
have H: 32 = 31 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 31 = 30 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 30 = 29 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 29 = 28 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 28 = 27 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 27 = 26 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 26 = 25 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 25 = 24 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 24 = 23 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 23 = 22 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 22 = 21 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 21 = 20 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 20 = 19 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 19 = 18 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 18 = 17 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 17 = 16 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 16 = 15 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 15 = 14 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 14 = 13 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 13 = 12 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 12 = 11 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 11 = 10 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 10 = 9 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 9 = 8 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 8 = 7 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 7 = 6 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 6 = 5 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 5 = 4 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 4 = 3 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 3 = 2 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 2 = 1 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 1 = 0 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
rewrite W64xN.R.bnk0 /q.
trivial.
qed.

op g : int = 2.
        
lemma bn_set_g_correct : phoare[ M.bn_set_g : true ==> W64xN.valR res = g ] = 1%r.
proof.
proc.
wp.
skip.
have H: 32 = 31 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 31 = 30 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 30 = 29 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 29 = 28 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 28 = 27 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 27 = 26 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 26 = 25 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 25 = 24 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 24 = 23 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 23 = 22 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 22 = 21 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 21 = 20 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 20 = 19 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 19 = 18 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 18 = 17 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 17 = 16 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 16 = 15 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 15 = 14 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 14 = 13 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 13 = 12 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 12 = 11 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 11 = 10 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 10 = 9 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 9 = 8 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 8 = 7 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 7 = 6 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 6 = 5 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 5 = 4 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 4 = 3 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 3 = 2 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 2 = 1 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 1 = 0 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
rewrite W64xN.R.bnk0 /g.
trivial.
qed.

op bp : int = 32317006071311007301090839450916075672074637894498330470309491614874605269258845429066617750438611497217172998255766216223761011478474532650974905473458381524348224983452534238842699055706528839316900073176359409123413739445397952234623184300460154670470987008412185029124584489601900670931121854398190604800292822877845957165654247519063010445688374293905515743037557007239230573090162415731314434935337651887720640264611889321352234483385341531370885728478742938129783934088697644527630028295616871380503535956364143710134154492766231832072494607343336005619107670188720508364918065676485338559326165037076233303652.
        
lemma bn_set_bp_correct : phoare[ M.bn_set_bp : true ==> W64x2N.valR res = bp ] = 1%r.
proof.
proc.
wp.
skip.
have H: 64 = 63 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 63 = 62 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 62 = 61 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 61 = 60 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 60 = 59 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 59 = 58 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 58 = 57 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 57 = 56 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 56 = 55 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 55 = 54 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 54 = 53 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 53 = 52 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 52 = 51 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 51 = 50 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 50 = 49 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 49 = 48 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 48 = 47 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 47 = 46 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 46 = 45 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 45 = 44 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 44 = 43 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 43 = 42 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 42 = 41 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 41 = 40 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 40 = 39 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 39 = 38 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 38 = 37 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 37 = 36 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 36 = 35 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 35 = 34 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 34 = 33 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 33 = 32 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 32 = 31 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 31 = 30 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 30 = 29 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 29 = 28 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 28 = 27 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 27 = 26 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 26 = 25 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 25 = 24 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 24 = 23 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 23 = 22 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 22 = 21 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 21 = 20 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 20 = 19 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 19 = 18 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 18 = 17 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 17 = 16 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 16 = 15 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 15 = 14 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 14 = 13 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 13 = 12 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 12 = 11 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 11 = 10 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 10 = 9 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 9 = 8 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 8 = 7 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 7 = 6 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 6 = 5 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 5 = 4 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 4 = 3 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 3 = 2 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 2 = 1 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 1 = 0 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
rewrite W64x2N.R.bnk0 /bp.
trivial.
qed.

op bq : int = 64634012142622014602181678901832151344149275788996660940618983229749210538517690858133235500877222994434345996511532432447522022956949065301949810946916763048696449966905068477685398111413057678633800146352718818246827478890795904469246368600920309340941974016824370058249168979203801341862243708796381209600585645755691914331308495038126020891376748587811031486075114014478461146180324831462628869870675303775441280529223778642704468966770683062741771456957485876259567868177395289055260056591233742761007071912728287420268308985532463664144989214686672011238215340377441016729836131352970677118652330074152466607306.
        
lemma bn_set_bq_correct : phoare[ M.bn_set_bq : true ==> W64x2N.valR res = bq ] = 1%r.
proof.
proc.
wp.
skip.
have H: 64 = 63 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 63 = 62 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 62 = 61 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 61 = 60 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 60 = 59 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 59 = 58 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 58 = 57 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 57 = 56 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 56 = 55 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 55 = 54 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 54 = 53 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 53 = 52 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 52 = 51 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 51 = 50 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 50 = 49 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 49 = 48 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 48 = 47 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 47 = 46 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 46 = 45 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 45 = 44 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 44 = 43 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 43 = 42 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 42 = 41 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 41 = 40 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 40 = 39 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 39 = 38 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 38 = 37 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 37 = 36 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 36 = 35 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 35 = 34 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 34 = 33 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 33 = 32 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 32 = 31 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 31 = 30 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 30 = 29 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 29 = 28 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 28 = 27 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 27 = 26 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 26 = 25 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 25 = 24 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 24 = 23 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 23 = 22 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 22 = 21 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 21 = 20 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 20 = 19 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 19 = 18 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 18 = 17 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 17 = 16 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 16 = 15 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 15 = 14 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 14 = 13 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 13 = 12 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 12 = 11 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 11 = 10 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 10 = 9 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 9 = 8 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 8 = 7 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 7 = 6 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 6 = 5 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 5 = 4 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 4 = 3 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 3 = 2 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 2 = 1 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 1 = 0 + 1. by trivial. rewrite H. clear H. rewrite W64x2N.R.bnkS; 1: trivial. rewrite /dig. simplify.
rewrite W64x2N.R.bnk0 /bq.
trivial.
qed.

op ex_w : int = 13562074942232698298179099715097584669743616762010001864533299997056731796296371039510377235748195022542024618898643826330807122904488341755722122148636711055263632491105526304501244287463084252119549757055178218173913102047978750988651708456497584278036673201887047222348131014704171051451256673650666629515213300997703806314646378361492063336814804438811067630413966929471013613663155038542386255423974557632334836982678865780618968772883384376382351839231415319749576574591601796022013741069051949170875806063999540180799183260929359622774470129812372649035895482951427131973688235088596275593114503240007521869714.
        
lemma bn_set_ex_w_correct : phoare[ M.bn_set_ex_w : true ==> W64xN.valR res = ex_w ] = 1%r.
proof.
proc.
wp.
skip.
have H: 32 = 31 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 31 = 30 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 30 = 29 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 29 = 28 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 28 = 27 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 27 = 26 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 26 = 25 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 25 = 24 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 24 = 23 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 23 = 22 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 22 = 21 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 21 = 20 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 20 = 19 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 19 = 18 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 18 = 17 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 17 = 16 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 16 = 15 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 15 = 14 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 14 = 13 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 13 = 12 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 12 = 11 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 11 = 10 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 10 = 9 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 9 = 8 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 8 = 7 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 7 = 6 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 6 = 5 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 5 = 4 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 4 = 3 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 3 = 2 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 2 = 1 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 1 = 0 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
rewrite W64xN.R.bnk0 /ex_w.
trivial.
qed.

op ex_s : int = 17448105564697743235596200779905060886140102301589836974870836993584491604725980549786805891101128905392483202643612799832388966813381742461470387725541672947131967359215271192071104242818534618159207393267571342157931998220631680702975123830881219215736803556617335999518588338804520261434697814567055925964501568025260046973303129822355476335079189622119622697775023077959076699091477716959124081583302657743773751866109946017718536963183669118715561381915446592752262392261234321714414999399944719644372451141711218530146601499574810057491831816916583316009757172316828411111743676667730848241028554193006466552845.
        
lemma bn_set_ex_s_correct : phoare[ M.bn_set_ex_s : true ==> W64xN.valR res = ex_s ] = 1%r.
proof.
proc.
wp.
skip.
have H: 32 = 31 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 31 = 30 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 30 = 29 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 29 = 28 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 28 = 27 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 27 = 26 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 26 = 25 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 25 = 24 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 24 = 23 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 23 = 22 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 22 = 21 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 21 = 20 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 20 = 19 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 19 = 18 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 18 = 17 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 17 = 16 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 16 = 15 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 15 = 14 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 14 = 13 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 13 = 12 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 12 = 11 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 11 = 10 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 10 = 9 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 9 = 8 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 8 = 7 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 7 = 6 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 6 = 5 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 5 = 4 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 4 = 3 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 3 = 2 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 2 = 1 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
have H: 1 = 0 + 1. by trivial. rewrite H. clear H. rewrite W64xN.R.bnkS; 1: trivial. rewrite /dig. simplify.
rewrite W64xN.R.bnk0 /ex_s.
trivial.
qed.
